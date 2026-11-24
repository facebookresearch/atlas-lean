/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Algebra.BigOperators.Field

/-! # Standard-simplex radial boundary core

For `n : ℕ`, work with `Convexity.StdSimplex ℝ (Fin (n + 1))` and its barycenter.
Define the minimum coordinate and the normalized radial projection

`r(x)_i = (x_i - min_j x_j) / (1 - (n + 1) * min_j x_j)`

on the complement of the barycenter. The packet proves denominator
positivity, membership in the simplex, a zero output coordinate,
continuity of the radial map, and identity on points that already have
a zero coordinate. It provides `radialCoord`, `radialMap`,
`radialMap_weights`, `radial_has_zero`,
`exists_radialMap_weights_eq_zero`, `continuous_radialMap`,
`radial_id_of_has_zero`, `radialMap_eq_of_has_zero`,
`radialMap_ne_bary`, `radialMapComplement`, `homotopyCoord`,
`homotopyMem`, `homotopyPoint`, `homotopyPoint_weights`,
`homotopyPoint_zero`, `homotopyPoint_one`,
`homotopyPoint_eq_of_has_zero`, `homotopy_ne_bary`,
`continuous_homotopyFun`, `radialHomotopy`, and `radialHomotopyRel`.

Nonclaims: no map into a realized boundary, no global chart, no
fibration or model-category result. The immediate consumer is the
realized-boundary radial retraction via the zero-coordinate bridge.
-/

@[expose] public section

open scoped BigOperators unitInterval

namespace StdSimplexRadialBoundary

variable (n : ℕ)

/-- Minimum coordinate on the standard simplex. -/
noncomputable def radMin (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℝ :=
  Finset.univ.inf' ⟨0, Finset.mem_univ (0 : Fin (n + 1))⟩ (fun i => x.weights i)

/-- The minimum is below every coordinate. -/
theorem radMin_le (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    radMin n x ≤ x.weights i := by
  unfold radMin
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The minimum is attained. -/
theorem exists_radMin_eq (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∃ j, radMin n x = x.weights j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf'
    (⟨0, Finset.mem_univ (0 : Fin (n + 1))⟩ : Finset.univ.Nonempty)
    (fun i => x.weights i)
  exact ⟨j, hj⟩

/-- The minimum is nonnegative. -/
theorem radMin_nonneg (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    0 ≤ radMin n x := by
  obtain ⟨j, hj⟩ := exists_radMin_eq n x
  rw [hj]
  exact x.weights_nonneg j

/-- The minimum coordinate is continuous. -/
theorem continuous_radMin : Continuous (radMin n) := by
  unfold radMin
  exact Continuous.finset_inf'_apply _ (fun i _ =>
    Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i)

/-- Radial denominator `1 - (n + 1) * min`. -/
noncomputable def radDenom (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℝ :=
  1 - ((n + 1 : ℕ) : ℝ) * radMin n x

/-- The denominator is continuous. -/
theorem continuous_radDenom : Continuous (radDenom n) :=
  continuous_const.sub (continuous_const.mul (continuous_radMin n))

/-- The denominator is nonnegative. -/
theorem radDenom_nonneg (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    0 ≤ radDenom n x := by
  unfold radDenom
  have h_le : ∀ i ∈ Finset.univ, radMin n x ≤ x.weights i :=
    fun i _ => radMin_le n x i
  have h_sum := Finset.card_nsmul_le_sum Finset.univ (fun i => x.weights i)
    (radMin n x) h_le
  have h_eq : ∑ i, x.weights i = 1 := x.total_of_fintype
  have hcard : Finset.univ.card (α := Fin (n + 1)) = n + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard, nsmul_eq_mul] at h_sum
  linarith

/-- On the complement of the barycenter the denominator is positive. -/
theorem radDenom_pos_of_ne_bary (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) : 0 < radDenom n x := by
  have h_nonneg := radDenom_nonneg n x
  rcases lt_or_eq_of_le h_nonneg with hpos | heq
  · exact hpos
  · exfalso
    apply hx
    have h_zero : radDenom n x = 0 := heq.symm
    have hc_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos n)
    have hc_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hc_pos
    have hcm : ((n + 1 : ℕ) : ℝ) * radMin n x = 1 := by
      unfold radDenom at h_zero
      linarith
    have hm_eq : radMin n x = 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [eq_div_iff hc_ne, mul_comm]
      exact hcm
    have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    have h_all : ∀ i, x.weights i = radMin n x := by
      intro i
      apply le_antisymm
      · have h_erase_card : (Finset.univ.erase i).card = n := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
        have h_le_erase :
            ∀ j ∈ Finset.univ.erase i, radMin n x ≤ x.weights j :=
          fun j _ => radMin_le n x j
        have h_sum_erase := Finset.card_nsmul_le_sum
          (Finset.univ.erase i) (fun j => x.weights j) (radMin n x) h_le_erase
        rw [h_erase_card, nsmul_eq_mul] at h_sum_erase
        have h_split := Finset.univ.add_sum_erase (fun j => x.weights j)
          (Finset.mem_univ i)
        have h_sum_one : ∑ j, x.weights j = 1 := x.total_of_fintype
        rw [h_cast] at hcm
        linarith
      · exact radMin_le n x i
    have h_min_inv : radMin n x = (((n + 1 : ℕ) : ℝ))⁻¹ := by
      rw [hm_eq, one_div]
    have h_bary : ∀ i,
        (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin (n + 1))).weights i =
          radMin n x := by
      intro i
      rw [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin]
      exact h_min_inv.symm
    apply Convexity.StdSimplex.ext
    ext i
    have h1 : x.weights i = radMin n x := h_all i
    have h2 : (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin (n + 1))).weights i = radMin n x := h_bary i
    change x.weights i = (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin (n + 1))).weights i
    rw [h1, h2]

/-- Radial coordinate before packaging as a simplex point. -/
noncomputable def radialCoord (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : ℝ :=
  (x.weights i - radMin n x) / radDenom n x

/-- The radial coordinates satisfy the simplex nonnegativity and total-weight laws
off the barycenter. -/
theorem radialMem (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    (∀ i, 0 ≤ radialCoord n x i) ∧ (∑ i, radialCoord n x i = 1) := by
  have h_pos := radDenom_pos_of_ne_bary n x hx
  have h_ne : radDenom n x ≠ 0 := ne_of_gt h_pos
  refine ⟨fun i => div_nonneg ?_ (le_of_lt h_pos), ?_⟩
  · exact sub_nonneg.mpr (radMin_le n x i)
  · simp only [radialCoord]
    rw [← Finset.sum_div]
    have h_num : ∑ i, (x.weights i - radMin n x) = radDenom n x := by
      rw [Finset.sum_sub_distrib, x.total_of_fintype,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rfl
    rw [h_num, div_self h_ne]

/-- Radial projection on the barycenter complement. -/
noncomputable def radialMap
    (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter}) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i => radialCoord n q.val i)
  nonneg m := by
    have h := (radialMem n q.val q.property).1 m
    simpa using h
  total := by
    have h := (radialMem n q.val q.property).2
    simpa [Finsupp.sum_fintype] using h

/-- Characteristic weights of the bundled radial map. -/
@[simp]
theorem radialMap_weights
    (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter}) (i : Fin (n + 1)) :
    (radialMap n q).weights i = radialCoord n q.val i := by
  simp [radialMap]

/-- Every radial image has a zero coordinate. -/
theorem radial_has_zero (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∃ i, radialCoord n x i = 0 := by
  obtain ⟨j, hj⟩ := exists_radMin_eq n x
  refine ⟨j, ?_⟩
  unfold radialCoord
  have h0 : x.weights j - radMin n x = 0 := sub_eq_zero.mpr hj.symm
  rw [h0, zero_div]

/-- Bundled radial images have a zero weight. -/
theorem exists_radialMap_weights_eq_zero
    (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter}) :
    ∃ i, (radialMap n q).weights i = 0 := by
  obtain ⟨j, hj⟩ := radial_has_zero n q.val
  exact ⟨j, by rw [radialMap_weights]; exact hj⟩

/-- The radial map is continuous. -/
theorem continuous_radialMap : Continuous (radialMap n) := by
  have hEmb := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  rw [hEmb.continuous_iff]
  apply continuous_pi
  intro i
  have h_eq : (fun q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter} => (radialMap n q).weights i) =
      (fun q => radialCoord n q.val i) := by
    funext q
    exact radialMap_weights n q i
  simp only [Function.comp_apply]
  rw [h_eq]
  apply Continuous.div
  · apply Continuous.sub
    · exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      continuous_subtype_val)
    · exact (continuous_radMin n).comp continuous_subtype_val
  · exact (continuous_radDenom n).comp continuous_subtype_val
  · intro q
    exact ne_of_gt (radDenom_pos_of_ne_bary n q.val q.property)

/-- Points with a zero coordinate are fixed. -/
theorem radial_id_of_has_zero (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (k : Fin (n + 1)) (hk : x.weights k = 0) (i : Fin (n + 1)) :
    radialCoord n x i = x.weights i := by
  have h_le_zero : radMin n x ≤ 0 := by
    have h := radMin_le n x k
    rw [hk] at h
    exact h
  have h_min_zero : radMin n x = 0 :=
    le_antisymm h_le_zero (radMin_nonneg n x)
  have h_denom_one : radDenom n x = 1 := by
    unfold radDenom
    rw [h_min_zero, mul_zero, sub_zero]
  unfold radialCoord
  rw [h_min_zero, h_denom_one, sub_zero, div_one]

/-- Bundled radial maps fix points with a zero weight. -/
theorem radialMap_eq_of_has_zero
    (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter})
    (k : Fin (n + 1)) (hk : q.val.weights k = 0) :
    radialMap n q = q.val := by
  apply Convexity.StdSimplex.ext
  ext i
  rw [radialMap_weights]
  exact radial_id_of_has_zero n q.val k hk i

/-- Straight-line homotopy coordinate from the identity to the radial map. -/
noncomputable def homotopyCoord (t : I) (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : ℝ :=
  (1 - (t : ℝ)) * x.weights i + (t : ℝ) * radialCoord n x i
/-- The straight-line homotopy coordinates satisfy the `Convexity.StdSimplex`
nonnegativity and total-weight laws off the barycenter. -/
theorem homotopyMem (t : I) (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    (∀ i, 0 ≤ homotopyCoord n t x i) ∧ (∑ i, homotopyCoord n t x i = 1) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have h1t : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr ht1
  have h_rad_nonneg := (radialMem n x hx).1
  have h_sum_r : ∑ i, radialCoord n x i = 1 := (radialMem n x hx).2
  refine ⟨fun i => add_nonneg (mul_nonneg h1t (x.weights_nonneg i))
    (mul_nonneg ht0 (h_rad_nonneg i)), ?_⟩
  unfold homotopyCoord
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    x.total_of_fintype, h_sum_r]
  ring

/-- Straight-line homotopy point in the simplex. -/
noncomputable def homotopyPoint (t : I) (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i => homotopyCoord n t x i)
  nonneg m := by
    have h := (homotopyMem n t x hx).1 m
    simpa using h
  total := by
    have h := (homotopyMem n t x hx).2
    simpa [Finsupp.sum_fintype] using h

/-- Characteristic weights of the homotopy point. -/
@[simp]
theorem homotopyPoint_weights (t : I) (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) (i : Fin (n + 1)) :
    (homotopyPoint n t x hx).weights i = homotopyCoord n t x i := by
  simp [homotopyPoint]

/-- The homotopy starts at the identity. -/
@[simp]
theorem homotopyPoint_zero (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    homotopyPoint n 0 x hx = x := by
  apply Convexity.StdSimplex.ext
  ext i
  rw [homotopyPoint_weights]
  simp [homotopyCoord]

/-- The homotopy ends at the bundled radial map. -/
@[simp]
theorem homotopyPoint_one (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    homotopyPoint n 1 x hx = radialMap n ⟨x, hx⟩ := by
  apply Convexity.StdSimplex.ext
  ext i
  rw [homotopyPoint_weights, radialMap_weights]
  simp [homotopyCoord]

/-- The homotopy fixes points with a zero weight. -/
theorem homotopyPoint_eq_of_has_zero (t : I)
    (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter})
    (k : Fin (n + 1)) (hk : q.val.weights k = 0) :
    homotopyPoint n t q.val q.property = q.val := by
  apply Convexity.StdSimplex.ext
  ext i
  rw [homotopyPoint_weights]
  have hr : radialCoord n q.val i = q.val.weights i :=
    radial_id_of_has_zero n q.val k hk i
  unfold homotopyCoord
  rw [hr]
  ring

/-- The straight-line homotopy avoids the barycenter. -/
theorem homotopy_ne_bary (t : I) (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    homotopyPoint n t x hx ≠ Convexity.StdSimplex.barycenter := by
  intro h_eq
  obtain ⟨j, hj⟩ := exists_radMin_eq n x
  have h_pos := radDenom_pos_of_ne_bary n x hx
  have hr_j : radialCoord n x j = 0 := by
    unfold radialCoord
    have h0 : x.weights j - radMin n x = 0 := sub_eq_zero.mpr hj.symm
    rw [h0, zero_div]
  have hHj : homotopyCoord n t x j = (1 - (t : ℝ)) * radMin n x := by
    unfold homotopyCoord
    rw [hj.symm, hr_j, mul_zero, add_zero]
  have h_eq_j : (1 - (t : ℝ)) * radMin n x = ((((n + 1 : ℕ)) : ℝ))⁻¹ := by
    have h0 := congrArg (fun y : Convexity.StdSimplex ℝ (Fin (n + 1)) => y.weights j) h_eq
    have h_show : (homotopyPoint n t x hx).weights j = homotopyCoord n t x j :=
      homotopyPoint_weights n t x hx j
    rw [h_show, hHj, Convexity.StdSimplex.weights_barycenter_apply,
      Fintype.card_fin] at h0
    exact h0
  have hc_pos : (0 : ℝ) < ((((n + 1 : ℕ)) : ℝ)) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have h1 : ((((n + 1 : ℕ)) : ℝ)) * ((1 - (t : ℝ)) * radMin n x) = 1 := by
    rw [h_eq_j, mul_inv_cancel₀ (ne_of_gt hc_pos)]
  have h_ring : (1 - (t : ℝ)) * ((((n + 1 : ℕ)) : ℝ) * radMin n x) =
      ((((n + 1 : ℕ)) : ℝ)) * ((1 - (t : ℝ)) * radMin n x) := by ring
  have h_prod : (1 - (t : ℝ)) * ((((n + 1 : ℕ)) : ℝ) * radMin n x) = 1 :=
    h_ring.trans h1
  have hB_nonneg : (0 : ℝ) ≤ ((((n + 1 : ℕ)) : ℝ)) * radMin n x :=
    mul_nonneg (le_of_lt hc_pos) (radMin_nonneg n x)
  have hB_le_one : ((((n + 1 : ℕ)) : ℝ)) * radMin n x ≤ 1 := by
    have h_nn := radDenom_nonneg n x
    unfold radDenom at h_nn
    linarith
  have hB_ge_one : (1 : ℝ) ≤ ((((n + 1 : ℕ)) : ℝ)) * radMin n x := by
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have h_mul : (0 : ℝ) ≤ (t : ℝ) * (((((n + 1 : ℕ)) : ℝ)) * radMin n x) :=
      mul_nonneg ht0 hB_nonneg
    have h_expand : (t : ℝ) * (((((n + 1 : ℕ)) : ℝ)) * radMin n x) =
        ((((n + 1 : ℕ)) : ℝ)) * radMin n x -
          (1 - (t : ℝ)) * (((((n + 1 : ℕ)) : ℝ)) * radMin n x) := by ring
    rw [h_expand, h_prod] at h_mul
    linarith
  have hB_eq : ((((n + 1 : ℕ)) : ℝ)) * radMin n x = 1 :=
    le_antisymm hB_le_one hB_ge_one
  have h_denom_zero : radDenom n x = 0 := by
    unfold radDenom
    linarith
  linarith
/-- Continuity of the unbundled straight-line homotopy function into the simplex. -/
theorem continuous_homotopyFun :
    Continuous (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter} =>
      homotopyPoint n p.1 p.2.val p.2.property) := by
  have hEmb := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  rw [hEmb.continuous_iff]
  apply continuous_pi
  intro i
  have h_eq : (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter} =>
      (homotopyPoint n p.1 p.2.val p.2.property).weights i) =
      (fun p => homotopyCoord n p.1 p.2.val i) := by
    funext p
    exact homotopyPoint_weights n p.1 p.2.val p.2.property i
  simp only [Function.comp_apply]
  rw [h_eq]
  have h_t :
      Continuous (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter} =>
      (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have h_xi :
      Continuous (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter} =>
      (p.2.val : Convexity.StdSimplex ℝ (Fin (n + 1))).weights i) :=
    ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      continuous_subtype_val).comp continuous_snd
  have h_ri :
      Continuous (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter} =>
      radialCoord n p.2.val i) := by
    have h_coord_eq : (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter} =>
        radialCoord n p.2.val i) =
        (fun p => ((radialMap n p.2).weights i)) := by
      funext p
      exact (radialMap_weights n p.2 i).symm
    rw [h_coord_eq]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      (continuous_radialMap n)).comp continuous_snd
  have h_coord :
      Continuous (fun p : I × {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter} =>
      homotopyCoord n p.1 p.2.val i) := by
    unfold homotopyCoord
    exact Continuous.add (Continuous.mul (Continuous.sub continuous_const h_t) h_xi)
      (Continuous.mul h_t h_ri)
  exact h_coord

/-- The radial image avoids the barycenter. -/
theorem radialMap_ne_bary (q : {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
    x ≠ Convexity.StdSimplex.barycenter}) :
    radialMap n q ≠ Convexity.StdSimplex.barycenter := by
  intro h_eq
  obtain ⟨j, hj⟩ := exists_radialMap_weights_eq_zero n q
  have h_congr :=
    congrArg (fun y : Convexity.StdSimplex ℝ (Fin (n + 1)) => y.weights j) h_eq
  have h_left : (radialMap n q).weights j = 0 := hj
  have h_bary : (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin (n + 1))).weights j = ((((n + 1 : ℕ)) : ℝ))⁻¹ := by
    rw [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  rw [h_left, h_bary] at h_congr
  have hc_pos : (0 : ℝ) < ((((n + 1 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  exact inv_ne_zero (ne_of_gt hc_pos) h_congr.symm

/-- Radial map as a continuous self-map of the complement. -/
noncomputable def radialMapComplement :
    C({x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter},
      {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      x ≠ Convexity.StdSimplex.barycenter}) :=
  ⟨fun q => ⟨radialMap n q, radialMap_ne_bary n q⟩,
    Continuous.subtype_mk (continuous_radialMap n)
      (fun q => radialMap_ne_bary n q)⟩

/-- Straight-line homotopy from the identity to the radial map. -/
noncomputable def radialHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id _) (radialMapComplement n) where
  toFun p :=
    ⟨homotopyPoint n p.1 p.2.val p.2.property,
      homotopy_ne_bary n p.1 p.2.val p.2.property⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_homotopyFun n)
      (fun p => homotopy_ne_bary n p.1 p.2.val p.2.property)
  map_zero_left q := by
    apply Subtype.ext
    change homotopyPoint n 0 q.val q.property = q.val
    exact homotopyPoint_zero n q.val q.property
  map_one_left q := by
    apply Subtype.ext
    change homotopyPoint n 1 q.val q.property = radialMap n q
    exact homotopyPoint_one n q.val q.property

/-- Straight-line homotopy fixing points with a zero coordinate. -/
noncomputable def radialHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id _) (radialMapComplement n)
      {q | ∃ k, q.val.weights k = 0} where
  toHomotopy := radialHomotopy n
  prop' t q hq := by
    obtain ⟨k, hk⟩ := hq
    apply Subtype.ext
    change homotopyPoint n t q.val q.property = q.val
    exact homotopyPoint_eq_of_has_zero n t q k hk

/-- The radial homotopy does not increase the minimum coordinate. -/
theorem radMin_homotopyPoint_le (t : I)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hx : x ≠ Convexity.StdSimplex.barycenter) :
    radMin n (homotopyPoint n t x hx) ≤ radMin n x := by
  obtain ⟨j, hj⟩ := exists_radMin_eq n x
  have hr_j : radialCoord n x j = 0 := by
    unfold radialCoord
    have h0 : x.weights j - radMin n x = 0 := sub_eq_zero.mpr hj.symm
    rw [h0, zero_div]
  have hHj : homotopyCoord n t x j = (1 - (t : ℝ)) * radMin n x := by
    unfold homotopyCoord
    rw [hj.symm, hr_j, mul_zero, add_zero]
  have h_show : (homotopyPoint n t x hx).weights j = homotopyCoord n t x j :=
    homotopyPoint_weights n t x hx j
  have h_le : radMin n (homotopyPoint n t x hx) ≤ (1 - (t : ℝ)) * radMin n x := by
    have h := radMin_le n (homotopyPoint n t x hx) j
    rw [h_show, hHj] at h
    exact h
  have hm : 0 ≤ radMin n x := radMin_nonneg n x
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have htm : (0 : ℝ) ≤ (t : ℝ) * radMin n x := mul_nonneg ht0 hm
  have h_final : (1 - (t : ℝ)) * radMin n x ≤ radMin n x := by
    have h_eq : (1 - (t : ℝ)) * radMin n x = radMin n x - (t : ℝ) * radMin n x := by
      ring
    rw [h_eq]
    exact sub_le_self _ htm
  exact le_trans h_le h_final

end StdSimplexRadialBoundary
