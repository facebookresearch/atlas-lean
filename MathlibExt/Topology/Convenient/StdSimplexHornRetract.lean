/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Constructions

/-!
# Affine horn retraction on the standard simplex

For `0 < n` and `k : Fin (n + 1)`, the geometric horn is the coordinate
locus where some non-`k` coordinate vanishes. The finite minimum over the
erased index set gives an affine retraction onto that locus and a
straight-line homotopy. Mathematical source: the standard affine
contraction of a geometric horn, cf. Goerss--Jardine, *Simplicial Homotopy
Theory*, Chapter I, §1; reconstructed here from the explicit finite-min
formula and pinned APIs.

The hypothesis `0 < n` is load-bearing: when `n = 0`, `Fin 1` erased at
its unique point is empty, the minimum is undefined, and the horn locus
is empty, so no retraction exists. The `n = 1` unary case is a readability
corollary: the minimum is the single off-`k` projection and the retraction
is the vertex.

No `SSet`, `TopCat`, strong-deformation-retract, weak-equivalence, or
model-category result is claimed here. The public retraction/homotopy and
their exact properties are the reusable input for a later realized-horn
descent packet, which owns all quotient/colimit transport.
-/

@[expose] public section

variable {n : ℕ}

/-- The erased index set is nonempty when `0 < n`, by explicit witness. -/
private lemma erase_nonempty (k : Fin (n + 1)) (hn : 0 < n) :
    (Finset.univ.erase k).Nonempty := by
  let a0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let a1 : Fin (n + 1) := ⟨1, by omega⟩
  have h01 : a0 ≠ a1 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [a0, a1] at hval
    omega
  by_cases hk : k = a0
  · refine ⟨a1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    rw [hk]
    exact Ne.symm h01
  · refine ⟨a0, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    exact Ne.symm hk

/-- Finite minimum of weights over the erased index set. -/
private noncomputable def hornMin (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℝ :=
  (Finset.univ.erase k).inf' (erase_nonempty k hn)
    (fun j => t.weights j)

/-- The minimum is nonnegative. -/
private lemma hornMin_nonneg (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    0 ≤ hornMin k hn t := by
  unfold hornMin
  rw [Finset.le_inf'_iff]
  intro j _
  exact t.weights_nonneg j

/-- The minimum bounds each off-`k` weight. -/
private lemma hornMin_le (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) (hj : j ≠ k) :
    hornMin k hn t ≤ t.weights j := by
  unfold hornMin
  exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

/-- The minimum is continuous in the simplex. -/
private lemma continuous_hornMin (k : Fin (n + 1)) (hn : 0 < n) :
    Continuous (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => hornMin k hn t) := by
  unfold hornMin
  exact Continuous.finset_inf'_apply _
    (fun i _ => Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i)

/-- Nonnegativity of the explicit retraction coordinates. -/
private lemma retractCoord_nonneg (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    0 ≤ (if j = k then t.weights k + (n : ℝ) * hornMin k hn t
      else t.weights j - hornMin k hn t) := by
  have hm_nonneg : 0 ≤ hornMin k hn t :=
    hornMin_nonneg k hn t
  by_cases hj : j = k
  · simp only [hj, ite_true]
    have hk_nonneg : 0 ≤ t.weights k := t.weights_nonneg k
    have hn_nonneg : 0 ≤ (n : ℝ) * hornMin k hn t :=
      mul_nonneg (Nat.cast_nonneg n) hm_nonneg
    linarith
  · simp only [hj, ite_false]
    have hle : hornMin k hn t ≤ t.weights j :=
      hornMin_le k hn t j hj
    linarith

/-- The explicit retraction coordinates sum to one. -/
private lemma retractCoord_sum (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∑ j, (if j = k then t.weights k + (n : ℝ) * hornMin k hn t
      else t.weights j - hornMin k hn t) = 1 := by
  have h_erase_card : (Finset.univ.erase k).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp [Fintype.card_fin]
  have h_split : ∑ j, (if j = k then t.weights k + (n : ℝ) * hornMin k hn t
        else t.weights j - hornMin k hn t) =
      (t.weights k + (n : ℝ) * hornMin k hn t) +
      ∑ j ∈ Finset.univ.erase k, (t.weights j - hornMin k hn t) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => if j = k then t.weights k + (n : ℝ) * hornMin k hn t
        else t.weights j - hornMin k hn t) (Finset.mem_univ k)]
    simp only [ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    simp [hjk]
  rw [h_split]
  have h_erase_sum : ∑ j ∈ Finset.univ.erase k, (t.weights j - hornMin k hn t) =
      (∑ j ∈ Finset.univ.erase k, t.weights j) - (n : ℝ) * hornMin k hn t := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, h_erase_card, nsmul_eq_mul]
  rw [h_erase_sum]
  have h_t_sum : ∑ j : Fin (n + 1), t.weights j = 1 := t.total_of_fintype
  have h_t_split : ∑ j : Fin (n + 1), t.weights j =
      t.weights k + ∑ j ∈ Finset.univ.erase k, t.weights j :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)).symm
  linarith

/-- Affine retraction onto the horn locus, on the new carrier.

Subtract the minimum off every non-`k` coordinate and add `n * minimum`
to `k`. The construction uses `Finsupp.equivFunOnFinite` directly, without
any bridge. -/
noncomputable def affineHornRetract (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) where
  weights :=
    Finsupp.equivFunOnFinite.symm (fun j =>
      have hne : (Finset.univ.erase k).Nonempty := by
        let a0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
        let a1 : Fin (n + 1) := ⟨1, by omega⟩
        have h01 : a0 ≠ a1 := by
          intro h
          have hval := congrArg Fin.val h
          simp only [a0, a1] at hval
          omega
        by_cases hk : k = a0
        · refine ⟨a1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
          rw [hk]
          exact Ne.symm h01
        · refine ⟨a0, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
          exact Ne.symm hk
      if j = k then t.weights k + (n : ℝ) *
        ((Finset.univ.erase k).inf' hne (fun j => t.weights j))
      else t.weights j -
        ((Finset.univ.erase k).inf' hne (fun j => t.weights j)))
  nonneg m := by
    have h := retractCoord_nonneg k hn t m
    unfold hornMin at h
    simpa using h
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact retractCoord_sum k hn t

/-- Pointwise description of the retraction via weights. -/
@[simp]
private theorem retract_apply (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    (affineHornRetract k hn t).weights j =
      if j = k then t.weights k + (n : ℝ) * hornMin k hn t
      else t.weights j - hornMin k hn t :=
  rfl

/-- The retraction lands in the horn-coordinate locus. -/
theorem affineHornRetract_horn (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∃ j, j ≠ k ∧ (affineHornRetract k hn t).weights j = 0 := by
  obtain ⟨j₀, hj₀_mem, hj₀_min⟩ :=
    Finset.exists_min_image _ (fun j => t.weights j) (erase_nonempty k hn)
  have hj₀_ne : j₀ ≠ k := (Finset.mem_erase.mp hj₀_mem).1
  have hm_le : hornMin k hn t ≤ t.weights j₀ :=
    hornMin_le k hn t j₀ hj₀_ne
  have hj₀_le : t.weights j₀ ≤ hornMin k hn t := by
    unfold hornMin
    rw [Finset.le_inf'_iff]
    intro c hc
    exact hj₀_min c hc
  have hj₀_eq : t.weights j₀ = hornMin k hn t :=
    le_antisymm hj₀_le hm_le
  refine ⟨j₀, hj₀_ne, ?_⟩
  simp only [retract_apply, hj₀_ne, ite_false, hj₀_eq, sub_self]

/-- The retraction fixes the horn-coordinate locus pointwise. -/
theorem affineHornRetract_fix (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (h : ∃ j₀, j₀ ≠ k ∧ t.weights j₀ = 0) :
    affineHornRetract k hn t = t := by
  obtain ⟨j₀, hj₀_ne, hj₀_zero⟩ := h
  have hm_le : hornMin k hn t ≤ t.weights j₀ :=
    hornMin_le k hn t j₀ hj₀_ne
  have hm_nonneg : 0 ≤ hornMin k hn t :=
    hornMin_nonneg k hn t
  have hm_zero : hornMin k hn t = 0 := by linarith
  apply Convexity.StdSimplex.ext
  ext j
  simp only [retract_apply]
  by_cases hj : j = k
  · simp [hj, hm_zero]
  · simp [hj, hm_zero]

/-- The retraction is continuous on the new carrier. -/
theorem continuous_affineHornRetract (k : Fin (n + 1)) (hn : 0 < n) :
    Continuous (affineHornRetract k hn) := by
  have hEmb :=
    Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  apply hEmb.continuous_iff.mpr
  have hsim : ((fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (t.weights : Fin (n + 1) → ℝ)) ∘ affineHornRetract k hn) =
      (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => (fun j =>
        if j = k then t.weights k + (n : ℝ) * hornMin k hn t
        else t.weights j - hornMin k hn t)) := by
    funext t j
    rfl
  rw [hsim, continuous_pi_iff]
  intro j
  by_cases hj : j = k
  · simp only [hj, ite_true]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) k).add
      (continuous_const.mul (continuous_hornMin k hn)))
  · simp only [hj, ite_false]
    exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).sub
      (continuous_hornMin k hn)

/-- Straight-line affine homotopy from the identity to the retraction.

The weights formula is the exact affine combination
`(1 - s) * t + s * retract t`; it is proved directly to keep the
coordinate identity definitional. `Convexity.convexCombPair` is not used
because the direct formula already gives the smallest transparent proof
for membership and continuity via the weights embedding. -/
noncomputable def affineHornHomotopy (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (s : ℝ)
    (_hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) where
  weights :=
    Finsupp.equivFunOnFinite.symm (fun j =>
      (1 - s) * t.weights j + s * (affineHornRetract k hn t).weights j)
  nonneg m := by
    obtain ⟨hs0, _⟩ := Set.mem_Icc.mp _hs
    have h1s : 0 ≤ 1 - s := by
      have hs1 : s ≤ 1 := (Set.mem_Icc.mp _hs).2
      linarith
    have htj : 0 ≤ t.weights m := t.weights_nonneg m
    have hrj : 0 ≤ (affineHornRetract k hn t).weights m :=
      (affineHornRetract k hn t).weights_nonneg m
    have h1 : 0 ≤ (1 - s) * t.weights m := mul_nonneg h1s htj
    have h2 : 0 ≤ s * (affineHornRetract k hn t).weights m :=
      mul_nonneg hs0 hrj
    have hsum : 0 ≤ (1 - s) * t.weights m +
        s * (affineHornRetract k hn t).weights m :=
      add_nonneg h1 h2
    simpa [Finsupp.coe_equivFunOnFinite_symm] using hsum
  total := by
    have h_t_sum : ∑ j : Fin (n + 1), t.weights j = 1 := t.total_of_fintype
    have h_r_sum : ∑ j : Fin (n + 1),
        (affineHornRetract k hn t).weights j = 1 :=
      (affineHornRetract k hn t).total_of_fintype
    have h_sum : ∑ j, ((1 - s) * t.weights j +
        s * (affineHornRetract k hn t).weights j) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        h_t_sum, h_r_sum]
      ring
    simpa [Finsupp.coe_equivFunOnFinite_symm,
      Finsupp.equivFunOnFinite_symm_sum] using h_sum

/-- Weights description of the homotopy. -/
@[simp]
theorem affineHornHomotopy_weights (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (j : Fin (n + 1)) :
    (affineHornHomotopy k hn t s hs).weights j =
      (1 - s) * t.weights j + s * (affineHornRetract k hn t).weights j :=
  rfl

/-- The homotopy is jointly continuous on the simplex times the interval. -/
theorem continuous_affineHornHomotopy (k : Fin (n + 1)) (hn : 0 < n) :
    Continuous (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1) =>
      affineHornHomotopy k hn p.1 p.2 p.2.2) := by
  have hEmb :=
    Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  apply hEmb.continuous_iff.mpr
  have hsim : ((fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (t.weights : Fin (n + 1) → ℝ)) ∘
      (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1) =>
        affineHornHomotopy k hn p.1 p.2 p.2.2)) =
      (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1) =>
        (fun j => (1 - (↑p.2 : ℝ)) * p.1.weights j +
          (↑p.2 : ℝ) * (affineHornRetract k hn p.1).weights j)) := by
    funext p j
    rfl
  rw [hsim, continuous_pi_iff]
  intro j
  have h_tj : Continuous (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) ×
      ↥(Set.Icc (0 : ℝ) 1) => p.1.weights j) :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).comp continuous_fst
  have h_rj : Continuous (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) ×
      ↥(Set.Icc (0 : ℝ) 1) => (affineHornRetract k hn p.1).weights j) :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).comp
      ((continuous_affineHornRetract k hn).comp continuous_fst)
  have h_s : Continuous (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) ×
      ↥(Set.Icc (0 : ℝ) 1) => (↑p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have h_1ms : Continuous (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) ×
      ↥(Set.Icc (0 : ℝ) 1) => 1 - (↑p.2 : ℝ)) :=
    continuous_const.sub h_s
  exact (h_1ms.mul h_tj).add (h_s.mul h_rj)

/-- Left endpoint of the homotopy is the identity. -/
theorem affineHornHomotopy_zero (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hs : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    affineHornHomotopy k hn t 0 hs = t := by
  apply Convexity.StdSimplex.ext
  ext j
  simp only [affineHornHomotopy_weights]
  ring

/-- Right endpoint of the homotopy is the retraction. -/
theorem affineHornHomotopy_one (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hs : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    affineHornHomotopy k hn t 1 hs =
      affineHornRetract k hn t := by
  apply Convexity.StdSimplex.ext
  ext j
  simp only [affineHornHomotopy_weights]
  ring

/-- The homotopy fixes the horn-coordinate locus pointwise. -/
theorem affineHornHomotopy_fix (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (h : ∃ j₀, j₀ ≠ k ∧ t.weights j₀ = 0) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    affineHornHomotopy k hn t s hs = t := by
  have hfix : affineHornRetract k hn t = t :=
    affineHornRetract_fix k hn t h
  apply Convexity.StdSimplex.ext
  ext j
  simp only [affineHornHomotopy_weights, hfix]
  ring
