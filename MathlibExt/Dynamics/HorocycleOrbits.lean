/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Horocycle orbits on the modular quotient

Every orbit of the horocycle flow on `SL(2, ℤ) \ SL(2, ℝ)` is closed or dense.
The proof uses the action of integral matrices on the second column.
-/

@[expose] public section

namespace MathlibExt.Dynamics.UnipotentFlowsWanted

open Matrix
open scoped MatrixGroups

/-- **Horocycle one-parameter subgroup.** `u_t = [[1, 0], [t, 1]]` in `SL(2, ℝ)` (D. W. Morris,
*Ratner's theorems on unipotent flows*, arXiv:math/0310402, Notation 1.1.5). -/
def horocycle (t : ℝ) : SL(2, ℝ) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

open Set Topology

private abbrev inclusion : SL(2, ℤ) →* SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ)

private abbrev Plane := Fin 2 → ℝ

private local instance integralAction : MulAction (SL(2, ℤ)) Plane := MulAction.compHom _ inclusion

private abbrev vectorOrbit := MulAction.orbit (SL(2, ℤ)) (α := Plane)

private def column (g : SL(2, ℝ)) : Plane := g.val.col 1

private lemma column_mul (g h : SL(2, ℝ)) : column (g * h) = g • column h := rfl

private lemma continuous_column : Continuous column := by
  apply continuous_pi
  intro i
  change Continuous fun g : SL(2, ℝ) => g i 1
  fun_prop

private lemma integral_smul (γ : SL(2, ℤ)) (p b : ℝ) :
    γ • ![p, b] = ![(γ 0 0 : ℝ) * p + (γ 0 1 : ℝ) * b, (γ 1 0 : ℝ) * p + (γ 1 1 : ℝ) * b] := by
  change (inclusion γ).val *ᵥ ![p, b] = _
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, inclusion]

private lemma column_eq_iff (g h : SL(2, ℝ)) :
    column g = column h ↔ ∃ t, h = g * horocycle t := by
  constructor
  · intro heq
    let k := g⁻¹ * h
    have hk : column k = column (1 : SL(2, ℝ)) := by
      rw [show k = g⁻¹ * h from rfl, column_mul, ← heq, ← column_mul, inv_mul_cancel]
    have hb : k 0 1 = 0 := congrFun hk 0
    have hd : k 1 1 = 1 := congrFun hk 1
    have ha : k 0 0 = 1 := by
      have hdet := k.property
      rw [Matrix.det_fin_two] at hdet
      simpa [hb, hd] using hdet
    have hform : k = horocycle (k 1 0) := by
      apply SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [horocycle, ha, hb, hd]
    exact ⟨k 1 0, by rw [← hform]; simp [k]⟩
  · rintro ⟨t, rfl⟩
    funext i
    change g i 1 = (g.val * !![1, 0; t, 1]) i 1
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma smul_mem_closure (γ : SL(2, ℤ)) {v w : Plane} (hw : w ∈ closure (vectorOrbit v)) :
    γ • w ∈ closure (vectorOrbit v) := by
  apply (MulAction.mapsTo_smul_orbit γ v).closure _ hw
  change Continuous fun w : Plane => (inclusion γ).val *ᵥ w
  fun_prop

-- The orbit of a horizontal vector is a scaled subset of the integer grid.
private lemma isClosed_horizontal (a : ℝ) : IsClosed (vectorOrbit ![a, 0]) := by
  by_cases ha : a = 0
  · subst a
    simp [vectorOrbit, MulAction.orbit, integral_smul]
  let f : ℤ → ℝ := fun m => (m : ℝ) * a
  have hf : IsClosedEmbedding f :=
    (Homeomorph.mulRight₀ a ha).isClosedEmbedding.comp Real.isClosedEmbedding_intCast
  let s := range fun γ : SL(2, ℤ) => γ.val.col 0
  have heq : vectorOrbit ![a, 0] = Pi.map (fun _ : Fin 2 => f) '' s := by
    dsimp only [s]
    rw [← range_comp]
    unfold vectorOrbit MulAction.orbit
    congr 1
    funext γ i
    fin_cases i <;> simp [integral_smul, f, Matrix.col]
  rw [heq]
  exact (IsClosedEmbedding.piMap fun _ : Fin 2 => hf).isClosedMap _ (isClosed_discrete _)

-- An integral shear can move the first coordinate within half a step of any target.
private lemma shear_approx {v : Plane} {p b : ℝ} (hw : ![p, b] ∈ vectorOrbit v)
    (hb : b ≠ 0) (a : ℝ) :
    ∃ p', ![p', b] ∈ vectorOrbit v ∧ |a - p'| ≤ |b| / 2 := by
  let k := round ((a - p) / b)
  refine ⟨p + k * b, ?_, ?_⟩
  · simpa [integral_smul, ModularGroup.coe_T_zpow] using
      MulAction.mem_orbit_of_mem_orbit (ModularGroup.T ^ k) hw
  calc
    |a - (p + k * b)| = |((a - p) / b - k) * b| := by
      congr 1
      field_simp
      ring
    _ = |(a - p) / b - k| * |b| := abs_mul _ _
    _ ≤ (1 / 2) * |b| := mul_le_mul_of_nonneg_right (abs_sub_round _) (abs_nonneg _)
    _ = |b| / 2 := by ring

private lemma rotate_mem {v : Plane} {p b : ℝ} (hw : ![p, b] ∈ vectorOrbit v) :
    ![-b, p] ∈ vectorOrbit v := by
  simpa [integral_smul] using MulAction.mem_orbit_of_mem_orbit ModularGroup.S hw

-- If the orbit misses the horizontal axis, shear and rotate repeatedly to halve the height.
private lemma horizontal_mem_closure {v : Plane} (h : ∀ a : ℝ, ![a, 0] ∉ vectorOrbit v)
    (a : ℝ) : ![a, 0] ∈ closure (vectorOrbit v) := by
  have ne {p b : ℝ} (hw : ![p, b] ∈ vectorOrbit v) : b ≠ 0 := fun hb => h p (hb ▸ hw)
  have hself : ![v 0, v 1] ∈ vectorOrbit v := by
    rw [show ![v 0, v 1] = v by ext i; fin_cases i <;> rfl]
    exact MulAction.mem_orbit_self v
  have small (n : ℕ) : ∃ p b : ℝ, ![p, b] ∈ vectorOrbit v ∧
      |b| ≤ (1 / 2 : ℝ) ^ n * |v 1| := by
    induction n with
    | zero => exact ⟨v 0, v 1, hself, by simp⟩
    | succ n ih =>
      obtain ⟨p, b, hw, hbound⟩ := ih
      obtain ⟨p', hw', hp'⟩ := shear_approx hw (ne hw) 0
      refine ⟨-b, p', rotate_mem hw', ?_⟩
      simp only [zero_sub, abs_neg] at hp'
      rw [pow_succ]
      linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hv := abs_pos.mpr (ne hself)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hv) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨p, b, hw, hbound⟩ := small n
  have hb := hbound.trans_lt ((lt_div_iff₀ hv).mp hn)
  obtain ⟨p', hw', hp'⟩ := shear_approx hw (ne hw) a
  refine ⟨![p', b], hw', ?_⟩
  apply (dist_pi_lt_iff hε).2
  intro i
  fin_cases i <;> simp [Real.dist_eq] <;> linarith

-- Integral translates of the horizontal axis include every line of rational slope.
private lemma dense_of_horizontal {v : Plane} (h : ∀ a : ℝ, ![a, 0] ∈ closure (vectorOrbit v)) :
    Dense (vectorOrbit v) := by
  intro w
  let a := w 0
  let b := w 1
  have hw : w = ![a, b] := by ext i; fin_cases i <;> rfl
  rw [hw]
  by_cases ha : a = 0
  · rw [ha]
    simpa [integral_smul] using smul_mem_closure ModularGroup.S (h b)
  have line (s : ℝ) : ![a, s * a] ∈ closure (vectorOrbit v) := by
    apply isClosed_property (Rat.denseRange_cast (𝕜 := ℝ)) (p := fun s =>
      ![a, s * a] ∈ closure (vectorOrbit v)) _ _ s
    · exact isClosed_closure.preimage (by fun_prop : Continuous fun s : ℝ => ![a, s * a])
    · intro q
      obtain ⟨γ, hc, hd⟩ := q.isCoprime_num_den.symm.exists_SL2_col 0
      have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      have heq : γ • ![a / q.den, 0] = ![a, (q : ℝ) * a] := by
        rw [integral_smul, hc, hd, Rat.cast_def]
        push_cast
        funext i
        fin_cases i <;> simp <;> field_simp
      exact heq ▸ smul_mem_closure γ (h _)
  simpa [ha] using line (b / a)

-- Near a given matrix, keep the direction of its first column and rescale to determinant one.
private lemma dense_column_preimage {s : Set Plane} (hs : Dense s) :
    Dense (column ⁻¹' s) := by
  intro g
  let d (w : Plane) := g 0 0 * w 1 - w 0 * g 1 0
  have hd : d (column g) = 1 := (Matrix.det_fin_two g.val).symm.trans g.property
  let U : Set Plane := {w | d w ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by unfold d; fun_prop) continuous_const
  let lift (w : U) : SL(2, ℝ) :=
    ⟨!![g 0 0 / d w, w.val 0; g 1 0 / d w, w.val 1], by
      have hw : d w ≠ 0 := w.property
      rw [Matrix.det_fin_two_of]
      field_simp
      rfl⟩
  have hcont : Continuous lift := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    have hcoord (i : Fin 2) : Continuous fun w : U => w.val i :=
      (continuous_apply i).comp continuous_subtype_val
    have hne (w : U) : d w ≠ 0 := w.property
    have hc : Continuous fun w : U => d w :=
      (continuous_const.mul (hcoord 1)).sub ((hcoord 0).mul continuous_const)
    fin_cases i <;> fin_cases j
    · exact continuous_const.div hc hne
    · exact hcoord 0
    · exact continuous_const.div hc hne
    · exact hcoord 1
  have hmap : MapsTo lift (Subtype.val ⁻¹' s) (column ⁻¹' s) := by
    intro w hw
    have heq : column (lift w) = w.val := by ext i; fin_cases i <;> rfl
    change column (lift w) ∈ s
    rwa [heq]
  let w : U := ⟨column g, hd.trans_ne one_ne_zero⟩
  have hgw : lift w = g := by
    apply SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lift, w, hd] <;> rfl
  rw [← hgw]
  exact hmap.closure hcont (hs.preimage hU.isOpenMap_subtype_val w)

private abbrev project := Quotient.mk (QuotientGroup.rightRel inclusion.range)

private def flowOrbit (x : SL(2, ℝ)) := range fun t : ℝ => project (x * horocycle t)

private lemma preimage_flowOrbit (x : SL(2, ℝ)) :
    project ⁻¹' flowOrbit x = column ⁻¹' vectorOrbit (column x) := by
  ext g
  change (∃ t, project (x * horocycle t) = project g) ↔
    ∃ γ : SL(2, ℤ), inclusion γ • column x = column g
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨γ, hγ⟩ := QuotientGroup.rightRel_apply.mp (Quotient.exact ht)
    have hg := mul_inv_eq_iff_eq_mul.mp hγ.symm
    refine ⟨γ, ?_⟩
    rw [hg, ← mul_assoc, ← column_mul]
    exact (column_eq_iff _ _).2 ⟨t, rfl⟩
  · rintro ⟨γ, hγ⟩
    rw [← column_mul] at hγ
    obtain ⟨t, rfl⟩ := (column_eq_iff _ _).1 hγ
    refine ⟨t, Quotient.sound (QuotientGroup.rightRel_apply.mpr ⟨γ, ?_⟩)⟩
    simp [mul_assoc]

/-- **Orbits of the horocycle flow on `SL(2, ℤ) \ SL(2, ℝ)` are closed or dense.** For every
`x ∈ SL(2, ℝ)`, the orbit `{Γ x u_t : t ∈ ℝ}` of the horocycle flow `η_t(Γ x) = Γ x u_t` on the
space of right cosets of `Γ = SL(2, ℤ)` is either closed or dense (D. W. Morris, *Ratner's theorems
on unipotent flows*, arXiv:math/0310402, Example 1.1.16, a consequence of Ratner's orbit closure
theorem, Theorem 1.1.14; the case of cocompact `Γ`, where every orbit is dense, is due to
Hedlund). -/
theorem horocycle_orbit_isClosed_or_dense (x : SL(2, ℝ)) :
    IsClosed (Set.range fun t : ℝ =>
        (Quotient.mk (QuotientGroup.rightRel (SpecialLinearGroup.map (Int.castRingHom ℝ)).range)
          (x * horocycle t))) ∨
      Dense (Set.range fun t : ℝ =>
        (Quotient.mk (QuotientGroup.rightRel (SpecialLinearGroup.map (Int.castRingHom ℝ)).range)
          (x * horocycle t))) := by
  change IsClosed (flowOrbit x) ∨ Dense (flowOrbit x)
  by_cases h : ∃ a : ℝ, ![a, 0] ∈ vectorOrbit (column x)
  · obtain ⟨a, ha⟩ := h
    left
    apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
    change IsClosed (project ⁻¹' flowOrbit x)
    have heq : vectorOrbit ![a, 0] = vectorOrbit (column x) := MulAction.orbit_eq_iff.mpr ha
    rw [preimage_flowOrbit, ← heq]
    exact (isClosed_horizontal a).preimage continuous_column
  · right
    have hv := dense_of_horizontal (horizontal_mem_closure (not_exists.mp h))
    have hg := dense_column_preimage hv
    rw [← preimage_flowOrbit] at hg
    have hq : IsQuotientMap project := isQuotientMap_quotient_mk'
    simpa [image_preimage_eq _ hq.surjective] using hq.surjective.denseRange.dense_image
      hq.continuous hg

end MathlibExt.Dynamics.UnipotentFlowsWanted
