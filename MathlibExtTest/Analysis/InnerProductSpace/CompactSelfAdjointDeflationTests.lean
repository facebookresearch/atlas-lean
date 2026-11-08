/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointDeflation

/-!
# Tests for the deflation (next-eigenvalue) step

* On `ℝ`, with the empty family of eigenvectors, the corollary recovers the
  first step: the scalar operator `2 • 1` has eigenvalue exactly `2`.
* On `EuclideanSpace ℝ (Fin 2)`, after the eigenvector `e₀` (eigenvalue
  `2`) of the diagonal operator `diag(2, 1)`, the next eigenvalue is
  exactly `1`, attained at a unit vector orthogonal to `e₀`.
* On `ℝ`, the invariant-subspace version with `S = ⊤` applied to
  `3 • 1` gives eigenvalue exactly `3`, with `|r| = ‖T‖`.
-/

open ContinuousLinearMap InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointDeflation

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointDeflationTests

/-- On `ℝ`, the scalar operator `2 • 1` has eigenvalue exactly `2`
(from the corollary with the empty family of eigenvectors). -/
example : ∃ r : ℝ, ∃ v : ℝ, ‖v‖ = 1 ∧
    ((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) v = (r : ℝ) • v ∧ r = 2 := by
  obtain ⟨r, v, hv1, _hort, hTv, _hmax, _hinner⟩ :=
    exists_next_eigenvector_of_finite_eigenvectors
      (T := (2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (u := fun i : Fin 0 => (0 : ℝ))
      (μ := fun i : Fin 0 => (0 : ℝ)) (by simp [IsSelfAdjoint])
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (fun i => i.elim0)
      ⟨1, by simp, by simp⟩
  have hTapply : ((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) v = (2 : ℝ) • v := by simp
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have h1 : (r : ℝ) • v = (2 : ℝ) • v := hTv.symm.trans hTapply
  have hdiff : ((r : ℝ) - 2) • v = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp hdiff with h | h
  · exact ⟨r, v, hv1, hTv, sub_eq_zero.mp h⟩
  · exact absurd h hv0

/-- On `ℝ`, the invariant-subspace version with `S = ⊤` applied to
`3 • 1` gives eigenvalue exactly `3`, with `|r| = ‖T‖`. -/
example : ∃ r : ℝ, ∃ v : ℝ, ‖v‖ = 1 ∧
    ((3 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) v = (r : ℝ) • v ∧ r = 3 ∧
    |r| = ‖(3 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖ := by
  obtain ⟨r, v, hv1, _hvS, hTv, hr_norm, _hr_le⟩ :=
    exists_next_eigenvector_of_invariant (S := (⊤ : Submodule ℝ ℝ))
      (T := (3 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (by simp [IsSelfAdjoint])
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (fun x _ => Submodule.mem_top)
      (by
        intro h0
        have h1 := congrArg (fun S : ℝ →L[ℝ] ℝ => S 1) h0
        simp only [ContinuousLinearMap.comp_apply, zero_apply,
          Submodule.starProjection_top, one_apply_eq_self,
          smul_apply] at h1
        norm_num at h1)
  have hTapply : ((3 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) v = (3 : ℝ) • v := by simp
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have h1 : (r : ℝ) • v = (3 : ℝ) • v := hTv.symm.trans hTapply
  have hdiff : ((r : ℝ) - 3) • v = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp hdiff with h | h
  · have hr : r = 3 := sub_eq_zero.mp h
    refine ⟨r, v, hv1, hTv, hr, ?_⟩
    have hcomp : (⊤ : Submodule ℝ ℝ).starProjection ∘L
        ((3 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) ∘L (⊤ : Submodule ℝ ℝ).starProjection
          = (3 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
      simp [Submodule.starProjection_top]
    rw [hr_norm, hcomp]
  · exact absurd h hv0

/-- The diagonal operator `diag(2, 1)` on `EuclideanSpace ℝ (Fin 2)`,
as a sum of coordinate projections. -/
private noncomputable def diagTwoOne :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (2 : ℝ) • (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℝ)).starProjection +
    (1 : ℝ) • (ℝ ∙ EuclideanSpace.single (1 : Fin 2) (1 : ℝ)).starProjection

/-- Component formula for `diagTwoOne`. -/
private theorem diagTwoOne_apply (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (diagTwoOne x) i = (if i = 0 then (2 : ℝ) else 1) * x i := by
  fin_cases i <;>
    simp [diagTwoOne, Submodule.starProjection_unit_singleton,
      EuclideanSpace.inner_single_left]

/-- `diagTwoOne` is self-adjoint. -/
private theorem diagTwoOne_selfAdjoint : IsSelfAdjoint diagTwoOne := by
  have h2 : IsSelfAdjoint
      ((2 : ℝ) • (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℝ)).starProjection) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (isSelfAdjoint_starProjection _)
  have h1 : IsSelfAdjoint
      ((1 : ℝ) • (ℝ ∙ EuclideanSpace.single (1 : Fin 2) (1 : ℝ)).starProjection) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (isSelfAdjoint_starProjection _)
  exact h2.add h1

/-- `e₀` is an eigenvector of `diagTwoOne` with eigenvalue `2`. -/
private theorem diagTwoOne_e0 :
    diagTwoOne (EuclideanSpace.single 0 1)
      = (2 : ℝ) • EuclideanSpace.single 0 1 := by
  ext i
  rw [diagTwoOne_apply]
  fin_cases i <;> simp

/-- `diagTwoOne` does not vanish on `e₁`. -/
private theorem diagTwoOne_e1_ne_zero :
    diagTwoOne (EuclideanSpace.single 1 1) ≠ 0 := by
  intro h
  have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
  rw [diagTwoOne_apply] at h1
  simp at h1

/-- On `EuclideanSpace ℝ (Fin 2)`, after the eigenvector `e₀` (eigenvalue
`2`) of `diag(2, 1)`, the next eigenvalue is exactly `1`. -/
example : ∃ r : ℝ, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
    diagTwoOne v = (r : ℝ) • v ∧ r = 1 := by
  have hzS : EuclideanSpace.single 1 1 ∈
      (Submodule.span ℝ (Set.range
        (![EuclideanSpace.single 0 1] :
          Fin 1 → EuclideanSpace ℝ (Fin 2))))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        simp [EuclideanSpace.inner_single_left]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  obtain ⟨r, v, hv_norm, hort, hv_eig, _hmax, _hinner⟩ :=
    exists_next_eigenvector_of_finite_eigenvectors
      (u := (![EuclideanSpace.single 0 1] :
        Fin 1 → EuclideanSpace ℝ (Fin 2)))
      (μ := ![2]) (T := diagTwoOne) diagTwoOne_selfAdjoint
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (Fin.forall_fin_one.mpr (by simpa using diagTwoOne_e0))
      ⟨EuclideanSpace.single 1 1, hzS, diagTwoOne_e1_ne_zero⟩
  -- The eigenvector `v` is orthogonal to `e₀`, so its `0`-component is `0`.
  have hv0 : v 0 = 0 := by
    have h := hort 0
    simp [EuclideanSpace.inner_single_right] at h
    exact h
  -- Its `1`-component is nonzero, since `‖v‖ = 1`.
  have hv1ne : v 1 ≠ 0 := by
    intro h1z
    have hnorm2 : ‖v‖ ^ 2 = 1 := by rw [hv_norm]; norm_num
    rw [EuclideanSpace.norm_eq] at hnorm2
    rw [Real.sq_sqrt (by positivity)] at hnorm2
    rw [Fin.sum_univ_two, hv0, h1z] at hnorm2
    simp at hnorm2

  -- Compare the `1`-components of `diagTwoOne v = r • v`.
  have h3 : r * v 1 = v 1 := by
    have hthis := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) hv_eig
    rw [diagTwoOne_apply, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hthis
    simpa using hthis.symm
  have hr : r = 1 := by
    have h4 : (r - 1) * v 1 = 0 := by
      rw [sub_mul, one_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · exact absurd h hv1ne
  exact ⟨r, v, hv_norm, hv_eig, hr⟩

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointDeflationTests
