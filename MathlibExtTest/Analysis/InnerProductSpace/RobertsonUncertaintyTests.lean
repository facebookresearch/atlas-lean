/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Robertson–Schrödinger uncertainty principle

For an orthonormal pair `x y` in a Hilbert space, the rank-one combinations

* `pauliLikeX x y = rankOne y x + rankOne x y` (Pauli-`X`-like),
* `pauliLikeY x y = I • rankOne y x - I • rankOne x y` (Pauli-`Y`-like),

are self-adjoint, swap `x` and `y` (up to the factor `I` for the `Y`-like
operator), and have zero mean in the state `x`. Their centered vectors are
`y` and `I • y`, so both variances are `1`, the centered inner product is
`I`, and the commutator expectation has norm `2`: the Schrödinger bound is
sharp (`schrodinger_pauliLike`), with equality `1 = 1`, and Robertson's
bound is an equality as well (`robertson_pauliLike_sharp`). The commuting
case (`commutator_eq_zero_of_commute`) and the identity operator on `ℂ`
(`variance_one`) are also checked.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.RobertsonUncertaintyTests

open scoped _root_.InnerProductSpace InnerProduct
open MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Pauli-`X`-like operator from an orthonormal pair: it swaps `x` and `y`. -/
noncomputable def pauliLikeX (x y : E) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ y x + InnerProductSpace.rankOne ℂ x y

/-- Pauli-`Y`-like operator from an orthonormal pair: it sends `x` to `I • y`. -/
noncomputable def pauliLikeY (x y : E) : E →L[ℂ] E :=
  Complex.I • InnerProductSpace.rankOne ℂ y x - Complex.I • InnerProductSpace.rankOne ℂ x y

omit [CompleteSpace E] in
theorem hyx_of {x y : E} (hxy : ⟪x, y⟫_ℂ = 0) : ⟪y, x⟫_ℂ = 0 := by
  rw [← inner_conj_symm (𝕜 := ℂ) y x, hxy, map_zero]

omit [CompleteSpace E] in
theorem hxx_of {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [hx]

/-- The Pauli-`X`-like operator is self-adjoint. -/
theorem pauliLikeX_selfAdjoint (x y : E) : IsSelfAdjoint (pauliLikeX x y) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [pauliLikeX, map_add, InnerProductSpace.adjoint_rankOne, add_comm]

/-- The Pauli-`Y`-like operator is self-adjoint. -/
theorem pauliLikeY_selfAdjoint (x y : E) : IsSelfAdjoint (pauliLikeY x y) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [pauliLikeY, map_sub, map_smulₛₗ, InnerProductSpace.adjoint_rankOne,
    Complex.conj_I]
  abel

omit [CompleteSpace E] in
/-- The Pauli-`X`-like operator sends `x` to `y`. -/
theorem pauliLikeX_apply {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    pauliLikeX x y x = y := by
  have hyx := hyx_of hxy
  have hxx := hxx_of hx
  rw [pauliLikeX]
  simp only [add_apply, InnerProductSpace.rankOne_apply, hxx, hyx, one_smul, zero_smul,
    add_zero]

omit [CompleteSpace E] in
/-- The Pauli-`X`-like operator sends `y` to `x`. -/
theorem pauliLikeX_apply_y {x y : E} (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    pauliLikeX x y y = x := by
  have hyy := hxx_of hy
  rw [pauliLikeX]
  simp only [add_apply, InnerProductSpace.rankOne_apply, hyy, hxy, one_smul, zero_smul,
    zero_add]

omit [CompleteSpace E] in
/-- The Pauli-`Y`-like operator sends `x` to `I • y`. -/
theorem pauliLikeY_apply {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    pauliLikeY x y x = Complex.I • y := by
  have hyx := hyx_of hxy
  have hxx := hxx_of hx
  rw [pauliLikeY]
  simp only [sub_apply, smul_apply, InnerProductSpace.rankOne_apply, hxx, hyx, one_smul,
    zero_smul, smul_zero, sub_zero]

omit [CompleteSpace E] in
/-- The Pauli-`X`-like operator has mean zero in the state `x`. -/
theorem meanValue_pauliLikeX {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    meanValue (pauliLikeX x y) x = 0 := by
  have hyx := hyx_of hxy
  rw [meanValue_of_norm_eq_one _ hx]
  show (⟪pauliLikeX x y x, x⟫_ℂ).re = 0
  rw [pauliLikeX_apply hx hxy, hyx]
  simp

omit [CompleteSpace E] in
/-- The Pauli-`Y`-like operator has mean zero in the state `x`. -/
theorem meanValue_pauliLikeY {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    meanValue (pauliLikeY x y) x = 0 := by
  have hyx := hyx_of hxy
  rw [meanValue_of_norm_eq_one _ hx]
  show (⟪pauliLikeY x y x, x⟫_ℂ).re = 0
  rw [pauliLikeY_apply hx hxy, inner_smul_left, hyx]
  simp

omit [CompleteSpace E] in
/-- The centered Pauli-`X`-like vector is `y`. -/
theorem centered_pauliLikeX {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    centered (pauliLikeX x y) x = y := by
  rw [centered, meanValue_pauliLikeX hx hxy, Complex.ofReal_zero, zero_smul, sub_zero,
    pauliLikeX_apply hx hxy]

omit [CompleteSpace E] in
/-- The centered Pauli-`Y`-like vector is `I • y`. -/
theorem centered_pauliLikeY {x y : E} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    centered (pauliLikeY x y) x = Complex.I • y := by
  rw [centered, meanValue_pauliLikeY hx hxy, Complex.ofReal_zero, zero_smul, sub_zero,
    pauliLikeY_apply hx hxy]

omit [CompleteSpace E] in
/-- The centered inner product is `I`: covariance `0`, imaginary part `1`. -/
theorem inner_centered_pauliLike {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    ⟪centered (pauliLikeX x y) x, centered (pauliLikeY x y) x⟫_ℂ = Complex.I := by
  have hyy := hxx_of hy
  rw [centered_pauliLikeX hx hxy, centered_pauliLikeY hx hxy, inner_smul_right, hyy]
  simp

omit [CompleteSpace E] in
/-- The variance of the Pauli-`X`-like operator in the state `x` is `1`. -/
theorem variance_pauliLikeX {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    variance (pauliLikeX x y) x = 1 := by
  rw [variance, centered_pauliLikeX hx hxy, hx, hy]
  norm_num

omit [CompleteSpace E] in
/-- The variance of the Pauli-`Y`-like operator in the state `x` is `1`. -/
theorem variance_pauliLikeY {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    variance (pauliLikeY x y) x = 1 := by
  rw [variance, centered_pauliLikeY hx hxy, norm_smul, Complex.norm_I, hx, hy]
  norm_num

/-- The commutator expectation of the Pauli-like pair has norm `2`. -/
theorem norm_commutator_pauliLike {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    ‖⟪(pauliLikeX x y ∘L pauliLikeY x y - pauliLikeY x y ∘L pauliLikeX x y) x,
      x⟫_ℂ‖ = 2 := by
  rw [norm_commutator_inner_eq (pauliLikeX_selfAdjoint x y) (pauliLikeY_selfAdjoint x y) hx,
    inner_centered_pauliLike hx hy hxy]
  simp [Complex.I_im]

/-- Schrödinger's inequality is sharp (an equality) for the Pauli-like pair. -/
theorem schrodinger_pauliLike {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    (⟪centered (pauliLikeX x y) x, centered (pauliLikeY x y) x⟫_ℂ).re ^ 2
        + (1 / 4) * ‖⟪(pauliLikeX x y ∘L pauliLikeY x y
          - pauliLikeY x y ∘L pauliLikeX x y) x, x⟫_ℂ‖ ^ 2
      = variance (pauliLikeX x y) x * variance (pauliLikeY x y) x := by
  rw [inner_centered_pauliLike hx hy hxy, norm_commutator_pauliLike hx hy hxy,
    variance_pauliLikeX hx hy hxy, variance_pauliLikeY hx hy hxy]
  simp [Complex.I_re]
  norm_num

/-- Robertson's inequality is sharp (an equality) for the Pauli-like pair. -/
theorem robertson_pauliLike_sharp {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    (1 / 4) * ‖⟪(pauliLikeX x y ∘L pauliLikeY x y
        - pauliLikeY x y ∘L pauliLikeX x y) x, x⟫_ℂ‖ ^ 2
      = variance (pauliLikeX x y) x * variance (pauliLikeY x y) x := by
  rw [norm_commutator_pauliLike hx hy hxy, variance_pauliLikeX hx hy hxy,
    variance_pauliLikeY hx hy hxy]
  norm_num

omit [CompleteSpace E] in
/-- The second moment of the Pauli-`X`-like operator in the state `x` is `1`. -/
theorem second_moment_pauliLikeX {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) :
    (⟪(pauliLikeX x y * pauliLikeX x y) x, x⟫_ℂ).re = 1 := by
  have hyx := hyx_of hxy
  have hxx := hxx_of hx
  rw [mul_apply_eq_comp, pauliLikeX_apply hx hxy, pauliLikeX_apply_y hy hxy, hxx]
  simp

/-- The second-moment form of the variance, instantiated at the Pauli-like pair. -/
theorem variance_eq_pauliLikeX {x y : E} (hx : ‖x‖ = 1) :
    variance (pauliLikeX x y) x
      = (⟪(pauliLikeX x y * pauliLikeX x y) x, x⟫_ℂ).re
        - (meanValue (pauliLikeX x y) x) ^ 2 :=
  variance_eq (pauliLikeX_selfAdjoint x y) hx

/-- An operator commutes with itself, so its commutator with itself vanishes. -/
example (x y : E) :
    pauliLikeX x y ∘L pauliLikeX x y - pauliLikeX x y ∘L pauliLikeX x y = 0 :=
  commutator_eq_zero_of_commute (Commute.refl _)

/-- The identity operator on `ℂ` has zero variance in every unit state. -/
example (x : ℂ) (hx : ‖x‖ = 1) : variance (1 : ℂ →L[ℂ] ℂ) x = 0 := by
  have hmean : meanValue (1 : ℂ →L[ℂ] ℂ) x = 1 := by
    rw [meanValue_of_norm_eq_one _ hx]
    show (⟪(1 : ℂ →L[ℂ] ℂ) x, x⟫_ℂ).re = 1
    simp [inner_self_eq_norm_sq_to_K, hx]
  rw [variance, centered, hmean]
  simp


/-- The concrete two-dimensional Pauli-like pair does not commute. -/
theorem concrete_pauli_noncommuting :
    ¬ Commute
      (pauliLikeX (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
      (pauliLikeY (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))) := by
  let x : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1
  let y : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1
  have hs := EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)
  have hx : ‖x‖ = 1 := hs.1 0
  have hy : ‖y‖ = 1 := hs.1 1
  have hxy : ⟪x, y⟫_ℂ = 0 := by
    simp [x, y, EuclideanSpace.inner_single_left, EuclideanSpace.single]
  intro h
  have hz := commutator_eq_zero_of_commute h
  have hnorm := norm_commutator_pauliLike hx hy hxy
  change ‖⟪(pauliLikeX x y ∘L pauliLikeY x y - pauliLikeY x y ∘L pauliLikeX x y) x,
    x⟫_ℂ‖ = 2 at hnorm
  change pauliLikeX x y ∘L pauliLikeY x y - pauliLikeY x y ∘L pauliLikeX x y = 0 at hz
  rw [hz, zero_apply, inner_zero_left, norm_zero] at hnorm
  norm_num at hnorm

/-- The normalized expectation of identity at a nonunit state is one. -/
theorem identity_mean_two : meanValue (1 : ℂ →L[ℂ] ℂ) (2 : ℂ) = 1 := by
  norm_num [meanValue, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_self_eq_norm_sq_to_K]

/-- Identity has a zero centered vector at a nonunit state. -/
theorem identity_centered_two : centered (1 : ℂ →L[ℂ] ℂ) (2 : ℂ) = 0 := by
  norm_num [centered, meanValue, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_self_eq_norm_sq_to_K]

/-- Identity has zero variance at a nonunit state. -/
theorem identity_variance_two : variance (1 : ℂ →L[ℂ] ℂ) (2 : ℂ) = 0 := by
  norm_num [variance, centered, meanValue, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_self_eq_norm_sq_to_K]

omit [CompleteSpace E] in
/-- Expectation depends on a ray, with Mathlib's canonical scalar invariance. -/
theorem mean_ray_invariant (A : E →L[ℂ] E) (x : E) {c : ℂ} (hc : c ≠ 0) :
    meanValue A (c • x) = meanValue A x := by
  change A.rayleighQuotient (c • x) = A.rayleighQuotient x
  exact A.rayleigh_smul x hc

omit [CompleteSpace E] in
/-- Normalized variance depends on a ray. -/
theorem variance_ray_invariant (A : E →L[ℂ] E) (x : E) {c : ℂ} (hc : c ≠ 0) :
    variance A (c • x) = variance A x :=
  variance_smul A x hc

omit [CompleteSpace E] in
/-- The totalized quantities at zero are all zero. -/
theorem zero_quantities (A : E →L[ℂ] E) :
    meanValue A 0 = 0 ∧ centered A 0 = 0 ∧ variance A 0 = 0 := by
  simp [meanValue, centered, variance]
end MathlibExtTest.Analysis.InnerProductSpace.RobertsonUncertaintyTests
