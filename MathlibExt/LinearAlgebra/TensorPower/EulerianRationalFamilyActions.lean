/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily
public import MathlibExt.LinearAlgebra.TensorPower.PermutationShuffleActions

/-!
# Actual rational convolution Eulerian actions on coefficient tensors

The rational group-ring representation transports the actual
rational multiplication and reciprocal identities to the original tensor
level. The convolution family bar-lambda commutes with independent
coefficient maps and uniform tail maps. The original signed tensor
shuffle law holds at every rational parameter. These are level actions;
this owner does not assume a Hochschild boundary or homology law.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v w v' w'

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {W : Type v'} [AddCommGroup W] [Module k W]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- The actual rational convolution family acts multiplicatively on the original coefficient tensor. -/
theorem coefficientEulerianLambda_mul (n : ℕ) (a b : ℚ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a)).comp
        (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n b)) =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n (a * b)) := by
  change coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a) *
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n b) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul]

/-- Every actual rational parameter acts by its original power on the original coefficient Eulerian piece. -/
theorem coefficientEulerianLambda_comp_eulerian (n i : ℕ) (hi : i ≤ n) (a : ℚ) :
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a)).comp
      (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianElement n i)) =
    algebraMap ℚ k (a ^ i) • coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.eulerianElement n i) := by
  change coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a) *
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianElement n i) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul_eulerianElement n i hi a,
    coefficientRationalPermutationAction_smul]

/-- The actual nonzero rational parameter has the original reciprocal-parameter inverse on every coefficient level. -/
def coefficientEulerianLambdaEquiv (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    M ⊗[k] TensorPower k n V ≃ₗ[k] M ⊗[k] TensorPower k n V :=
  LinearEquiv.ofLinearMap
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a))
    (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a⁻¹))
    (by rw [coefficientEulerianLambda_mul (k := k) (M := M) (V := V), mul_inv_cancel₀ ha,
      Equiv.Perm.eulerianLambda_one, map_one]; rfl)
    (by rw [coefficientEulerianLambda_mul (k := k) (M := M) (V := V), inv_mul_cancel₀ ha,
      Equiv.Perm.eulerianLambda_one, map_one]; rfl)

/-- The actual equivalence's forward map is the original convolution family action. -/
theorem coefficientEulerianLambdaEquiv_toLinearMap (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (coefficientEulerianLambdaEquiv (k := k) (M := M) (V := V) n a ha).toLinearMap =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a) := rfl

/-- The actual equivalence's inverse map is the original reciprocal convolution family action. -/
theorem coefficientEulerianLambdaEquiv_symm_toLinearMap (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (coefficientEulerianLambdaEquiv (k := k) (M := M) (V := V) n a ha).symm.toLinearMap =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a⁻¹) := rfl

/-- The actual finite rational family commutes with independent coefficient maps and uniform original tail maps. -/
theorem coefficientEulerianLambda_naturality (n : ℕ) (a : ℚ) (f : M →ₗ[k] N) (g : V →ₗ[k] W) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
        (coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (Equiv.Perm.eulerianLambda n a)) =
      (coefficientRationalPermutationAction (k := k) (M := N) (V := W) n (Equiv.Perm.eulerianLambda n a)).comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  rw [Equiv.Perm.eulerianLambda, coefficientRationalPermutationAction_sum,
    coefficientRationalPermutationAction_sum]
  exact coefficientPermutationOperator_naturality n _ g f

/-- The actual rational convolution operation respects the original signed tensor shuffle product. -/
theorem rationalEulerianLambda_signedShuffleProduct_rat (p q : ℕ) (a : ℚ) :
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.eulerianLambda (p + q) a)).comp
        (signedShuffleProduct (k := k) (V := V) p q) =
      (signedShuffleProduct (k := k) (V := V) p q).comp (TensorProduct.map
        (rationalPermutationAction (k := k) (V := V) p (Equiv.Perm.eulerianLambda p a))
        (rationalPermutationAction (k := k) (V := V) q (Equiv.Perm.eulerianLambda q a))) := by
  have h := congrArg (rationalPermutationAction (k := k) (V := V) (p + q))
    (Equiv.Perm.eulerianLambda_mul_signedShuffle_rat p q a)
  rw [map_mul, map_mul, rationalPermutationAction_signedShuffle] at h
  change (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.eulerianLambda (p + q) a)).comp
      (signedShuffleEnd (k := k) (V := V) p q) = (signedShuffleEnd (k := k) (V := V) p q).comp
    (rationalPermutationAction (k := k) (V := V) (p + q) (Equiv.Perm.splitEulerianLambda p q a)) at h
  have hcomp := congrArg (fun f => f.comp
    (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap) h
  simpa only [signedShuffleProduct, LinearMap.comp_assoc,
    rationalPermutationAction_splitEulerianLambda] using hcomp

end TensorPower
