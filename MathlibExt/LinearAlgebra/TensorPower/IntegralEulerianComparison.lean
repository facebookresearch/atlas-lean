/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.IntegralConvolutionOperators
public import MathlibExt.Combinatorics.Perm.EulerianComposition

/-!
# The actual integral convolution inside the rational Eulerian family

The existing stable-sort fibre count identifies the integral operation at
each natural parameter with the original rational descent polynomial. The
identification is transported through the actual ground algebra map and
the original coefficient-word representation. The sign of true integer
lambda is retained; no sign is interpolated at rational parameters.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace Equiv.Perm

/-- The integral labeling sum at rational coefficients is the same original sorting sum. -/
theorem integralConvolutionElement_rat (n m : ℕ) :
    integralConvolutionElement ℚ n m = eulerianLambda n (m : ℚ) :=
  signedStableSortElement_eq_eulerianLambda n m

variable (k : Type u) [CommRing k] [Algebra ℚ k]

/-- Scalar extension sends the actual rational convolution to the integral operation over the original ground. -/
theorem map_eulerianLambda_nat (n m : ℕ) :
    (MonoidAlgebra.mapRingHom (Perm (Fin n)) (algebraMap ℚ k))
        (eulerianLambda n (m : ℚ)) = integralConvolutionElement k n m := by
  classical
  rw [← integralConvolutionElement_rat, integralConvolutionElement, map_sum,
    integralConvolutionElement]
  simp only [MonoidAlgebra.mapRingHom_single, map_intCast]

end Equiv.Perm

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The actual neutral integral operation is the original rational family at its natural parameter. -/
theorem coefficientIntegralConvolutionOperator_eq_eulerian (n m : ℕ) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m =
      coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (Equiv.Perm.eulerianLambda n (m : ℚ)) := by
  rw [coefficientRationalPermutationAction]
  change _ = coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
      (Equiv.Perm.eulerianLambda n (m : ℚ)))
  rw [Equiv.Perm.map_eulerianLambda_nat]
  rfl

/-- The original true integer lambda is the exact signed rational convolution value. -/
theorem coefficientTrueIntegerLambdaOperator_eq_eulerian (n m : ℕ) (hm : 0 < m) :
    coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm =
      (-1 : k) ^ (m - 1) • coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (Equiv.Perm.eulerianLambda n (m : ℚ)) := by
  rw [coefficientTrueIntegerLambdaOperator_eq_signed,
    coefficientIntegralConvolutionOperator_eq_eulerian]

end TensorPower
