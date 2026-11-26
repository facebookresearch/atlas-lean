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
# Integral convolution at rational Eulerian parameters

Let k be a commutative ℚ-algebra and M,V k-modules. At every natural parameter m, scalar
extension identifies the integral labeling element Bₙ(m) with the rational Eulerian element
Λₙ(m). Consequently their coefficient tensor actions agree. The signed integer lambda operator
is (-1)^(m-1) times this action for m > 0.

The integral labeling operators are defined over arbitrary commutative rings; the comparison
with rational coefficients uses ℚ → k. See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace Equiv.Perm

/-- The integral labeling element at a rational parameter.

For n,m ≥ 0, the signed stable-sort sum in ℚ[Sₙ] equals the Eulerian convolution element
Λₙ(m), with m viewed as a rational number. -/
theorem integralConvolutionElement_rat (n m : ℕ) :
    integralConvolutionElement ℚ n m = eulerianLambda n (m : ℚ) :=
  signedStableSortElement_eq_eulerianLambda n m

variable (k : Type u) [CommRing k] [Algebra ℚ k]

/-- Scalar extension of a natural Eulerian parameter.

For a commutative ℚ-algebra k and n,m ≥ 0, extending coefficients along ℚ → k sends Λₙ(m) ∈
ℚ[Sₙ] to the integral convolution element Bₙ(m) ∈ k[Sₙ]. -/
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

/-- Agreement of integral and rational coefficient tensor actions.

For a commutative ℚ-algebra k, k-modules M,V and m ≥ 0, integral convolution Bₙ(m) on M ⊗
V⊗n equals the action of Λₙ(m) with its rational coefficients mapped to k. -/
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

/-- The rational expression of the signed integer operator.

For a commutative ℚ-algebra k, k-modules M,V and m > 0, Lₙ(m) = (-1)^(m-1) · ρₙ,M(Λₙ(m)) on
M ⊗ V⊗n. -/
theorem coefficientTrueIntegerLambdaOperator_eq_eulerian (n m : ℕ) (hm : 0 < m) :
    coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm =
      (-1 : k) ^ (m - 1) • coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (Equiv.Perm.eulerianLambda n (m : ℚ)) := by
  rw [coefficientTrueIntegerLambdaOperator_eq_signed,
    coefficientIntegralConvolutionOperator_eq_eulerian]

end TensorPower
