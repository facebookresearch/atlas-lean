/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.IntegralConvolution
public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation

/-!
# Integral convolution on coefficient tensor words

The finite signed labeling sum acts by place permutations on the tensor
factors while fixing the coefficient. The stable-sort product identity gives
composition over every commutative ground ring. The signed integer operation
includes the additional scalar `(-1)^(m - 1)` at positive parameter `m`.
No rational coefficients are required.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The original signed finite-alphabet convolution on actual coefficient words. -/
def coefficientIntegralConvolutionOperator (n m : ℕ) :
    Module.End k (M ⊗[k] TensorPower k n V) :=
  coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.integralConvolutionElement k n m)

/-- Every labeling acts by its scalar sign and its original place permutation. -/
theorem coefficientIntegralConvolutionOperator_eq_sum (n m : ℕ) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m =
      ∑ f : Fin n → Fin m, (((Tuple.sort f).sign : ℤ) : k) •
        coefficientPermutationRepresentation (k := k) (M := M) (V := V) n (Tuple.sort f) := by
  classical
  rw [coefficientIntegralConvolutionOperator, Equiv.Perm.integralConvolutionElement, map_sum]
  simp only [coefficientPermutationGroupAlgebraAction_single]

/-- Actual coefficient convolution composes by the product of its integral parameters. -/
theorem coefficientIntegralConvolutionOperator_comp (n l m : ℕ) :
    (coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n l).comp
      (coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m) =
        coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n (l * m) := by
  change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.integralConvolutionElement k n l) *
    coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.integralConvolutionElement k n m) = _
  rw [← map_mul, Equiv.Perm.integralConvolutionElement_mul]
  rfl

/-- The empty original word retains the actual unit convolution. -/
theorem coefficientIntegralConvolutionOperator_degree_zero (m : ℕ) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) 0 m = LinearMap.id := by
  rw [coefficientIntegralConvolutionOperator, Equiv.Perm.integralConvolutionElement_degree_zero,
    map_one]
  rfl

/-- The empty alphabet has zero actual action on positive-degree words. -/
theorem coefficientIntegralConvolutionOperator_zero_parameter (n : ℕ) (hn : 0 < n) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n 0 = 0 := by
  rw [coefficientIntegralConvolutionOperator,
    Equiv.Perm.integralConvolutionElement_zero_parameter k n hn, map_zero]

/-- The true integer operation on actual coefficient words, with the original parameter sign. -/
def coefficientTrueIntegerLambdaOperator (n m : ℕ) (hm : 0 < m) :
    Module.End k (M ⊗[k] TensorPower k n V) :=
  coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.trueLambdaElement k n m hm)

/-- The true lambda operation is the actual signed convolution, not a differently named projector. -/
theorem coefficientTrueIntegerLambdaOperator_eq_signed (n m : ℕ) (hm : 0 < m) :
    coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm =
      (-1 : k) ^ (m - 1) • coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m := by
  rw [coefficientTrueIntegerLambdaOperator, Equiv.Perm.trueLambdaElement, map_smul]
  rfl

/-- The real integral true-lambda composition retains its exact positive-parameter parity scalar. -/
theorem coefficientTrueIntegerLambdaOperator_comp (n l m : ℕ) (hl : 0 < l) (hm : 0 < m) :
    (coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n l hl).comp
      (coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm) =
        (-1 : k) ^ ((l - 1) * (m - 1)) •
          coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n (l * m) (Nat.mul_pos hl hm) := by
  change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.trueLambdaElement k n l hl) *
    coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.trueLambdaElement k n m hm) = _
  rw [← map_mul, Equiv.Perm.trueLambdaElement_mul k n l m hl hm, map_smul]
  rfl

end TensorPower
