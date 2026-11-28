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

Let k be a commutative ring and M,V k-modules. For n,m ≥ 0, define Bₙ(m) on M ⊗ V⊗n by summing
over labelings f : Fin n → Fin m. Each summand is sign(sort(f)) times the place permutation
sort(f), and it fixes the coefficient in M. Stable sorting gives Bₙ(l)Bₙ(m) = Bₙ(lm).

For m > 0 the signed integer operation is Lₙ(m) = (-1)^(m-1)Bₙ(m). Its composition retains the
scalar (-1)^((l-1)(m-1)). These operators are defined over every commutative ring. For Eulerian
convolution and its integer parameters, see J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The signed stable-sort convolution operator.

For a commutative ring k, k-modules M,V and n,m ≥ 0, Bₙ(m) is the endomorphism of M ⊗ V⊗n
given by ∑f:Fin n→Fin m sign(sort(f)) · ρₙ,M(sort(f)). The coefficient in M is fixed. -/
def coefficientIntegralConvolutionOperator (n m : ℕ) :
    Module.End k (M ⊗[k] TensorPower k n V) :=
  coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.integralConvolutionElement k n m)

/-- The labeling sum for integral convolution.

For a commutative ring k and k-modules M,V, Bₙ(m) equals ∑f:Fin n→Fin m sign(sort(f)) ·
ρₙ,M(sort(f)) on M ⊗ V⊗n. The stable-sort sign is mapped from ℤ to k. -/
theorem coefficientIntegralConvolutionOperator_eq_sum (n m : ℕ) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m =
      ∑ f : Fin n → Fin m, (((Tuple.sort f).sign : ℤ) : k) •
        coefficientPermutationRepresentation (k := k) (M := M) (V := V) n (Tuple.sort f) := by
  classical
  rw [coefficientIntegralConvolutionOperator, Equiv.Perm.integralConvolutionElement, map_sum]
  simp only [coefficientPermutationGroupAlgebraAction_single]

/-- Composition of integral convolution operators.

For a commutative ring k, k-modules M,V and natural parameters l,m, Bₙ(l) ∘ Bₙ(m) = Bₙ(lm)
on M ⊗ V⊗n. -/
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

/-- Integral convolution on the empty tensor word.

For a commutative ring k, k-modules M,V and every m ≥ 0, B₀(m) is the identity on M ⊗ V⊗0,
including when the labeling alphabet is empty. -/
theorem coefficientIntegralConvolutionOperator_degree_zero (m : ℕ) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) 0 m = LinearMap.id := by
  rw [coefficientIntegralConvolutionOperator, Equiv.Perm.integralConvolutionElement_degree_zero,
    map_one]
  rfl

/-- The empty-alphabet operator in positive degree.

For a commutative ring k, k-modules M,V and n > 0, Bₙ(0) = 0 on M ⊗ V⊗n, since no labeling
Fin n → Fin 0 exists. -/
theorem coefficientIntegralConvolutionOperator_zero_parameter (n : ℕ) (hn : 0 < n) :
    coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n 0 = 0 := by
  rw [coefficientIntegralConvolutionOperator,
    Equiv.Perm.integralConvolutionElement_zero_parameter k n hn, map_zero]

/-- The signed integer lambda operator.

For a commutative ring k, k-modules M,V and m > 0, Lₙ(m) is the endomorphism (-1)^(m-1)Bₙ(m)
of M ⊗ V⊗n, where Bₙ(m) is signed stable-sort convolution. -/
def coefficientTrueIntegerLambdaOperator (n m : ℕ) (hm : 0 < m) :
    Module.End k (M ⊗[k] TensorPower k n V) :=
  coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
    (Equiv.Perm.trueLambdaElement k n m hm)

/-- The parameter sign in integer lambda.

For a commutative ring k, k-modules M,V and m > 0, Lₙ(m) = (-1)^(m-1) · Bₙ(m) on M ⊗ V⊗n. -/
theorem coefficientTrueIntegerLambdaOperator_eq_signed (n m : ℕ) (hm : 0 < m) :
    coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm =
      (-1 : k) ^ (m - 1) •
        coefficientIntegralConvolutionOperator (k := k) (M := M) (V := V) n m := by
  rw [coefficientTrueIntegerLambdaOperator, Equiv.Perm.trueLambdaElement, map_smul]
  rfl

/-- The parity scalar in integer lambda composition.

For a commutative ring k, k-modules M,V and l,m > 0, Lₙ(l) ∘ Lₙ(m) = (-1)^((l-1)(m-1)) ·
Lₙ(lm) on M ⊗ V⊗n. -/
theorem coefficientTrueIntegerLambdaOperator_comp (n l m : ℕ) (hl : 0 < l) (hm : 0 < m) :
    (coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n l hl).comp
      (coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n m hm) =
        (-1 : k) ^ ((l - 1) * (m - 1)) •
          coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := V) n (l * m)
            (Nat.mul_pos hl hm) := by
  change coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.trueLambdaElement k n l hl) *
    coefficientPermutationGroupAlgebraAction (k := k) (M := M) (V := V) n
      (Equiv.Perm.trueLambdaElement k n m hm) = _
  rw [← map_mul, Equiv.Perm.trueLambdaElement_mul k n l m hl hm, map_smul]
  rfl

end TensorPower
