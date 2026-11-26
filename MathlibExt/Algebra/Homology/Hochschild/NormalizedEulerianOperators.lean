/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily

/-!
# Rational Eulerian operators on normalized coefficient tails

Let `k` be a commutative `ℚ`-algebra, `A` a commutative `k`-algebra, and `M` a compatible
symmetric `A`-module. The rational Eulerian element `e_n^i ∈ ℚ[S_n]` acts on the `n` factors
of the ground quotient `Ā = A/k·1`, retaining the coefficient `M`.

The resulting operators `E_n^i` are orthogonal idempotents, vanish for `i>n`, and satisfy
`∑_(i=0)^n E_n^i = id`. The rational parameter family has expansion `Ψ_n(a) = ∑_(i=0)^n a^i
E_n^i` and eigenvalue `a^i` on weight `i`. Boundary compatibility makes each weight a chain
projector. The quotient tails are ground modules, and the scalar, algebra, and coefficient
universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A

/-- The rational Eulerian operator on normalized coefficient tensors.

In degree `n`, the group-algebra element `e_n^i` acts by permutations of the `n` quotient-tail
factors of `M ⊗[k] (A/k·1)^⊗n`, retaining the coefficient. -/
def normalizedEulerianOperator (n i : ℕ) : Module.End k (M ⊗[k] TensorPower k n Q) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianElement n i)

/-- The rational convolution family on normalized coefficient tensors.

For `a ∈ ℚ`, the element `λ_n(a)` acts on the normalized tensor tails, giving the parameter
operator `Ψ_n(a)`. -/
def normalizedConvolutionOperator (n : ℕ) (a : ℚ) : Module.End k (M ⊗[k] TensorPower k n Q) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianLambda n a)

/-- The Eulerian expansion of normalized convolution.

In degree `n`, one has `Ψ_n(a) = ∑_(i=0)^n algebraMap(ℚ,k)(a^i) • E_n^i`. -/
theorem normalizedConvolutionOperator_eq_sum (n : ℕ) (a : ℚ) :
    normalizedConvolutionOperator k A M n a =
      ∑ i : Fin (n + 1), algebraMap ℚ k (a ^ i.val) • normalizedEulerianOperator k A M n i.val := by
  rw [normalizedConvolutionOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp only [TensorPower.coefficientRationalPermutationAction_smul, normalizedEulerianOperator]

/-- Completeness of normalized Eulerian operators in one degree.

The sum of the weight operators `E_n^i` for `0 ≤ i ≤ n` is the identity on the normalized
degree-`n` coefficient tensor module. -/
theorem normalizedEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), normalizedEulerianOperator k A M n i.val) = LinearMap.id := by
  change (∑ i : Fin (n + 1),
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n (Equiv.Perm.eulerianElement n i.val)) = 1
  rw [← map_sum, (Equiv.Perm.eulerianElement_projector_laws n).1, map_one]

/-- Orthogonality and idempotence of normalized Eulerian operators.

For all weights `i,j`, one has `E_n^i ∘ E_n^j = E_n^i` when `i=j`, and zero otherwise. -/
theorem normalizedEulerianOperator_comp (n i j : ℕ) :
    (normalizedEulerianOperator k A M n i).comp (normalizedEulerianOperator k A M n j) =
      if i = j then normalizedEulerianOperator k A M n i else 0 := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n i) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n j) = _
  rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j]
  split_ifs
  · rfl
  · exact map_zero (TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := Q) n)

/-- Vanishing of normalized Eulerian weights above the tensor degree.

If `n<i`, the normalized weight-`i` operator in degree `n` is zero. -/
theorem normalizedEulerianOperator_outside (n i : ℕ) (h : n < i) :
    normalizedEulerianOperator k A M n i = 0 := by
  rw [normalizedEulerianOperator, Equiv.Perm.eulerianElement_outside n i h, map_zero]

/-- The left convolution eigenvalue on a normalized Eulerian weight.

For `i ≤ n` and `a ∈ ℚ`, `Ψ_n(a) ∘ E_n^i = algebraMap(ℚ,k)(a^i) • E_n^i`. -/
theorem normalizedConvolutionOperator_comp_eulerian
    (n i : ℕ) (h : i ≤ n) (a : ℚ) :
    (normalizedConvolutionOperator k A M n a).comp (normalizedEulerianOperator k A M n i) =
      algebraMap ℚ k (a ^ i) • normalizedEulerianOperator k A M n i := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianLambda n a) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := Q) n
      (Equiv.Perm.eulerianElement n i) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul_eulerianElement n i h a,
    TensorPower.coefficientRationalPermutationAction_smul]
  rfl

/-- The right convolution eigenvalue on a normalized Eulerian weight.

For `i ≤ n` and `a ∈ ℚ`, `E_n^i ∘ Ψ_n(a) = algebraMap(ℚ,k)(a^i) • E_n^i`. -/
theorem normalizedEulerianOperator_comp_convolution
    (n i : ℕ) (h : i ≤ n) (a : ℚ) :
    (normalizedEulerianOperator k A M n i).comp (normalizedConvolutionOperator k A M n a) =
      algebraMap ℚ k (a ^ i) • normalizedEulerianOperator k A M n i := by
  classical
  let i₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le h⟩
  rw [normalizedConvolutionOperator_eq_sum]
  have hsum : (normalizedEulerianOperator k A M n i).comp
      (∑ j : Fin (n + 1), algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) =
    ∑ j : Fin (n + 1), (normalizedEulerianOperator k A M n i).comp
      (algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) := by
    apply LinearMap.ext
    intro x
    have hmap := map_sum (normalizedEulerianOperator k A M n i)
      (fun j : Fin (n + 1) =>
        (algebraMap ℚ k (a ^ j.val) • normalizedEulerianOperator k A M n j.val) x) Finset.univ
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using hmap
  rw [hsum]
  simp only [LinearMap.comp_smul, normalizedEulerianOperator_comp]
  rw [Finset.sum_eq_single i₀]
  · simp [i₀]
  · intro j _ hj
    have hne : i ≠ j.val := fun he => hj (Fin.ext he.symm)
    simp only [hne, if_false, smul_zero]
  · simp

/-- The ground restriction of a normalized coefficient-algebra Eulerian operator.

Restricting the `A`-linear normalized Eulerian operator to `k` gives the coefficient-fixed
ground operator `E_n^i`. -/
theorem algebraNormalizedEulerianOperator_eq_ground (n i : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).restrictScalars k =
      normalizedEulerianOperator k A M n i :=
  algebraNormalizedEulerianOperator_restrictScalars k A M n i

/-- Boundary compatibility of normalized Eulerian weights.

The normalized Hochschild boundary intertwines the same weight in consecutive degrees: `b_n ∘
E_(n+1)^i = E_n^i ∘ b_n`. -/
theorem normalizedEulerianOperator_boundary (n i : ℕ) :
    ((normalizedChainComplex k A M).d (n + 1) n).hom.comp
        (normalizedEulerianOperator k A M (n + 1) i) =
      (normalizedEulerianOperator k A M n i).comp
        ((normalizedChainComplex k A M).d (n + 1) n).hom := by
  change ((algebraNormalizedBoundary k A M n).restrictScalars k).comp
      (normalizedEulerianOperator k A M (n + 1) i) =
    (normalizedEulerianOperator k A M n i).comp ((algebraNormalizedBoundary k A M n).restrictScalars k)
  have h := congrArg (fun f => f.restrictScalars k)
    (algebraNormalizedEulerianOperator_boundary k A M n i)
  simpa only [LinearMap.restrictScalars_comp, algebraNormalizedEulerianOperator_eq_ground] using h

/-- The normalized Eulerian chain projector of a fixed weight.

For weight `i`, the degree components `E_n^i` commute with the normalized boundary and define
a chain endomorphism. -/
def normalizedEulerianChainMap (i : ℕ) : normalizedChainComplex k A M ⟶ normalizedChainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (normalizedEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    exact normalizedEulerianOperator_boundary k A M n i)

end ModuleCat.Algebra.Hochschild.Symmetric
