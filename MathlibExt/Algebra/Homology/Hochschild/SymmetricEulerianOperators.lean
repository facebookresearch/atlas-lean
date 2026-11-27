/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianShuffle
public import MathlibExt.Combinatorics.Perm.EulerianProjectors

/-!
# Rational Eulerian projectors and convolution on coefficient tensors

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module. The
projectors eₙ⁽ⁱ⁾ act on M ⊗[k] A⊗n by rational signed place permutations fixing M. Their
convolution family is Λₙ(a)=∑ᵢaⁱeₙ⁽ⁱ⁾. The operator lambdaTwoOperator is Λₙ(2); for positive
degree it differs from 2·id by a proper both-positive shuffle image. Loday's integer operation
at m>0 has the additional scalar (-1)^(m-1), so its second operation is -Λₙ(2). Degree zero
has e₀⁽⁰⁾=id.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for Eulerian idempotents and lambda
operations.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The rational Eulerian projector of a coefficient tensor level.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾
acts on M ⊗[k] A⊗n through the rational permutation element eulerianElement(n,i), fixing the
coefficient M. -/
def coefficientEulerianOperator (n i : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianElement n i)

/-- The coefficient convolution operator at parameter two.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
lambdaTwoOperator(n) is the action of Λₙ(2)=∑ᵢ₌₀ⁿ 2ⁱeₙ⁽ⁱ⁾. It is the convolution family at
two; the signed integer second lambda operation is its negative. -/
def lambdaTwoOperator (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianLambda n 2)

/-- The coefficient Eulerian operators are a complete orthogonal projector family.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
weights 0,…,n sum to id, and eₙ⁽ⁱ⁾eₙ⁽ʲ⁾ is eₙ⁽ⁱ⁾ if i=j and zero otherwise. -/
theorem coefficientEulerian_projector_laws (n : ℕ) :
    (∑ i : Fin (n + 1), coefficientEulerianOperator k A M n i.val) = LinearMap.id ∧
      ∀ i j : ℕ, (coefficientEulerianOperator k A M n i).comp
          (coefficientEulerianOperator k A M n j) =
        if i = j then coefficientEulerianOperator k A M n i else 0 := by
  classical
  let ρ := TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := A) n
  constructor
  · change (∑ i : Fin (n + 1), ρ (Equiv.Perm.eulerianElement n i.val)) = 1
    rw [← map_sum, (Equiv.Perm.eulerianElement_projector_laws n).1, map_one]
  · intro i j
    change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n j) =
      if i = j then ρ (Equiv.Perm.eulerianElement n i) else 0
    rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j]
    split_ifs <;> simp

/-- Coefficient Eulerian weights above their tensor degree vanish.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾=0
when n<i. -/
theorem coefficientEulerian_outside (n i : ℕ) (hi : n < i) :
    coefficientEulerianOperator k A M n i = 0 := by
  rw [coefficientEulerianOperator, Equiv.Perm.eulerianElement_outside n i hi, map_zero]

/-- The zero Eulerian weight vanishes in positive tensor degree.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽⁰⁾=0
for n>0. -/
theorem coefficientEulerian_zero_weight (n : ℕ) (hn : 0 < n) :
    coefficientEulerianOperator k A M n 0 = 0 := by
  unfold coefficientEulerianOperator Equiv.Perm.eulerianElement
  simp_rw [Equiv.Perm.eulerianCoefficient_zero_weight n _ hn, MonoidAlgebra.single_zero]
  rw [Finset.sum_const_zero, map_zero]

/-- The degree-zero coefficient Eulerian projector is the identity.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, e₀⁽⁰⁾=id
on M ⊗[k] A⊗0. -/
theorem coefficientEulerian_degree_zero : coefficientEulerianOperator k A M 0 0 = LinearMap.id := by
  classical
  have h0 : Equiv.Perm.eulerianElement 0 0 = 1 := by
    letI : Unique (Equiv.Perm (Fin 0)) :=
      { default := 1, uniq := fun σ => Subsingleton.elim _ _ }
    unfold Equiv.Perm.eulerianElement
    rw [Fintype.sum_unique, Equiv.Perm.eulerianCoefficient_degree_zero]
    rfl
  rw [coefficientEulerianOperator, h0, map_one]
  rfl

/-- The eigenvalue expansion of coefficient convolution at two.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
Λₙ(2)=∑ᵢ₌₀ⁿ algebraMap(2ⁱ)·eₙ⁽ⁱ⁾ on coefficient tensors. -/
theorem lambdaTwoOperator_eq_sum (n : ℕ) :
    lambdaTwoOperator k A M n = ∑ i : Fin (n + 1),
      algebraMap ℚ k ((2 : ℚ) ^ i.val) • coefficientEulerianOperator k A M n i.val := by
  classical
  rw [lambdaTwoOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp_rw [TensorPower.coefficientRationalPermutationAction_smul]
  rfl

/-- Each both-positive coefficient shuffle cut lands in the proper relation module.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, for
p,q>0 with p+q=n, coefficientShuffleCutEnd(p,q)(x) lies in rawPositiveRelations(n). -/
theorem properCoefficientShuffleCut_mem (n : ℕ) (z : TensorPower.ProperShuffleDegreeCut n)
    (x : M ⊗[k] TensorPower k n A) :
    coefficientShuffleCutEnd k A M z.val x ∈ rawPositiveRelations k A M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages (pairing.{u, v, w} k A M)
    z.val.val.1 z.val.val.2 n z.val.property z.property.1 z.property.2
      (coefficientShuffleCutInput k A M z.val x)

/-- Convolution at two equals twice the identity modulo proper shuffles.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, for n>0,
Λₙ(2)(x)-2x lies in rawPositiveRelations(n) for every coefficient tensor x. -/
theorem lambdaTwo_sub_two_mem (n : ℕ) (hn : 0 < n) (x : M ⊗[k] TensorPower k n A) :
    lambdaTwoOperator k A M n x - (2 : k) • x ∈ rawPositiveRelations k A M n := by
  rw [lambdaTwoOperator, coefficientEulerianLambda_two_eq_proper_pairings k A M n hn,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, add_sub_cancel_left,
    totalProperCoefficientShuffleCutEnd, LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun z _ => properCoefficientShuffleCut_mem k A M n z x)

/-- Convolution at two intertwines the coefficient shuffle pairing.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, on a
(p,q) pairing, applying Λₚ₊ᵩ(2) to the output equals pairing the two inputs after their
respective convolution-at-two operators. -/
theorem lambdaTwo_pairing (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  (lambdaTwoOperator k A M (p + q)).comp ((pairing.{u, v, w} k A M).pair p q).hom =
    ((pairing.{u, v, w} k A M).pair p q).hom.comp
      (TensorProduct.map (lambdaTwoOperator k A (ULift.{w} A) p) (lambdaTwoOperator k A M q)) :=
  coefficientEulerianLambda_pairing k A M p q 2

/-- The right Eulerian eigenspace identity at parameter two.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, for i≤n,
Λₙ(2) ∘ eₙ⁽ⁱ⁾=algebraMap(2ⁱ)·eₙ⁽ⁱ⁾. -/
theorem lambdaTwo_comp_eulerian (n i : ℕ) (hi : i ≤ n) :
    (lambdaTwoOperator k A M n).comp (coefficientEulerianOperator k A M n i) =
      algebraMap ℚ k ((2 : ℚ) ^ i) • coefficientEulerianOperator k A M n i := by
  classical
  let j₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  rw [lambdaTwoOperator_eq_sum]
  have hsum : (∑ j : Fin (n + 1),
      algebraMap ℚ k ((2 : ℚ) ^ j.val) • coefficientEulerianOperator k A M n j.val).comp
        (coefficientEulerianOperator k A M n i) =
    ∑ j : Fin (n + 1),
      (algebraMap ℚ k ((2 : ℚ) ^ j.val) • coefficientEulerianOperator k A M n j.val).comp
        (coefficientEulerianOperator k A M n i) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hsum]
  simp only [LinearMap.smul_comp]
  simp_rw [(coefficientEulerian_projector_laws k A M n).2]
  rw [Finset.sum_eq_single j₀]
  · simp [j₀]
  · intro j hj hne
    have hji : j.val ≠ i := fun h => hne (Fin.ext h)
    simp [hji]
  · simp

/-- The left Eulerian eigenspace identity at parameter two.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, for i≤n,
eₙ⁽ⁱ⁾ ∘ Λₙ(2)=algebraMap(2ⁱ)·eₙ⁽ⁱ⁾. -/
theorem eulerian_comp_lambdaTwo (n i : ℕ) (hi : i ≤ n) :
    (coefficientEulerianOperator k A M n i).comp (lambdaTwoOperator k A M n) =
      algebraMap ℚ k ((2 : ℚ) ^ i) • coefficientEulerianOperator k A M n i := by
  classical
  let j₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  rw [lambdaTwoOperator_eq_sum]
  have hsum : (coefficientEulerianOperator k A M n i).comp
      (∑ j : Fin (n + 1),
        algebraMap ℚ k ((2 : ℚ) ^ j.val) • coefficientEulerianOperator k A M n j.val) =
    ∑ j : Fin (n + 1), (coefficientEulerianOperator k A M n i).comp
      (algebraMap ℚ k ((2 : ℚ) ^ j.val) • coefficientEulerianOperator k A M n j.val) := by
    apply LinearMap.ext
    intro x
    have h := map_sum (coefficientEulerianOperator k A M n i)
      (fun j : Fin (n + 1) =>
        (algebraMap ℚ k ((2 : ℚ) ^ j.val) • coefficientEulerianOperator k A M n j.val) x) Finset.univ
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using h
  rw [hsum]
  simp only [LinearMap.comp_smul]
  simp_rw [(coefficientEulerian_projector_laws k A M n).2]
  rw [Finset.sum_eq_single j₀]
  · simp [j₀]
  · intro j hj hne
    have hji : i ≠ j.val := fun h => hne (Fin.ext h.symm)
    simp [hji]
  · simp

end ModuleCat.Algebra.Hochschild.Symmetric
