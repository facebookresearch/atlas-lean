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
# Rational coefficient Eulerian operators

Over a ground ring containing ℚ, rational permutation
projectors act on the coefficient-fixed tensor tails.
The convolution family is bar-lambda,
eulerianLambda n a = ∑ i, a^i eₙⁱ. For a positive
integer m, Loday’s lambdaₙᵐ is (-1)^(m - 1) times
bar-lambda at m. Thus lambdaTwo denotes bar-lambda
at two, and Loday’s second lambda is its negative.
Rational parameters interpolate the convolution family;
degree zero retains its stated unit convention.
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

/-- The original coefficient-fixed operator of the rational Eulerian group-ring element. -/
def coefficientEulerianOperator (n i : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianElement n i)

/-- The original coefficient-fixed second operation is the rational evaluation at two. -/
def lambdaTwoOperator (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianLambda n 2)

/-- The finite rational projectors act as coefficient-fixed projectors. -/
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

/-- Every coefficient projector beyond its original homogeneous degree is zero. -/
theorem coefficientEulerian_outside (n i : ℕ) (hi : n < i) :
    coefficientEulerianOperator k A M n i = 0 := by
  rw [coefficientEulerianOperator, Equiv.Perm.eulerianElement_outside n i hi, map_zero]

/-- The zero-weight coefficient projector vanishes in every positive degree. -/
theorem coefficientEulerian_zero_weight (n : ℕ) (hn : 0 < n) :
    coefficientEulerianOperator k A M n 0 = 0 := by
  unfold coefficientEulerianOperator Equiv.Perm.eulerianElement
  simp_rw [Equiv.Perm.eulerianCoefficient_zero_weight n _ hn, MonoidAlgebra.single_zero]
  rw [Finset.sum_const_zero, map_zero]

/-- The original zero-degree coefficient is retained by the zero-weight projector. -/
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

/-- The second operation has the exact original finite Eulerian expansion. -/
theorem lambdaTwoOperator_eq_sum (n : ℕ) :
    lambdaTwoOperator k A M n = ∑ i : Fin (n + 1),
      algebraMap ℚ k ((2 : ℚ) ^ i.val) • coefficientEulerianOperator k A M n i.val := by
  classical
  rw [lambdaTwoOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp_rw [TensorPower.coefficientRationalPermutationAction_smul]
  rfl

/-- Every proper cut value lies in the original proper relation family. -/
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

/-- The reduced second lambda value lies in the original proper relation module. -/
theorem lambdaTwo_sub_two_mem (n : ℕ) (hn : 0 < n) (x : M ⊗[k] TensorPower k n A) :
    lambdaTwoOperator k A M n x - (2 : k) • x ∈ rawPositiveRelations k A M n := by
  rw [lambdaTwoOperator, coefficientEulerianLambda_two_eq_proper_pairings k A M n hn,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, add_sub_cancel_left,
    totalProperCoefficientShuffleCutEnd, LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun z _ => properCoefficientShuffleCut_mem k A M n z x)

/-- The second lambda operation respects the original concrete coefficient pairing. -/
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

/-- The second operation has the original Eulerian eigenvalue on each original projector. -/
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

/-- Projecting an second-operation eigenvector retains the original eigenvalue. -/
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
