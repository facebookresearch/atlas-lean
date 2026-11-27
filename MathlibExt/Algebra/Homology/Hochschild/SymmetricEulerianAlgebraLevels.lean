/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNormalizedPositiveAlgebra
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianPositiveKernel
public import MathlibExt.LinearAlgebra.TensorPower.EulerianRationalFamilyActions

/-!
# A-linear Eulerian projectors and proper-shuffle quotient levels

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module. The
coefficient-fixed Eulerian projectors eₙ⁽ⁱ⁾ are A-linear on M ⊗[k] A⊗n and on its normalized
tails. Normalization intertwines their actions. The projector pₙ=eₙ⁽⁰⁾+eₙ⁽¹⁾ has kernel equal
to the proper both-positive shuffle relation module, giving a quotient-to-image equivalence in
both raw and normalized coordinates.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for the rational Eulerian decomposition.
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

/-- The A-linear Eulerian projector on raw coefficient tensors.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾
acts by its rational signed permutation weights on the A-tail word and fixes M. -/
def algebraEulerianOperator (n i : ℕ) : Module.End A (M ⊗[k] TensorPower k n A) :=
  TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.rationalPermutationAction (V := A) n (Equiv.Perm.eulerianElement n i))

/-- The A-linear Eulerian projector on normalized coefficient tensors.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾
acts on M ⊗[k] (A/(k·1))⊗n by the same coefficient-fixed permutation representation. -/
def algebraNormalizedEulerianOperator (n i : ℕ) : Module.End A
    (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.rationalPermutationAction (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
      (Equiv.Perm.eulerianElement n i))

/-- The ground restriction of a raw algebra-linear Eulerian operator.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
restricting algebraEulerianOperator(n,i) to k gives coefficientEulerianOperator(n,i). -/
theorem algebraEulerianOperator_restrictScalars (n i : ℕ) :
    (algebraEulerianOperator k A M n i).restrictScalars k = coefficientEulerianOperator k A M n i := by
  rw [coefficientEulerianOperator, TensorPower.coefficientRationalPermutationAction_eq_map]
  rfl

/-- The ground restriction of a normalized algebra-linear Eulerian operator.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, its
k-linear restriction is the rational permutation action of eₙ⁽ⁱ⁾ on the quotient-tail module
A/(k·1). -/
theorem algebraNormalizedEulerianOperator_restrictScalars (n i : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).restrictScalars k =
      TensorPower.coefficientRationalPermutationAction (M := M)
        (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n (Equiv.Perm.eulerianElement n i) := by
  rw [TensorPower.coefficientRationalPermutationAction_eq_map]
  rfl

/-- Normalization intertwines each algebra-linear Eulerian projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
degree-n normalization map qₙ satisfies qₙeₙ⁽ⁱ⁾ = ēₙ⁽ⁱ⁾qₙ. -/
theorem algebraNormalizationLevelMap_eulerian (n i : ℕ) :
    (algebraNormalizationLevelMap k A M n).comp (algebraEulerianOperator k A M n i) =
      (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizationLevelMap k A M n) := by
  apply LinearMap.restrictScalars_injective k
  simp only [LinearMap.restrictScalars_comp, algebraNormalizationLevelMap_restrictScalars,
    algebraEulerianOperator_restrictScalars, algebraNormalizedEulerianOperator_restrictScalars,
    coefficientEulerianOperator, Equiv.Perm.eulerianElement,
    TensorPower.coefficientRationalPermutationAction_sum]
  exact TensorPower.coefficientQuotientMap_permutationOperator
    (ModuleCat.Algebra.Hochschild.unitSubmodule k A) n
    (fun σ => algebraMap ℚ k (Equiv.Perm.eulerianCoefficient n i σ))

/-- The raw algebra-linear zero-plus-first Eulerian projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
pₙ=eₙ⁽⁰⁾+eₙ⁽¹⁾ projects the raw coefficient tensors onto their lowest Eulerian summands. -/
def algebraFirstEulerianOperator (n : ℕ) : Module.End A (M ⊗[k] TensorPower k n A) :=
  algebraEulerianOperator k A M n 0 + algebraEulerianOperator k A M n 1

/-- The normalized algebra-linear zero-plus-first Eulerian projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
p̄ₙ=ēₙ⁽⁰⁾+ēₙ⁽¹⁾ acts on M ⊗[k] (A/(k·1))⊗n. -/
def algebraNormalizedFirstEulerianOperator (n : ℕ) : Module.End A
    (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  algebraNormalizedEulerianOperator k A M n 0 + algebraNormalizedEulerianOperator k A M n 1

/-- Ground restriction of the raw zero-plus-first A-linear projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
k-linear restriction of pₙ is firstEulerianOperator(n), with the same zero-plus-first
convention. -/
theorem algebraFirstEulerianOperator_restrictScalars (n : ℕ) :
    (algebraFirstEulerianOperator k A M n).restrictScalars k = firstEulerianOperator k A M n := by
  simp only [algebraFirstEulerianOperator, firstEulerianOperator, LinearMap.restrictScalars_add,
    algebraEulerianOperator_restrictScalars]

/-- The raw zero-plus-first A-linear Eulerian operator is idempotent.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, pₙ ∘ pₙ
= pₙ on M ⊗[k] A⊗n. -/
theorem algebraFirstEulerianOperator_idempotent (n : ℕ) :
    (algebraFirstEulerianOperator k A M n).comp (algebraFirstEulerianOperator k A M n) =
      algebraFirstEulerianOperator k A M n := by
  apply LinearMap.restrictScalars_injective k
  simp only [LinearMap.restrictScalars_comp, algebraFirstEulerianOperator_restrictScalars,
    firstEulerianOperator, LinearMap.add_comp, LinearMap.comp_add]
  simp only [(coefficientEulerian_projector_laws k A M n).2, if_pos rfl,
    if_neg (by omega : (0 : ℕ) ≠ 1), if_neg (by omega : (1 : ℕ) ≠ 0), add_zero, zero_add]
  rfl

/-- Normalization intertwines the two zero-plus-first projectors.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, qₙpₙ =
p̄ₙqₙ between raw and normalized coefficient tensor levels. -/
theorem algebraNormalizationLevelMap_firstEulerian (n : ℕ) :
    (algebraNormalizationLevelMap k A M n).comp (algebraFirstEulerianOperator k A M n) =
      (algebraNormalizedFirstEulerianOperator k A M n).comp (algebraNormalizationLevelMap k A M n) := by
  simp only [algebraFirstEulerianOperator, algebraNormalizedFirstEulerianOperator,
    LinearMap.comp_add, LinearMap.add_comp, algebraNormalizationLevelMap_eulerian]

/-- The raw A-linear proper-shuffle relations are the lowest-projector kernel.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveRelations(n)=ker(pₙ), where pₙ=eₙ⁽⁰⁾+eₙ⁽¹⁾ and the relations use only both-
positive shuffle degrees. -/
theorem algebraPositiveRelations_eq_firstEulerianKernel (n : ℕ) :
    algebraPositiveRelations k A M n = LinearMap.ker (algebraFirstEulerianOperator k A M n) := by
  ext x
  change x ∈ rawPositiveRelations k A M n ↔ algebraFirstEulerianOperator k A M n x = 0
  rw [rawPositiveRelations_eq_firstEulerianKernel]
  change firstEulerianOperator k A M n x = 0 ↔ algebraFirstEulerianOperator k A M n x = 0
  exact Iff.of_eq (congrArg (fun f => f x = 0) (algebraFirstEulerianOperator_restrictScalars k A M n)).symm

/-- Normalized proper-shuffle relations are the normalized lowest-projector kernel.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
algebraNormalizedPositiveRelations(n)=ker(p̄ₙ), with p̄ₙ=ēₙ⁽⁰⁾+ēₙ⁽¹⁾. -/
theorem algebraNormalizedPositiveRelations_eq_firstEulerianKernel (n : ℕ) :
    algebraNormalizedPositiveRelations k A M n =
      LinearMap.ker (algebraNormalizedFirstEulerianOperator k A M n) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hx0 : algebraFirstEulerianOperator k A M n x = 0 := by
      rw [algebraPositiveRelations_eq_firstEulerianKernel] at hx
      exact hx
    change algebraNormalizedFirstEulerianOperator k A M n (algebraNormalizationLevelMap k A M n x) = 0
    have hc := DFunLike.congr_fun (algebraNormalizationLevelMap_firstEulerian k A M n) x
    simp only [LinearMap.comp_apply] at hc
    rw [hx0, map_zero] at hc
    exact hc.symm
  · intro y hy
    obtain ⟨x, hx⟩ := algebraNormalizationLevelMap_surjective k A M n y
    apply Submodule.mem_map.mpr
    refine ⟨x - algebraFirstEulerianOperator k A M n x, ?_, ?_⟩
    · rw [algebraPositiveRelations_eq_firstEulerianKernel]
      change algebraFirstEulerianOperator k A M n (x - algebraFirstEulerianOperator k A M n x) = 0
      rw [map_sub]
      have h := DFunLike.congr_fun (algebraFirstEulerianOperator_idempotent k A M n) x
      simp only [LinearMap.comp_apply] at h
      rw [h, sub_self]
    · change algebraNormalizationLevelMap k A M n (x - algebraFirstEulerianOperator k A M n x) = y
      rw [map_sub]
      have hc := DFunLike.congr_fun (algebraNormalizationLevelMap_firstEulerian k A M n) x
      simp only [LinearMap.comp_apply] at hc
      rw [hc, hx]
      change algebraNormalizedFirstEulerianOperator k A M n y = 0 at hy
      rw [hy, sub_zero]

/-- The raw proper-shuffle quotient identifies with the lowest Eulerian image.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
quotient (M ⊗[k] A⊗n)/algebraPositiveRelations(n) is A-linearly equivalent to range(pₙ). -/
def algebraFirstEulerianQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) ≃ₗ[A]
      LinearMap.range (algebraFirstEulerianOperator k A M n) :=
  (Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_eq_firstEulerianKernel k A M n)).trans
    (algebraFirstEulerianOperator k A M n).quotKerEquivRange

/-- The normalized proper-shuffle quotient identifies with the normalized lowest image.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
normalized quotient is A-linearly equivalent to range(p̄ₙ), retaining M and the ground-module
tails A/(k·1). -/
def algebraNormalizedFirstEulerianQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) ≃ₗ[A]
        LinearMap.range (algebraNormalizedFirstEulerianOperator k A M n) :=
  (Submodule.quotEquivOfEq _ _ (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n)).trans
    (algebraNormalizedFirstEulerianOperator k A M n).quotKerEquivRange

end ModuleCat.Algebra.Hochschild.Symmetric
