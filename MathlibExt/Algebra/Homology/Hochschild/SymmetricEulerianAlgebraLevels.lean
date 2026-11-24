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
# Algebra-linear Eulerian operators and normalized kernels

Over a rational ground ring, coefficient-fixed permutation
operators and Eulerian projectors are A-linear. Normalization
intertwines these operators, identifying the normalized
proper relation module with the kernel of the zero-plus-first
projector. The quotient tails remain ground modules.
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

/-- The coefficient-fixed raw Eulerian operator with its original A-linearity. -/
def algebraEulerianOperator (n i : ℕ) : Module.End A (M ⊗[k] TensorPower k n A) :=
  TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.rationalPermutationAction (V := A) n (Equiv.Perm.eulerianElement n i))

/-- The normalized Eulerian operator needs only the original ground-module quotient tails. -/
def algebraNormalizedEulerianOperator (n i : ℕ) : Module.End A
    (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.rationalPermutationAction (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
      (Equiv.Perm.eulerianElement n i))

/-- Restriction of the A-linear raw operator is the original coefficient Eulerian operator. -/
theorem algebraEulerianOperator_restrictScalars (n i : ℕ) :
    (algebraEulerianOperator k A M n i).restrictScalars k = coefficientEulerianOperator k A M n i := by
  rw [coefficientEulerianOperator, TensorPower.coefficientRationalPermutationAction_eq_map]
  rfl

/-- Restriction of the A-linear normalized operator is the original normalized coefficient
  representation. -/
theorem algebraNormalizedEulerianOperator_restrictScalars (n i : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).restrictScalars k =
      TensorPower.coefficientRationalPermutationAction (M := M)
        (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n (Equiv.Perm.eulerianElement n i) := by
  rw [TensorPower.coefficientRationalPermutationAction_eq_map]
  rfl

/-- The A-linear original normalization commutes with every coefficient Eulerian operator. -/
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

/-- The full nonnegative first raw projector retains the original degree-zero coefficient. -/
def algebraFirstEulerianOperator (n : ℕ) : Module.End A (M ⊗[k] TensorPower k n A) :=
  algebraEulerianOperator k A M n 0 + algebraEulerianOperator k A M n 1

/-- The corresponding zero-plus-first projector on the original normalized ground-module tails. -/
def algebraNormalizedFirstEulerianOperator (n : ℕ) : Module.End A
    (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  algebraNormalizedEulerianOperator k A M n 0 + algebraNormalizedEulerianOperator k A M n 1

/-- The original A-linear raw first projector restricts to the original full zero-plus-first ground projector. -/
theorem algebraFirstEulerianOperator_restrictScalars (n : ℕ) :
    (algebraFirstEulerianOperator k A M n).restrictScalars k = firstEulerianOperator k A M n := by
  simp only [algebraFirstEulerianOperator, firstEulerianOperator, LinearMap.restrictScalars_add,
    algebraEulerianOperator_restrictScalars]

/-- The raw first A-linear projector is idempotent by the rational group-ring laws. -/
theorem algebraFirstEulerianOperator_idempotent (n : ℕ) :
    (algebraFirstEulerianOperator k A M n).comp (algebraFirstEulerianOperator k A M n) =
      algebraFirstEulerianOperator k A M n := by
  apply LinearMap.restrictScalars_injective k
  simp only [LinearMap.restrictScalars_comp, algebraFirstEulerianOperator_restrictScalars,
    firstEulerianOperator, LinearMap.add_comp, LinearMap.comp_add]
  simp only [(coefficientEulerian_projector_laws k A M n).2, if_pos rfl,
    if_neg (by omega : (0 : ℕ) ≠ 1), if_neg (by omega : (1 : ℕ) ≠ 0), add_zero, zero_add]
  rfl

/-- The raw and normalized first A-linear projectors commute with the original normalization. -/
theorem algebraNormalizationLevelMap_firstEulerian (n : ℕ) :
    (algebraNormalizationLevelMap k A M n).comp (algebraFirstEulerianOperator k A M n) =
      (algebraNormalizedFirstEulerianOperator k A M n).comp (algebraNormalizationLevelMap k A M n) := by
  simp only [algebraFirstEulerianOperator, algebraNormalizedFirstEulerianOperator,
    LinearMap.comp_add, LinearMap.add_comp, algebraNormalizationLevelMap_eulerian]

/-- The exact original raw proper relation module is the kernel of the A-linear first projector. -/
theorem algebraPositiveRelations_eq_firstEulerianKernel (n : ℕ) :
    algebraPositiveRelations k A M n = LinearMap.ker (algebraFirstEulerianOperator k A M n) := by
  ext x
  change x ∈ rawPositiveRelations k A M n ↔ algebraFirstEulerianOperator k A M n x = 0
  rw [rawPositiveRelations_eq_firstEulerianKernel]
  change firstEulerianOperator k A M n x = 0 ↔ algebraFirstEulerianOperator k A M n x = 0
  exact Iff.of_eq (congrArg (fun f => f x = 0) (algebraFirstEulerianOperator_restrictScalars k A M n)).symm

/-- The normalized relation image is exactly the first-projector kernel, from original surjectivity
  and projector identities. -/
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

/-- The raw proper quotient level is the A-linear first projector image. -/
def algebraFirstEulerianQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) ≃ₗ[A]
      LinearMap.range (algebraFirstEulerianOperator k A M n) :=
  (Submodule.quotEquivOfEq _ _ (algebraPositiveRelations_eq_firstEulerianKernel k A M n)).trans
    (algebraFirstEulerianOperator k A M n).quotKerEquivRange

/-- The normalized proper quotient level is the A-linear normalized first projector image. -/
def algebraNormalizedFirstEulerianQuotientLevelEquiv (n : ℕ) :
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) ≃ₗ[A]
        LinearMap.range (algebraNormalizedFirstEulerianOperator k A M n) :=
  (Submodule.quotEquivOfEq _ _ (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n)).trans
    (algebraNormalizedFirstEulerianOperator k A M n).quotKerEquivRange

end ModuleCat.Algebra.Hochschild.Symmetric
