/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED source proposal. Original A-linear carriers and boundaries. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianBoundary
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianAlgebraLevels

/-!
# A-linear raw and normalized Eulerian chain maps

The original coefficient boundary square makes the raw
Eulerian operators chain maps. Surjectivity of the original normalization
and its permutation and boundary squares give the original normalized
boundary square. These maps retain the coefficient-head A-action and only
the original ground-module quotient tails. No section or homotopy
commutation is assumed.
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

/-- Finite completeness of the A-linear raw Eulerian operators. -/
theorem algebraEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), algebraEulerianOperator k A M n i.val) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  have hi (i : ℕ) : algebraEulerianOperator k A M n i x =
      coefficientEulerianOperator k A M n i x :=
    DFunLike.congr_fun (algebraEulerianOperator_restrictScalars k A M n i) x
  have h := DFunLike.congr_fun (coefficientEulerian_projector_laws k A M n).1 x
  simpa only [LinearMap.sum_apply, LinearMap.id_apply, hi] using h

/-- Actual A-linear orthogonality is inherited from the original rational representation. -/
theorem algebraEulerianOperator_comp (n i j : ℕ) :
    (algebraEulerianOperator k A M n i).comp (algebraEulerianOperator k A M n j) =
      if i = j then algebraEulerianOperator k A M n i else 0 := by
  apply LinearMap.restrictScalars_injective k
  by_cases hij : i = j
  · simp only [if_pos hij, LinearMap.restrictScalars_comp,
      algebraEulerianOperator_restrictScalars]
    simpa only [if_pos hij] using (coefficientEulerian_projector_laws k A M n).2 i j
  · simp only [if_neg hij, LinearMap.restrictScalars_comp,
      LinearMap.restrictScalars_zero, algebraEulerianOperator_restrictScalars]
    simpa only [if_neg hij] using (coefficientEulerian_projector_laws k A M n).2 i j

/-- The original A-linear raw family has its original finite support. -/
theorem algebraEulerianOperator_outside (n i : ℕ) (hi : n < i) :
    algebraEulerianOperator k A M n i = 0 := by
  apply LinearMap.restrictScalars_injective k
  simpa only [algebraEulerianOperator_restrictScalars, LinearMap.restrictScalars_zero] using
    coefficientEulerian_outside k A M n i hi

/-- The normalized quotient-tail operators have the same original finite completeness. -/
theorem algebraNormalizedEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), algebraNormalizedEulerianOperator k A M n i.val) = LinearMap.id := by
  classical
  let ρ := TensorPower.coefficientRationalPermutationAction (k := k) (M := M)
    (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
  have h : (∑ i : Fin (n + 1), ρ (Equiv.Perm.eulerianElement n i.val)) = LinearMap.id := by
    change (∑ i : Fin (n + 1), ρ (Equiv.Perm.eulerianElement n i.val)) = 1
    rw [← map_sum, (Equiv.Perm.eulerianElement_projector_laws n).1, map_one]
  apply LinearMap.ext
  intro x
  have hi (i : ℕ) : algebraNormalizedEulerianOperator k A M n i x =
      ρ (Equiv.Perm.eulerianElement n i) x :=
    DFunLike.congr_fun (algebraNormalizedEulerianOperator_restrictScalars k A M n i) x
  simpa only [LinearMap.sum_apply, LinearMap.id_apply, hi] using DFunLike.congr_fun h x

/-- The original normalized coefficient representation gives orthogonal projectors. -/
theorem algebraNormalizedEulerianOperator_comp (n i j : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).comp
        (algebraNormalizedEulerianOperator k A M n j) =
      if i = j then algebraNormalizedEulerianOperator k A M n i else 0 := by
  let ρ := TensorPower.coefficientRationalPermutationAction (k := k) (M := M)
    (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
  apply LinearMap.restrictScalars_injective k
  by_cases hij : i = j
  · simp only [if_pos hij, LinearMap.restrictScalars_comp,
      algebraNormalizedEulerianOperator_restrictScalars]
    change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n j) =
      ρ (Equiv.Perm.eulerianElement n i)
    rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j, if_pos hij]
  · simp only [if_neg hij, LinearMap.restrictScalars_comp, LinearMap.restrictScalars_zero,
      algebraNormalizedEulerianOperator_restrictScalars]
    change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n j) = 0
    rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j, if_neg hij, map_zero]

/-- The normalized family vanishes above its original tensor degree. -/
theorem algebraNormalizedEulerianOperator_outside (n i : ℕ) (hi : n < i) :
    algebraNormalizedEulerianOperator k A M n i = 0 := by
  apply LinearMap.restrictScalars_injective k
  simp only [algebraNormalizedEulerianOperator_restrictScalars, LinearMap.restrictScalars_zero,
    Equiv.Perm.eulerianElement_outside n i hi, map_zero]

/-- The coefficient boundary square is also the original A-linear boundary square. -/
theorem algebraEulerianOperator_boundary (n i : ℕ) :
    (algebraBoundary k A M n).comp (algebraEulerianOperator k A M (n + 1) i) =
      (algebraEulerianOperator k A M n i).comp (algebraBoundary k A M n) := by
  have h : ((algebraBoundary k A M n).restrictScalars k).comp
      (coefficientEulerianOperator k A M (n + 1) i) =
    (coefficientEulerianOperator k A M n i).comp ((algebraBoundary k A M n).restrictScalars k) :=
    coefficientEulerian_boundary k A M n i
  apply LinearMap.restrictScalars_injective k
  simpa only [LinearMap.restrictScalars_comp, algebraEulerianOperator_restrictScalars] using h

/-- The normalized operators commute with the original normalized
boundary by surjective original normalization and the raw square. -/
theorem algebraNormalizedEulerianOperator_boundary (n i : ℕ) :
    (algebraNormalizedBoundary k A M n).comp (algebraNormalizedEulerianOperator k A M (n + 1) i) =
      (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizedBoundary k A M n) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := algebraNormalizationLevelMap_surjective k A M (n + 1) y
  have hq (z : M ⊗[k] TensorPower k (n + 1) A) :
      algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) z) =
        algebraNormalizationLevelMap k A M n (algebraBoundary k A M n z) :=
    nativeNormalizationBoundary_apply k A M n z
  change algebraNormalizedBoundary k A M n
      (algebraNormalizedEulerianOperator k A M (n + 1) i
        (algebraNormalizationLevelMap k A M (n + 1) x)) =
    algebraNormalizedEulerianOperator k A M n i
      (algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) x))
  have hs := DFunLike.congr_fun (algebraNormalizationLevelMap_eulerian k A M (n + 1) i) x
  have hb := DFunLike.congr_fun (algebraEulerianOperator_boundary k A M n i) x
  have ht := DFunLike.congr_fun (algebraNormalizationLevelMap_eulerian k A M n i)
    (algebraBoundary k A M n x)
  simp only [LinearMap.comp_apply] at hs hb ht
  rw [← hs, hq, hb, ht, ← hq]

/-- The coefficient-fixed A-linear Eulerian chain map on the original raw complex. -/
def algebraEulerianChainMap (i : ℕ) : algebraRawComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M ⊗[k] TensorPower k (n + 1) A at x
    dsimp only [algebraRawComplex]
    rw [ChainComplex.of_d]
    change algebraBoundary k A M n (algebraEulerianOperator k A M (n + 1) i x) =
      algebraEulerianOperator k A M n i (algebraBoundary k A M n x)
    exact congrArg (fun f : M ⊗[k] TensorPower k (n + 1) A →ₗ[A]
      M ⊗[k] TensorPower k n A => f x) (algebraEulerianOperator_boundary k A M n i))

/-- The original raw coefficient permutation value is retained in every chain degree. -/
theorem algebraEulerianChainMap_f (n i : ℕ) :
    ((algebraEulerianChainMap k A M i).f n).hom = algebraEulerianOperator k A M n i := rfl

/-- The coefficient-fixed A-linear Eulerian chain map on the original normalized complex. -/
def algebraNormalizedEulerianChainMap (i : ℕ) :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizedEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) at x
    dsimp only [algebraNormalizedChainComplex]
    rw [ChainComplex.of_d]
    change algebraNormalizedBoundary k A M n (algebraNormalizedEulerianOperator k A M (n + 1) i x) =
      algebraNormalizedEulerianOperator k A M n i (algebraNormalizedBoundary k A M n x)
    exact congrArg (fun f :
      M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x)
        (algebraNormalizedEulerianOperator_boundary k A M n i))

/-- The original normalized coefficient permutation value is retained in every chain degree. -/
theorem algebraNormalizedEulerianChainMap_f (n i : ℕ) :
    ((algebraNormalizedEulerianChainMap k A M i).f n).hom =
      algebraNormalizedEulerianOperator k A M n i := rfl

/-- The A-linear original normalization commutes with each Eulerian chain map. -/
@[reassoc]
theorem algebraNormalizationProjection_eulerian (i : ℕ) :
    algebraNormalizationProjection k A M ≫ algebraNormalizedEulerianChainMap k A M i =
      algebraEulerianChainMap k A M i ≫ algebraNormalizationProjection k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizationLevelMap k A M n) =
    (algebraNormalizationLevelMap k A M n).comp (algebraEulerianOperator k A M n i)
  exact (algebraNormalizationLevelMap_eulerian k A M n i).symm

/-- The raw Eulerian chain maps are orthogonal idempotents. -/
theorem algebraEulerianChainMap_comp (i j : ℕ) :
    algebraEulerianChainMap k A M i ≫ algebraEulerianChainMap k A M j =
      if i = j then algebraEulerianChainMap k A M i else 0 := by
  by_cases hij : i = j
  · rw [if_pos hij]
    subst j
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraEulerianOperator k A M n i).comp (algebraEulerianOperator k A M n i) =
      algebraEulerianOperator k A M n i
    exact (algebraEulerianOperator_comp k A M n i i).trans (if_pos rfl)
  · rw [if_neg hij]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraEulerianOperator k A M n j).comp (algebraEulerianOperator k A M n i) = 0
    exact (algebraEulerianOperator_comp k A M n j i).trans (if_neg (Ne.symm hij))

/-- The normalized Eulerian chain maps are orthogonal idempotents. -/
theorem algebraNormalizedEulerianChainMap_comp (i j : ℕ) :
    algebraNormalizedEulerianChainMap k A M i ≫ algebraNormalizedEulerianChainMap k A M j =
      if i = j then algebraNormalizedEulerianChainMap k A M i else 0 := by
  by_cases hij : i = j
  · rw [if_pos hij]
    subst j
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizedEulerianOperator k A M n i) =
      algebraNormalizedEulerianOperator k A M n i
    exact (algebraNormalizedEulerianOperator_comp k A M n i i).trans (if_pos rfl)
  · rw [if_neg hij]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraNormalizedEulerianOperator k A M n j).comp (algebraNormalizedEulerianOperator k A M n i) = 0
    exact (algebraNormalizedEulerianOperator_comp k A M n j i).trans (if_neg (Ne.symm hij))

/-- The original full first projector retains degree zero by adding weights zero and one. -/
def algebraFirstEulerianChainMap : algebraRawComplex k A M ⟶ algebraRawComplex k A M :=
  algebraEulerianChainMap k A M 0 + algebraEulerianChainMap k A M 1

/-- The normalized zero-plus-first projector has the original quotient tails. -/
def algebraNormalizedFirstEulerianChainMap :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  algebraNormalizedEulerianChainMap k A M 0 + algebraNormalizedEulerianChainMap k A M 1

/-- The raw first chain map keeps the original first operator at every level. -/
theorem algebraFirstEulerianChainMap_f (n : ℕ) :
    ((algebraFirstEulerianChainMap k A M).f n).hom = algebraFirstEulerianOperator k A M n := rfl

/-- The normalized first chain map keeps the original normalized first operator. -/
theorem algebraNormalizedFirstEulerianChainMap_f (n : ℕ) :
    ((algebraNormalizedFirstEulerianChainMap k A M).f n).hom =
      algebraNormalizedFirstEulerianOperator k A M n := rfl

/-- The normalization respects the original full first projector. -/
@[reassoc]
theorem algebraNormalizationProjection_firstEulerian :
    algebraNormalizationProjection k A M ≫ algebraNormalizedFirstEulerianChainMap k A M =
      algebraFirstEulerianChainMap k A M ≫ algebraNormalizationProjection k A M := by
  simp only [algebraNormalizedFirstEulerianChainMap, algebraFirstEulerianChainMap,
    Preadditive.comp_add, Preadditive.add_comp, algebraNormalizationProjection_eulerian]

/-- The original normalized first level operator is idempotent by the rational projectors. -/
theorem algebraNormalizedFirstEulerianOperator_idempotent (n : ℕ) :
    (algebraNormalizedFirstEulerianOperator k A M n).comp
        (algebraNormalizedFirstEulerianOperator k A M n) =
      algebraNormalizedFirstEulerianOperator k A M n := by
  simp only [algebraNormalizedFirstEulerianOperator, LinearMap.add_comp, LinearMap.comp_add,
    algebraNormalizedEulerianOperator_comp, if_pos rfl,
    if_neg (by omega : (0 : ℕ) ≠ 1), if_neg (by omega : (1 : ℕ) ≠ 0), add_zero, zero_add]
  rfl

end ModuleCat.Algebra.Hochschild.Symmetric
