/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianProperImage

/-!
# Naturality of rational coefficient Eulerian maps

Coefficient and algebra maps on raw,
normalized and proper quotients commute
with rational Eulerian operators,
sections and first-image comparisons.
Their ground and carrier universes
remain those of the coefficient maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [SMulCommClass k A M] [SMulCommClass k A N]
  [IsScalarTower k A M] [IsScalarTower k A N]

section Eulerian

variable [Algebra ℚ k]

/-- Every original rational Eulerian operator commutes with the original coefficient-head map. -/
theorem algebraEulerianOperator_coefficient (f : M →ₗ[A] N) (n i : ℕ) :
    (algebraCoefficientLevelMap k A f n).comp (algebraEulerianOperator k A M n i) =
      (algebraEulerianOperator k A N n i).comp (algebraCoefficientLevelMap k A f n) := by
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext'
  intro m x
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, algebraCoefficientLevelMap,
    algebraEulerianOperator, TensorProduct.AlgebraTensorModule.map_tmul,
    TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.id_apply]

/-- The full first projectors commute with the original coefficient-head map. -/
theorem algebraFirstEulerianOperator_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    (algebraCoefficientLevelMap k A f n).comp (algebraFirstEulerianOperator k A M n) =
      (algebraFirstEulerianOperator k A N n).comp (algebraCoefficientLevelMap k A f n) := by
  simp only [algebraFirstEulerianOperator, LinearMap.comp_add, LinearMap.add_comp,
    algebraEulerianOperator_coefficient]

/-- The quotient section is natural in original A-linear coefficient maps. -/
@[reassoc]
theorem algebraPositiveEulerianSection_coefficient (f : M →ₗ[A] N) :
    algebraPositiveCoefficientMap k A f ≫ algebraPositiveEulerianSection k A N =
      algebraPositiveEulerianSection k A M ≫ algebraRawCoefficientMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact (DFunLike.congr_fun (algebraFirstEulerianOperator_coefficient k A f n) x).symm

/-- The original coefficient map on the full first Eulerian images. -/
def algebraFirstEulerianImageCoefficientMap (f : M →ₗ[A] N) :
    algebraFirstEulerianImageComplex k A M ⟶ algebraFirstEulerianImageComplex k A N :=
  image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawCoefficientMap k A f ≫
    factorThruImage (algebraFirstEulerianChainMap k A N)

private theorem positiveSection_firstEulerian :
    algebraPositiveEulerianSection k A M ≫ algebraFirstEulerianChainMap k A M =
      algebraPositiveEulerianSection k A M := by
  rw [← algebraRawPositiveProjection_eulerianSection, ← Category.assoc,
    algebraPositiveEulerianSection_projection, Category.id_comp]

/-- The proper quotient to first-image chain isomorphism is natural in
the original A-linear coefficient map, with no coefficient projectivity. -/
@[reassoc]
theorem algebraFirstEulerianQuotientIso_coefficient (f : M →ₗ[A] N) :
    algebraPositiveCoefficientMap k A f ≫ (algebraFirstEulerianQuotientIso k A N).hom =
      (algebraFirstEulerianQuotientIso k A M).hom ≫ algebraFirstEulerianImageCoefficientMap k A f := by
  change algebraPositiveCoefficientMap k A f ≫
      (algebraPositiveEulerianSection k A N ≫ factorThruImage (algebraFirstEulerianChainMap k A N)) =
    (algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawCoefficientMap k A f ≫
        factorThruImage (algebraFirstEulerianChainMap k A N))
  have h := congrArg
    (fun t : algebraPositiveQuotientComplex k A M ⟶ algebraRawComplex k A N =>
      t ≫ factorThruImage (algebraFirstEulerianChainMap k A N))
    (algebraPositiveEulerianSection_coefficient k A f)
  simp only [Category.assoc] at h
  simp only [Category.assoc, image.fac_assoc]
  rw [← Category.assoc (algebraPositiveEulerianSection k A M)
    (algebraFirstEulerianChainMap k A M), positiveSection_firstEulerian]
  exact h

end Eulerian

end ModuleCat.Algebra.Hochschild.Symmetric
