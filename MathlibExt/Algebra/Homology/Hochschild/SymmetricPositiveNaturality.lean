/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPairingNaturality
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient

/-!
# Naturality of proper shuffle quotients

Compatible algebra and coefficient maps preserve the images
of the signed shuffle pairings and induce quotient chain maps.
The proper relations require both input degrees to be positive;
the full coefficient-ideal action also permits a degree-zero
second factor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped TensorProduct Simplicial MonoidalCategory
universe u v v' z
namespace ModuleCat.Algebra.Hochschild.Symmetric
variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M N : Type (max u v v' z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [IsScalarTower k A M] [IsScalarTower k B N]
/-- Actual parameter maps preserve the positive shuffle relations. -/
theorem positiveImages_coefficientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, max u v v' z} k A M) n ≤
    (HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v', max u v v' z} k B N) n).comap
      ((coefficientChainMap.{u, v, v', z} g f hf).f n).hom := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages_naturality
    (pairing.{u, v, max u v v' z} k A M) (pairing.{u, v', max u v v' z} k B N)
    (coefficientChainMap.{u, v, v', z} g
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
      (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf)
    (coefficientChainMap.{u, v, v', z} g f hf) (pairing_naturality.{u, v, v', z} g f hf) n

/-- The native positive-image quotient map induced by the parameter
maps and their proved shuffle square. This quotient uses positive factors
on both inputs; identification with the full printed Harrison quotient is
a separate source comparison. -/
def positiveQuotientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.ChainGradedPairing.positiveImageQuotient (pairing.{u, v, max u v v' z} k A M)
      (boundary_one_zero.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
      (boundary_one_zero.{u, v, max u v v' z} k A M) ⟶
    HomologicalComplex.ChainGradedPairing.positiveImageQuotient (pairing.{u, v', max u v v' z} k B N)
      (boundary_one_zero.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
      (boundary_one_zero.{u, v', max u v v' z} k B N) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImageQuotientMap
    (pairing.{u, v, max u v v' z} k A M) (boundary_one_zero.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
    (boundary_one_zero.{u, v, max u v v' z} k A M)
    (pairing.{u, v', max u v v' z} k B N) (boundary_one_zero.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
    (boundary_one_zero.{u, v', max u v v' z} k B N)
    (coefficientChainMap.{u, v, v', z} g
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
      (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf)
    (coefficientChainMap.{u, v, v', z} g f hf) (pairing_naturality.{u, v, v', z} g f hf)

/-- The quotient map commutes with the original coefficient target
projection; its defining pairing square has been proved above. -/
@[reassoc]
theorem positiveQuotientMap_projection (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.ChainGradedPairing.positiveImageProjection (pairing.{u, v, max u v v' z} k A M)
      (boundary_one_zero.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
      (boundary_one_zero.{u, v, max u v v' z} k A M) ≫ positiveQuotientMap.{u, v, v', z} g f hf =
    coefficientChainMap.{u, v, v', z} g f hf ≫
      HomologicalComplex.ChainGradedPairing.positiveImageProjection (pairing.{u, v', max u v v' z} k B N)
        (boundary_one_zero.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
        (boundary_one_zero.{u, v', max u v v' z} k B N) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImageProjection_map
    (pairing.{u, v, max u v v' z} k A M) (boundary_one_zero.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
    (boundary_one_zero.{u, v, max u v v' z} k A M)
    (pairing.{u, v', max u v v' z} k B N) (boundary_one_zero.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
    (boundary_one_zero.{u, v', max u v v' z} k B N)
    (coefficientChainMap.{u, v, v', z} g
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
      (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf)
    (coefficientChainMap.{u, v, v', z} g f hf) (pairing_naturality.{u, v, v', z} g f hf)

end ModuleCat.Algebra.Hochschild.Symmetric
