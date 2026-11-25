/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Diagonal
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality

/-!
# The split Chevalley–Eilenberg homology diagonal

For a Lie algebra over a commutative ring, the chain coproduct induces a natural graded map
from Chevalley–Eilenberg homology to homology of the tensor square. The counit supplies a
retraction.

The homology coaugmentation and counit retain their identities, and the ground ring and Lie
carrier may have independent universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ChevalleyEilenberg.HomologyCoalgebra

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

open scoped ModuleCat.UniverseTensor

local instance : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)

/-- The canonical closed module tensor structure at the carrier height. -/
local instance rawHomologyDiagonalClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- The canonical CE comonoid on the unchanged chain complex. -/
local instance rawDiagonalComon : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L





/-- The CE homology diagonal into homology of the tensor square, with independent ring and Lie
carrier universes. -/
def canonicalToTensorHomologyRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
  (ComplexShape.down ℕ)).obj ((canonicalChainData R L).complex) ⟶ (HomologicalComplex.gradedHomologyFunctor
    (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj (nativeTensorComplex R L) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexComul R L)

@[simp]
theorem canonicalToTensorHomologyRaw_apply (n : ℕ) :
    canonicalToTensorHomologyRaw R L n =
      HomologicalComplex.homologyMap (nativeComplexComul R L) n := rfl

/-- This carrier-universe diagonal is the general canonical homology diagonal of the CE chain
comonoid. -/
theorem canonicalToTensorHomologyRaw_eq :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
    canonicalToTensorHomologyRaw R L =
      HomologicalComplex.HomologyCoalgebra.canonicalToTensorHomology ((canonicalChainData R L).complex) := rfl

/-- The counit/unitor composite retracts the carrier-universe homology diagonal. No tensor of
homologies is used. -/
def rawDiagonalRetraction : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down
  ℕ)).obj (nativeTensorComplex R L) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).obj ((canonicalChainData R L).complex) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
  exact HomologicalComplex.HomologyCoalgebra.diagonalRetraction ((canonicalChainData R L).complex)

@[reassoc (attr := simp)]
theorem canonicalToTensorHomologyRaw_retraction :
    canonicalToTensorHomologyRaw R L ≫ rawDiagonalRetraction R L = 𝟙 ((HomologicalComplex.gradedHomologyFunctor
      (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj ((canonicalChainData R L).complex)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
  exact HomologicalComplex.HomologyCoalgebra.canonicalToTensorHomology_retraction ((canonicalChainData R L).complex)

variable {L' : Type v} [LieRing L'] [LieAlgebra R L']

/-- Naturality is the homology image of the CE coproduct equation, in the unchanged scalar ring
and working coefficient universe. -/
@[reassoc]
theorem canonicalToTensorHomologyRaw_naturality (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexMap R L
      f) ≫ canonicalToTensorHomologyRaw R L' =
      canonicalToTensorHomologyRaw R L ≫
        (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map
          (HomologicalComplex.tensorHom (nativeComplexMap R L f) (nativeComplexMap R L f)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  simp only [canonicalToTensorHomologyRaw, ← Functor.map_comp]
  rw [nativeComplexMap_comul]
  exact (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).map_comp _ _

/-- The carrier-universe homology counit, before any graded tensor Künneth transport. -/
def homologyCounitRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj
  ((canonicalChainData R L).complex) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).obj (nativeUnitComplex.{u,v} R) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexCounit R L)

/-- The carrier-universe homology coaugmentation, before any graded tensor Künneth transport. -/
def homologyCoaugRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj
  (nativeUnitComplex.{u,v} R) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down
    ℕ)).obj ((canonicalChainData R L).complex) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexCoaug R L)

@[reassoc (attr := simp)]
theorem homologyCoaugRaw_counit : homologyCoaugRaw R L ≫ homologyCounitRaw R L = 𝟙 _ := by
  simp only [homologyCoaugRaw, homologyCounitRaw, ← Functor.map_comp,
    nativeComplexCoaug_counit, Functor.map_id]
  exact (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).map_id _

end ChevalleyEilenberg.HomologyCoalgebra
