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
# The split diagonal into tensor-square CE homology

Let `R` be a commutative ring and `L` an `R`-Lie algebra, with independent carrier universes.
The chain coproduct induces a graded map `H(C) → H(C ⊗ C)` in the joint module universe.

Applying the counit to a tensor factor and then the unitor gives a retraction of this
diagonal. The homology counit and coaugmentation retain the chain-level retraction equation.
These maps take values in homology of the tensor complex and are natural in Lie homomorphisms.
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

/-- The closed tensor structure at the CE carrier height.

The module category in the joint scalar-Lie universe has the closed tensor structure used by
the graded homology diagonal. -/
local instance rawHomologyDiagonalClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- The CE chain comonoid for the carrier-universe diagonal.

Equip the canonical CE chain complex with its exterior coproduct and scalar-unit counit. -/
local instance rawDiagonalComon : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L





/-- The carrier-universe CE diagonal into tensor-square homology.

The graded homology map of the CE chain coproduct has source `H(C)` and target `H(C ⊗ C)` in
the joint carrier universe. -/
def canonicalToTensorHomologyRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
  (ComplexShape.down ℕ)).obj ((canonicalChainData R L).complex) ⟶ (HomologicalComplex.gradedHomologyFunctor
    (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj (nativeTensorComplex R L) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexComul R L)

/-- The degree component of the carrier-universe homology diagonal.

In degree `n`, the diagonal is the homology map of the CE comultiplication chain map. -/
@[simp]
theorem canonicalToTensorHomologyRaw_apply (n : ℕ) :
    canonicalToTensorHomologyRaw R L n =
      HomologicalComplex.homologyMap (nativeComplexComul R L) n := rfl

/-- The CE diagonal as a chain-comonoid homology diagonal.

Under the specified module tensor structure, the CE coproduct homology map is the general
canonical diagonal of its chain comonoid. -/
theorem canonicalToTensorHomologyRaw_eq :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
    canonicalToTensorHomologyRaw R L =
      HomologicalComplex.HomologyCoalgebra.canonicalToTensorHomology ((canonicalChainData R L).complex) := rfl

/-- The counit retraction of the carrier-universe CE homology diagonal.

The counit and tensor unitor induce a graded map from tensor-square homology back to CE
homology. -/
def rawDiagonalRetraction : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down
  ℕ)).obj (nativeTensorComplex R L) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).obj ((canonicalChainData R L).complex) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
  exact HomologicalComplex.HomologyCoalgebra.diagonalRetraction ((canonicalChainData R L).complex)

/-- The split identity of the carrier-universe CE homology diagonal.

The homology diagonal followed by its counit-unitor retraction is the identity on graded CE
homology. -/
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

/-- Naturality of the carrier-universe CE homology diagonal.

For a Lie homomorphism, its CE homology map commutes with the diagonal and the homology map of
the tensor square of its chain map. -/
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

/-- The CE homology counit into homology of the chain unit.

Take the graded homology map of the CE chain counit, retaining its unit-complex target. -/
def homologyCounitRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj
  ((canonicalChainData R L).complex) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).obj (nativeUnitComplex.{u,v} R) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexCounit R L)

/-- The CE homology coaugmentation from homology of the chain unit.

Take the graded homology map of the chain coaugmentation, retaining its unit-complex source. -/
def homologyCoaugRaw : (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).obj
  (nativeUnitComplex.{u,v} R) ⟶ (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down
    ℕ)).obj ((canonicalChainData R L).complex) :=
  (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map (nativeComplexCoaug R L)

/-- The unit retraction equation in CE homology.

The homology coaugmentation followed by the homology counit is the identity on homology of the
chain unit. -/
@[reassoc (attr := simp)]
theorem homologyCoaugRaw_counit : homologyCoaugRaw R L ≫ homologyCounitRaw R L = 𝟙 _ := by
  simp only [homologyCoaugRaw, homologyCounitRaw, ← Functor.map_comp,
    nativeComplexCoaug_counit, Functor.map_id]
  exact (HomologicalComplex.gradedHomologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℕ)).map_id _

end ChevalleyEilenberg.HomologyCoalgebra
