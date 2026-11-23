/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFilteredHomotopy
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralHomotopy
public import MathlibExt.CategoryTheory.Preadditive.Skeleton

/-!
# The actual translation representation on the complete BK spectral object

The scalar, zero and biproduct cylinders give equality of the actual complete
horizontal-filtration spectral maps. They construct a representation of the
biproduct monoid of isomorphism classes, with its specified translation maps
as the generator values. No chain-level monoid action is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject HomologicalComplex₂

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "D" => SSet.rightCommaNerveDiagram (translationProjection (C := C))
local notation "K" => SSet.bkAlternatingBicomplex AddCommGrpCat R D
local notation "E" => horizontalCompleteFiltrationSpectralObject K

/-- The actual second-coordinate translation on the complete BK spectral object. -/
def secondTranslationBKSpectralMap (A : C) : End E :=
  .of (horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A))

/-- The prescribed scalar cylinder identifies the actual spectral maps for
isomorphic translating objects. -/
theorem secondTranslationBKSpectralMap_eq_of_iso {A A' : C} (e : A ≅ A') :
    secondTranslationBKSpectralMap R A = secondTranslationBKSpectralMap R A' := by
  apply End.ext
  exact horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R)

/-- Zero translation is the literal identity of the actual spectral object. -/
@[simp]
theorem secondTranslationBKSpectralMap_zero :
    secondTranslationBKSpectralMap R (0 : C) = 1 := by
  apply End.ext
  have h := horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R)
  rw [CategoryTheory.Functor.map_id] at h
  exact h.trans ((horizontalCompleteFiltrationSpectralObjectFunctor
    (C := AddCommGrpCat.{u})).map_id _)

/-- Biproduct translation is the prescribed product of actual endomorphisms.
Endomorphism multiplication retains the composite with the second factor first. -/
theorem secondTranslationBKSpectralMap_biprod (A A' : C) :
    secondTranslationBKSpectralMap R (A ⊞ A') =
      secondTranslationBKSpectralMap R A * secondTranslationBKSpectralMap R A' := by
  apply End.ext
  have h := horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R)
  rw [CategoryTheory.Functor.map_comp] at h
  exact h.trans ((horizontalCompleteFiltrationSpectralObjectFunctor
    (C := AddCommGrpCat.{u})).map_comp _ _)

/-- The genuine representation of the biproduct monoid of isomorphism classes
on the actual complete-horizontal-filtration BK spectral object. -/
def secondTranslationBKSpectralAction : Multiplicative (Skeleton C) →* End E where
  toFun x := secondTranslationBKSpectralMap R x.toAdd.out
  map_one' := by
    change secondTranslationBKSpectralMap R (toSkeleton (0 : C)).out = 1
    exact (secondTranslationBKSpectralMap_eq_of_iso R
      (fromSkeletonToSkeletonIso (0 : C))).trans (secondTranslationBKSpectralMap_zero R)
  map_mul' x y := by
    change secondTranslationBKSpectralMap R
        (toSkeleton (x.toAdd.out ⊞ y.toAdd.out)).out =
      secondTranslationBKSpectralMap R x.toAdd.out *
        secondTranslationBKSpectralMap R y.toAdd.out
    exact (secondTranslationBKSpectralMap_eq_of_iso R
      (fromSkeletonToSkeletonIso (x.toAdd.out ⊞ y.toAdd.out))).trans
        (secondTranslationBKSpectralMap_biprod R x.toAdd.out y.toAdd.out)

/-- A class generator has precisely the original second-translation value. -/
@[simp]
theorem secondTranslationBKSpectralAction_toSkeleton (A : C) :
    secondTranslationBKSpectralAction R (Multiplicative.ofAdd (toSkeleton A)) =
      secondTranslationBKSpectralMap R A :=
  secondTranslationBKSpectralMap_eq_of_iso R (fromSkeletonToSkeletonIso A)

/-- The class action retains the exact existing complete-filtration spectral
map induced by the original second-translation bicomplex map. -/
theorem secondTranslationBKSpectralAction_toSkeleton_map (A : C) :
    secondTranslationBKSpectralAction R (Multiplicative.ofAdd (toSkeleton A)) =
      .of (horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A)) :=
  secondTranslationBKSpectralAction_toSkeleton R A

end CategoryTheory.SInverseS

end
