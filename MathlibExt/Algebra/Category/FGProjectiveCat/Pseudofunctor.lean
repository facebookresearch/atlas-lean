/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty

/-!
# Pseudofunctoriality for `FGProjectiveCat` under base change

`R ↦ FGProjectiveCat R` assembles into a pseudofunctor
`LocallyDiscrete CommRingCat ⥤ᵖ Cat` via `ObjectProperty.fullsubcategory`.
This pseudofunctor records underlying categorical coherence while each
`FGProjectiveCat.baseChange` functor is separately strong monoidal.
-/

@[expose] public section

open CategoryTheory

universe u

namespace FGProjectiveCat

/-- Property selecting FG-projective modules. -/
noncomputable def isFGProjectiveProperty :
    (CommRingCat.moduleCatExtendScalarsPseudofunctor :
      Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat).ObjectProperty where
  prop R := ModuleCat.isFGProjective (R := (R.as : Type u))

/-- FG-projective modules are preserved by base change. -/
instance isFGProjectiveProperty_isClosedUnderMapObj :
    isFGProjectiveProperty.IsClosedUnderMapObj where
  map_obj := by
    intro X Y M hM f
    exact ModuleCat.isFGProjective_extendScalars f.as.hom hM

/-- Pseudofunctor `R ↦ FGProjectiveCat R` from the module pseudofunctor. -/
noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  isFGProjectiveProperty.fullsubcategory

@[simp]
lemma pseudofunctor_obj (R : LocallyDiscrete CommRingCat.{u}) :
    pseudofunctor.obj R = Cat.of (FGProjectiveCat.{u} (R.as : Type u)) :=
  rfl

@[simp]
lemma pseudofunctor_map {R S : LocallyDiscrete CommRingCat.{u}}
    (f : R ⟶ S) :
    (pseudofunctor.map f).toFunctor =
      FGProjectiveCat.baseChange (R := (R.as : Type u)) (S := (S.as : Type u)) f.as.hom := by
  rfl

/-- Identity `baseChange (RingHom.id R) ≅ 𝟭` from `pseudofunctor.mapId`. -/
noncomputable def baseChangeId (R : Type u) [CommRing R] :
    FGProjectiveCat.baseChange (R := R) (S := R) (RingHom.id R) ≅ 𝟭 (FGProjectiveCat.{u} R) :=
  isFGProjectiveProperty.mapId (LocallyDiscrete.mk (CommRingCat.of R))

/-- Composition `baseChange (g.comp f) ≅ baseChange f ⋙ baseChange g`
from `pseudofunctor.mapComp`. -/
noncomputable def baseChangeComp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    FGProjectiveCat.baseChange (g.comp f) ≅
      FGProjectiveCat.baseChange f ⋙ FGProjectiveCat.baseChange g :=
  isFGProjectiveProperty.mapComp
    (f := (CommRingCat.ofHom f).toLoc)
    (g := (CommRingCat.ofHom g).toLoc)

end FGProjectiveCat
