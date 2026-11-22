/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidClone
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingArrowFreeSingleHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerObjectLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalTwoLabelUnitGroupoid
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialUnitScalarFunctor

/-!
# The SAME original two-label unit groupoid maps to the literal clone

The original terminal unit-Hom enrichment keeps its original source and
target labels. Its whole map to the actual clone selects the SAME old
object and the actual new label. Every original unit coefficient maps
by the SAME full original identity of the selected original object,
with only the proved fold-label equations retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
open FixedObjects OriginalWalkingArrowFreeSingleHomIso

/-- The SAME original two-label full unit-Hom target used by the actual interval projection. -/
abbrev unitDomain : Carrier.{u} := OriginalTwoLabelUnitGroupoid.object.{u}

/-- Retain the original source as the SAME old object and the original target as the actual new clone label. -/
def unitLabel (C : Carrier.{u}) (x : C) (a : walking.{u}) : object C x :=
  match a.down with
  | .source => Sum.inl x
  | .target => newObject C x

/-- Both original unit-groupoid labels have the SAME selected original fold image. -/
theorem fold_unitLabel (C : Carrier.{u}) (x : C) (a : walking.{u}) : fold C x (unitLabel C x a) = x := by
  rcases a with ⟨a⟩
  cases a <;> rfl

/-- Retain the SAME whole original identity unit coefficient at both original unit-groupoid labels. -/
def unitHom (C : Carrier.{u}) (x : C) (a b : walking.{u}) :
    𝟙_ SSet.{u} ⟶ (unitLabel C x a ⟶[SSet.{u}] unitLabel C x b) :=
  eId SSet.{u} x ≫ eqToHom
    (congrArg₂ (fun y z : C => y ⟶[SSet.{u}] z) (fold_unitLabel C x a) (fold_unitLabel C x b)).symm

/-- The SAME original full unit-groupoid functor keeps its two labels and every original identity coefficient. -/
def unitMap (C : Carrier.{u}) (x : C) : unitDomain.{u} ⟶ object C x where
  obj a := unitLabel C x a
  map a b := unitHom C x a b
  map_id a := by
    rcases a with ⟨a⟩
    cases a
    all_goals
      apply NatTrans.ext
      funext q
      apply ConcreteCategory.hom_ext
      intro p
      cases p
      rfl
  map_comp a b c := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    cases a <;> cases b <;> cases c
    all_goals
      apply NatTrans.ext
      funext q
      apply ConcreteCategory.hom_ext
      intro p
      rcases p with ⟨p, r⟩
      cases p
      cases r
      let z : SSet.ScalarObject C q := ⟨x⟩
      change 𝟙 z = 𝟙 z ≫ 𝟙 z
      exact (Category.id_comp _).symm

/-- The original source point retains the SAME whole old-object selection in the actual clone. -/
theorem unitMap_source (C : Carrier.{u}) (x : C) :
    BergnerObjects.select (C := unitDomain.{u}) OriginalTwoLabelUnitGroupoid.source ≫ unitMap C x =
      BergnerObjects.select (C := object C x) (Sum.inl x) :=
  BergnerObjects.select_comp (C := unitDomain.{u}) (D := object C x) _ _

/-- The original target point retains the SAME whole actual new-label selection in the clone. -/
theorem unitMap_target (C : Carrier.{u}) (x : C) :
    BergnerObjects.select (C := unitDomain.{u}) OriginalTwoLabelUnitGroupoid.target ≫ unitMap C x =
      BergnerObjects.select (C := object C x) (newObject C x) :=
  BergnerObjects.select_comp (C := unitDomain.{u}) (D := object C x) _ _

/-- The SAME complete original unit coefficient is read literally at every original label pair. -/
theorem unitMap_hom (C : Carrier.{u}) (x : C) (a b : walking.{u}) :
    (unitMap C x).map a b = unitHom C x a b := rfl

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
