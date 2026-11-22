/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordPushoutWeak

/-!
# Actual pushouts of componentwise anodyne free-quiver maps

The attaching data are constructed from the supplied original enriched
map and genuine scalar anodyne quiver maps. The full word filtration
proves the old enriched pushout leg has anodyne Hom maps. No enriched
source cofibrancy, fibrancy or model-transfer outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverPushout
open RelativeAttachment

variable {O : Type u} {Q R : SimplicialQuiver.Data O} {C : FixedObjects O}

/-- The actual original attaching data from a whole free-domain map and scalar anodyne inclusions. -/
abbrev data (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
    (hm : ∀ x y, SSet.anodyneExtensions (m x y)) (s : FreeQuiver.object Q ⟶ C) : Data C where
  domain := Q
  target := R
  inclusion := m
  mono x y := by
    have h := hm x y
    rw [SSet.anodyneExtensions_eq_trivialCofibrations] at h
    let _ : Cofibration (m x y) := ((mem_trivialCofibrations_iff _).mp h).1
    exact SSet.modelCategoryQuillen.mono_of_cofibration _
  attaching x y := FreeQuiver.generator Q x y ≫ homMap s x y

/-- The actual derived free-domain attaching map is the same supplied whole original enriched map. -/
theorem data_domainMap (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
    (hm : ∀ x y, SSet.anodyneExtensions (m x y)) (s : FreeQuiver.object Q ⟶ C) :
    domainMap (data m hm s) = s := by
  apply FreeQuiver.generators_ext Q
  intro x y
  exact FreeQuiver.generator_extend Q C _ x y

/-- The actual derived target map is the existing whole free map of the same original quiver inclusions. -/
theorem data_targetMap (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
    (hm : ∀ x y, SSet.anodyneExtensions (m x y)) (s : FreeQuiver.object Q ⟶ C) :
    targetMap (data m hm s) = FreeQuiver.map m := rfl

/-- Every actual enriched pushout of these supplied free-quiver maps is anodyne on the same old Homs. -/
theorem hom_anodyne_of_isPushout (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
    (hm : ∀ x y, SSet.anodyneExtensions (m x y)) (s : FreeQuiver.object Q ⟶ C)
    {D : FixedObjects O} (j : C ⟶ D) (k : FreeQuiver.object R ⟶ D)
    (hp : IsPushout s (FreeQuiver.map m) j k) (x y : O) : SSet.anodyneExtensions (homMap j x y) := by
  have ht : IsPushout (domainMap (data m hm s)) (targetMap (data m hm s)) j k := by
    rw [data_domainMap, data_targetMap]
    exact hp
  exact pushout_leftHom_anodyne (data m hm s) hm j k ht x y

/-- The literal canonical old leg of the actual free-quiver pushout is anodyne on all original Homs. -/
theorem canonical_hom_anodyne (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
    (hm : ∀ x y, SSet.anodyneExtensions (m x y)) (s : FreeQuiver.object Q ⟶ C)
    [HasPushout (FreeQuiver.map m) s] (x y : O) :
    SSet.anodyneExtensions (homMap (pushout.inr (FreeQuiver.map m) s) x y) :=
  hom_anodyne_of_isPushout m hm s _ _ (IsPushout.of_hasPushout _ _).flip x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverPushout
