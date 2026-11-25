/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Extension
public import MathlibExt.CategoryTheory.Reedy.Prefix

/-!
# Actual Reedy coefficient factorization by well-founded degree

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageFactory

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))

/-- The unchanged original lower left factor induces the actual latching comparison. -/
def latchingI (j : J) (hj : r.degree j = d) :
    colimit (r.latchingDiagram X j) ⟶ colimit (r.lowerLatchingDiagram L.Z j hj) :=
  (lowerLatchingFunctor r (C := C) j hj).map L.i

/-- The unchanged original lower right factor induces the actual matching comparison. -/
def matchingP (j : J) (hj : r.degree j = d) :
    limit (r.lowerMatchingDiagram L.Z j hj) ⟶ limit (r.matchingDiagram Y j) :=
  (lowerMatchingFunctor r (C := C) j hj).map L.p

/-- The original source coefficient maps to the whole actual lower matching object through the
lower left factor. -/
def matchingI (j : J) (hj : r.degree j = d) : X.obj j ⟶ limit (r.lowerMatchingDiagram L.Z j hj) :=
  matchingMap r X j ≫ (lowerMatchingFunctor r (C := C) j hj).map L.i

/-- The whole actual lower latching object maps to the original target coefficient through the
lower right factor. -/
def latchingP (j : J) (hj : r.degree j = d) : colimit (r.lowerLatchingDiagram L.Z j hj) ⟶ Y.obj j :=
  (lowerLatchingFunctor r (C := C) j hj).map L.p ≫ latchingMap r Y j

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The exact original lower factor equation survives its whole latching comparison. -/
theorem latching_fac (j : J) (hj : r.degree j = d) :
    latchingMap r X j ≫ f.app j = latchingI r f L j hj ≫ latchingP r f L j hj := by
  dsimp only [latchingI, latchingP]
  rw [← (lowerLatchingFunctor r (C := C) j hj).map_comp_assoc, L.fac]
  exact latchingMap_naturality r f j

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The exact original lower factor equation survives its whole matching comparison. -/
theorem matching_fac (j : J) (hj : r.degree j = d) :
    matchingI r f L j hj ≫ matchingP r f L j hj = f.app j ≫ matchingMap r Y j := by
  dsimp only [matchingI, matchingP]
  rw [Category.assoc, ← (lowerMatchingFunctor r (C := C) j hj).map_comp, L.fac]
  exact matchingMap_naturality r f j

omit [HasPushouts C] [HasPullbacks C] in
/-- The original lower left factor commutes with the complete actual latching-to-matching
boundary. -/
theorem incoming_condition (j : J) (hj : r.degree j = d) :
    latchingMap r X j ≫ matchingI r f L j hj =
      latchingI r f L j hj ≫ lowerBoundaryMap r L.Z j hj := by
  have h := lowerBoundaryMap_naturality r L.i j hj
  rw [lowerBoundaryMap_restrict r X j hj] at h
  simpa only [latchingI, matchingI, Category.assoc] using h.symm

omit [HasPushouts C] [HasPullbacks C] in
/-- The original lower right factor commutes with the complete actual latching-to-matching
boundary. -/
theorem outgoing_condition (j : J) (hj : r.degree j = d) :
    lowerBoundaryMap r L.Z j hj ≫ matchingP r f L j hj =
      latchingP r f L j hj ≫ matchingMap r Y j := by
  have h := lowerBoundaryMap_naturality r L.p j hj
  rw [lowerBoundaryMap_restrict r Y j hj] at h
  simpa only [matchingP, latchingP, Category.assoc] using h.symm

/-- The actual original latching-corner source of the coefficient factorization. -/
abbrev coefficientSource (j : J) (hj : r.degree j = d) :=
  pushout (latchingMap r X j) (latchingI r f L j hj)

/-- The actual original matching-corner target of the coefficient factorization. -/
abbrev coefficientTarget (j : J) (hj : r.degree j = d) :=
  pullback (matchingP r f L j hj) (matchingMap r Y j)

/-- The actual coefficient source maps to the whole actual lower matching object. -/
def coefficientToMatching (j : J) (hj : r.degree j = d) :
    coefficientSource r f L j hj ⟶ limit (r.lowerMatchingDiagram L.Z j hj) :=
  pushout.desc (matchingI r f L j hj) (lowerBoundaryMap r L.Z j hj) (incoming_condition r f L j hj)

/-- The actual coefficient source maps to the original target coefficient. -/
def coefficientToTarget (j : J) (hj : r.degree j = d) : coefficientSource r f L j hj ⟶ Y.obj j :=
  pushout.desc (f.app j) (latchingP r f L j hj) (latching_fac r f L j hj)

omit [HasPullbacks C] in
/-- The full actual pushout-to-pullback coefficient square commutes. -/
theorem coefficient_condition (j : J) (hj : r.degree j = d) :
    coefficientToMatching r f L j hj ≫ matchingP r f L j hj =
      coefficientToTarget r f L j hj ≫ matchingMap r Y j := by
  apply pushout.hom_ext
  · rw [coefficientToMatching, coefficientToTarget, pushout.inl_desc_assoc, pushout.inl_desc_assoc]
    exact matching_fac r f L j hj
  · rw [coefficientToMatching, coefficientToTarget, pushout.inr_desc_assoc, pushout.inr_desc_assoc]
    exact outgoing_condition r f L j hj

/-- The full original coefficient arrow factored at the new Reedy degree. -/
def coefficientMap (j : J) (hj : r.degree j = d) :
    coefficientSource r f L j hj ⟶ coefficientTarget r f L j hj :=
  pullback.lift (coefficientToMatching r f L j hj) (coefficientToTarget r f L j hj)
    (coefficient_condition r f L j hj)

/-- The original source coefficient of the first matching projection is the unchanged lower left
comparison. -/
@[reassoc]
theorem coefficientMap_inl_fst (j : J) (hj : r.degree j = d) :
    pushout.inl (latchingMap r X j) (latchingI r f L j hj) ≫ coefficientMap r f L j hj ≫
      pullback.fst (matchingP r f L j hj) (matchingMap r Y j) = matchingI r f L j hj := by
  rw [coefficientMap, pullback.lift_fst, coefficientToMatching, pushout.inl_desc]

/-- The original source coefficient of the second matching projection is the unchanged original
component map. -/
@[reassoc]
theorem coefficientMap_inl_snd (j : J) (hj : r.degree j = d) :
    pushout.inl (latchingMap r X j) (latchingI r f L j hj) ≫ coefficientMap r f L j hj ≫
      pullback.snd (matchingP r f L j hj) (matchingMap r Y j) = f.app j := by
  rw [coefficientMap, pullback.lift_snd, coefficientToTarget, pushout.inl_desc]

/-- The original lower latching coefficient of the first matching projection is the complete
original boundary map. -/
@[reassoc]
theorem coefficientMap_inr_fst (j : J) (hj : r.degree j = d) :
    pushout.inr (latchingMap r X j) (latchingI r f L j hj) ≫ coefficientMap r f L j hj ≫
      pullback.fst (matchingP r f L j hj) (matchingMap r Y j) = lowerBoundaryMap r L.Z j hj := by
  rw [coefficientMap, pullback.lift_fst, coefficientToMatching, pushout.inr_desc]

/-- The original lower latching coefficient of the second matching projection is the unchanged
lower right comparison.
-/
@[reassoc]
theorem coefficientMap_inr_snd (j : J) (hj : r.degree j = d) :
    pushout.inr (latchingMap r X j) (latchingI r f L j hj) ≫ coefficientMap r f L j hj ≫
      pullback.snd (matchingP r f L j hj) (matchingMap r Y j) = latchingP r f L j hj := by
  rw [coefficientMap, pullback.lift_snd, coefficientToTarget, pushout.inr_desc]


variable {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The complete source coefficient factory is applied to the unchanged original stage arrow. -/
abbrev coefficientFactor (j : J) (hj : r.degree j = d) :
    MapFactorizationData P Q (coefficientMap r f L j hj) := F (coefficientMap r f L j hj)

/-- The original new-degree source factor retains the original source injection and factory left
map. -/
def newI (j : J) (hj : r.degree j = d) : X.obj j ⟶ (coefficientFactor r f L F j hj).Z :=
  pushout.inl (latchingMap r X j) (latchingI r f L j hj) ≫ (coefficientFactor r f L F j hj).i

/-- The original new-degree target factor retains the original factory right map and target
projection. -/
def newP (j : J) (hj : r.degree j = d) : (coefficientFactor r f L F j hj).Z ⟶ Y.obj j :=
  (coefficientFactor r f L F j hj).p ≫ pullback.snd (matchingP r f L j hj) (matchingMap r Y j)

/-- The actual new-degree latching map is the original source pushout injection followed by the
factory left map. -/
def newIncoming (j : J) (hj : r.degree j = d) :
    colimit (r.lowerLatchingDiagram L.Z j hj) ⟶ (coefficientFactor r f L F j hj).Z :=
  pushout.inr (latchingMap r X j) (latchingI r f L j hj) ≫ (coefficientFactor r f L F j hj).i

/-- The actual new-degree matching map is the factory right map followed by the original target
pullback projection. -/
def newOutgoing (j : J) (hj : r.degree j = d) :
    (coefficientFactor r f L F j hj).Z ⟶ limit (r.lowerMatchingDiagram L.Z j hj) :=
  (coefficientFactor r f L F j hj).p ≫ pullback.fst (matchingP r f L j hj) (matchingMap r Y j)

/-- The unchanged new-degree factory maps factor the original caller component. -/
theorem new_fac (j : J) (hj : r.degree j = d) :
    newI r f L F j hj ≫ newP r f L F j hj = f.app j := by
  dsimp only [newI, newP]
  rw [Category.assoc, MapFactorizationData.fac_assoc, coefficientMap_inl_snd]

/-- The unchanged new-degree factory boundary maps factor the complete original lower boundary. -/
theorem new_boundary_fac (j : J) (hj : r.degree j = d) :
    newIncoming r f L F j hj ≫ newOutgoing r f L F j hj = lowerBoundaryMap r L.Z j hj := by
  dsimp only [newIncoming, newOutgoing]
  rw [Category.assoc, MapFactorizationData.fac_assoc, coefficientMap_inr_fst]

/-- The actual source factory constructs the complete new-degree layer from the original lower
factor. -/
abbrev layer : LayerData (C := C) r d where
  lower := L.Z
  obj j hj := (coefficientFactor r f L F j hj).Z
  incoming j hj := newIncoming r f L F j hj
  outgoing j hj := newOutgoing r f L F j hj
  fac j hj := new_boundary_fac r f L F j hj

/-- The original lower source factor and factory source maps extend across the new degree. -/
abbrev leftLayerHom : LayerHom (layerOfFunctor r X d) (layer r f L F) where
  lower := L.i
  app j hj := newI r f L F j hj
  incoming j hj := by
    change latchingMap r X j ≫ newI r f L F j hj = latchingI r f L j hj ≫ newIncoming r f L F j hj
    dsimp only [newI, newIncoming]
    exact pushout.condition_assoc ((coefficientFactor r f L F j hj).i)
  outgoing j hj := by
    change newI r f L F j hj ≫ newOutgoing r f L F j hj = matchingI r f L j hj
    dsimp only [newI, newOutgoing]
    rw [Category.assoc, MapFactorizationData.fac_assoc, coefficientMap_inl_fst]

/-- The original lower target factor and factory target maps extend across the new degree. -/
abbrev rightLayerHom : LayerHom (layer r f L F) (layerOfFunctor r Y d) where
  lower := L.p
  app j hj := newP r f L F j hj
  incoming j hj := by
    change newIncoming r f L F j hj ≫ newP r f L F j hj = latchingP r f L j hj
    dsimp only [newIncoming, newP]
    rw [Category.assoc, MapFactorizationData.fac_assoc, coefficientMap_inr_snd]
  outgoing j hj := by
    change newP r f L F j hj ≫ matchingMap r Y j = newOutgoing r f L F j hj ≫ matchingP r f L j hj
    dsimp only [newP, newOutgoing]
    rw [Category.assoc, Category.assoc, pullback.condition]

/-- The full original source factor on the actual extended intermediate diagram. -/
def leftTransformation : r.restrictThrough X d ⟶ (layer r f L F).extension :=
  (layerOfFunctorIso r X d).inv ≫ (leftLayerHom r f L F).transformation

/-- The full original target factor on the actual extended intermediate diagram. -/
def rightTransformation : (layer r f L F).extension ⟶ r.restrictThrough Y d :=
  (rightLayerHom r f L F).transformation ≫ (layerOfFunctorIso r Y d).hom

/-- Every original lower source component is unchanged through the actual intermediate equality
transport. -/
theorem leftTransformation_old (j : r.Through d) (hj : r.degree j.obj < d) :
    (leftTransformation r f L F).app j = L.i.app ⟨j.obj, hj⟩ ≫
      ((layer r f L F).oldIso j hj).inv := by
  rw [leftTransformation, NatTrans.comp_app, layerOfFunctorIso_inv_app r,
    LayerHom.transformation_app_old _ _ hj, layerOfFunctor_oldIso r X d j hj]
  change (layerOfFunctorObjIso r X d j).inv ≫
    (layerOfFunctorObjIso r X d j).hom ≫ L.i.app ⟨j.obj, hj⟩ ≫ ((layer r f L F).oldIso j hj).inv = _
  rw [Iso.inv_hom_id_assoc]

/-- Every original lower target component is unchanged through the actual intermediate equality
transport. -/
theorem rightTransformation_old (j : r.Through d) (hj : r.degree j.obj < d) :
    (rightTransformation r f L F).app j =
      ((layer r f L F).oldIso j hj).hom ≫ L.p.app ⟨j.obj, hj⟩ := by
  rw [rightTransformation, NatTrans.comp_app, LayerHom.transformation_app_old _ _ hj,
    layerOfFunctorIso_hom_app r, layerOfFunctor_oldIso r Y d j hj]
  change (((layer r f L F).oldIso j hj).hom ≫ L.p.app ⟨j.obj, hj⟩ ≫
    (layerOfFunctorObjIso r Y d j).inv) ≫ (layerOfFunctorObjIso r Y d j).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original new-degree source component retains the original factory source map. -/
theorem leftTransformation_new (j : r.Through d) (hj : r.degree j.obj = d) :
    (leftTransformation r f L F).app j = newI r f L F j.obj hj ≫
      ((layer r f L F).newIso j hj).inv := by
  rw [leftTransformation, NatTrans.comp_app, layerOfFunctorIso_inv_app r,
    LayerHom.transformation_app_new _ _ hj, layerOfFunctor_newIso r X d j hj]
  change (layerOfFunctorObjIso r X d j).inv ≫
    (layerOfFunctorObjIso r X d j).hom ≫ newI r f L F j.obj hj ≫
      ((layer r f L F).newIso j hj).inv = _
  rw [Iso.inv_hom_id_assoc]

/-- Every original new-degree target component retains the original factory target map. -/
theorem rightTransformation_new (j : r.Through d) (hj : r.degree j.obj = d) :
    (rightTransformation r f L F).app j =
      ((layer r f L F).newIso j hj).hom ≫ newP r f L F j.obj hj := by
  rw [rightTransformation, NatTrans.comp_app, LayerHom.transformation_app_new _ _ hj,
    layerOfFunctorIso_hom_app r, layerOfFunctor_newIso r Y d j hj]
  change (((layer r f L F).newIso j hj).hom ≫ newP r f L F j.obj hj ≫
    (layerOfFunctorObjIso r Y d j).inv) ≫ (layerOfFunctorObjIso r Y d j).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Both whole new-degree factors recover the unchanged original restricted caller map. -/
theorem transformation_fac : leftTransformation r f L F ≫ rightTransformation r f L F =
    Functor.whiskerLeft (r.throughObjects d).ι f := by
  ext j
  by_cases hj : r.degree j.obj < d
  · rw [NatTrans.comp_app, leftTransformation_old _ _ _ _ _ hj,
      rightTransformation_old _ _ _ _ _ hj,
      ]
    change (L.i.app ⟨j.obj, hj⟩ ≫ ((layer r f L F).oldIso j hj).inv) ≫
      (((layer r f L F).oldIso j hj).hom ≫ L.p.app ⟨j.obj, hj⟩) = f.app j.obj
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congr_app L.fac ⟨j.obj, hj⟩
  · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    rw [NatTrans.comp_app, leftTransformation_new _ _ _ _ _ hj',
      rightTransformation_new _ _ _ _ _ hj',
      ]
    change (newI r f L F j.obj hj' ≫ ((layer r f L F).newIso j hj').inv) ≫
      (((layer r f L F).newIso j hj').hom ≫ newP r f L F j.obj hj') = f.app j.obj
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact new_fac r f L F j.obj hj'

/-- The source coefficient factory constructs the full actual next prefix factor. -/
def nextPrefix : PrefixFactor r f d where
  Z := (layer r f L F).extension
  i := leftTransformation r f L F
  p := rightTransformation r f L F
  fac := transformation_fac r f L F

end CategoryTheory.ReedyStructure.StageFactory

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageFactory

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))
  {P Q : MorphismProperty C} (F : FactorizationData P Q)

omit [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C] in
/-- Equality of the actual middle objects and both original factor maps determines the complete
coefficient record. -/
theorem coefficient_ext {U V : C} {u : U ⟶ V}
    {a b : MapFactorizationData (⊤ : MorphismProperty C) ⊤ u}
    (hZ : a.Z = b.Z) (hi : HEq a.i b.i) (hp : HEq a.p b.p) : a = b := by
  cases a with
  | mk aZ ai ap af ahi ahp =>
    cases b with
    | mk bZ bi bp bf bhi bhp =>
      dsimp only at hZ hi hp
      cases hZ
      have hi' : ai = bi := eq_of_heq hi
      have hp' : ap = bp := eq_of_heq hp
      cases hi'
      cases hp'
      rfl

/-- Every actual smaller coefficient retains the complete original lower factor record. -/
theorem nextPrefix_coefficient_old (j : J) (hj : r.degree j < d) (hj' : r.degree j ≤ d) :
    (nextPrefix r f L F).component j hj' =
      PrefixGluing.coefficient L (⟨j, hj⟩ : r.Below d) := by
  let q : r.Through d := ⟨j, hj'⟩
  have hZ : ((nextPrefix r f L F).component j hj').Z =
      (PrefixGluing.coefficient L (⟨j, hj⟩ : r.Below d)).Z :=
    (layer r f L F).extendedObj_old q hj
  apply coefficient_ext hZ
  · apply (conj_eqToHom_iff_heq _ _ (rfl : X.obj j = X.obj j) hZ).mp
    simp only [eqToHom_refl, Category.id_comp]
    change (leftTransformation r f L F).app q =
      L.i.app ⟨j, hj⟩ ≫ ((layer r f L F).oldIso q hj).inv
    exact leftTransformation_old r f L F q hj
  · apply (conj_eqToHom_iff_heq _ _ hZ (rfl : Y.obj j = Y.obj j)).mp
    simp only [eqToHom_refl, Category.comp_id]
    change (rightTransformation r f L F).app q =
      ((layer r f L F).oldIso q hj).hom ≫ L.p.app ⟨j, hj⟩
    exact rightTransformation_old r f L F q hj

/-- Every actual smaller intermediate arrow retains the unchanged original lower-factor arrow. -/
theorem nextPrefix_map_old_heq (i j : J) (hi : r.degree i < d) (hj : r.degree j < d)
    (hi' : r.degree i ≤ d) (hj' : r.degree j ≤ d) (g : i ⟶ j) :
    HEq ((nextPrefix r f L F).map i j hi' hj' g)
      (L.Z.map (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩)) := by
  let qi : r.Through d := ⟨i, hi'⟩
  let qj : r.Through d := ⟨j, hj'⟩
  let u : qi ⟶ qj := ObjectProperty.homMk g
  have hmap : (nextPrefix r f L F).map i j hi' hj' g = (layer r f L F).oldMap u hi hj :=
    (layer r f L F).extension_map_old u hi hj
  have hZ_i := (layer r f L F).extendedObj_old qi hi
  have hZ_j := (layer r f L F).extendedObj_old qj hj
  apply (heq_of_eq hmap).trans
  exact (conj_eqToHom_iff_heq _ _ hZ_i hZ_j).mp rfl

variable (A : ∀ e : D, e < d → PrefixFactor r f e)
  (hA : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
    (A e' he').Extends (A e he) hle)

/-- The actual source factory preserves every adequate original strict-lower input prefix. -/
theorem nextPrefix_extends (e : D) (he : e < d) :
    (nextPrefix r f (PrefixGluing.lowerFactor r f d A hA) F).Extends (A e he) (le_of_lt he) where
  components j hj :=
    (nextPrefix_coefficient_old r f (PrefixGluing.lowerFactor r f d A hA) F j (hj.trans_lt he)
      (hj.trans (le_of_lt he))).trans
      (PrefixGluing.lowerFactor_coefficient r f d A hA j (hj.trans_lt he) e he hj)
  maps i j hi hj g :=
    (nextPrefix_map_old_heq r f (PrefixGluing.lowerFactor r f d A hA) F i j
      (hi.trans_lt he) (hj.trans_lt he) (hi.trans (le_of_lt he)) (hj.trans (le_of_lt he)) g).trans
      (PrefixGluing.lowerFactor_map_heq r f d A hA i j (hi.trans_lt he)
        (hj.trans_lt he) g e he hi hj)

end CategoryTheory.ReedyStructure.StageFactory

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.DegreeFactorization

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The actual compatible smaller prefixes retained by the recursive stage, with their exact
original provenance. -/
private structure ActualLowerFamily (d : D)
    (previous : ∀ e, e < d → Option (PrefixFactor r f e)) where
  part : ∀ e, e < d → PrefixFactor r f e
  compatible : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
    (part e' he').Extends (part e he) hle
  actual (e : D) (he : e < d) : previous e he = some (part e he)

/-- The original coefficient factory step, applied only to its actual compatible smaller source
prefixes. -/
private def step (d : D) (previous : ∀ e, e < d →
    Option (PrefixFactor r f e)) : Option (PrefixFactor r f d) := by
  classical
  exact if h : Nonempty (ActualLowerFamily r f d previous) then
    let A := h.some
    some (StageFactory.nextPrefix r f (PrefixGluing.lowerFactor r f d A.part A.compatible) F)
  else none

/-- The actual source coefficient factory recursively constructs original prefixes at every
source degree. -/
private def values : ∀ d, Option (PrefixFactor r f d) :=
  (wellFounded_lt : WellFounded ((· < ·) : D → D → Prop)).fix (step r f F)

/-- Every recursive prefix value is exactly the original coefficient step on its own smaller
actual prefixes. -/
private theorem values_eq (d : D) : values r f F d = step r f F d (fun e _ => values r f F e) :=
  (wellFounded_lt : WellFounded ((· < ·) : D → D → Prop)).fix_eq (step r f F) d

/-- Successful original degree construction retains every original smaller prefix object and map. -/
private def Spec (d : D) : Prop :=
  ∃ a : PrefixFactor r f d, values r f F d = some a ∧
    ∀ (e : D) (he : e < d) (b : PrefixFactor r f e), values r f F e = some b →
      a.Extends b (le_of_lt he)

/-- Every original source degree succeeds with full exact smaller-prefix compatibility. -/
private theorem values_spec (d : D) : Spec r f F d := by
  classical
  induction d using (wellFounded_lt : WellFounded ((· < ·) : D → D → Prop)).induction with
  | h d ih =>
    let A : ∀ e, e < d → PrefixFactor r f e := fun e he => (ih e he).choose
    have hA : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
        (A e' he').Extends (A e he) hle := by
      intro e e' he he' hle
      by_cases hEq : e = e'
      · subst e'
        exact (A e he).extends_refl
      · have hlt : e < e' := lt_of_le_of_ne hle hEq
        exact (ih e' he').choose_spec.2 e hlt (A e he) (ih e he).choose_spec.1
    have hn : Nonempty (ActualLowerFamily r f d (fun e _ => values r f F e)) :=
      ⟨⟨A, hA, fun e he => (ih e he).choose_spec.1⟩⟩
    let B := hn.some
    let a := StageFactory.nextPrefix r f (PrefixGluing.lowerFactor r f d B.part B.compatible) F
    refine ⟨a, ?_, ?_⟩
    · rw [values_eq, step, dite_eq_left hn]
    · intro e he b hb
      have hB : B.part e he = b := Option.some.inj ((B.actual e he).symm.trans hb)
      rw [← hB]
      exact StageFactory.nextPrefix_extends r f F B.part B.compatible e he

/-- The recursively constructed full original prefix at the supplied arbitrary source degree. -/
@[no_expose] def prefixAt (d : D) : PrefixFactor r f d := by
  exact (values_spec r f F d).choose

/-- Every original constructed prefix retains the original prefix at every smaller-or-equal
degree. -/
theorem prefixAt_extends (d e : D) (he : e ≤ d) :
    (prefixAt r f F d).Extends (prefixAt r f F e) he := by
  by_cases hEq : e = d
  · subst e
    exact (prefixAt r f F d).extends_refl
  · have hlt : e < d := lt_of_le_of_ne he hEq
    exact (values_spec r f F d).choose_spec.2 e hlt (prefixAt r f F e)
      (values_spec r f F e).choose_spec.1

/-- The original C source factory constructs the full actual factor of the original J diagram
map. -/
def factor : MapFactorizationData (⊤ : MorphismProperty (J ⥤ C)) ⊤ f :=
  PrefixGluing.fullFactor r f (prefixAt r f F) (prefixAt_extends r f F)

/-- Every complete original coefficient factor record is retained from each adequate constructed
prefix. -/
theorem factor_coefficient (j : J) (d : D) (hj : r.degree j ≤ d) :
    PrefixGluing.coefficient (factor r f F) j = (prefixAt r f F d).component j hj :=
  PrefixGluing.fullFactor_coefficient r f (prefixAt r f F) (prefixAt_extends r f F) j d hj

/-- Every original intermediate diagram arrow is retained from each adequate constructed prefix. -/
theorem factor_map_heq (i j : J) (g : i ⟶ j) (d : D) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) :
    HEq ((factor r f F).Z.map g) ((prefixAt r f F d).map i j hi hj g) :=
  PrefixGluing.fullFactor_map_heq r f (prefixAt r f F) (prefixAt_extends r f F) i j g d hi hj

/-- Both whole original natural factors recover the unchanged original J diagram map. -/
theorem factor_fac : (factor r f F).i ≫ (factor r f F).p = f := (factor r f F).fac

end CategoryTheory.ReedyStructure.DegreeFactorization

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.DegreeFactorization

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The actual family of all strictly smaller constructed original prefixes. -/
def past (d : D) : ∀ e, e < d → PrefixFactor r f e := fun e _ => prefixAt r f F e

/-- Every pair of actual smaller prefixes retains the full original compatibility. -/
theorem past_compatible (d : D) (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e') :
    (past r f F d e' he').Extends (past r f F d e he) hle := prefixAt_extends r f F e' e hle

/-- The actual smaller family is the source family used by the original degree recursion. -/
private def pastActual (d : D) : ActualLowerFamily r f d (fun e _ => values r f F e) where
  part := past r f F d
  compatible := past_compatible r f F d
  actual e _ := (values_spec r f F e).choose_spec.1

omit [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C] in
/-- An actual smaller family is determined by its complete original prefix values. -/
private theorem actualLowerFamily_ext {d : D} {previous : ∀ e, e < d → Option (PrefixFactor r f e)}
    {a b : ActualLowerFamily r f d previous} (h : a.part = b.part) : a = b := by
  cases a
  cases b
  dsimp only at h
  cases h
  rfl

/-- The actual smaller family is unique because every prefix value is the same original
recursive value. -/
private theorem actualLowerFamily_unique (d : D)
    (a : ActualLowerFamily r f d (fun e _ => values r f F e)) : a = pastActual r f F d := by
  apply actualLowerFamily_ext
  funext e he
  exact Option.some.inj ((a.actual e he).symm.trans (values_spec r f F e).choose_spec.1)

/-- Each selected arbitrary-degree prefix is exactly the original coefficient-factory
construction on its past. -/
theorem prefixAt_eq_nextPrefix (d : D) :
    prefixAt r f F d = StageFactory.nextPrefix r f
      (PrefixGluing.lowerFactor r f d (past r f F d) (past_compatible r f F d)) F := by
  classical
  have hn : Nonempty (ActualLowerFamily r f d (fun e _ => values r f F e)) := ⟨pastActual r f F d⟩
  have hu : hn.some = pastActual r f F d := actualLowerFamily_unique r f F d hn.some
  have hv : values r f F d = some (StageFactory.nextPrefix r f
      (PrefixGluing.lowerFactor r f d (past r f F d) (past_compatible r f F d)) F) := by
    rw [values_eq, step, dite_eq_left hn, hu]
    rfl
  exact Option.some.inj ((values_spec r f F d).choose_spec.1.symm.trans hv)

/-- The exact actual lower factor on which the source coefficient factory operates at the
supplied degree. -/
def lowerAt (d : D) : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f) :=
  PrefixGluing.lowerFactor r f d (past r f F d) (past_compatible r f F d)

/-- Every original lower coefficient record is the actual record of every adequate constructed
prefix. -/
theorem lowerAt_coefficient (d : D) (j : J) (hj : r.degree j < d) (e : D) (he : e < d)
    (hje : r.degree j ≤ e) :
    PrefixGluing.coefficient (lowerAt r f F d) (⟨j, hj⟩ : r.Below d) =
      (prefixAt r f F e).component j hje :=
  PrefixGluing.lowerFactor_coefficient r f d (past r f F d) (past_compatible r f F d) j hj e he hje

/-- Every original lower intermediate arrow is the actual arrow of every adequate constructed
prefix. -/
theorem lowerAt_map_heq (d : D) (i j : J) (hi : r.degree i < d) (hj : r.degree j < d)
    (g : i ⟶ j) (e : D) (he : e < d) (hie : r.degree i ≤ e) (hje : r.degree j ≤ e) :
    HEq ((lowerAt r f F d).Z.map (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩))
      ((prefixAt r f F e).map i j hie hje g) :=
  PrefixGluing.lowerFactor_map_heq r f d (past r f F d)
    (past_compatible r f F d) i j hi hj g e he hie hje

end CategoryTheory.ReedyStructure.DegreeFactorization

end ReedyPart4

section ReedyPart5

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.DegreeFactorization

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {P Q : MorphismProperty C} (F : FactorizationData P Q) (j : J)

/-- The actual global object is the original source coefficient factory object at the object's
own degree. -/
theorem factor_obj_new_eq :
    (factor r f F).Z.obj j =
      (StageFactory.coefficientFactor r f (lowerAt r f F (r.degree j)) F j rfl).Z := by
  calc
    _ = (prefixAt r f F (r.degree j)).Z.obj (⟨j, le_rfl⟩ : r.Through (r.degree j)) :=
      congrArg MapFactorizationData.Z (factor_coefficient r f F j (r.degree j) le_rfl)
    _ = (StageFactory.nextPrefix r f (lowerAt r f F (r.degree j)) F).Z.obj
        (⟨j, le_rfl⟩ : r.Through (r.degree j)) :=
      congrArg (fun a : PrefixFactor r f (r.degree j) => a.Z.obj ⟨j, le_rfl⟩)
        (prefixAt_eq_nextPrefix r f F (r.degree j))
    _ = _ := (StageFactory.layer r f (lowerAt r f F (r.degree j)) F).extension_obj_new
      (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl

/-- The whole global left component retains the original source injection and coefficient
factory left map. -/
theorem factor_i_new_heq :
    HEq ((factor r f F).i.app j) (StageFactory.newI r f (lowerAt r f F (r.degree j)) F j rfl) := by
  have hi : HEq ((factor r f F).i.app j)
      ((prefixAt r f F (r.degree j)).i.app (⟨j, le_rfl⟩ : r.Through (r.degree j))) :=
    Eq.mp (congrArg (fun a => HEq ((factor r f F).i.app j) a.i)
      (factor_coefficient r f F j (r.degree j) le_rfl)) HEq.rfl
  apply hi.trans
  rw [prefixAt_eq_nextPrefix]
  have hs := StageFactory.leftTransformation_new r f (lowerAt r f F (r.degree j)) F
    (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl
  exact (heq_of_eq hs).trans (comp_eqToHom_heq _
    ((StageFactory.layer r f (lowerAt r f F (r.degree j)) F).extendedObj_new
      (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl).symm)

/-- The whole global right component retains the original coefficient factory right map and
target projection. -/
theorem factor_p_new_heq :
    HEq ((factor r f F).p.app j) (StageFactory.newP r f (lowerAt r f F (r.degree j)) F j rfl) := by
  have hp : HEq ((factor r f F).p.app j)
      ((prefixAt r f F (r.degree j)).p.app (⟨j, le_rfl⟩ : r.Through (r.degree j))) :=
    Eq.mp (congrArg (fun a => HEq ((factor r f F).p.app j) a.p)
      (factor_coefficient r f F j (r.degree j) le_rfl)) HEq.rfl
  apply hp.trans
  rw [prefixAt_eq_nextPrefix]
  have hs := StageFactory.rightTransformation_new r f (lowerAt r f F (r.degree j)) F
    (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl
  exact (heq_of_eq hs).trans (eqToHom_comp_heq _
    ((StageFactory.layer r f (lowerAt r f F (r.degree j)) F).extendedObj_new
      (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl))

/-- The full original left component commutes with its exact source coefficient object
comparison. -/
theorem factor_i_new :
    (factor r f F).i.app j ≫ eqToHom (factor_obj_new_eq r f F j) =
      StageFactory.newI r f (lowerAt r f F (r.degree j)) F j rfl := by
  apply (comp_eqToHom_iff (factor_obj_new_eq r f F j) _ _).mpr
  simpa only [eqToHom_refl, Category.id_comp] using
    (conj_eqToHom_iff_heq _ _ (rfl : X.obj j = X.obj j) (factor_obj_new_eq r f F j)).mpr
      (factor_i_new_heq r f F j)

/-- The full original right component commutes with the same exact source coefficient object
comparison. -/
theorem factor_p_new :
    eqToHom (factor_obj_new_eq r f F j) ≫
      StageFactory.newP r f (lowerAt r f F (r.degree j)) F j rfl =
      (factor r f F).p.app j := by
  simpa only [eqToHom_refl, Category.comp_id] using
    ((conj_eqToHom_iff_heq _ _ (factor_obj_new_eq r f F j) (rfl : Y.obj j = Y.obj j)).mpr
      (factor_p_new_heq r f F j)).symm

end CategoryTheory.ReedyStructure.DegreeFactorization

end ReedyPart5
