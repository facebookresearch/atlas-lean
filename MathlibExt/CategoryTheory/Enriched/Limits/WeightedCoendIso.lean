/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory

/-!
# Isomorphisms of full weighted-coend presentations

The maps are the existing complete graded weight maps. Their actual
generator formulas and both inverse laws retain the entire weight and
diagram functions and the particular selected colimit presentations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uI

open CategoryTheory MonoidalCategory Opposite Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.weightedCoend

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

section Weight

variable {W W' : EnrichedFunctorCat V Iᵒᵖ}
  (F : EnrichedFunctor V I V) (e : W ≅ W')
  [HasCoproduct (relations W.toEnrichedFunctor F)]
  [HasCoproduct (objects W.toEnrichedFunctor F)]
  [HasCoequalizer (leftMap W.toEnrichedFunctor F) (rightMap W.toEnrichedFunctor F)]
  [HasCoproduct (relations W'.toEnrichedFunctor F)]
  [HasCoproduct (objects W'.toEnrichedFunctor F)]
  [HasCoequalizer (leftMap W'.toEnrichedFunctor F) (rightMap W'.toEnrichedFunctor F)]

/-- The actual full weight isomorphism induces an isomorphism of the selected coends. -/
@[no_expose]
def weightIso :
    Enriched.weightedCoend W.toEnrichedFunctor F ≅
      Enriched.weightedCoend W'.toEnrichedFunctor F where
  hom := mapWeightGraded F e.hom
  inv := mapWeightGraded F e.inv
  hom_inv_id := by
    rw [← mapWeightGraded_comp]
    have h : GradedNatTrans.unitComp e.hom e.inv =
        GradedNatTrans.unitId W.toEnrichedFunctor := e.hom_inv_id
    rw [h, mapWeightGraded_id]
  inv_hom_id := by
    rw [← mapWeightGraded_comp]
    have h : GradedNatTrans.unitComp e.inv e.hom =
        GradedNatTrans.unitId W'.toEnrichedFunctor := e.inv_hom_id
    rw [h, mapWeightGraded_id]

/-- Every full original generator retains the actual forward weight component. -/
@[reassoc]
theorem weightIso_gen_hom (i : I) :
    ι W.toEnrichedFunctor F i ≫ (weightIso F e).hom =
      (EnrichedFunctorCat.component e.hom (op i) ⊗ₘ 𝟙 (F.obj i)) ≫
        ι W'.toEnrichedFunctor F i :=
  mapWeightGraded_ι F e.hom i

/-- Every inverse generator uses the inverse of the same complete weight map. -/
@[reassoc]
theorem weightIso_gen_inv (i : I) :
    ι W'.toEnrichedFunctor F i ≫ (weightIso F e).inv =
      (EnrichedFunctorCat.component e.inv (op i) ⊗ₘ 𝟙 (F.obj i)) ≫
        ι W.toEnrichedFunctor F i :=
  mapWeightGraded_ι F e.inv i

/-- The complete forward function is the original graded coend weight map. -/
theorem weightIso_hom_value :
    (weightIso F e).hom = mapWeightGraded F e.hom := by
  unfold weightIso
  rfl

/-- The complete inverse function is the actual inverse graded coend weight map. -/
theorem weightIso_inv_value :
    (weightIso F e).inv = mapWeightGraded F e.inv := by
  unfold weightIso
  rfl

end Weight

section Diagram

variable (W : EnrichedFunctor V Iᵒᵖ V)
  {F F' : EnrichedFunctorCat V I} (e : F ≅ F')
  [HasCoproduct (relations W F.toEnrichedFunctor)]
  [HasCoproduct (objects W F.toEnrichedFunctor)]
  [HasCoequalizer (leftMap W F.toEnrichedFunctor) (rightMap W F.toEnrichedFunctor)]
  [HasCoproduct (relations W F'.toEnrichedFunctor)]
  [HasCoproduct (objects W F'.toEnrichedFunctor)]
  [HasCoequalizer (leftMap W F'.toEnrichedFunctor) (rightMap W F'.toEnrichedFunctor)]

/-- A complete actual diagram isomorphism gives the existing coend diagram maps. -/
@[no_expose]
def diagramIso :
    Enriched.weightedCoend W F.toEnrichedFunctor ≅
      Enriched.weightedCoend W F'.toEnrichedFunctor where
  hom := mapDiagramGraded W e.hom
  inv := mapDiagramGraded W e.inv
  hom_inv_id := by
    rw [← mapDiagramGraded_comp]
    have h : GradedNatTrans.unitComp e.hom e.inv =
        GradedNatTrans.unitId F.toEnrichedFunctor := e.hom_inv_id
    rw [h, mapDiagramGraded_id]
  inv_hom_id := by
    rw [← mapDiagramGraded_comp]
    have h : GradedNatTrans.unitComp e.inv e.hom =
        GradedNatTrans.unitId F'.toEnrichedFunctor := e.inv_hom_id
    rw [h, mapDiagramGraded_id]

/-- Every original diagram generator keeps the full forward component. -/
@[reassoc]
theorem diagramIso_gen_hom (i : I) :
    ι W F.toEnrichedFunctor i ≫ (diagramIso W e).hom =
      (𝟙 (W.obj (op i)) ⊗ₘ EnrichedFunctorCat.component e.hom i) ≫
        ι W F'.toEnrichedFunctor i :=
  mapDiagramGraded_ι W e.hom i

/-- Every inverse diagram generator retains its actual inverse component. -/
@[reassoc]
theorem diagramIso_gen_inv (i : I) :
    ι W F'.toEnrichedFunctor i ≫ (diagramIso W e).inv =
      (𝟙 (W.obj (op i)) ⊗ₘ EnrichedFunctorCat.component e.inv i) ≫
        ι W F.toEnrichedFunctor i :=
  mapDiagramGraded_ι W e.inv i

end Diagram

end CategoryTheory.Enriched.weightedCoend

/-!
## Transport of both complete coend factors

The component comparisons below retain the full original weight and diagram
Hom actions and descend both actual factors through the selected coends.
-/

universe uA

namespace CategoryTheory.Enriched.weightedCoend.ComponentIso

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  (W W' : EnrichedFunctor V Aᵒᵖ V) (Q Q' : EnrichedFunctor V A V)
  (eW : ∀ a, W.obj (op a) ≅ W'.obj (op a))
  (eQ : ∀ a, Q.obj a ≅ Q'.obj a)

/-- The actual isomorphism of each original object summand. -/
abbrev objectIso (a : A) :
    Enriched.weightedCoend.objects W Q a ≅ Enriched.weightedCoend.objects W' Q' a :=
  eW a ⊗ᵢ eQ a

/-- The actual isomorphism of each full original relation summand. -/
abbrev relationIso (a b : A) :
    Enriched.weightedCoend.relations W Q (a, b) ≅
      Enriched.weightedCoend.relations W' Q' (a, b) :=
  eW b ⊗ᵢ (Iso.refl (a ⟶[V] b) ⊗ᵢ eQ a)

variable
  (hW : ∀ a b,
    MonoidalClosed.uncurry (W.map (op b) (op a)) ≫ (eW a).hom =
      ((eW b).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (W'.map (op b) (op a)))
  (hQ : ∀ a b,
    MonoidalClosed.uncurry (Q.map a b) ≫ (eQ b).hom =
      ((eQ a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (Q'.map a b))

include hW hQ

omit hQ in
/-- The complete original weight face commutes with both actual component isomorphisms. -/
@[reassoc]
theorem face0 (a b : A) :
    Enriched.weightedCoend.face0 W Q a b ≫ (objectIso W W' Q Q' eW eQ a).hom =
      (relationIso W W' Q Q' eW eQ a b).hom ≫ Enriched.weightedCoend.face0 W' Q' a b := by
  simp only [Enriched.weightedCoend.face0, objectIso, relationIso, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [hW a b]

omit hW in
/-- The complete original diagram-action face commutes on the whole enriched Hom object. -/
@[reassoc]
theorem face1 (a b : A) :
    Enriched.weightedCoend.face1 W Q a b ≫ (objectIso W W' Q Q' eW eQ b).hom =
      (relationIso W W' Q Q' eW eQ a b).hom ≫ Enriched.weightedCoend.face1 W' Q' a b := by
  have ha : (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
      MonoidalClosed.uncurry (Q.map a b) ≫ (eQ b).hom =
      (a ⟶[V] b) ◁ (eQ a).hom ≫ (β_ (a ⟶[V] b) (Q'.obj a)).hom ≫
        MonoidalClosed.uncurry (Q'.map a b) := by
    rw [hQ a b]
    simpa only [tensorHom_id, Category.assoc] using
      (BraidedCategory.braiding_naturality_right_assoc
        (a ⟶[V] b) (eQ a).hom (MonoidalClosed.uncurry (Q'.map a b))).symm
  simp only [Enriched.weightedCoend.face1, objectIso, relationIso, tensorIso_hom,
    Iso.refl_hom, ← id_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]
  simpa only [id_tensorHom, Category.assoc] using
    congrArg (fun f => (eW b).hom ⊗ₘ f) ha

omit hQ in
/-- The inverse comparison preserves the same complete weight face. -/
@[reassoc]
theorem face0_inv (a b : A) :
    Enriched.weightedCoend.face0 W' Q' a b ≫ (objectIso W W' Q Q' eW eQ a).inv =
      (relationIso W W' Q Q' eW eQ a b).inv ≫ Enriched.weightedCoend.face0 W Q a b := by
  apply (cancel_epi (relationIso W W' Q Q' eW eQ a b).hom).1
  calc
    _ = (Enriched.weightedCoend.face0 W Q a b ≫
        (objectIso W W' Q Q' eW eQ a).hom) ≫
        (objectIso W W' Q Q' eW eQ a).inv := by
      rw [← Category.assoc, ← face0 W W' Q Q' eW eQ hW]
    _ = Enriched.weightedCoend.face0 W Q a b := by simp
    _ = (relationIso W W' Q Q' eW eQ a b).hom ≫
        ((relationIso W W' Q Q' eW eQ a b).inv ≫
          Enriched.weightedCoend.face0 W Q a b) := by simp

omit hW in
/-- The inverse comparison preserves the same complete diagram-action face. -/
@[reassoc]
theorem face1_inv (a b : A) :
    Enriched.weightedCoend.face1 W' Q' a b ≫ (objectIso W W' Q Q' eW eQ b).inv =
      (relationIso W W' Q Q' eW eQ a b).inv ≫ Enriched.weightedCoend.face1 W Q a b := by
  apply (cancel_epi (relationIso W W' Q Q' eW eQ a b).hom).1
  calc
    _ = (Enriched.weightedCoend.face1 W Q a b ≫
        (objectIso W W' Q Q' eW eQ b).hom) ≫
        (objectIso W W' Q Q' eW eQ b).inv := by
      rw [← Category.assoc, ← face1 W W' Q Q' eW eQ hQ]
    _ = Enriched.weightedCoend.face1 W Q a b := by simp
    _ = (relationIso W W' Q Q' eW eQ a b).hom ≫
        ((relationIso W W' Q Q' eW eQ a b).inv ≫
          Enriched.weightedCoend.face1 W Q a b) := by simp

variable [HasCoproduct (Enriched.weightedCoend.objects W Q)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q)]
  [HasCoproduct (Enriched.weightedCoend.objects W' Q')]
  [HasCoproduct (Enriched.weightedCoend.relations W' Q')]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q') (Enriched.weightedCoend.rightMap W' Q')]

omit [HasCoproduct (Enriched.weightedCoend.objects W Q)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q)
    (Enriched.weightedCoend.rightMap W Q)] in
private theorem forwardCondition (a b : A) :
    Enriched.weightedCoend.face0 W Q a b ≫ (objectIso W W' Q Q' eW eQ a).hom ≫
        Enriched.weightedCoend.ι W' Q' a =
      Enriched.weightedCoend.face1 W Q a b ≫ (objectIso W W' Q Q' eW eQ b).hom ≫
        Enriched.weightedCoend.ι W' Q' b := by
  have h0 := face0_assoc W W' Q Q' eW eQ hW a b (Enriched.weightedCoend.ι W' Q' a)
  have h1 := face1_assoc W W' Q Q' eW eQ hQ a b (Enriched.weightedCoend.ι W' Q' b)
  have hc := congrArg (fun f => (relationIso W W' Q Q' eW eQ a b).hom ≫ f)
    (Enriched.weightedCoend.condition W' Q' a b)
  simp only [Enriched.weightedCoend.face0, Enriched.weightedCoend.face1, Category.assoc]
    at h0 h1 hc ⊢
  exact h0.trans (hc.trans h1.symm)

omit [HasCoproduct (Enriched.weightedCoend.objects W' Q')]
  [HasCoproduct (Enriched.weightedCoend.relations W' Q')]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q')
    (Enriched.weightedCoend.rightMap W' Q')] in
private theorem inverseCondition (a b : A) :
    Enriched.weightedCoend.face0 W' Q' a b ≫ (objectIso W W' Q Q' eW eQ a).inv ≫
        Enriched.weightedCoend.ι W Q a =
      Enriched.weightedCoend.face1 W' Q' a b ≫ (objectIso W W' Q Q' eW eQ b).inv ≫
        Enriched.weightedCoend.ι W Q b := by
  have h0 := face0_inv_assoc W W' Q Q' eW eQ hW a b (Enriched.weightedCoend.ι W Q a)
  have h1 := face1_inv_assoc W W' Q Q' eW eQ hQ a b (Enriched.weightedCoend.ι W Q b)
  have hc := congrArg (fun f => (relationIso W W' Q Q' eW eQ a b).inv ≫ f)
    (Enriched.weightedCoend.condition W Q a b)
  simp only [Enriched.weightedCoend.face0, Enriched.weightedCoend.face1, Category.assoc]
    at h0 h1 hc ⊢
  exact h0.trans (hc.trans h1.symm)

/-- The original chosen coends are isomorphic through the actual weight and coefficient maps. -/
@[no_expose]
def iso : Enriched.weightedCoend W Q ≅ Enriched.weightedCoend W' Q' where
  hom := Enriched.weightedCoend.desc W Q
    (fun a => (objectIso W W' Q Q' eW eQ a).hom ≫ Enriched.weightedCoend.ι W' Q' a)
    (forwardCondition W W' Q Q' eW eQ hW hQ)
  inv := Enriched.weightedCoend.desc W' Q'
    (fun a => (objectIso W W' Q Q' eW eQ a).inv ≫ Enriched.weightedCoend.ι W Q a)
    (inverseCondition W W' Q Q' eW eQ hW hQ)
  hom_inv_id := by
    apply Enriched.weightedCoend.hom_ext W Q
    intro a
    rw [← Category.assoc, Enriched.weightedCoend.ι_desc, Category.assoc,
      Enriched.weightedCoend.ι_desc]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply Enriched.weightedCoend.hom_ext W' Q'
    intro a
    rw [← Category.assoc, Enriched.weightedCoend.ι_desc, Category.assoc,
      Enriched.weightedCoend.ι_desc]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The forward comparison retains every actual original coend generator and both factors. -/
@[reassoc]
theorem ι_iso_hom (a : A) :
    Enriched.weightedCoend.ι W Q a ≫ (iso W W' Q Q' eW eQ hW hQ).hom =
      ((eW a).hom ⊗ₘ (eQ a).hom) ≫ Enriched.weightedCoend.ι W' Q' a :=
  Enriched.weightedCoend.ι_desc W Q _ _ a

/-- The inverse comparison retains every actual original generator and both inverse factors. -/
@[reassoc]
theorem ι_iso_inv (a : A) :
    Enriched.weightedCoend.ι W' Q' a ≫ (iso W W' Q Q' eW eQ hW hQ).inv =
      ((eW a).inv ⊗ₘ (eQ a).inv) ≫ Enriched.weightedCoend.ι W Q a :=
  Enriched.weightedCoend.ι_desc W' Q' _ _ a

end CategoryTheory.Enriched.weightedCoend.ComponentIso
