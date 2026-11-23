/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationComponents
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletionSpace
public import Mathlib.CategoryTheory.ConnectedComponents
public import MathlibExt.CategoryTheory.ConnectedComponents.NerveDecomposition
public import Mathlib.CategoryTheory.Whiskering

/-!
# Translations between components of S⁻¹S

Indexes the components of the pair category by Grothendieck-group differences
and constructs translations to and from the zero component. Both composites have
specified natural transformations and nerve homotopies, and the component
decomposition recovers the pair category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Algebra

universe u v

public section

namespace CategoryTheory.SInverseS.ComponentTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The literal class predicate used as the public full-subcategory type constructor. -/
abbrev componentProperty (g : GrothendieckAddGroup (Skeleton C)) : ObjectProperty (Pair C) :=
  fun X => X.difference = g

/-- All objects and stabilized arrows in the specified original class. -/
abbrev Component (g : GrothendieckAddGroup (Skeleton C)) := (componentProperty g).FullSubcategory

/-- Every original component class has an actual stabilized-pair representative. -/
theorem exists_pair_difference (g : GrothendieckAddGroup (Skeleton C)) :
    ∃ X : Pair C, X.difference = g := by
  obtain ⟨c, hc⟩ := connectedComponentsToGrothendieck_surjective (C := C) g
  obtain ⟨X, hX⟩ := Quotient.exists_rep c
  exact ⟨X, (congrArg (connectedComponentsToGrothendieck (C := C)) hX).trans hc⟩

/-- A computed representative for every class, with the zero representative exactly the unit. -/
def representative (g : GrothendieckAddGroup (Skeleton C)) : Pair C := by
  classical
  exact if g = 0 then (zeroComponentBaseObject (C := C)).obj else
                       Classical.choose (exists_pair_difference g)

/-- The chosen representative retains the entire original difference class. -/
theorem representative_difference (g : GrothendieckAddGroup (Skeleton C)) :
    (representative g).difference = g := by
  classical
  by_cases h : g = 0
  · subst g
    simp only [representative]
    exact (zeroComponentBaseObject (C := C)).property
  · simp only [representative, ite_eq_right h]
    exact Classical.choose_spec (exists_pair_difference g)

/-- The specified zero representative is the literal original pair (0,0). -/
theorem representative_zero : representative (C := C) 0 = (⟨0,0⟩ : Pair C) := by
  classical
  simp only [representative]
  rfl

/-- The actual chosen object of the full class category. -/
def representativeObject (g : GrothendieckAddGroup (Skeleton C)) : Component g :=
  ⟨representative g, representative_difference g⟩

/-- Every full class category is nonempty, including every nonzero class. -/
theorem component_nonempty (g : GrothendieckAddGroup (Skeleton C)) : Nonempty (Component g) :=
  ⟨representativeObject g⟩

/-- The full category is connected by the existing common-target classification. -/
theorem component_isConnected (g : GrothendieckAddGroup (Skeleton C)) :
    IsConnected (Component g) := by
  let : Nonempty (Component g) := component_nonempty g
  apply zigzag_isConnected
  intro X Y
  have hXY : X.obj.difference = Y.obj.difference := X.property.trans Y.property.symm
  obtain ⟨Z, ⟨f⟩, ⟨k⟩⟩ := Pair.exists_cospan_of_difference_eq hXY
  have hZ : Z.difference = g := (Hom.difference_eq f).symm.trans X.property
  let Z' : Component g := ⟨Z,hZ⟩
  exact Zigzag.of_hom_inv (ObjectProperty.homMk f : X ⟶ Z') (ObjectProperty.homMk k : Y ⟶ Z')

/-- Swap the two original pair coordinates for the computed inverse translation. -/
abbrev swappedPair (X : Pair C) : Pair C := ⟨X.snd,X.fst⟩

/-- Coordinate swap negates the entire original Grothendieck difference. -/
theorem swappedPair_difference (X : Pair C) : (swappedPair X).difference = -X.difference := by
  unfold Pair.difference swappedPair
  abel

/-- The objectwise translation formula is the existing full component-map equation. -/
theorem translateToZero_difference (r X : Pair C) :
    ((translateToZeroFunctor r).obj X).difference = X.difference - r.difference := by
  have h := connectedComponentsToGrothendieck_mapConnectedComponents_translateToZero r
      (ConnectedComponents.mk X)
  simpa only [Functor.mapConnectedComponents_mk, connectedComponentsToGrothendieck_mk] using h

/-- The actual residual translation restricts the whole original class to zero. -/
def rawToZero (g : GrothendieckAddGroup (Skeleton C)) : Component g ⥤ ZeroComponent (C := C) :=
  ObjectProperty.lift (zeroComponentProperty (C := C))
    ((componentProperty g).ι ⋙ translateToZeroFunctor (representative g)) (fun X => by
      change ((translateToZeroFunctor (representative g)).obj X.obj).difference = 0
      rw [translateToZero_difference, X.property, representative_difference, sub_self])

/-- The computed swapped residual translation restricts zero to the entire original class. -/
def rawFromZero (g : GrothendieckAddGroup (Skeleton C)) : ZeroComponent (C := C) ⥤ Component g :=
  ObjectProperty.lift (componentProperty g)
    ((zeroComponentProperty (C := C)).ι ⋙
        translateToZeroFunctor (swappedPair (representative g))) (fun X => by
      change ((translateToZeroFunctor (swappedPair (representative g))).obj X.obj).difference = g
      have h0 : X.obj.difference = 0 := X.property
      rw [translateToZero_difference, h0, swappedPair_difference, representative_difference,
          zero_sub, neg_neg])

/-- The forward class map is the original translation, with a literal identity zero branch. -/
def toZero (g : GrothendieckAddGroup (Skeleton C)) : Component g ⥤ ZeroComponent (C := C) := by
  classical
  by_cases h : g = 0
  · subst g
    exact 𝟭 (ZeroComponent (C := C))
  · exact rawToZero g

/-- The inverse class map is the swapped original translation, with the same identity zero
branch. -/
def fromZero (g : GrothendieckAddGroup (Skeleton C)) : ZeroComponent (C := C) ⥤ Component g := by
  classical
  by_cases h : g = 0
  · subst g
    exact 𝟭 (ZeroComponent (C := C))
  · exact rawFromZero g

/-- The zero-component forward functor is exactly identity. -/
theorem toZero_zero : toZero (C := C) 0 = 𝟭 (ZeroComponent (C := C)) := by
  classical
  unfold toZero
  rw [dite_eq_left rfl]

/-- The zero-component inverse functor is exactly identity. -/
theorem fromZero_zero : fromZero (C := C) 0 = 𝟭 (ZeroComponent (C := C)) := by
  classical
  unfold fromZero
  rw [dite_eq_left rfl]

/-- The nonzero forward object is the SAME residual translation of the original object. -/
theorem toZero_obj_of_ne_zero (g : GrothendieckAddGroup (Skeleton C)) (hg : g ≠ 0)
    (X : Component g) :
    ((toZero g).obj X).obj = (translateToZeroFunctor (representative g)).obj X.obj := by
  classical
  simp only [toZero, dite_eq_right hg]
  rfl

/-- The nonzero inverse object is the SAME swapped translation of the original zero object. -/
theorem fromZero_obj_of_ne_zero (g : GrothendieckAddGroup (Skeleton C)) (hg : g ≠ 0)
    (X : ZeroComponent (C := C)) :
    ((fromZero g).obj X).obj =
        (translateToZeroFunctor (swappedPair (representative g))).obj X.obj := by
  classical
  simp only [fromZero, dite_eq_right hg]
  rfl


/-- Nonzero forward morphisms are the same residual stabilized-arrow translations. -/
theorem toZero_map_of_ne_zero (g : GrothendieckAddGroup (Skeleton C)) (hg : g ≠ 0)
    {X Y : Component g} (f : X ⟶ Y) :
    ((toZero g).map f).hom =
      eqToHom (toZero_obj_of_ne_zero g hg X) ≫
        (translateToZeroFunctor (representative g)).map f.hom ≫
          eqToHom (toZero_obj_of_ne_zero g hg Y).symm := by
  classical
  have hMap : ((toZero g).map f).hom ≍
      (translateToZeroFunctor (representative g)).map f.hom := by
    unfold toZero
    rw [dite_eq_right hg]
    rfl
  exact (conj_eqToHom_iff_heq _ _
    (toZero_obj_of_ne_zero g hg X) (toZero_obj_of_ne_zero g hg Y)).2 hMap

/-- Nonzero inverse morphisms are the same swapped residual translations. -/
theorem fromZero_map_of_ne_zero (g : GrothendieckAddGroup (Skeleton C)) (hg : g ≠ 0)
    {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    ((fromZero g).map f).hom =
      eqToHom (fromZero_obj_of_ne_zero g hg X) ≫
        (translateToZeroFunctor (swappedPair (representative g))).map f.hom ≫
          eqToHom (fromZero_obj_of_ne_zero g hg Y).symm := by
  classical
  have hMap : ((fromZero g).map f).hom ≍
      (translateToZeroFunctor (swappedPair (representative g))).map f.hom := by
    unfold fromZero
    rw [dite_eq_right hg]
    rfl
  exact (conj_eqToHom_iff_heq _ _
    (fromZero_obj_of_ne_zero g hg X) (fromZero_obj_of_ne_zero g hg Y)).2 hMap

/-- The two existing diagonal-addition transformations give the actual global residual inverse
unit. -/
def translationInverseUnit (r : Pair C) :
    𝟭 (Pair C) ⟶ translateToZeroFunctor r ⋙ translateToZeroFunctor (swappedPair r) := by
  let SP := translateSecondFunctor r.fst
  let FP := translateFirstFunctor r.fst
  let SD := translateSecondFunctor r.snd
  let FD := translateFirstFunctor r.snd
  let a : 𝟭 (Pair C) ⟶ SP ⋙ FP := diagonalAddSecondFirstNatTrans r.fst
  let d : 𝟭 (Pair C) ⟶ FD ⋙ SD := diagonalAddFirstSecondNatTrans r.snd
  let b : SP ⋙ FP ⟶ (SP ⋙ FD) ⋙ (SD ⋙ FP) :=
    Functor.whiskerLeft SP (Functor.whiskerRight d FP)
  exact a ≫ b

/-- Restrict the actual inverse unit to every complete original class. -/
def rawForwardInverseUnit (g : GrothendieckAddGroup (Skeleton C)) :
    𝟭 (Component g) ⟶ rawToZero g ⋙ rawFromZero g where
  app X := ObjectProperty.homMk ((translationInverseUnit (representative g)).app X.obj)
  naturality := by
    intro X Y f
    apply ObjectProperty.hom_ext
    simpa only [rawToZero, rawFromZero, Functor.comp_obj, Functor.comp_map,
      Functor.id_obj, Functor.id_map,
      ObjectProperty.lift, ObjectProperty.ι, inducedFunctor, ObjectProperty.homMk,
      ObjectProperty.FullSubcategory.comp_hom] using
        (translationInverseUnit (representative g)).naturality f.hom

/-- Restrict the other actual inverse unit to the complete zero category. -/
def rawInverseForwardUnit (g : GrothendieckAddGroup (Skeleton C)) :
    𝟭 (ZeroComponent (C := C)) ⟶ rawFromZero g ⋙ rawToZero g where
  app X :=
      ObjectProperty.homMk ((translationInverseUnit (swappedPair (representative g))).app X.obj)
  naturality := by
    intro X Y f
    apply ObjectProperty.hom_ext
    have hNat := (translationInverseUnit (swappedPair (representative g))).naturality f.hom
    dsimp only [swappedPair] at hNat
    simpa only [rawToZero, rawFromZero, Functor.comp_obj, Functor.comp_map,
      Functor.id_obj, Functor.id_map,
      ObjectProperty.lift, ObjectProperty.ι, inducedFunctor, ObjectProperty.homMk,
      ObjectProperty.FullSubcategory.comp_hom, swappedPair] using hNat

/-- Every class has its actual forward/inverse unit; at zero it is exactly identity. -/
def forwardInverseUnit (g : GrothendieckAddGroup (Skeleton C)) :
    𝟭 (Component g) ⟶ toZero g ⋙ fromZero g := by
  classical
  by_cases h : g = 0
  · subst g
    have hF : toZero (C := C) 0 ⋙ fromZero 0 = 𝟭 (ZeroComponent (C := C)) := by
      rw [toZero_zero, fromZero_zero]
      exact Functor.id_comp _
    exact eqToHom hF.symm
  · simpa only [toZero, fromZero, dite_eq_right h] using rawForwardInverseUnit g

/-- Every class has its actual inverse/forward unit; at zero it is the same identity branch. -/
def inverseForwardUnit (g : GrothendieckAddGroup (Skeleton C)) :
    𝟭 (ZeroComponent (C := C)) ⟶ fromZero g ⋙ toZero g := by
  classical
  by_cases h : g = 0
  · subst g
    have hF : fromZero (C := C) 0 ⋙ toZero 0 = 𝟭 (ZeroComponent (C := C)) := by
      rw [fromZero_zero, toZero_zero]
      exact Functor.id_comp _
    exact eqToHom hF.symm
  · simpa only [toZero, fromZero, dite_eq_right h] using rawInverseForwardUnit g

/-- Both computed maps compose to a nerve map homotopic to identity on EVERY class. -/
def forwardInverseNerveHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    SSet.Homotopy (𝟙 (CategoryTheory.nerve (Component g)))
      (CategoryTheory.nerveMap (toZero g) ≫ CategoryTheory.nerveMap (fromZero g)) := by
  simpa only [CategoryTheory.nerveMap_id, CategoryTheory.nerveMap_comp] using
    CategoryTheory.NatTrans.nerveHomotopy (forwardInverseUnit g)

/-- The reverse computed composite has its actual nerve homotopy on the full zero category. -/
def inverseForwardNerveHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    SSet.Homotopy (𝟙 (CategoryTheory.nerve (ZeroComponent (C := C))))
      (CategoryTheory.nerveMap (fromZero g) ≫ CategoryTheory.nerveMap (toZero g)) := by
  simpa only [CategoryTheory.nerveMap_id, CategoryTheory.nerveMap_comp] using
    CategoryTheory.NatTrans.nerveHomotopy (inverseForwardUnit g)

/-- The literal difference predicate is the stock connected-component predicate. -/
theorem componentProperty_eq_stock (g : GrothendieckAddGroup (Skeleton C)) :
    componentProperty g =
      ((connectedComponentsEquivGrothendieck (C := C)).symm g).objectProperty := by
  funext X
  apply propext
  let e := connectedComponentsEquivGrothendieck (C := C)
  change X.difference = g ↔ ConnectedComponents.mk X = e.symm g
  constructor
  · intro h
    apply e.injective
    exact h.trans (e.apply_symm_apply g).symm
  · intro h
    exact (congrArg e h).trans (e.apply_symm_apply g)

/-- Retag a literal difference class as its existing stock categorical component. -/
def componentToStock (g : GrothendieckAddGroup (Skeleton C)) :
    Component g ⥤
      ((connectedComponentsEquivGrothendieck (C := C)).symm g).Component :=
  ObjectProperty.ιOfLE (by
    intro X hX
    rw [← componentProperty_eq_stock g]
    exact hX)

/-- The whole class family, including every original Grothendieck class. -/
abbrev ComponentTotal := Σ g : GrothendieckAddGroup (Skeleton C), Component g

/-- This is the original stock decomposition reindexed by its canonical Grothendieck dictionary. -/
def classToStockDecomposition : ComponentTotal (C := C) ⥤ Decomposed (Pair C) :=
  CategoryTheory.Sigma.desc (fun g =>
    componentToStock g ⋙ CategoryTheory.Sigma.incl
      ((connectedComponentsEquivGrothendieck (C := C)).symm g))

private theorem stock_sigma_index_eq {X Y : Decomposed (Pair C)} (f : X ⟶ Y) :
    X.1 = Y.1 := by
  cases f
  rfl

private instance classToStockDecomposition_full :
    (classToStockDecomposition (C := C)).Full where
  map_surjective := by
    rintro ⟨g, X⟩ ⟨h, Y⟩ f
    have hIndex := stock_sigma_index_eq f
    have hg : g = h := (connectedComponentsEquivGrothendieck (C := C)).symm.injective hIndex
    cases hg
    cases f with
    | mk f =>
      exact ⟨CategoryTheory.Sigma.SigmaHom.mk (ObjectProperty.homMk f.hom), rfl⟩

private instance classToStockDecomposition_faithful :
    (classToStockDecomposition (C := C)).Faithful where
  map_injective := by
    rintro ⟨g, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨k⟩ h
    simp only [classToStockDecomposition, CategoryTheory.Sigma.desc_map_mk,
      Functor.comp_map, CategoryTheory.Sigma.incl_map] at h
    apply congrArg CategoryTheory.Sigma.SigmaHom.mk
    apply ObjectProperty.hom_ext
    simpa only [componentToStock, ObjectProperty.ιOfLE, ObjectProperty.homMk] using
      congrArg InducedCategory.Hom.hom (CategoryTheory.Sigma.SigmaHom.mk.inj h)

/-- The reindexing is bijective on actual objects, with no choice of a replacement source. -/
theorem classToStockDecomposition_bijective_obj :
    Function.Bijective (classToStockDecomposition (C := C)).obj := by
  let e := connectedComponentsEquivGrothendieck (C := C)
  constructor
  · rintro ⟨g, X, hX⟩ ⟨h, Y, hY⟩ hObj
    have hIndex : e.symm g = e.symm h := congrArg Sigma.fst hObj
    have hg : g = h := e.symm.injective hIndex
    cases hg
    have hXY : X = Y := congrArg (fun Z : Decomposed (Pair C) => Z.2.obj) hObj
    cases hXY
    rfl
  · rintro ⟨k, Y⟩
    obtain ⟨g, rfl⟩ := e.symm.surjective k
    have hY : Y.obj.difference = g := by
      have h := congrArg e Y.property
      exact h.trans (e.apply_symm_apply g)
    exact ⟨⟨g, ⟨Y.obj, hY⟩⟩, rfl⟩

/-- The actual class reindexing is a strict category isomorphism. -/
def classToStockDecompositionIsoCat :
    IsoCat (ComponentTotal (C := C)) (Decomposed (Pair C)) := by
  letI : (classToStockDecomposition (C := C)).IsIso :=
    { bijective_obj := classToStockDecomposition_bijective_obj }
  exact (classToStockDecomposition (C := C)).asIsomorphism

/-- The entire original pair category is the stock decomposition with its canonical class labels. -/
def componentDecompositionIsoCat : IsoCat (ComponentTotal (C := C)) (Pair C) :=
  (classToStockDecompositionIsoCat (C := C)).trans (decomposedIsoCat (Pair C))

private theorem componentDecompositionIsoCat_functor_computation :
    (componentDecompositionIsoCat (C := C)).functor =
      classToStockDecomposition ⋙ decomposedTo (Pair C) := by
  unfold componentDecompositionIsoCat
  change (classToStockDecompositionIsoCat (C := C)).functor ⋙
    (decomposedIsoCat (Pair C)).functor = _
  rw [decomposedIsoCat_functor]
  rfl

/-- The comparison is exactly the original class reindexing followed by the stock decomposition. -/
theorem componentDecompositionIsoCat_functor :
    (componentDecompositionIsoCat (C := C)).functor =
      classToStockDecomposition ⋙ decomposedTo (Pair C) :=
  componentDecompositionIsoCat_functor_computation

/-- The forward comparison retains the same original underlying pair in every class. -/
theorem componentDecompositionIsoCat_obj
    (g : GrothendieckAddGroup (Skeleton C)) (X : Component g) :
    (componentDecompositionIsoCat (C := C)).functor.obj ⟨g, X⟩ = X.obj := by
  rw [componentDecompositionIsoCat_functor]
  rfl

/-- On each class, the forward comparison is exactly the original full-subcategory inclusion. -/
theorem componentDecompositionIsoCat_incl (g : GrothendieckAddGroup (Skeleton C)) :
    CategoryTheory.Sigma.incl g ⋙ (componentDecompositionIsoCat (C := C)).functor =
      (componentProperty g).ι := by
  rw [componentDecompositionIsoCat_functor]
  rfl

/-- The specified zero pair is retained by the entire original decomposition. -/
theorem componentDecompositionIsoCat_zero :
    (componentDecompositionIsoCat (C := C)).functor.obj
      ⟨0, zeroComponentBaseObject (C := C)⟩ = (⟨0, 0⟩ : Pair C) := by
  rw [componentDecompositionIsoCat_obj]
  rfl

/-- Assemble every actual forward class translation into the whole zero-component family. -/
def totalToZero : ComponentTotal (C := C) ⥤
    Σ _ : GrothendieckAddGroup (Skeleton C), ZeroComponent (C := C) :=
  CategoryTheory.Sigma.Functor.sigma (fun g => toZero g)

/-- Assemble every computed inverse translation, preserving every original class label. -/
def totalFromZero : (Σ _ : GrothendieckAddGroup (Skeleton C), ZeroComponent (C := C)) ⥤
    ComponentTotal (C := C) :=
  CategoryTheory.Sigma.Functor.sigma (fun g => fromZero g)

/-- The whole forward/inverse unit is assembled from the actual classwise units. -/
def totalForwardInverseUnit :
    𝟭 (ComponentTotal (C := C)) ⟶ totalToZero ⋙ totalFromZero where
  app X := CategoryTheory.Sigma.SigmaHom.mk ((forwardInverseUnit X.1).app X.2)
  naturality := by
    rintro ⟨g, X⟩ ⟨_, Y⟩ ⟨f⟩
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk ((forwardInverseUnit g).naturality f)

/-- The whole inverse/forward unit retains the other actual inverse family. -/
def totalInverseForwardUnit :
    𝟭 (Σ _ : GrothendieckAddGroup (Skeleton C), ZeroComponent (C := C)) ⟶
      totalFromZero ⋙ totalToZero where
  app X := CategoryTheory.Sigma.SigmaHom.mk ((inverseForwardUnit X.1).app X.2)
  naturality := by
    rintro ⟨g, X⟩ ⟨_, Y⟩ ⟨f⟩
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk ((inverseForwardUnit g).naturality f)

end CategoryTheory.SInverseS.ComponentTranslation
