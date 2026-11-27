/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Basic

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IntervalHomotopyExtension
variable {C : Type uC} [Category.{vC} C] (T : C ⥤ C) (e : 𝟭 C ⟶ T)

/-- The ALL-target genuine extension property for the selected actual interval endpoint. -/
def property : MorphismProperty C := fun A X i =>
  ∀ (Y : C) (f : X ⟶ Y) (H : T.obj A ⟶ Y), e.app A ≫ H = i ≫ f →
    ∃ K : T.obj X ⟶ Y, e.app X ≫ K = f ∧ T.map i ≫ K = H

/-- The entire identity extension uses the original supplied homotopy itself. -/
theorem id_mem (X : C) : property T e (𝟙 X) := by
  intro Y f H h
  exact ⟨H, by simpa only [Category.id_comp] using h,
    by rw [T.map_id, Category.id_comp]⟩

/-- Genuine extension along BOTH original maps proves closure under their full composition. -/
theorem comp_mem {A X Z : C} (i : A ⟶ X) (j : X ⟶ Z)
    (hi : property T e i) (hj : property T e j) : property T e (i ≫ j) := by
  intro Y f H h
  obtain ⟨K, hK0, hKi⟩ := hi Y (j ≫ f) H (by simpa only [Category.assoc] using h)
  obtain ⟨L, hL0, hLj⟩ := hj Y f K hK0
  refine ⟨L, hL0, ?_⟩
  rw [T.map_comp, Category.assoc, hLj, hKi]

/-- The genuine extension property contains identities and is closed under composition. -/
instance isMultiplicative : (property T e).IsMultiplicative where
  id_mem := id_mem T e
  comp_mem := comp_mem T e

/--
The ACTUAL preserved pushout and BOTH original maps extend the new homotopy, with all four
square maps retained.
-/
theorem of_isPushout [PreservesColimitsOfShape WalkingSpan T]
    {A X Z B : C} {i : A ⟶ X} {j : A ⟶ Z} {inl : X ⟶ B} {inr : Z ⟶ B}
    (sq : IsPushout i j inl inr) (hj : property T e j) : property T e inl := by
  intro Y f H h0
  have hA : e.app A ≫ (T.map i ≫ H) = j ≫ (inr ≫ f) := by
    calc
      _ = (i ≫ e.app X) ≫ H := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ H) (e.naturality i).symm
      _ = i ≫ (inl ≫ f) := by rw [Category.assoc, h0]
      _ = _ := by rw [← Category.assoc, sq.w, Category.assoc]
  obtain ⟨K, hK0, hKj⟩ := hj Y (inr ≫ f) (T.map i ≫ H) hA
  let sqT := sq.map T
  let L : T.obj B ⟶ Y := sqT.desc H K hKj.symm
  have hLleft : T.map inl ≫ L = H := sqT.inl_desc H K hKj.symm
  have hLright : T.map inr ≫ L = K := sqT.inr_desc H K hKj.symm
  refine ⟨L, ?_, hLleft⟩
  apply sq.hom_ext
  · calc
      inl ≫ (e.app B ≫ L) = (e.app X ≫ T.map inl) ≫ L := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ L) (e.naturality inl)
      _ = inl ≫ f := by rw [Category.assoc, hLleft, h0]
  · calc
      inr ≫ (e.app B ≫ L) = (e.app Z ≫ T.map inr) ≫ L := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ L) (e.naturality inr)
      _ = inr ≫ f := by rw [Category.assoc, hLright, hK0]

/-- Actual pushout preservation proves full cobase-change stability of the extension property. -/
instance isStableUnderCobaseChange [PreservesColimitsOfShape WalkingSpan T] :
    (property T e).IsStableUnderCobaseChange where
  of_isPushout := of_isPushout T e

/-- The entire extension property is invariant under original whole Arrow isomorphisms. -/
instance respectsIso [PreservesColimitsOfShape WalkingSpan T] :
    (property T e).RespectsIso := inferInstance

/--
The preserved original coproduct and the actual constant-time projection extend BOTH summands;
no endpoint cofibrancy or point hypothesis is added.
-/
theorem coprod_inl_mem [HasBinaryCoproducts C]
    [PreservesColimitsOfShape (Discrete WalkingPair) T]
    (p : T ⟶ 𝟭 C) (hp : e ≫ p = 𝟙 (𝟭 C)) (X Z : C) :
    property T e (coprod.inl : X ⟶ X ⨿ Z) := by
  intro Y f H h0
  let K : T.obj Z ⟶ Y := p.app Z ≫ (coprod.inr : Z ⟶ X ⨿ Z) ≫ f
  let hT := isColimitOfHasBinaryCoproductOfPreservesColimit T X Z
  let L : T.obj (X ⨿ Z) ⟶ Y := hT.desc (BinaryCofan.mk H K)
  have hLleft : T.map (coprod.inl : X ⟶ X ⨿ Z) ≫ L = H :=
    hT.fac (BinaryCofan.mk H K) (Discrete.mk WalkingPair.left)
  have hLright : T.map (coprod.inr : Z ⟶ X ⨿ Z) ≫ L = K :=
    hT.fac (BinaryCofan.mk H K) (Discrete.mk WalkingPair.right)
  have hep : e.app Z ≫ p.app Z = 𝟙 Z := congr_app hp Z
  refine ⟨L, ?_, hLleft⟩
  apply coprod.hom_ext
  · calc
      (coprod.inl : X ⟶ X ⨿ Z) ≫ (e.app (X ⨿ Z) ≫ L) =
          (e.app X ≫ T.map coprod.inl) ≫ L := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ L) (e.naturality coprod.inl)
      _ = coprod.inl ≫ f := by rw [Category.assoc, hLleft, h0]
  · calc
      (coprod.inr : Z ⟶ X ⨿ Z) ≫ (e.app (X ⨿ Z) ≫ L) =
          (e.app Z ≫ T.map coprod.inr) ≫ L := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ L) (e.naturality coprod.inr)
      _ = coprod.inr ≫ f := by
        rw [Category.assoc, hLright]
        change e.app Z ≫ (p.app Z ≫ coprod.inr ≫ f) = _
        rw [← Category.assoc, ← Category.assoc, hep]
        exact congrArg (fun q : Z ⟶ X ⨿ Z => q ≫ f)
          (Category.id_comp (coprod.inr : Z ⟶ X ⨿ Z))

variable [HasPushouts C]

/-- The ACTUAL universal based interval test is the chosen pushout of its original endpoint. -/
def universalObject {A X : C} (i : A ⟶ X) : C := pushout (e.app A) i

/-- The exact universal cylinder comparison descends BOTH original time and endpoint maps. -/
def comparison {A X : C} (i : A ⟶ X) : universalObject T e i ⟶ T.obj X :=
  pushout.desc (T.map i) (e.app X) (e.naturality i).symm

/-- The entire original time leg of the universal comparison is retained. -/
@[reassoc]
theorem inl_comparison {A X : C} (i : A ⟶ X) :
    pushout.inl (e.app A) i ≫ comparison T e i = T.map i := pushout.inl_desc _ _ _

/-- The entire original target leg of the universal comparison is retained. -/
@[reassoc]
theorem inr_comparison {A X : C} (i : A ⟶ X) :
    pushout.inr (e.app A) i ≫ comparison T e i = e.app X := pushout.inr_desc _ _ _

/-- The universal SAME chosen based pushout test is equivalent to the ALL-target extension. -/
theorem universal_iff {A X : C} (i : A ⟶ X) :
    property T e i ↔ ∃ r : T.obj X ⟶ universalObject T e i,
      e.app X ≫ r = pushout.inr (e.app A) i ∧
        T.map i ≫ r = pushout.inl (e.app A) i := by
  constructor
  · intro h
    exact h (universalObject T e i) (pushout.inr (e.app A) i)
      (pushout.inl (e.app A) i) pushout.condition
  · rintro ⟨r, hr0, hri⟩ Y f H h0
    let d : universalObject T e i ⟶ Y := pushout.desc H f h0
    refine ⟨r ≫ d, ?_, ?_⟩
    · rw [← Category.assoc, hr0]
      exact pushout.inr_desc _ _ _
    · rw [← Category.assoc, hri]
      exact pushout.inl_desc _ _ _

/-- The SAME full universal comparison has a retraction exactly when genuine extension holds. -/
theorem retraction_iff {A X : C} (i : A ⟶ X) :
    property T e i ↔ ∃ r : T.obj X ⟶ universalObject T e i,
      comparison T e i ≫ r = 𝟙 (universalObject T e i) := by
  rw [universal_iff]
  have hn : e.app A ≫ T.map i = i ≫ e.app X := (e.naturality i).symm
  change (∃ r : T.obj X ⟶ pushout (e.app A) i,
      e.app X ≫ r = pushout.inr (e.app A) i ∧
        T.map i ≫ r = pushout.inl (e.app A) i) ↔
    ∃ r : T.obj X ⟶ pushout (e.app A) i,
      pushout.desc (T.map i) (e.app X) hn ≫ r = 𝟙 (pushout (e.app A) i)
  constructor
  · rintro ⟨r, hr0, hri⟩
    refine ⟨r, ?_⟩
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, hri, Category.comp_id]
    · rw [pushout.inr_desc_assoc, hr0, Category.comp_id]
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_, ?_⟩
    · have h := congrArg (fun q : pushout (e.app A) i ⟶ pushout (e.app A) i =>
        pushout.inr (e.app A) i ≫ q) hr
      simpa only [pushout.inr_desc_assoc, Category.comp_id] using h
    · have h := congrArg (fun q : pushout (e.app A) i ⟶ pushout (e.app A) i =>
        pushout.inl (e.app A) i ≫ q) hr
      simpa only [pushout.inl_desc_assoc, Category.comp_id] using h

end CategoryTheory.IntervalHomotopyExtension

namespace CategoryTheory.IntervalHomotopyExtension
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {G : D ⥤ C}

/--
An ACTUAL adjunction and whole time/endpoint comparison preserve genuine ALL-target extension;
all original maps and BOTH source/target extension equations are retained.
-/
theorem map_mem_of_adjunction (adj : F ⊣ G) (TC : C ⥤ C) (eC : 𝟭 C ⟶ TC)
    (TD : D ⥤ D) (eD : 𝟭 D ⟶ TD) (a : TC ⋙ F ≅ F ⋙ TD)
    (ha : ∀ X : C, F.map (eC.app X) ≫ (a.app X).hom = eD.app (F.obj X))
    {A X : C} (i : A ⟶ X) (hi : property TC eC i) : property TD eD (F.map i) := by
  intro Y f H h0
  let HC : TC.obj A ⟶ G.obj Y :=
    adj.homEquiv (TC.obj A) Y ((a.app A).hom ≫ H)
  let fc : X ⟶ G.obj Y := adj.homEquiv X Y f
  have hc : eC.app A ≫ HC = i ≫ fc := by
    calc
      _ = adj.homEquiv A Y (F.map (eC.app A) ≫ ((a.app A).hom ≫ H)) :=
        (adj.homEquiv_naturality_left (eC.app A) ((a.app A).hom ≫ H)).symm
      _ = adj.homEquiv A Y (eD.app (F.obj A) ≫ H) := by
        rw [← Category.assoc, ha]
      _ = adj.homEquiv A Y (F.map i ≫ f) := congrArg (adj.homEquiv A Y) h0
      _ = i ≫ fc := adj.homEquiv_naturality_left i f
  obtain ⟨KC, hKC0, hKCi⟩ := hi (G.obj Y) fc HC hc
  let L : F.obj (TC.obj X) ⟶ Y := (adj.homEquiv (TC.obj X) Y).symm KC
  have hL0 : F.map (eC.app X) ≫ L = f := by
    apply (adj.homEquiv X Y).injective
    rw [adj.homEquiv_naturality_left]
    change eC.app X ≫ (adj.homEquiv (TC.obj X) Y)
      ((adj.homEquiv (TC.obj X) Y).symm KC) = fc
    rw [Equiv.apply_symm_apply, hKC0]
  have hLi : F.map (TC.map i) ≫ L = (a.app A).hom ≫ H := by
    apply (adj.homEquiv (TC.obj A) Y).injective
    rw [adj.homEquiv_naturality_left]
    change TC.map i ≫ (adj.homEquiv (TC.obj X) Y)
      ((adj.homEquiv (TC.obj X) Y).symm KC) = HC
    rw [Equiv.apply_symm_apply, hKCi]
  refine ⟨(a.app X).inv ≫ L, ?_, ?_⟩
  · calc
      _ = (F.map (eC.app X) ≫ (a.app X).hom) ≫ ((a.app X).inv ≫ L) :=
        congrArg (fun q => q ≫ ((a.app X).inv ≫ L)) (ha X).symm
      _ = F.map (eC.app X) ≫ L := by
        rw [Category.assoc, ← Category.assoc (a.app X).hom, Iso.hom_inv_id, Category.id_comp]
      _ = f := hL0
  · calc
      _ = ((a.app A).inv ≫ F.map (TC.map i)) ≫ L := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ L) (a.inv.naturality i)
      _ = (a.app A).inv ≫ (F.map (TC.map i) ≫ L) := Category.assoc _ _ _
      _ = (a.app A).inv ≫ ((a.app A).hom ≫ H) := by rw [hLi]
      _ = H := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.IntervalHomotopyExtension
