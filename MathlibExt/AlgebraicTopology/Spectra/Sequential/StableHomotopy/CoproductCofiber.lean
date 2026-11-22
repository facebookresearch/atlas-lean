/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Limits.CoproductPushout
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalISuspensionComparison
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.ModelCategory.CoproductWeakEquivalences
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi

/-!
# The actual cone cofiber of an original coproduct inclusion

The unreplaced native cone pushout of the whole original left coproduct
inclusion is the actual coproduct of that cone and the right spectrum.
Both complete pushout legs and the original right-summand section are
retained. Its collapse uses the same original cone contraction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductCofiberGeometry

private theorem collapseCoproduct_factor {C : Type (v + 1)} [Category.{v} C] [HasBinaryCoproducts C]
    {A Z Y : C} (c : A ⟶ Z) (z : Z ⟶ Y) :
    coprod.desc (c ≫ z) (𝟙 Y) = coprod.map c (𝟙 Y) ≫ coprod.desc z (𝟙 Y) := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc, ← Category.assoc, coprod.inl_map, Category.assoc, coprod.inl_desc]
  · rw [coprod.inr_desc, ← Category.assoc, coprod.inr_map, Category.assoc, coprod.inr_desc,
      Category.id_comp]

private theorem inclusionCollapse_factor {C : Type (v + 1)} [Category.{v} C] [HasBinaryCoproducts C]
    {X A Z Y : C} (i : X ⟶ A) (c : A ⟶ Z) (z : Z ⟶ Y) (x : X ⟶ Z)
    (h : i ≫ c = x) :
    coprod.desc (i ≫ coprod.inl) (coprod.inr : Y ⟶ A ⨿ Y) ≫
      coprod.desc (c ≫ z) (𝟙 Y) = coprod.desc (x ≫ z) (𝟙 Y) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inl_desc,
      ← Category.assoc, h, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_desc, coprod.inr_desc, coprod.inr_desc]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
variable (X Y : Carrier.{u, v})

/-- The original left coproduct inclusion is the entire source arrow used by the chosen cone pushout. -/
def arrow : Arrow Carrier.{u, v} := Arrow.mk (coprod.inl : X ⟶ X ⨿ Y)

/-- The actual original cone cofiber before applying a separate whole-arrow replacement. -/
abbrev coneCofiber : Carrier.{u, v} := (OriginalISuspension.cocone (B := B) (arrow X Y)).pt

/-- The chosen cone pushout is the same actual cone/right-summand coproduct. -/
def coneCofiberIso : coneCofiber (B := B) X Y ≅ (OriginalICone.cone (B := B)).obj X ⨿ Y :=
  CategoryTheory.Limits.CoproductPushout.iso ((OriginalICone.inclusion (B := B)).app X)

/-- The whole original cone leg is the same actual coproduct inclusion. -/
theorem coneCofiberIso_cone :
    (OriginalISuspension.cocone (B := B) (arrow X Y)).inl ≫ (coneCofiberIso X Y).hom =
      (coprod.inl : (OriginalICone.cone (B := B)).obj X ⟶ (OriginalICone.cone (B := B)).obj X ⨿ Y) :=
  CategoryTheory.Limits.CoproductPushout.iso_hom_inl _

/-- The entire original target leg preserves the exact original source inclusion and right identity. -/
theorem coneCofiberIso_target :
    (OriginalISuspension.cocone (B := B) (arrow X Y)).inr ≫ (coneCofiberIso X Y).hom =
      coprod.desc ((OriginalICone.inclusion (B := B)).app X ≫ coprod.inl)
        (coprod.inr : Y ⟶ _) := by
  exact (CategoryTheory.Limits.CoproductPushout.iso_hom_inr
    (Y := Y) ((OriginalICone.inclusion (B := B)).app X)).trans (by
      apply coprod.hom_ext <;> simp)

/-- The actual cone collapse keeps the same right-summand identity and original cone contraction. -/
def collapse : coneCofiber (B := B) X Y ⟶ Y :=
  (coneCofiberIso X Y).hom ≫ coprod.desc
    ((OriginalICone.contraction (B := B)).app X ≫ Diagrams.zeroTo Y) (𝟙 Y)

/-- The original right-summand map is the actual section of this whole cone collapse. -/
def sectionMap : Y ⟶ coneCofiber (B := B) X Y :=
  (coprod.inr : Y ⟶ X ⨿ Y) ≫ (OriginalISuspension.cocone (B := B) (arrow X Y)).inr

/-- The entire original target inclusion followed by collapse is the literal original right projection. -/
theorem target_collapse :
    (OriginalISuspension.cocone (B := B) (arrow X Y)).inr ≫ collapse X Y =
      coprod.desc (Diagrams.toZero X ≫ Diagrams.zeroTo Y) (𝟙 Y) := by
  let e := (coneCofiberIso X Y).hom
  let r := coprod.desc ((OriginalICone.contraction (B := B)).app X ≫ Diagrams.zeroTo Y) (𝟙 Y)
  let i : X ⟶ (OriginalICone.cone (B := B)).obj X := (OriginalICone.inclusion (B := B)).app X
  let c : (OriginalICone.cone (B := B)).obj X ⟶ Diagrams.zeroDiagram :=
    (OriginalICone.contraction (B := B)).app X
  have h := coneCofiberIso_target X Y
  exact (Category.assoc (OriginalISuspension.cocone (B := B) (arrow X Y)).inr e r).symm.trans
    ((congrArg (fun m => m ≫ r) h).trans
      (inclusionCollapse_factor i c (Diagrams.zeroTo Y) (Diagrams.toZero X)
        (OriginalICone.inclusion_contraction X)))

/-- The same original right section and whole cone collapse compose to the literal identity spectrum map. -/
theorem section_collapse : sectionMap (B := B) X Y ≫ collapse X Y = 𝟙 Y := by
  let t : X ⨿ Y ⟶ coneCofiber (B := B) X Y :=
    (OriginalISuspension.cocone (B := B) (arrow X Y)).inr
  let e : coneCofiber (B := B) X Y ⟶ (OriginalICone.cone (B := B)).obj X ⨿ Y :=
    (coneCofiberIso X Y).hom
  let r : (OriginalICone.cone (B := B)).obj X ⨿ Y ⟶ Y :=
    coprod.desc ((OriginalICone.contraction (B := B)).app X ≫ Diagrams.zeroTo Y) (𝟙 Y)
  have h : (coprod.inr : Y ⟶ X ⨿ Y) ≫ t ≫ e =
      (coprod.inr : Y ⟶ (OriginalICone.cone (B := B)).obj X ⨿ Y) :=
    (congrArg (fun m => (coprod.inr : Y ⟶ X ⨿ Y) ≫ m) (coneCofiberIso_target X Y)).trans
      (coprod.inr_desc _ _)
  exact (Category.assoc (coprod.inr : Y ⟶ X ⨿ Y) t (e ≫ r)).trans
    ((congrArg (fun m => (coprod.inr : Y ⟶ X ⨿ Y) ≫ m) (Category.assoc t e r).symm).trans
      ((Category.assoc (coprod.inr : Y ⟶ X ⨿ Y) (t ≫ e) r).symm.trans
        ((congrArg (fun m => m ≫ r) h).trans (coprod.inr_desc _ _))))

/-- The same whole cone collapse is level weak for cofibrant original summands. -/
theorem collapse_weak [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (collapse (B := B) X Y) := by
  let z : Carrier.{u, v} := Diagrams.zeroDiagram
  let c : (OriginalICone.cone (B := B)).obj X ⟶ z := (OriginalICone.contraction (B := B)).app X
  let _ : IsCofibrant ((OriginalICone.cone (B := B)).obj X) :=
    OriginalICone.cone_isCofibrant X
  let _ : WeakEquivalence c :=
    (HomotopicalAlgebra.weakEquivalence_iff ((OriginalICone.contraction (B := B)).app X)).mpr
      (OriginalICone.contraction_trivialFibration X).2
  let _ : IsCofibrant z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 z) Diagrams.zeroDiagramIsInitial]
    infer_instance
  let m : (OriginalICone.cone (B := B)).obj X ⨿ Y ⟶ z ⨿ Y := coprod.map c (𝟙 Y)
  let Xs : WalkingPair → Carrier.{u, v} := fun j => j.casesOn ((OriginalICone.cone (B := B)).obj X) Y
  let Ys : WalkingPair → Carrier.{u, v} := fun j => j.casesOn z Y
  let maps : ∀ j, Xs j ⟶ Ys j := fun j => by
    cases j
    · exact c
    · exact 𝟙 Y
  let _ : WeakEquivalence m :=
    @weakEquivalence_of_cofibrantCoproductCocones Carrier.{u, v} inferInstance
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory.{u, v} (B := B))
      WalkingPair inferInstance Xs Ys maps
      (by intro j; cases j <;> infer_instance)
      (by intro j; cases j <;> infer_instance)
      (by
        intro j
        cases j
        · change WeakEquivalence c
          infer_instance
        · change WeakEquivalence (𝟙 Y)
          infer_instance)
      _ _ (coprodIsCoprod ((OriginalICone.cone (B := B)).obj X) Y) (coprodIsCoprod z Y) m (by
        intro j
        cases j
        · exact coprod.inl_map c (𝟙 Y)
        · exact coprod.inr_map c (𝟙 Y))
  let e : z ⨿ Y ≅ Y := {
    hom := coprod.desc (Diagrams.zeroTo Y) (𝟙 Y)
    inv := coprod.inr
    hom_inv_id := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, Category.comp_id]
        exact Diagrams.zeroDiagramIsInitial.hom_ext _ _
      · simp
    inv_hom_id := coprod.inr_desc _ _ }
  have h : collapse (B := B) X Y = (coneCofiberIso X Y).hom ≫ m ≫ e.hom := by
    exact congrArg (fun f => (coneCofiberIso X Y).hom ≫ f)
      (collapseCoproduct_factor c (Diagrams.zeroTo Y))
  rw [h]
  let _ : WeakEquivalence (coneCofiberIso X Y).hom := by infer_instance
  let _ : IsIso e.hom := e.isIso_hom
  let _ : WeakEquivalence e.hom := (HomotopicalAlgebra.weakEquivalence_iff e.hom).mpr (mem_weakEquivalences e.hom)
  infer_instance

end PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductCofiberGeometry
