/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeInjectivity
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transport of relative projectivity and injectivity

Natural isomorphisms of functors transport their relative projective and injective objects.
Equivalences of source categories and the displayed natural identifications give the corresponding
transport laws for the lifting properties.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uB vB uA vA uE vE

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {B : Type uB} [Category.{vB} B]
  {A : Type uA} [Category.{vA} A]
  {E : Type uE} [Category.{vE} E]

namespace SplitEpi

/-- Conjugate a section by the endpoint components of a natural isomorphism. -/
def ofNatIso {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) : SplitEpi (U'.map g) where
  section_ := e.inv.app Z ≫ s.section_ ≫ e.hom.app Y
  id := by
    calc
      (e.inv.app Z ≫ s.section_ ≫ e.hom.app Y) ≫ U'.map g =
          e.inv.app Z ≫ s.section_ ≫ (e.hom.app Y ≫ U'.map g) := by
        simp only [Category.assoc]
      _ = e.inv.app Z ≫ s.section_ ≫ (U.map g ≫ e.hom.app Z) := by
        rw [← e.hom.naturality g]
      _ = e.inv.app Z ≫ (s.section_ ≫ U.map g) ≫ e.hom.app Z := by
        simp only [Category.assoc]
      _ = 𝟙 (U'.obj Z) := by
        rw [s.id, Category.id_comp, e.inv_hom_id_app Z]

/-- The transported data uses the original section and isomorphism components. -/
@[simp]
theorem ofNatIso_section {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) :
    (ofNatIso e g s).section_ = e.inv.app Z ≫ s.section_ ≫ e.hom.app Y := rfl

/-- Transport along the identity retains the original section data. -/
@[simp]
theorem ofNatIso_refl {U : D ⥤ C} {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) : ofNatIso (Iso.refl U) g s = s := by
  apply SplitEpi.ext
  simp [ofNatIso]

/-- Two successive endpoint conjugations equal the single composite conjugation. -/
theorem ofNatIso_trans {U U' U'' : D ⥤ C} (e : U ≅ U') (e' : U' ≅ U'')
    {Y Z : D} (g : Y ⟶ Z) (s : SplitEpi (U.map g)) :
    ofNatIso (e ≪≫ e') g s = ofNatIso e' g (ofNatIso e g s) := by
  apply SplitEpi.ext
  simp [ofNatIso, Category.assoc]

/-- Transport by the inverse natural isomorphism recovers every original section. -/
@[simp]
theorem ofNatIso_symm {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) : ofNatIso e.symm g (ofNatIso e g s) = s := by
  apply SplitEpi.ext
  simp [ofNatIso, Category.assoc]

/-- The complete section data on the original arrow is equivalent under natural isomorphism. -/
def natIsoEquiv {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z) :
    SplitEpi (U.map g) ≃ SplitEpi (U'.map g) where
  toFun := ofNatIso e g
  invFun := ofNatIso e.symm g
  left_inv := ofNatIso_symm e g
  right_inv := ofNatIso_symm e.symm g

/-- Source whiskering evaluates the same conjugation at the original image arrow. -/
theorem ofNatIso_whiskerLeft {U U' : D ⥤ C} (e : U ≅ U') (K : E ⥤ D)
    {Y Z : E} (g : Y ⟶ Z) (s : SplitEpi ((K ⋙ U).map g)) :
    ofNatIso (Functor.isoWhiskerLeft K e) g s = ofNatIso e (K.map g) s := by
  apply SplitEpi.ext
  rfl

/-- Target whiskering transports all section components through the functor map. -/
theorem ofNatIso_whiskerRight {U U' : D ⥤ C} (e : U ≅ U') (V : C ⥤ B)
    {Y Z : D} (g : Y ⟶ Z) (s : SplitEpi (U.map g)) :
    ofNatIso (Functor.isoWhiskerRight e V) g (s.map V) = (ofNatIso e g s).map V := by
  apply SplitEpi.ext
  change V.map (e.inv.app Z) ≫ V.map s.section_ ≫ V.map (e.hom.app Y) =
    V.map (e.inv.app Z ≫ s.section_ ≫ e.hom.app Y)
  rw [Functor.map_comp, Functor.map_comp]

/-- A full faithful functor lowers a section through its Hom preimage. -/
noncomputable def ofMap (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) (s : SplitEpi (V.map g)) : SplitEpi g where
  section_ := V.preimage s.section_
  id := by
    apply V.map_injective
    rw [Functor.map_comp, V.map_preimage, s.id, Functor.map_id]

/-- The image of the lowered section is the original given section. -/
@[simp]
theorem map_ofMap_section (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) (s : SplitEpi (V.map g)) :
    V.map (ofMap V g s).section_ = s.section_ := V.map_preimage _

end SplitEpi

namespace Functor

/-- Natural isomorphism preserves the split-image arrow class without changing its original arrow. -/
theorem isSplitEpi_map_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U')
    {Y Z : D} (g : Y ⟶ Z) : IsSplitEpi (U.map g) ↔ IsSplitEpi (U'.map g) := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofNatIso e g s)
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofNatIso e.symm g s)

/-- Full faithfulness reflects splitting by lifting the section and its equation. -/
theorem isSplitEpi_map_iff_of_full_faithful (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) : IsSplitEpi (V.map g) ↔ IsSplitEpi g := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofMap V g s)
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (s.map V)

/-- Relative projectivity is contravariant in inclusion of the split-image arrow classes. -/
theorem IsRelativeProjective.of_split_class {U : D ⥤ C} {U' : D ⥤ B}
    {P : D} (hP : U'.IsRelativeProjective P)
    (h : ∀ {Y Z : D} (g : Y ⟶ Z), IsSplitEpi (U.map g) → IsSplitEpi (U'.map g)) :
    U.IsRelativeProjective P := by
  intro Y Z g s f
  obtain ⟨s'⟩ := (h g (IsSplitEpi.mk' s)).exists_splitEpi
  exact hP g s' f

/-- Every original U-section remains split after V, so the composite property implies the U-property. -/
theorem IsRelativeProjective.of_comp {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : (U ⋙ V).IsRelativeProjective P) : U.IsRelativeProjective P := by
  intro Y Z g s f
  exact hP g (s.map V) f

/-- Reflection is needed only on the original U-image arrows for the reverse composite implication. -/
theorem IsRelativeProjective.comp_of_reflects {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : U.IsRelativeProjective P)
    (hV : ∀ {Y Z : D} (g : Y ⟶ Z),
      IsSplitEpi (V.map (U.map g)) → IsSplitEpi (U.map g)) :
    (U ⋙ V).IsRelativeProjective P := by
  intro Y Z g s f
  obtain ⟨t⟩ := (hV g (IsSplitEpi.mk' s)).exists_splitEpi
  exact hP g t f

/-- The weakest arrow-class reflection assumption gives equality of the two full predicates. -/
theorem isRelativeProjective_comp_iff_of_reflects (U : D ⥤ C) (V : C ⥤ B) (P : D)
    (hV : ∀ {Y Z : D} (g : Y ⟶ Z),
      IsSplitEpi (V.map (U.map g)) → IsSplitEpi (U.map g)) :
    (U ⋙ V).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  ⟨fun h => Functor.IsRelativeProjective.of_comp V h,
    fun h => Functor.IsRelativeProjective.comp_of_reflects V h hV⟩

/-- Full faithful postcomposition leaves the complete relative lifting predicate unchanged. -/
theorem isRelativeProjective_comp_iff_of_full_faithful (U : D ⥤ C) (V : C ⥤ B)
    [V.Full] [V.Faithful] (P : D) :
    (U ⋙ V).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  isRelativeProjective_comp_iff_of_reflects U V P
    (fun g h => (isSplitEpi_map_iff_of_full_faithful V (U.map g)).mp h)

/-- Equivalence of target categories is a particular full faithful transport. -/
theorem isRelativeProjective_comp_equivalence_iff (U : D ⥤ C) (e : C ≌ B) (P : D) :
    (U ⋙ e.functor).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  isRelativeProjective_comp_iff_of_full_faithful U e.functor P

/-- Natural isomorphism identifies the full lifting predicates by section conjugation. -/
theorem isRelativeProjective_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U') (P : D) :
    U.IsRelativeProjective P ↔ U'.IsRelativeProjective P :=
  ⟨fun h => Functor.IsRelativeProjective.of_split_class h
      (fun g hs => (isSplitEpi_map_iff_of_natIso e g).mpr hs),
    fun h => Functor.IsRelativeProjective.of_split_class h
      (fun g hs => (isSplitEpi_map_iff_of_natIso e g).mp hs)⟩

/-- Restriction of a comparison to an arbitrary source functor keeps the same original lifts. -/
theorem isRelativeProjective_whiskerLeft_iff (K : E ⥤ D) {U U' : D ⥤ C}
    (e : U ≅ U') (P : E) :
    (K ⋙ U).IsRelativeProjective P ↔ (K ⋙ U').IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (isoWhiskerLeft K e) P

/-- Target whiskering uses the mapped endpoint isomorphisms. -/
theorem isRelativeProjective_whiskerRight_iff {U U' : D ⥤ C} (e : U ≅ U')
    (V : C ⥤ B) (P : D) :
    (U ⋙ V).IsRelativeProjective P ↔ (U' ⋙ V).IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (isoWhiskerRight e V) P

/-- An existing comparison with a composite functor gives the original intermediate relative property. -/
theorem IsRelativeProjective.of_comp_natIso {U : D ⥤ C} (V : C ⥤ B)
    {W : D ⥤ B} (e : U ⋙ V ≅ W) {P : D} (hP : W.IsRelativeProjective P) :
    U.IsRelativeProjective P :=
  Functor.IsRelativeProjective.of_comp V
    ((isRelativeProjective_iff_of_natIso e P).mpr hP)

/-- Parenthesizing a true composite is immaterial by the associator. -/
theorem isRelativeProjective_assoc_iff (U : D ⥤ C) (V : C ⥤ B) (W : B ⥤ A) (P : D) :
    ((U ⋙ V) ⋙ W).IsRelativeProjective P ↔ (U ⋙ (V ⋙ W)).IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (Functor.associator U V W) P

/-- The dual split-image class comparison follows from opposite section transport. -/
theorem isSplitMono_map_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U')
    {X Y : D} (g : X ⟶ Y) : IsSplitMono (U.map g) ↔ IsSplitMono (U'.map g) := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.exists_splitMono
    let t := SplitEpi.ofNatIso (NatIso.op e).symm g.op s.op
    exact IsSplitMono.mk'
      { retraction := t.section_.unop
        id := Quiver.Hom.op_inj (by simp) }
  · intro h
    obtain ⟨s⟩ := h.exists_splitMono
    let t := SplitEpi.ofNatIso (NatIso.op e) g.op s.op
    exact IsSplitMono.mk'
      { retraction := t.section_.unop
        id := Quiver.Hom.op_inj (by simp) }

/-- Opposite projectivity supplies the composite implication for relative injectivity. -/
theorem IsRelativeInjective.of_comp {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : (U ⋙ V).IsRelativeInjective P) : U.IsRelativeInjective P := by
  apply (isRelativeInjective_iff_op_isRelativeProjective U P).mpr
  have h : (U ⋙ V).op.IsRelativeProjective (Opposite.op P) :=
    (isRelativeInjective_iff_op_isRelativeProjective (U ⋙ V) P).mp hP
  have h' : (U.op ⋙ V.op).IsRelativeProjective (Opposite.op P) :=
    (isRelativeProjective_iff_of_natIso (Functor.opComp U V) (Opposite.op P)).mp h
  intro Y Z g s f
  exact Functor.IsRelativeProjective.of_comp V.op h' g s f

/-- Split-mono reflection on the original image arrows earns the reverse extension implication. -/
theorem IsRelativeInjective.comp_of_reflects {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : U.IsRelativeInjective P)
    (hV : ∀ {X Y : D} (g : X ⟶ Y),
      IsSplitMono (V.map (U.map g)) → IsSplitMono (U.map g)) :
    (U ⋙ V).IsRelativeInjective P := by
  apply (isRelativeInjective_iff_op_isRelativeProjective (U ⋙ V) P).mpr
  apply (isRelativeProjective_iff_of_natIso (Functor.opComp U V) (Opposite.op P)).mpr
  apply Functor.IsRelativeProjective.comp_of_reflects V.op
    ((isRelativeInjective_iff_op_isRelativeProjective U P).mp hP)
  intro X Y g hs
  obtain ⟨s⟩ := hs.exists_splitEpi
  have hm : IsSplitMono (V.map (U.map g.unop)) := IsSplitMono.mk'
    { retraction := s.section_.unop
      id := Quiver.Hom.op_inj (by simp) }
  obtain ⟨t⟩ := (hV g.unop hm).exists_splitMono
  exact IsSplitEpi.mk' (by simpa using t.op)

/-- The exact split-mono reflection hypothesis identifies the complete relative extension predicates. -/
theorem isRelativeInjective_comp_iff_of_reflects (U : D ⥤ C) (V : C ⥤ B) (P : D)
    (hV : ∀ {X Y : D} (g : X ⟶ Y),
      IsSplitMono (V.map (U.map g)) → IsSplitMono (U.map g)) :
    (U ⋙ V).IsRelativeInjective P ↔ U.IsRelativeInjective P :=
  ⟨fun h => Functor.IsRelativeInjective.of_comp V h,
    fun h => Functor.IsRelativeInjective.comp_of_reflects V h hV⟩

/-- The dual full faithful law reuses projectivity of the opposite functor. -/
theorem isRelativeInjective_comp_iff_of_full_faithful (U : D ⥤ C) (V : C ⥤ B)
    [V.Full] [V.Faithful] (P : D) :
    (U ⋙ V).IsRelativeInjective P ↔ U.IsRelativeInjective P := by
  rw [isRelativeInjective_iff_op_isRelativeProjective,
    isRelativeInjective_iff_op_isRelativeProjective]
  exact (isRelativeProjective_iff_of_natIso (Functor.opComp U V) (Opposite.op P)).trans
    (isRelativeProjective_comp_iff_of_full_faithful U.op V.op (Opposite.op P))

/-- An equivalence of target categories also preserves the full relative extension property. -/
theorem isRelativeInjective_comp_equivalence_iff (U : D ⥤ C) (e : C ≌ B) (P : D) :
    (U ⋙ e.functor).IsRelativeInjective P ↔ U.IsRelativeInjective P :=
  isRelativeInjective_comp_iff_of_full_faithful U e.functor P

/-- Natural isomorphism transports relative injectivity through the existing opposite criterion. -/
theorem isRelativeInjective_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U') (P : D) :
    U.IsRelativeInjective P ↔ U'.IsRelativeInjective P := by
  rw [isRelativeInjective_iff_op_isRelativeProjective,
    isRelativeInjective_iff_op_isRelativeProjective]
  exact (isRelativeProjective_iff_of_natIso (NatIso.op e) (Opposite.op P)).symm

/-- An composite comparison yields the intermediate relative extension property. -/
theorem IsRelativeInjective.of_comp_natIso {U : D ⥤ C} (V : C ⥤ B)
    {W : D ⥤ B} (e : U ⋙ V ≅ W) {P : D} (hP : W.IsRelativeInjective P) :
    U.IsRelativeInjective P :=
  Functor.IsRelativeInjective.of_comp V
    ((isRelativeInjective_iff_of_natIso e P).mpr hP)

/-- Relative extension is coherent with the functor associator. -/
theorem isRelativeInjective_assoc_iff (U : D ⥤ C) (V : C ⥤ B) (W : B ⥤ A) (P : D) :
    ((U ⋙ V) ⋙ W).IsRelativeInjective P ↔ (U ⋙ (V ⋙ W)).IsRelativeInjective P :=
  isRelativeInjective_iff_of_natIso (Functor.associator U V W) P

end Functor
end CategoryTheory
