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
# Transport of relative lifting and extension properties

For a functor `U : D → C` between categories, an object `P` is
`U`-relative-projective if maps from `P` lift through every arrow whose
`U`-image is split epi. It is `U`-relative-injective if maps to `P`
extend across every arrow whose `U`-image is split mono.
Natural isomorphisms preserve these properties by conjugating sections
and retractions. Postcomposition gives one implication in general;
reflection of the relevant split-image arrows gives the converse,
in particular for full faithful functors and equivalences. All category
object and morphism universes are independent.
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

/-- Let `D,C` be categories, `U,U′ : D → C`, and `e : U ≅ U′`.
For `g : Y → Z` in `D` and a section `s : U(Z) → U(Y)` of `U(g)`, conjugation gives the section `e_Z⁻¹ ≫ s ≫ e_Y` of
`U′(g)`. -/
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

/-- Let `D,C` be categories, `U,U′ : D → C`, and `e : U ≅ U′`.
For `g : Y → Z` in `D` and a section `s : U(Z) → U(Y)` of `U(g)`, the transported section is exactly `e_Z⁻¹ ≫ s ≫ e_Y`,
with domain `U′(Z)` and codomain `U′(Y)`. -/
@[simp]
theorem ofNatIso_section {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) :
    (ofNatIso e g s).section_ = e.inv.app Z ≫ s.section_ ≫ e.hom.app Y := rfl

/-- For categories `D,C`, `U : D → C`, and a section of the image
of `g : Y → Z`, transport along the identity natural isomorphism
of `U` leaves the section unchanged. -/
@[simp]
theorem ofNatIso_refl {U : D ⥤ C} {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) : ofNatIso (Iso.refl U) g s = s := by
  apply SplitEpi.ext
  simp [ofNatIso]

/-- For categories `D,C`, functors `U,U′,U″ : D → C` and
isomorphisms `e : U ≅ U′`, `e′ : U′ ≅ U″`, transporting a section
of `U(g)` first by `e` then by `e′` equals transport by `e ≪≫ e′`. -/
theorem ofNatIso_trans {U U' U'' : D ⥤ C} (e : U ≅ U') (e' : U' ≅ U'')
    {Y Z : D} (g : Y ⟶ Z) (s : SplitEpi (U.map g)) :
    ofNatIso (e ≪≫ e') g s = ofNatIso e' g (ofNatIso e g s) := by
  apply SplitEpi.ext
  simp [ofNatIso, Category.assoc]

/-- Let `D,C` be categories, `U,U′ : D → C`, and `e : U ≅ U′`.
For `g : Y → Z` in `D` and a section `s : U(Z) → U(Y)` of `U(g)`, transport first by `e` and then by `e⁻¹` recovers the
original section of `U(g)`. -/
@[simp]
theorem ofNatIso_symm {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z)
    (s : SplitEpi (U.map g)) : ofNatIso e.symm g (ofNatIso e g s) = s := by
  apply SplitEpi.ext
  simp [ofNatIso, Category.assoc]

/-- For categories `D,C`, functors `U,U′ : D → C`, `e : U ≅ U′`,
and `g : Y → Z`, conjugation by the endpoint components gives a
bijection between sections of `U(g)` and sections of `U′(g)`. -/
def natIsoEquiv {U U' : D ⥤ C} (e : U ≅ U') {Y Z : D} (g : Y ⟶ Z) :
    SplitEpi (U.map g) ≃ SplitEpi (U'.map g) where
  toFun := ofNatIso e g
  invFun := ofNatIso e.symm g
  left_inv := ofNatIso_symm e g
  right_inv := ofNatIso_symm e.symm g

/-- Let `E,D,C` be categories, `K : E → D`, `U,U′ : D → C`,
and `e : U ≅ U′`. Transport of a section over `g : Y → Z` in `E`
by the source-whiskered isomorphism equals transport by `e` over
`K(g)`. -/
theorem ofNatIso_whiskerLeft {U U' : D ⥤ C} (e : U ≅ U') (K : E ⥤ D)
    {Y Z : E} (g : Y ⟶ Z) (s : SplitEpi ((K ⋙ U).map g)) :
    ofNatIso (Functor.isoWhiskerLeft K e) g s = ofNatIso e (K.map g) s := by
  apply SplitEpi.ext
  rfl

/-- Let `D,C` be categories, `U,U′ : D → C`, and `e : U ≅ U′`.
For `g : Y → Z` in `D` and a section `s : U(Z) → U(Y)` of `U(g)`, for any functor `V : C → B`, transporting its image
section by the target-whiskered isomorphism equals applying `V`
to the section transported by `e`. -/
theorem ofNatIso_whiskerRight {U U' : D ⥤ C} (e : U ≅ U') (V : C ⥤ B)
    {Y Z : D} (g : Y ⟶ Z) (s : SplitEpi (U.map g)) :
    ofNatIso (Functor.isoWhiskerRight e V) g (s.map V) = (ofNatIso e g s).map V := by
  apply SplitEpi.ext
  change V.map (e.inv.app Z) ≫ V.map s.section_ ≫ V.map (e.hom.app Y) =
    V.map (e.inv.app Z ≫ s.section_ ≫ e.hom.app Y)
  rw [Functor.map_comp, Functor.map_comp]

/-- Let `C,B` be categories and `V : C → B` full and faithful.
For `g : X → Y`, any section of `V(g)` lifts through fullness to a
section of `g`, with its section equation reflected by faithfulness. -/
noncomputable def ofMap (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) (s : SplitEpi (V.map g)) : SplitEpi g where
  section_ := V.preimage s.section_
  id := by
    apply V.map_injective
    rw [Functor.map_comp, V.map_preimage, s.id, Functor.map_id]

/-- Let `C,B` be categories and `V : C → B` full and faithful.
The image under `V` of the section lifted from a section of `V(g)`
is exactly that specified image section. -/
@[simp]
theorem map_ofMap_section (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) (s : SplitEpi (V.map g)) :
    V.map (ofMap V g s).section_ = s.section_ := V.map_preimage _

end SplitEpi

namespace Functor

/-- For categories `D,C`, naturally isomorphic `U,U′ : D → C`,
and `g : Y → Z`, the image `U(g)` is split epi if and only if
`U′(g)` is split epi. -/
theorem isSplitEpi_map_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U')
    {Y Z : D} (g : Y ⟶ Z) : IsSplitEpi (U.map g) ↔ IsSplitEpi (U'.map g) := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofNatIso e g s)
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofNatIso e.symm g s)

/-- Let `C,B` be categories and `V : C → B` full and faithful.
For `g : X → Y`, `V(g)` is split epi if and only if `g` is split epi. -/
theorem isSplitEpi_map_iff_of_full_faithful (V : C ⥤ B) [V.Full] [V.Faithful]
    {X Y : C} (g : X ⟶ Y) : IsSplitEpi (V.map g) ↔ IsSplitEpi g := by
  constructor
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (SplitEpi.ofMap V g s)
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact IsSplitEpi.mk' (s.map V)

/-- Let `D,C,B` be categories, `U : D → C`, `U′ : D → B`,
and `P : D`. If every arrow with split-epi `U`-image also has
split-epi `U′`-image, relative projectivity of `P` for `U′` implies
relative projectivity for `U`. -/
theorem IsRelativeProjective.of_split_class {U : D ⥤ C} {U' : D ⥤ B}
    {P : D} (hP : U'.IsRelativeProjective P)
    (h : ∀ {Y Z : D} (g : Y ⟶ Z), IsSplitEpi (U.map g) → IsSplitEpi (U'.map g)) :
    U.IsRelativeProjective P := by
  intro Y Z g s f
  obtain ⟨s'⟩ := (h g (IsSplitEpi.mk' s)).exists_splitEpi
  exact hP g s' f

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. Relative projectivity of `P` for `U ⋙ V` implies relative
projectivity for `U`, since functors preserve split epimorphisms. -/
theorem IsRelativeProjective.of_comp {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : (U ⋙ V).IsRelativeProjective P) : U.IsRelativeProjective P := by
  intro Y Z g s f
  exact hP g (s.map V) f

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. Suppose `P` is `U`-relative-projective and every `g` in `D`
with split-epi `V(U(g))` also has split-epi `U(g)`. Then `P` is
relative-projective for `U ⋙ V`. -/
theorem IsRelativeProjective.comp_of_reflects {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : U.IsRelativeProjective P)
    (hV : ∀ {Y Z : D} (g : Y ⟶ Z),
      IsSplitEpi (V.map (U.map g)) → IsSplitEpi (U.map g)) :
    (U ⋙ V).IsRelativeProjective P := by
  intro Y Z g s f
  obtain ⟨t⟩ := (hV g (IsSplitEpi.mk' s)).exists_splitEpi
  exact hP g t f

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. If `V(U(g))` split epi implies `U(g)` split epi for every
arrow `g` in `D`, then relative projectivity of `P` for `U ⋙ V`
is equivalent to relative projectivity for `U`. -/
theorem isRelativeProjective_comp_iff_of_reflects (U : D ⥤ C) (V : C ⥤ B) (P : D)
    (hV : ∀ {Y Z : D} (g : Y ⟶ Z),
      IsSplitEpi (V.map (U.map g)) → IsSplitEpi (U.map g)) :
    (U ⋙ V).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  ⟨fun h => Functor.IsRelativeProjective.of_comp V h,
    fun h => Functor.IsRelativeProjective.comp_of_reflects V h hV⟩

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. If `V` is full and faithful, `P` is relative-projective for
`U ⋙ V` if and only if it is relative-projective for `U`. -/
theorem isRelativeProjective_comp_iff_of_full_faithful (U : D ⥤ C) (V : C ⥤ B)
    [V.Full] [V.Faithful] (P : D) :
    (U ⋙ V).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  isRelativeProjective_comp_iff_of_reflects U V P
    (fun g h => (isSplitEpi_map_iff_of_full_faithful V (U.map g)).mp h)

/-- For categories `D,C,B`, functor `U : D → C`, equivalence
`e : C ≌ B`, and `P : D`, relative projectivity for `U ⋙ e` is
equivalent to relative projectivity for `U`. -/
theorem isRelativeProjective_comp_equivalence_iff (U : D ⥤ C) (e : C ≌ B) (P : D) :
    (U ⋙ e.functor).IsRelativeProjective P ↔ U.IsRelativeProjective P :=
  isRelativeProjective_comp_iff_of_full_faithful U e.functor P

/-- For categories `D,C`, naturally isomorphic `U,U′ : D → C`,
and `P : D`, the relative-projectivity properties for `U` and
`U′` are equivalent. -/
theorem isRelativeProjective_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U') (P : D) :
    U.IsRelativeProjective P ↔ U'.IsRelativeProjective P :=
  ⟨fun h => Functor.IsRelativeProjective.of_split_class h
      (fun g hs => (isSplitEpi_map_iff_of_natIso e g).mpr hs),
    fun h => Functor.IsRelativeProjective.of_split_class h
      (fun g hs => (isSplitEpi_map_iff_of_natIso e g).mp hs)⟩

/-- For categories `E,D,C`, functor `K : E → D`, naturally
isomorphic `U,U′ : D → C`, and `P : E`, relative projectivity for
`K ⋙ U` is equivalent to that for `K ⋙ U′`. -/
theorem isRelativeProjective_whiskerLeft_iff (K : E ⥤ D) {U U' : D ⥤ C}
    (e : U ≅ U') (P : E) :
    (K ⋙ U).IsRelativeProjective P ↔ (K ⋙ U').IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (isoWhiskerLeft K e) P

/-- For categories `D,C,B`, naturally isomorphic `U,U′ : D → C`,
functor `V : C → B`, and `P : D`, relative projectivity for
`U ⋙ V` is equivalent to that for `U′ ⋙ V`. -/
theorem isRelativeProjective_whiskerRight_iff {U U' : D ⥤ C} (e : U ≅ U')
    (V : C ⥤ B) (P : D) :
    (U ⋙ V).IsRelativeProjective P ↔ (U' ⋙ V).IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (isoWhiskerRight e V) P

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. For `W : D → B` with `U ⋙ V ≅ W`, relative projectivity
of `P` for `W` implies relative projectivity for `U`. -/
theorem IsRelativeProjective.of_comp_natIso {U : D ⥤ C} (V : C ⥤ B)
    {W : D ⥤ B} (e : U ⋙ V ≅ W) {P : D} (hP : W.IsRelativeProjective P) :
    U.IsRelativeProjective P :=
  Functor.IsRelativeProjective.of_comp V
    ((isRelativeProjective_iff_of_natIso e P).mpr hP)

/-- For categories `D,C,B,A`, functors `U : D → C`, `V : C → B`,
`W : B → A`, and `P : D`, relative projectivity for `(U ⋙ V) ⋙ W`
is equivalent to that for `U ⋙ (V ⋙ W)`. -/
theorem isRelativeProjective_assoc_iff (U : D ⥤ C) (V : C ⥤ B) (W : B ⥤ A) (P : D) :
    ((U ⋙ V) ⋙ W).IsRelativeProjective P ↔ (U ⋙ (V ⋙ W)).IsRelativeProjective P :=
  isRelativeProjective_iff_of_natIso (Functor.associator U V W) P

/-- For categories `D,C`, naturally isomorphic `U,U′ : D → C`,
and `g : X → Y`, `U(g)` is split mono if and only if `U′(g)` is
split mono, by transport of retractions. -/
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

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. Relative injectivity of `P` for `U ⋙ V` implies relative
injectivity for `U`, since functors preserve split monomorphisms. -/
theorem IsRelativeInjective.of_comp {U : D ⥤ C} (V : C ⥤ B) {P : D}
    (hP : (U ⋙ V).IsRelativeInjective P) : U.IsRelativeInjective P := by
  apply (isRelativeInjective_iff_op_isRelativeProjective U P).mpr
  have h : (U ⋙ V).op.IsRelativeProjective (Opposite.op P) :=
    (isRelativeInjective_iff_op_isRelativeProjective (U ⋙ V) P).mp hP
  have h' : (U.op ⋙ V.op).IsRelativeProjective (Opposite.op P) :=
    (isRelativeProjective_iff_of_natIso (Functor.opComp U V) (Opposite.op P)).mp h
  intro Y Z g s f
  exact Functor.IsRelativeProjective.of_comp V.op h' g s f

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. Suppose `P` is `U`-relative-injective and every `g` in `D`
with split-mono `V(U(g))` also has split-mono `U(g)`. Then `P` is
relative-injective for `U ⋙ V`. -/
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

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. If `V(U(g))` split mono implies `U(g)` split mono for every
arrow `g` in `D`, relative injectivity of `P` for `U ⋙ V` is
equivalent to relative injectivity for `U`. -/
theorem isRelativeInjective_comp_iff_of_reflects (U : D ⥤ C) (V : C ⥤ B) (P : D)
    (hV : ∀ {X Y : D} (g : X ⟶ Y),
      IsSplitMono (V.map (U.map g)) → IsSplitMono (U.map g)) :
    (U ⋙ V).IsRelativeInjective P ↔ U.IsRelativeInjective P :=
  ⟨fun h => Functor.IsRelativeInjective.of_comp V h,
    fun h => Functor.IsRelativeInjective.comp_of_reflects V h hV⟩

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. If `V` is full and faithful, `P` is relative-injective for
`U ⋙ V` if and only if it is relative-injective for `U`. -/
theorem isRelativeInjective_comp_iff_of_full_faithful (U : D ⥤ C) (V : C ⥤ B)
    [V.Full] [V.Faithful] (P : D) :
    (U ⋙ V).IsRelativeInjective P ↔ U.IsRelativeInjective P := by
  rw [isRelativeInjective_iff_op_isRelativeProjective,
    isRelativeInjective_iff_op_isRelativeProjective]
  exact (isRelativeProjective_iff_of_natIso (Functor.opComp U V) (Opposite.op P)).trans
    (isRelativeProjective_comp_iff_of_full_faithful U.op V.op (Opposite.op P))

/-- For categories `D,C,B`, functor `U : D → C`, equivalence
`e : C ≌ B`, and `P : D`, relative injectivity for `U ⋙ e` is
equivalent to relative injectivity for `U`. -/
theorem isRelativeInjective_comp_equivalence_iff (U : D ⥤ C) (e : C ≌ B) (P : D) :
    (U ⋙ e.functor).IsRelativeInjective P ↔ U.IsRelativeInjective P :=
  isRelativeInjective_comp_iff_of_full_faithful U e.functor P

/-- For categories `D,C`, naturally isomorphic `U,U′ : D → C`,
and `P : D`, relative injectivity for `U` is equivalent to that
for `U′`. -/
theorem isRelativeInjective_iff_of_natIso {U U' : D ⥤ C} (e : U ≅ U') (P : D) :
    U.IsRelativeInjective P ↔ U'.IsRelativeInjective P := by
  rw [isRelativeInjective_iff_op_isRelativeProjective,
    isRelativeInjective_iff_op_isRelativeProjective]
  exact (isRelativeProjective_iff_of_natIso (NatIso.op e) (Opposite.op P)).symm

/-- Let `D,C,B` be categories, `U : D → C`, `V : C → B` functors,
and `P : D`. For `W : D → B` with `U ⋙ V ≅ W`, relative injectivity of
`P` for `W` implies relative injectivity for `U`. -/
theorem IsRelativeInjective.of_comp_natIso {U : D ⥤ C} (V : C ⥤ B)
    {W : D ⥤ B} (e : U ⋙ V ≅ W) {P : D} (hP : W.IsRelativeInjective P) :
    U.IsRelativeInjective P :=
  Functor.IsRelativeInjective.of_comp V
    ((isRelativeInjective_iff_of_natIso e P).mpr hP)

/-- For categories `D,C,B,A`, functors `U : D → C`, `V : C → B`,
`W : B → A`, and `P : D`, relative injectivity for `(U ⋙ V) ⋙ W`
is equivalent to that for `U ⋙ (V ⋙ W)`. -/
theorem isRelativeInjective_assoc_iff (U : D ⥤ C) (V : C ⥤ B) (W : B ⥤ A) (P : D) :
    ((U ⋙ V) ⋙ W).IsRelativeInjective P ↔ (U ⋙ (V ⋙ W)).IsRelativeInjective P :=
  isRelativeInjective_iff_of_natIso (Functor.associator U V W) P

end Functor
end CategoryTheory
