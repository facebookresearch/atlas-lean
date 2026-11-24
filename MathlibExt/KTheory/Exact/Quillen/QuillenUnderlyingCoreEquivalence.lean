/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# The core of the Quillen Q-construction

Every isomorphism in `QuillenQ` between underlying objects is induced by a
unique isomorphism in the exact category.  Existence follows by choosing raw
spans for the isomorphism and its inverse: regular epi/mono cancellation makes
both legs of the forward span invertible.  Uniqueness follows directly from a
fixed-endpoint span isomorphism representing equality of the induced Quillen
morphisms.

Consequently the core groupoid of an exact category is equivalent to the core
groupoid of its Quillen Q-construction.  The fully faithful witness and the
equivalence are theorem-valued; this file installs no global fullness,
faithfulness, or equivalence instance and contains no Stage grid, nerve,
realization, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- An admissible epimorphism is regular because its admissible exact
sequence exhibits it as a cokernel. -/
private noncomputable def regularEpiOfAdmissibleEpi
    {X Y : C} {p : X ⟶ Y}
    (hp : admissibleEpisOf C IsAdmissibleExact p) :
    RegularEpi p := by
  exact Classical.choice (show Nonempty (RegularEpi p) from by
    obtain ⟨K, i, w, hE⟩ := hp
    refine ⟨
      { W := K
        left := i
        right := 0
        w := ?_
        isColimit := ?_ }⟩
    · simpa only [zero_comp] using w
    · exact isColimit_cokernelCofork_of_isAdmissibleExact hE)

/-- An admissible monomorphism is regular because its admissible exact
sequence exhibits it as a kernel. -/
private noncomputable def regularMonoOfAdmissibleMono
    {X Y : C} {i : X ⟶ Y}
    (hi : admissibleMonosOf C IsAdmissibleExact i) :
    RegularMono i := by
  exact Classical.choice (show Nonempty (RegularMono i) from by
    obtain ⟨Z, p, w, hE⟩ := hi
    refine ⟨
      { Z := Z
        left := p
        right := 0
        w := ?_
        isLimit := ?_ }⟩
    · simpa only [comp_zero] using w
    · exact isLimit_kernelFork_of_isAdmissibleExact hE)

/-- The first projection in span composition is an admissible epimorphism. -/
private theorem spanCompFst_admissible
    {X Y Z : C} (S : QuillenSpan X Y) (T : QuillenSpan Y Z) :
    admissibleEpisOf C IsAdmissibleExact
      (Span.SpanBicat.πₗ S T) := by
  let hpb : IsPullback (Span.SpanBicat.πₗ S T)
      (Span.SpanBicat.πᵣ S T) S.r T.l :=
    IsPullback.of_isLimit
      (c := Span.SpanBicat.compPullbackCone S T)
      (Span.SpanBicat.isLimitCompPullbackCone S T)
  exact MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
    (P := admissibleEpisOf C IsAdmissibleExact) hpb.flip T.wl

set_option linter.style.haveILetI false in
/-- If the left leg of a composite span is invertible, then the first
span's left leg is invertible. -/
private theorem isIso_left_of_isIso_spanComp_left
    {X Y Z : C} (S : QuillenSpan X Y) (T : QuillenSpan Y Z)
    (hcomp : IsIso (Span.comp S T).l) : IsIso S.l := by
  letI : IsIso (Span.comp S T).l := hcomp
  have hfac : (Span.comp S T).l =
      Span.SpanBicat.πₗ S T ≫ S.l := Span.SpanBicat.comp_l S T
  have hmonoComp : Mono (Span.SpanBicat.πₗ S T ≫ S.l) :=
    hfac ▸ inferInstance
  letI : Mono (Span.SpanBicat.πₗ S T ≫ S.l) := hmonoComp
  have hisoComp : IsIso (Span.SpanBicat.πₗ S T ≫ S.l) :=
    hfac ▸ hcomp
  letI : IsIso (Span.SpanBicat.πₗ S T ≫ S.l) := hisoComp
  letI : Mono (Span.SpanBicat.πₗ S T) :=
    mono_of_mono (Span.SpanBicat.πₗ S T) S.l
  have hfst : IsIso (Span.SpanBicat.πₗ S T) :=
    isIso_of_regularEpi_of_mono _
      (regularEpiOfAdmissibleEpi (spanCompFst_admissible S T))
  letI : IsIso (Span.SpanBicat.πₗ S T) := hfst
  exact IsIso.of_isIso_comp_left (Span.SpanBicat.πₗ S T) S.l

set_option linter.style.haveILetI false in
/-- If the right leg of a composite span is invertible, then the second
span's right leg is invertible. -/
private theorem isIso_right_of_isIso_spanComp_right
    {X Y Z : C} (S : QuillenSpan X Y) (T : QuillenSpan Y Z)
    (hcomp : IsIso (Span.comp S T).r) : IsIso T.r := by
  letI : IsIso (Span.comp S T).r := hcomp
  have hfac : (Span.comp S T).r =
      Span.SpanBicat.πᵣ S T ≫ T.r := Span.SpanBicat.comp_r S T
  have hepiComp : Epi (Span.SpanBicat.πᵣ S T ≫ T.r) :=
    hfac ▸ inferInstance
  letI : Epi (Span.SpanBicat.πᵣ S T ≫ T.r) := hepiComp
  letI : Epi T.r := epi_of_epi (Span.SpanBicat.πᵣ S T) T.r
  exact isIso_of_regularMono_of_epi T.r
    (regularMonoOfAdmissibleMono T.wr)

/-- If a span composite is isomorphic to the identity span, its outer left
and right legs are isomorphisms. -/
private theorem spanOuterLegs_isIso_of_comp_iso_id
    {X Y : C} (S : QuillenSpan X Y) (T : QuillenSpan Y X)
    (e : Span.comp S T ≅ (Span.id (c := X) : QuillenSpan X X)) :
    IsIso S.l ∧ IsIso T.r := by
  let a := Span.SpanBicat.apexIso e
  have hl : (Span.comp S T).l = a.hom := by
    change (Span.comp S T).l = e.hom.hom
    simpa using e.hom.hom_l.symm
  have hr : (Span.comp S T).r = a.hom := by
    change (Span.comp S T).r = e.hom.hom
    simpa using e.hom.hom_r.symm
  have hli : IsIso (Span.comp S T).l := hl ▸ inferInstance
  have hri : IsIso (Span.comp S T).r := hr ▸ inferInstance
  exact ⟨isIso_left_of_isIso_spanComp_left S T hli,
    isIso_right_of_isIso_spanComp_right S T hri⟩

set_option linter.style.haveILetI false in
/-- A Q-isomorphism between underlying objects admits an underlying
isomorphism whose induced Q-isomorphism is the supplied one. -/
theorem quillenQ_iso_lifts_to_underlying_iso_eq
    {X Y : C} (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) :
    Nonempty { f : X ≅ Y // QuillenQ.underlyingIso f = e } := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep e.hom
  obtain ⟨T, hT⟩ := Quotient.exists_rep e.inv
  change QuillenQ.mkHom S = e.hom at hS
  change QuillenQ.mkHom T = e.inv at hT
  have hST : QuillenQ.mkHom (Span.comp S T) =
      QuillenQ.mkHom (Span.id (c := X) : QuillenSpan X X) := by
    calc
      QuillenQ.mkHom (Span.comp S T) =
          quillenComp (QuillenQ.mkHom S) (QuillenQ.mkHom T) :=
        (mkHom_comp S T).symm
      _ = quillenComp e.hom e.inv := congrArg₂ quillenComp hS hT
      _ = (𝟙 (⟨X⟩ : QuillenQ C) :
          (⟨X⟩ : QuillenQ C) ⟶ ⟨X⟩) := e.hom_inv_id
      _ = QuillenQ.mkHom (Span.id (c := X) : QuillenSpan X X) :=
        (mkHom_id (⟨X⟩ : QuillenQ C)).symm
  have hTS : QuillenQ.mkHom (Span.comp T S) =
      QuillenQ.mkHom (Span.id (c := Y) : QuillenSpan Y Y) := by
    calc
      QuillenQ.mkHom (Span.comp T S) =
          quillenComp (QuillenQ.mkHom T) (QuillenQ.mkHom S) :=
        (mkHom_comp T S).symm
      _ = quillenComp e.inv e.hom := congrArg₂ quillenComp hT hS
      _ = (𝟙 (⟨Y⟩ : QuillenQ C) :
          (⟨Y⟩ : QuillenQ C) ⟶ ⟨Y⟩) := e.inv_hom_id
      _ = QuillenQ.mkHom (Span.id (c := Y) : QuillenSpan Y Y) :=
        (mkHom_id (⟨Y⟩ : QuillenQ C)).symm
  obtain ⟨eST⟩ := QuillenQ.mkHom_eq_iff.mp hST
  obtain ⟨eTS⟩ := QuillenQ.mkHom_eq_iff.mp hTS
  obtain ⟨hSl, _⟩ := spanOuterLegs_isIso_of_comp_iso_id S T eST
  obtain ⟨_, hSr⟩ := spanOuterLegs_isIso_of_comp_iso_id T S eTS
  letI : IsIso S.l := hSl
  letI : IsIso S.r := hSr
  let f : X ≅ Y := (asIso S.l).symm.trans (asIso S.r)
  refine ⟨⟨f, ?_⟩⟩
  apply Iso.ext
  rw [QuillenQ.underlyingIso_hom, ← hS]
  symm
  apply QuillenQ.mkHom_sound
  refine Span.mkIso (asIso S.l) ?_ ?_
  · simp
  · change S.l ≫ f.hom = S.r
    simp [f]

/-- An isomorphism in `QuillenQ` between underlying objects lifts, merely
existentially, to an isomorphism in the exact category. -/
theorem quillenQ_iso_lifts_to_underlying_iso
    {X Y : C} (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) :
    Nonempty (X ≅ Y) := by
  obtain ⟨f, _⟩ := quillenQ_iso_lifts_to_underlying_iso_eq e
  exact ⟨f⟩

/-- The hom component of the underlying-isomorphism lift is injective. -/
theorem QuillenQ.underlyingIso_hom_injective
    {X Y : C} {e f : X ≅ Y}
    (h : (QuillenQ.underlyingIso e).hom =
      (QuillenQ.underlyingIso f).hom) :
    e = f := by
  rw [QuillenQ.underlyingIso_hom, QuillenQ.underlyingIso_hom] at h
  obtain ⟨i⟩ := QuillenQ.mkHom_eq_iff.mp h
  apply Iso.ext
  have hApex : i.hom.hom = 𝟙 X := by
    simpa using i.hom.hom_l
  have hRight := i.hom.hom_r
  change i.hom.hom ≫ f.hom = e.hom at hRight
  rw [hApex, Category.id_comp] at hRight
  exact hRight.symm

/-- The underlying-isomorphism lift into `QuillenQ` is injective. -/
theorem QuillenQ.underlyingIso_injective {X Y : C} :
    Function.Injective
      (fun e : X ≅ Y => QuillenQ.underlyingIso e) := by
  intro e f h
  exact QuillenQ.underlyingIso_hom_injective (congrArg Iso.hom h)

namespace QuillenQ

/-- The functor from the core of an exact category to the core of its
Quillen Q-construction. -/
noncomputable def underlyingCoreFunctor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    Core C ⥤ Core (QuillenQ C) where
  obj X := ⟨⟨X.of⟩⟩
  map f := ⟨QuillenQ.underlyingIso f.iso⟩
  map_id X := by
    apply Core.hom_ext
    exact congrArg Iso.hom (QuillenQ.underlyingIso_refl X.of)
  map_comp f g := by
    apply Core.hom_ext
    exact congrArg Iso.hom (QuillenQ.underlyingIso_trans f.iso g.iso)

@[simp]
theorem underlyingCoreFunctor_obj
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (X : Core C) :
    (underlyingCoreFunctor C).obj X = ⟨(⟨X.of⟩ : QuillenQ C)⟩ :=
  rfl

@[simp]
theorem underlyingCoreFunctor_map_iso
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {X Y : Core C} (f : X ⟶ Y) :
    ((underlyingCoreFunctor C).map f).iso =
      QuillenQ.underlyingIso f.iso :=
  rfl

/-- A selected exact-category core morphism lifting a core morphism in
`QuillenQ`. -/
private noncomputable def underlyingCorePreimage
    {X Y : Core C}
    (f : (underlyingCoreFunctor C).obj X ⟶
      (underlyingCoreFunctor C).obj Y) :
    X ⟶ Y :=
  ⟨(Classical.choice
    (quillenQ_iso_lifts_to_underlying_iso_eq f.iso)).1⟩

/-- The selected core preimage induces exactly the supplied Q-isomorphism. -/
private theorem underlyingCorePreimage_spec
    {X Y : Core C}
    (f : (underlyingCoreFunctor C).obj X ⟶
      (underlyingCoreFunctor C).obj Y) :
    QuillenQ.underlyingIso (underlyingCorePreimage f).iso = f.iso :=
  (Classical.choice
    (quillenQ_iso_lifts_to_underlying_iso_eq f.iso)).2

/-- The underlying-core functor is fully faithful.  This is a theorem-valued
witness and is not installed as a global instance. -/
@[no_expose]
noncomputable def underlyingCoreFunctor_fullyFaithful
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (underlyingCoreFunctor C).FullyFaithful where
  preimage := underlyingCorePreimage
  map_preimage f := by
    apply Core.hom_ext
    exact congrArg Iso.hom (underlyingCorePreimage_spec f)
  preimage_map f := by
    apply Core.hom_ext
    have hIso : (underlyingCorePreimage
        ((underlyingCoreFunctor C).map f)).iso = f.iso :=
      QuillenQ.underlyingIso_injective (by
        simpa using underlyingCorePreimage_spec
          ((underlyingCoreFunctor C).map f))
    exact congrArg Iso.hom hIso

/-- The fully faithful preimage induces exactly the supplied Q-isomorphism. -/
theorem underlyingCoreFunctor_fullyFaithful_preimage_iso
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {X Y : Core C}
    (f : (underlyingCoreFunctor C).obj X ⟶
      (underlyingCoreFunctor C).obj Y) :
    QuillenQ.underlyingIso
        (((underlyingCoreFunctor_fullyFaithful C).preimage f).iso) =
      f.iso := by
  have h := congrArg (fun g => g.iso)
    ((underlyingCoreFunctor_fullyFaithful C).map_preimage f)
  change QuillenQ.underlyingIso
      (((underlyingCoreFunctor_fullyFaithful C).preimage f).iso) =
    f.iso at h
  exact h

/-- The core of an exact category is equivalent to the core of its Quillen
Q-construction. -/
noncomputable def underlyingCoreEquivalence
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    Core C ≌ Core (QuillenQ C) := by
  let F := underlyingCoreFunctor C
  let hff : F.FullyFaithful := underlyingCoreFunctor_fullyFaithful C
  let hEss : F.EssSurj := ⟨by
    rintro ⟨⟨X⟩⟩
    exact ⟨⟨X⟩, ⟨Iso.refl _⟩⟩⟩
  letI : F.Faithful := hff.faithful
  letI : F.Full := hff.full
  letI : F.EssSurj := hEss
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact F.asEquivalence

@[simp]
theorem underlyingCoreEquivalence_functor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (underlyingCoreEquivalence C).functor = underlyingCoreFunctor C :=
  rfl

end QuillenQ

end AlgebraicKTheory

end
