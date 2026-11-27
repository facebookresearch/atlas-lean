/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlagGroupoid
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagIso
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Grothendieck

/-!
# The Grothendieck category of flagged Quillen spans

Transport of explicit flag data along an isomorphism of raw Quillen spans is
strictly functorial.  It therefore defines a `Cat`-valued functor on the core
of the raw-span category.  Its Grothendieck construction records a raw span
together with a flag over it, and a span isomorphism together with the unique
compatible material flag comparison.

The projection from this total category to the raw-span core is an
equivalence: the fixed-span flag fibers are nonempty and have unique homs.
This is only representative-level, atomic coherence.  This file constructs
no quotient-valued composition, selected global flag, coherent all-interval
grid, simplicial comparison, realization, additivity, or Q/S equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem flagData_ext {X Y : C} {S : QuillenSpan X Y}
    (A B : QuillenSpanFlagData S)
    (hKernelObj : A.kernelObj = B.kernelObj)
    (hPushoutObj : A.pushoutObj = B.pushoutObj)
    (hQuotientObj : A.quotientObj = B.quotientObj)
    (hKernelι : HEq A.kernelι B.kernelι)
    (hQuotientπ : HEq A.quotientπ B.quotientπ)
    (hSourceToPushout : HEq A.sourceToPushout B.sourceToPushout)
    (hTargetToPushout : HEq A.targetToPushout B.targetToPushout)
    (hPushoutToQuotient : HEq A.pushoutToQuotient B.pushoutToQuotient) :
    A = B := by
  cases A
  cases B
  simp_all only [QuillenSpanFlagData.mk.injEq, true_and]

/-- Transport along the identity span isomorphism retains the original flag
packet. -/
theorem QuillenSpanFlagData.transport_refl
    {X Y : C} {S : QuillenSpan X Y}
    (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport (Iso.refl S) A = A := by
  apply flagData_ext
  · simp
  · simp
  · simp
  · change HEq (A.kernelι ≫ 𝟙 S.apex) A.kernelι
    rw [Category.comp_id]
  · simp
  · simp
  · simp
  · simp

/-- Direct transport along a composite span isomorphism equals successive
transport. -/
theorem QuillenSpanFlagData.transport_trans
    {X Y : C} {S S' S'' : QuillenSpan X Y}
    (e : S ≅ S') (e' : S' ≅ S'')
    (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport (e ≪≫ e') A =
      QuillenSpanFlagData.transport e'
        (QuillenSpanFlagData.transport e A) := by
  apply flagData_ext
  · simp
  · simp
  · simp
  · simp only [QuillenSpanFlagData.transport_kernelι,
      QuillenSpanFlagData.transport_kernelObj, Category.assoc]
    rfl
  · simp
  · simp
  · simp
  · simp

/-- Transport of flags along a span isomorphism, functorial on the genuine
fixed-span flag groupoids. -/
noncomputable def QuillenSpanFlagData.transportFunctor
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S') :
    QuillenSpanFlagData S ⥤ QuillenSpanFlagData S' where
  obj A := QuillenSpanFlagData.transport e A
  map {A B} f := by
    dsimp only [QuillenSpanFlagData.transport]
    exact
      { kernelHom := f.kernelHom
        pushoutHom := f.pushoutHom
        quotientHom := f.quotientHom
        kernelHom_kernelι := by
          rw [← Category.assoc, f.kernelHom_kernelι]
        sourceToPushout_naturality := f.sourceToPushout_naturality
        targetToPushout_naturality := f.targetToPushout_naturality
        quotientπ_quotientHom := f.quotientπ_quotientHom }
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem QuillenSpanFlagData.transportFunctor_obj
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (A : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transportFunctor e).obj A =
      QuillenSpanFlagData.transport e A := by
  simp [QuillenSpanFlagData.transportFunctor]

@[simp]
theorem QuillenSpanFlagData.transportFunctor_map_kernelHom
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).kernelHom =
      f.kernelHom := by
  simp [QuillenSpanFlagData.transportFunctor]
  rfl

@[simp]
theorem QuillenSpanFlagData.transportFunctor_map_pushoutHom
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).pushoutHom =
      f.pushoutHom := by
  simp [QuillenSpanFlagData.transportFunctor]
  rfl

@[simp]
theorem QuillenSpanFlagData.transportFunctor_map_quotientHom
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).quotientHom =
      f.quotientHom := by
  simp [QuillenSpanFlagData.transportFunctor]
  rfl

/-- The flag transport functor of a reflexive span isomorphism is the identity
functor. -/
theorem QuillenSpanFlagData.transportFunctor_refl
    {X Y : C} {S : QuillenSpan X Y} :
    QuillenSpanFlagData.transportFunctor (Iso.refl S) =
      Functor.id (QuillenSpanFlagData S) := by
  apply CategoryTheory.Functor.ext
    (fun A : QuillenSpanFlagData S => by
      rw [QuillenSpanFlagData.transportFunctor_obj]
      exact QuillenSpanFlagData.transport_refl A)

/-- The transport functor of a composite span isomorphism is the composite of
the two transport functors. -/
theorem QuillenSpanFlagData.transportFunctor_trans
    {X Y : C} {S S' S'' : QuillenSpan X Y}
    (e : S ≅ S') (e' : S' ≅ S'') :
    QuillenSpanFlagData.transportFunctor (e ≪≫ e') =
      QuillenSpanFlagData.transportFunctor e ⋙
        QuillenSpanFlagData.transportFunctor e' := by
  apply CategoryTheory.Functor.ext
    (fun A : QuillenSpanFlagData S => by
      simp only [QuillenSpanFlagData.transportFunctor_obj,
        Functor.comp_obj]
      exact QuillenSpanFlagData.transport_trans e e' A)

/-- The category of explicit flag choices varies functorially over the core
of raw Quillen-span representatives. -/
noncomputable def quillenSpanFlagFiberFunctor (X Y : C) :
    Core (QuillenSpan X Y) ⥤ Cat.{v, max u v} where
  obj S := Cat.of (QuillenSpanFlagData S.of)
  map e :=
    (QuillenSpanFlagData.transportFunctor e.iso).toCatHom
  map_id S :=
    congrArg Functor.toCatHom
      (QuillenSpanFlagData.transportFunctor_refl
        (S := S.of))
  map_comp e e' :=
    congrArg Functor.toCatHom
      (QuillenSpanFlagData.transportFunctor_trans e.iso e'.iso)

/-- Raw Quillen spans together with explicit flag choices, with morphisms
given by representative isomorphisms and compatible material flag maps. -/
abbrev QuillenSpanFlagTotal (X Y : C) :=
  Grothendieck (quillenSpanFlagFiberFunctor X Y)

/-- Forget a flagged representative to the underlying raw-span object in the
core. -/
def quillenSpanFlagProjection (X Y : C) :
    QuillenSpanFlagTotal X Y ⥤ Core (QuillenSpan X Y) :=
  Grothendieck.forget _

noncomputable instance quillenSpanFlagProjection_full (X Y : C) :
    (quillenSpanFlagProjection X Y).Full where
  map_surjective f := by
    refine ⟨{ base := f, fiber := QuillenSpanFlagHom.canonical _ _ }, rfl⟩

instance quillenSpanFlagProjection_faithful (X Y : C) :
    (quillenSpanFlagProjection X Y).Faithful where
  map_injective {A B} f g h := by
    apply Grothendieck.ext f g h
    dsimp [quillenSpanFlagFiberFunctor,
      QuillenSpanFlagData.transportFunctor]
    exact (instSubsingletonQuillenSpanFlagHom
      (S := B.base.of)
      (QuillenSpanFlagData.transport g.base.iso A.fiber)
      B.fiber).allEq _ _

noncomputable instance quillenSpanFlagProjection_essSurj (X Y : C) :
    (quillenSpanFlagProjection X Y).EssSurj where
  mem_essImage S := by
    obtain ⟨A⟩ := QuillenSpanFlagData.nonempty S.of
    exact ⟨⟨S, A⟩, ⟨Iso.refl S⟩⟩

noncomputable instance quillenSpanFlagProjection_isEquivalence (X Y : C) :
    (quillenSpanFlagProjection X Y).IsEquivalence where

/-- The total category of flagged representatives is equivalent to the core
of raw spans. -/
noncomputable def quillenSpanFlagTotalEquivalenceCore (X Y : C) :
    QuillenSpanFlagTotal X Y ≌ Core (QuillenSpan X Y) :=
  (quillenSpanFlagProjection X Y).asEquivalence

/-- Every morphism in the total category of flagged representatives is
invertible. -/
noncomputable instance quillenSpanFlagTotal_isGroupoid (X Y : C) :
    IsGroupoid (QuillenSpanFlagTotal X Y) :=
  isGroupoid_of_reflects_iso (quillenSpanFlagProjection X Y)

end AlgebraicKTheory
