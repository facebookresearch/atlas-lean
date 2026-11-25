/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlag

/-!
# Transport of Quillen span flags along representative isomorphisms

An isomorphism of raw Quillen spans changes only the apex. Explicit six-cell
flag data transports by postcomposing the kernel inclusion with the apex
isomorphism, transporting the pushout square, and transporting the first
three admissible exact sequences. The lower-right sequence is unchanged.

This file provides one-way transport and its field computations only. It
constructs no transport identity/composition laws, equivalence of flag
types, quotient lift or descent, chosen flag, flag groupoid or functor,
Stage-3 or all-degree map, realization, equivalence, additivity, or Q/S
comparison.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Transport explicit flag data along an isomorphism of raw span
representatives. The kernel inclusion is postcomposed with the apex
isomorphism; all other stored objects and primitive maps are retained. -/
noncomputable def QuillenSpanFlagData.transport
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) : QuillenSpanFlagData S' := by
  let a : S.apex ≅ S'.apex := Span.SpanBicat.apexIso e
  let k' : D.kernelObj ⟶ S'.apex := D.kernelι ≫ a.hom
  have wLeft : k' ≫ S'.l = 0 := by
    dsimp only [k', a, Span.SpanBicat.apexIso]
    rw [Category.assoc, e.hom.hom_l, D.kernel_left_zero]
  have wRight : S'.r ≫ D.quotientπ = 0 := by
    rw [← e.inv.hom_r, Category.assoc, D.right_quotient_zero, comp_zero]
  have sq' : IsPushout S'.l S'.r D.sourceToPushout D.targetToPushout := by
    apply D.pushoutSquare.of_iso a (Iso.refl X) (Iso.refl Y)
      (Iso.refl D.pushoutObj)
    · simpa only [a, Span.SpanBicat.apexIso, Iso.refl_hom, Category.comp_id] using
        e.hom.hom_l.symm
    · simpa only [a, Span.SpanBicat.apexIso, Iso.refl_hom, Category.comp_id] using
        e.hom.hom_r.symm
    · simp
    · simp
  have wLowerLeft : (k' ≫ S'.r) ≫ D.targetToPushout = 0 := by
    calc
      (k' ≫ S'.r) ≫ D.targetToPushout =
          (D.kernelι ≫ S.r) ≫ D.targetToPushout := by
        simp only [k', a, Category.assoc, e.hom.hom_r]
      _ = 0 := D.kernel_targetToPushout_zero
  let leftOld : ShortComplex C :=
    ShortComplex.mk D.kernelι S.l D.kernel_left_zero
  let leftNew : ShortComplex C :=
    ShortComplex.mk k' S'.l wLeft
  have leftIso : leftOld ≅ leftNew :=
    ShortComplex.isoMk (Iso.refl D.kernelObj) a (Iso.refl X)
      (by simp [leftOld, leftNew, k'])
      (by
        simpa only [leftOld, leftNew, a, Span.SpanBicat.apexIso, Iso.refl_hom,
          Category.comp_id] using e.hom.hom_l)
  have hLeft : IsAdmissibleExact leftNew :=
    isAdmissibleExact_of_iso leftIso D.kernel_apex_source_exact
  let rightOld : ShortComplex C :=
    ShortComplex.mk S.r D.quotientπ D.right_quotient_zero
  let rightNew : ShortComplex C :=
    ShortComplex.mk S'.r D.quotientπ wRight
  have rightIso : rightOld ≅ rightNew :=
    ShortComplex.isoMk a (Iso.refl Y) (Iso.refl D.quotientObj)
      (by
        simpa only [rightOld, rightNew, a, Span.SpanBicat.apexIso, Iso.refl_hom,
          Category.comp_id] using e.hom.hom_r)
      (by simp [rightOld, rightNew])
  have hRight : IsAdmissibleExact rightNew :=
    isAdmissibleExact_of_iso rightIso D.apex_target_quotient_exact
  let lowerLeftOld : ShortComplex C :=
    ShortComplex.mk (D.kernelι ≫ S.r) D.targetToPushout
      D.kernel_targetToPushout_zero
  let lowerLeftNew : ShortComplex C :=
    ShortComplex.mk (k' ≫ S'.r) D.targetToPushout wLowerLeft
  have lowerLeftIso : lowerLeftOld ≅ lowerLeftNew :=
    ShortComplex.isoMk (Iso.refl D.kernelObj) (Iso.refl Y)
      (Iso.refl D.pushoutObj)
      (by
        simp only [lowerLeftOld, lowerLeftNew, k', a, Span.SpanBicat.apexIso,
          Iso.refl_hom, Category.id_comp, Category.comp_id, Category.assoc,
          e.hom.hom_r])
      (by simp [lowerLeftOld, lowerLeftNew])
  have hLowerLeft : IsAdmissibleExact lowerLeftNew :=
    isAdmissibleExact_of_iso lowerLeftIso
      D.kernel_target_pushout_exact
  exact
    { kernelObj := D.kernelObj
      pushoutObj := D.pushoutObj
      quotientObj := D.quotientObj
      kernelι := k'
      quotientπ := D.quotientπ
      sourceToPushout := D.sourceToPushout
      targetToPushout := D.targetToPushout
      pushoutToQuotient := D.pushoutToQuotient
      kernel_left_zero := wLeft
      right_quotient_zero := wRight
      pushoutSquare := sq'
      target_pushoutToQuotient := D.target_pushoutToQuotient
      source_pushoutToQuotient_zero :=
        D.source_pushoutToQuotient_zero
      kernel_targetToPushout_zero := wLowerLeft
      kernel_apex_source_exact := hLeft
      apex_target_quotient_exact := hRight
      kernel_target_pushout_exact := hLowerLeft
      source_pushout_quotient_exact :=
        D.source_pushout_quotient_exact }

@[simp]
theorem QuillenSpanFlagData.transport_kernelObj
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).kernelObj = D.kernelObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_pushoutObj
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).pushoutObj = D.pushoutObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_quotientObj
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).quotientObj = D.quotientObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_kernelι
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).kernelι =
      D.kernelι ≫ (Span.SpanBicat.apexIso e).hom :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_quotientπ
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).quotientπ = D.quotientπ :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_sourceToPushout
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).sourceToPushout =
      D.sourceToPushout :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_targetToPushout
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).targetToPushout =
      D.targetToPushout :=
  rfl

@[simp]
theorem QuillenSpanFlagData.transport_pushoutToQuotient
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S')
    (D : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport e D).pushoutToQuotient =
      D.pushoutToQuotient :=
  rfl

end AlgebraicKTheory
