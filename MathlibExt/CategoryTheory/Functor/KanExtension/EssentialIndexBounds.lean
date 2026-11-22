/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Functor.SmallIndex
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Original comma bounds from actual small-index equivalences

The source index is transported through its supplied complete equivalence.
The target index's supplied equivalence gives local smallness of its ORIGINAL
Hom sets. Both original comma categories are therefore essentially small in
the working universe. Their objects and morphisms retain the actual index
functor and the original target object. No comma bound or Kan existence is
an input.

These are the original essentially small index bridges for *Higher Topos
Theory*, author version of April 9, 2017, Proposition A.2.8.7, printed page
833 (PDF page 851).
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uE vE uC vC

namespace CategoryTheory.Functor.EssentialIndexData

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C]
  (sD : EssentialIndexData.{w} D C) (sE : EssentialIndexData.{w} E C)

/-- The full actual source equivalence compares the right comma category to
the original one without changing its target object or index functor. -/
def structuredArrowEquivalence (u : D ⥤ E) (e : E) :
    StructuredArrow e (sD.equivalence.inverse ⋙ u) ≌ StructuredArrow e u :=
  (StructuredArrow.pre e sD.equivalence.inverse u).asEquivalence

/-- The same complete source equivalence retains every original left comma map. -/
def costructuredArrowEquivalence (u : D ⥤ E) (e : E) :
    CostructuredArrow (sD.equivalence.inverse ⋙ u) e ≌ CostructuredArrow u e :=
  (CostructuredArrow.pre sD.equivalence.inverse u e).asEquivalence

include sD sE

/-- The actual target equivalence bounds the original right-comma labels on
the supplied small source model. -/
theorem structuredArrow_small (u : D ⥤ E) (e : E) :
    Small.{w} (StructuredArrow e (sD.equivalence.inverse ⋙ u)) := by
  let : LocallySmall.{w} E := sE.locallySmallIndex
  infer_instance

/-- The actual target Hom bound also bounds the unchanged left-comma labels. -/
theorem costructuredArrow_small (u : D ⥤ E) (e : E) :
    Small.{w} (CostructuredArrow (sD.equivalence.inverse ⋙ u) e) := by
  let : LocallySmall.{w} E := sE.locallySmallIndex
  infer_instance

/-- The original right comma category is essentially small through the supplied
full source equivalence; the original source presentation need not be small. -/
theorem structuredArrow_essentiallySmall (u : D ⥤ E) (e : E) :
    EssentiallySmall.{w} (StructuredArrow e u) := by
  let : Small.{w} (StructuredArrow e (sD.equivalence.inverse ⋙ u)) :=
    structuredArrow_small sD sE u e
  let : LocallySmall.{w} sD.index := locallySmall_self sD.index
  have h : EssentiallySmall.{w} (StructuredArrow e (sD.equivalence.inverse ⋙ u)) :=
    essentiallySmall_of_small_of_locallySmall _
  exact (essentiallySmall_congr (structuredArrowEquivalence sD u e)).mp h

/-- The original left comma category has the same genuine source bounds. -/
theorem costructuredArrow_essentiallySmall (u : D ⥤ E) (e : E) :
    EssentiallySmall.{w} (CostructuredArrow u e) := by
  let : Small.{w} (CostructuredArrow (sD.equivalence.inverse ⋙ u) e) :=
    costructuredArrow_small sD sE u e
  let : LocallySmall.{w} sD.index := locallySmall_self sD.index
  have h : EssentiallySmall.{w} (CostructuredArrow (sD.equivalence.inverse ⋙ u) e) :=
    essentiallySmall_of_small_of_locallySmall _
  exact (essentiallySmall_congr (costructuredArrowEquivalence sD u e)).mp h

/-- Both original comma categories are outputs at every original target object. -/
theorem comma_essentiallySmall (u : D ⥤ E) (e : E) :
    EssentiallySmall.{w} (StructuredArrow e u) ∧
      EssentiallySmall.{w} (CostructuredArrow u e) :=
  ⟨structuredArrow_essentiallySmall sD sE u e,
    costructuredArrow_essentiallySmall sD sE u e⟩

end CategoryTheory.Functor.EssentialIndexData
