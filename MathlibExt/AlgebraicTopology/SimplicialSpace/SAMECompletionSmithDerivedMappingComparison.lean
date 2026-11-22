/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- The genuine original-completion completeness and all-target unit-CSS inputs are compiled.
-- All comparison legs use the actual units and independently computed native replacements.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSmithDerivedSpanData
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerRealizationUnitCSSWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSmithCompleteComparison

/-!
# Weak derived mapping comparisons for the two completions

For arbitrary simplicial spaces, the actual diagonal-completion and Smith units form a Rezk weak
span, and the Smith-to-common comparison is Rezk weak. Their actions on the native derived
mapping ends give a natural zigzag whose four legs are realization weak equivalences, preserving
the independently chosen replacements.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite

namespace SimplicialSpace.RezkCompletionSmithComparison
open OriginalSmithCSS

/-- The common-source comparison is a real natural weak span of the two actual units. -/
theorem spans_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences (spanLeft.app W) ∧ rezkWeakEquivalences (spanRight.app W) :=
  ⟨RezkCompletionData.unit_rezkWeak W, spanRight_rezkWeak W⟩

theorem smithToCommon_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences (smithToCommon.app W) :=
  OriginalSmithCSS.replacement_map_rezkWeak (RezkCompletionData.unit.app W)
    (RezkCompletionData.unit_rezkWeak W)

/-- Both SAME-completion end legs are weak by their actual unit actions. -/
theorem completionSpans_weak (A B : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences ((completionPreSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences ((completionPostSpan.app (op A)).app B) :=
  ⟨derivedPrecomp_rezkWeak (RezkCompletionData.unit.app A) (RezkCompletionData.unit_rezkWeak A) B,
    derivedPostcomp_rezkWeak (RezkCompletionData.completion.obj A)
      (RezkCompletionData.unit.app B) (RezkCompletionData.unit_rezkWeak B)⟩

/-- A natural zigzag of genuine derived ends relates SAME and Smith completions.
Each of the four arrows retains its independently computed native Q and R. -/
theorem all_four_derived_span_legs_weak (A B : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences ((completionPreSpan.app (op A)).app B) ∧
    SSet.realizationWeakEquivalences ((completionPostSpan.app (op A)).app B) ∧
    SSet.realizationWeakEquivalences ((smithPreSpan.app (op A)).app B) ∧
    SSet.realizationWeakEquivalences ((smithPostSpan.app (op A)).app B) :=
  ⟨(completionSpans_weak A B).1, (completionSpans_weak A B).2,
    (smithSpans_weak A B).1, (smithSpans_weak A B).2⟩

end SimplicialSpace.RezkCompletionSmithComparison
