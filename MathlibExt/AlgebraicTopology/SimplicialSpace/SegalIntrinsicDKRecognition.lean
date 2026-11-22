/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerRealizationUnitCSSWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionIntrinsicDKTransport
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreDerivedImageCompleteness
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalIntrinsicDKRecognition

/-!
# Intrinsic Dwyer–Kan recognition for arbitrary original RF Segal maps

The same original completion unit is weak on every complete-target test.
Its literal naturality square transports the specified CSS weak class.
The actual constructed completion is complete and its unit is intrinsically
Dwyer–Kan, so complete-endpoint recognition applies to the same original map.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.RezkCompletionData

/-- The same completion preserves and reflects the original all-complete-target weak class. -/
theorem completion_map_rezkWeak_iff {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    rezkWeakEquivalences (completion.map f) ↔ rezkWeakEquivalences f := by
  have huW := unit_rezkWeak W
  have huV := unit_rezkWeak V
  have hn : f ≫ unit.app V = unit.app W ≫ completion.map f := unit_naturality f
  constructor
  · intro h
    have hc := rezkWeakEquivalences.comp_mem (unit.app W) (completion.map f) huW h
    rw [← hn] at hc
    exact (rezkWeakEquivalences.postcomp_iff f (unit.app V) huV).mp hc
  · intro h
    have hc := rezkWeakEquivalences.comp_mem f (unit.app V) h huV
    rw [hn] at hc
    exact (rezkWeakEquivalences.precomp_iff (unit.app W) (completion.map f) huW).mp hc

end SimplicialSpace.RezkCompletionData

namespace SimplicialSpace

/-- The specified CSS weak class is exactly intrinsic DK for every original map of RF Segal
spaces. -/
theorem segalMap_cssWeak_iff_intrinsicDK {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    rezkWeakEquivalences f ↔ IntrinsicDK.isEquivalence f hW hV := by
  have hCW := RezkCompletionCoreDiagonal.sameCompletion_completeSegal_from_derived_image_fibres W hW
  have hCV := RezkCompletionCoreDiagonal.sameCompletion_completeSegal_from_derived_image_fibres V hV
  have hc : rezkWeakEquivalences (RezkCompletionData.completion.map f) ↔
      IntrinsicDK.isEquivalence (RezkCompletionData.completion.map f)
        (RezkCompletionAllVertex.sameCompletion_segal W hW)
        (RezkCompletionAllVertex.sameCompletion_segal V hV) :=
    completeSegalMap_cssWeak_iff_intrinsicDK (RezkCompletionData.completion.map f) hCW hCV
  exact (RezkCompletionData.completion_map_rezkWeak_iff f).symm.trans
    (hc.trans (RezkCompletionData.completion_map_intrinsicDK_iff f hW hV))

/-- Recognition retains every original mapping fibre and the original homotopy-category map. -/
theorem segalMap_cssWeak_iff_mappingWeak_and_essSurj {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    rezkWeakEquivalences f ↔
      (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
        SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl)) ∧
      (SegalHomotopy.map f hW hV).EssSurj := by
  simpa only [IntrinsicDK.isEquivalence] using segalMap_cssWeak_iff_intrinsicDK f hW hV

end SimplicialSpace
