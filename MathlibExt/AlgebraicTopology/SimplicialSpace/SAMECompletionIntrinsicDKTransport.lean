/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionIntrinsicDK
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKSaturation

/-!
# Completion preserves and reflects intrinsic Dwyer–Kan equivalences

The designated completion functor preserves and reflects intrinsic Dwyer–Kan equivalences
between Segal spaces. Naturality of its actual units and the two-out-of-six property compare
each original map with its completed map.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace SimplicialSpace.RezkCompletionData

/-- The actual completion preserves and reflects intrinsic DK on original
RF-Segal maps. Both unit comparisons and both target Segal proofs are constructed. -/
theorem completion_map_intrinsicDK_iff {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    IntrinsicDK.isEquivalence (completion.map f)
      (RezkCompletionAllVertex.sameCompletion_segal W hW)
      (RezkCompletionAllVertex.sameCompletion_segal V hV) ↔
        IntrinsicDK.isEquivalence f hW hV := by
  let hCW := RezkCompletionAllVertex.sameCompletion_segal W hW
  let hCV := RezkCompletionAllVertex.sameCompletion_segal V hV
  let uW : W ⟶ completion.obj W := unit.app W
  let uV : V ⟶ completion.obj V := unit.app V
  have huW : IntrinsicDK.isEquivalence uW hW hCW := unit_intrinsicDK W hW
  have huV : IntrinsicDK.isEquivalence uV hV hCV := unit_intrinsicDK V hV
  have hn : f ≫ uV = uW ≫ completion.map f := unit_naturality f
  constructor
  · intro hf
    have hfu : IntrinsicDK.isEquivalence (f ≫ uV) hW hCV := by
      rw [hn]
      exact IntrinsicDK.comp uW (completion.map f) hW hCW hCV huW hf
    have hui : IntrinsicDK.isEquivalence (uV ≫ 𝟙 (completion.obj V)) hV hCV := by
      simpa only [Category.comp_id] using huV
    exact (IntrinsicDK.two_out_of_six f uV (𝟙 (completion.obj V))
      hW hV hCV hCV hfu hui).1
  · intro hf
    have huc : IntrinsicDK.isEquivalence (uW ≫ completion.map f) hW hCV := by
      rw [← hn]
      exact IntrinsicDK.comp f uV hW hV hCV hf huV
    have hiu : IntrinsicDK.isEquivalence (𝟙 W ≫ uW) hW hCW := by
      simpa only [Category.id_comp] using huW
    exact (IntrinsicDK.two_out_of_six (𝟙 W) uW (completion.map f)
      hW hW hCW hCV hiu huc).2.2.1

end SimplicialSpace.RezkCompletionData
