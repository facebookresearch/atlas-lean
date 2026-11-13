/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Sharpness.BackboneOrderedDeterminedCut
import Code.Sharpness.BackboneSupportLexK4Realization

open Finset

namespace StatMech.Sharpness





theorem shb_supportLex_not_local_to_acceptedPath :
    ∃ A B : Finset shbK4Edge,
      A ⊆ shbK4G ∧ B ⊆ shbK4G ∧
      shbK4Boundary A = {(0 : Fin 4), 3} ∧
      shbK4Boundary B = {(0 : Fin 4), 3} ∧
      (shbK4Edge.e03 ∈ A ↔ shbK4Edge.e03 ∈ B) ∧
      shbK4SelectsDirect03 A ∧ ¬shbK4SelectsDirect03 B := by
  decide



theorem shb_no_directEdge_local_characterization :
    ¬∃ q : Bool -> Bool,
      ∀ A : Finset shbK4Edge,
        A ⊆ shbK4G -> shbK4Boundary A = {(0 : Fin 4), 3} ->
          decide (shbK4SelectsDirect03 A) = q (decide (shbK4Edge.e03 ∈ A)) := by
  decide

end StatMech.Sharpness

