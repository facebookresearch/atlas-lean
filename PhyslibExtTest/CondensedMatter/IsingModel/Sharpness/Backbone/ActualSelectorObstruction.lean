/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorObstruction

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorObstruction`

* `shb_CurrentDynamicSelector_isEmpty_of_exists_ne` on `Fin 3` and
  `shb_no_CurrentDynamicSelector_bool`: no current dynamic selector exists on two or more vertices;
* `shb_singleEdge_edgeCopyMultiplicity_two` on the single edge `0 — 1` of `Fin 2`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorObstruction

open _root_.StatMech _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _


-- No current dynamic selector on `Fin 3`.
example : IsEmpty (shb_CurrentDynamicSelector (V := Fin 3)) :=
  shb_CurrentDynamicSelector_isEmpty_of_exists_ne ⟨0, 1, by decide⟩

-- No current dynamic selector on `Bool`.
example : ¬ Nonempty (shb_CurrentDynamicSelector (V := Bool)) :=
  not_nonempty_iff.mpr shb_no_CurrentDynamicSelector_bool

-- Edge-copy multiplicity two on a single edge at `β = J = 1`.
example :
    2 * (weight (shb_singleEdgeGraph (0 : Fin 2) 1) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph (0 : Fin 2) 1) (shb_singleEdgeConstantFlux 0 1 0)) *
        weight (shb_singleEdgeGraph (0 : Fin 2) 1) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph (0 : Fin 2) 1) (shb_singleEdgeConstantFlux 0 1 2))) =
      weight (shb_singleEdgeGraph (0 : Fin 2) 1) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph (0 : Fin 2) 1) (shb_singleEdgeConstantFlux 0 1 1)) *
        weight (shb_singleEdgeGraph (0 : Fin 2) 1) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph (0 : Fin 2) 1) (shb_singleEdgeConstantFlux 0 1 1)) :=
  shb_singleEdge_edgeCopyMultiplicity_two (x := (0 : Fin 2)) (y := 1) (by decide)

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorObstruction
