/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondProgram

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondProgram`

* `program_realizes_selectorSpec` on `Fin 4` (concrete inhabitant);
* `program_complete_functional`: completion is functional;
* `fin3_twoSegment_fiber_iff_orientation_and_scan` (the explicit three-vertex path computation)
  and `selectorSpec_nonempty_canonicalCertificate_iff_toggleExists` applied.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondProgram

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneTwoEdgeBondProgram

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The two-edge program realizes its specification on four vertices.
example : BackboneConcreteBondProgram.ProgramRealizes (program (V := Fin 4))
    selectorSpec.toPartialSelector :=
  program_realizes_selectorSpec

-- Completion is functional.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (w w' : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d w m) (h' : program.CompleteEvent d w' m) : w = w' :=
  program_complete_functional d m w w' h h'

-- The two-segment fibers on the three-vertex path.
example := fin3_twoSegment_fiber_iff_orientation_and_scan

-- Certificates exist exactly when the canonical toggle does.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :=
  selectorSpec_nonempty_canonicalCertificate_iff_toggleExists β J d s ss hs

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondProgram
