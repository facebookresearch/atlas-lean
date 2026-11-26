/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialEdgeCopySwitching

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialEdgeCopySwitching`

* `shb_vacuumPartialSelector_admissible_iff` and `shb_oneStepPartialSelector_admissible_iff`:
  admissibility of the two concrete partial selectors;
* `rawPairFiberMass_tsum_eq_mul` (unconditional) for any pair of predicates;
* `rawFiberMass_eq_of_labeledToggle` applied under its toggle hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.PartialEdgeCopySwitching

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneLabeledSwitching
open _root_.StatMech.Sharpness.BackboneLabeledSwitching

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Admissibility for the vacuum and one-step selectors.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) :
    (shb_vacuumPartialSelector.Admissible d m ↔ sources d.graph (ofEdgeFun d.graph m) = ∅) ∧
      (shb_oneStepPartialSelector.Admissible d m ↔
        sources d.graph (ofEdgeFun d.graph m) = ∅ ∨ ∃ s, shb_oneStepCandidate d m s) :=
  ⟨shb_vacuumPartialSelector_admissible_iff d m, shb_oneStepPartialSelector_admissible_iff d m⟩

-- Product of two restricted masses as a sum of raw pair fiber masses, on `K₂`.
example (Q R : ((⊤ : SimpleGraph (Fin 2)).edgeFinset → ℕ) → Prop) [DecidablePred Q]
    [DecidablePred R] :=
  rawPairFiberMass_tsum_eq_mul (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) Q R

-- Labeled toggles preserve raw fiber masses.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (m : G.edgeFinset → ℕ) (A C : Finset V) (P : Finset (FluxEdgeCopy.Copy G m))
    (hP : RandomCurrent.sources (FluxEdgeCopy.endsM G m) P = C) (Q R : (G.edgeFinset → ℕ) → Prop)
    [DecidablePred Q] [DecidablePred R]
    (h : ∀ S, Q (FluxEdgeCopy.profileFlux G m S) ↔
      R (FluxEdgeCopy.profileFlux G m (symmDiff S P))) :
    rawFiberMass G β J m A Q = rawFiberMass G β J m (symmDiff A C) R :=
  rawFiberMass_eq_of_labeledToggle G β J m A C P hP Q R h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.PartialEdgeCopySwitching
