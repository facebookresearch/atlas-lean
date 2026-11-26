/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationCutAdmissible

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationCutAdmissible`

* `shb_generatedExplorationFiberMass_cutResummation` on `Fin 2` at `β = J = 1`: the generated
  fiber mass satisfies the cut resummation identities (so the predicate is satisfiable);
* `shb_LocalSelectorFiberCutResummation_iff_eq_generated`: it is the only such fiber mass;
* `shb_cutPredicateMass_factor` applied under admissibility.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationCutAdmissible

open _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The generated fiber mass satisfies the cut resummation identities.
example : shb_LocalSelectorFiberCutResummation (V := Fin 2) 1 (fun _ => 1)
    (shb_generatedExplorationFiberMass 1 fun _ => 1) :=
  shb_generatedExplorationFiberMass_cutResummation 1 _

-- Any fiber mass satisfying them is the generated one.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (f : shb_ExplorationFiberMass V) (h : shb_LocalSelectorFiberCutResummation β J f) :
    f = shb_generatedExplorationFiberMass β J :=
  (shb_LocalSelectorFiberCutResummation_iff_eq_generated β J f).mp h

-- Admissible cut predicates factorize the mass.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (P : G.edgeFinset → Prop) [DecidablePred P] (full : (G.edgeFinset → ℕ) → Prop)
    [DecidablePred full] (left : ({ e // P e } → ℕ) → Prop) [DecidablePred left]
    (right : ({ e // ¬ P e } → ℕ) → Prop) [DecidablePred right]
    (h : shb_CutPredicateAdmissible G P full left right) :
    shb_cutFullPredicateMass G β J full =
      shb_cutLeftPredicateMass G β J P left * shb_cutRightPredicateMass G β J P right :=
  shb_cutPredicateMass_factor G β J P full left right h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationCutAdmissible
