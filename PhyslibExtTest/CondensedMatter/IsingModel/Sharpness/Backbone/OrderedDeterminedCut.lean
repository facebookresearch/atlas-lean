/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCut

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCut`

* `firstAccepted_iff_of_agreeOn_determinedCut` on the one-bond ordered tests along `[1, 2, 3]`
  for two configurations that differ only at bond `4` (outside every determined cut);
* `selects_iff_of_agreeOn_traceCut` for agreeing configurations;
* `rawFiberMass_eq_of_determinedCutToggle` applied under its cut hypotheses.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCut

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.shb_OrderedLocalTests
open _root_.StatMech.Sharpness.shb_OrderedLocalExploration
open _root_.StatMech.Sharpness.BackboneDeterminedCutSwitching
open _root_.StatMech.Sharpness.BackboneDeterminedCutSwitching

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

/-- Ordered one-bond tests along `[1, 2, 3]`. -/
def T123 : shb_OrderedLocalTests ℕ ℕ where
  order := [1, 2, 3]
  order_nodup := by decide
  test ω b := ω b
  exposure b := {b}
  test_local _ _ _ h := h _ rfl

-- Two configurations differing only at bond `4` accept the same first bond.
example : List.find? (T123.test fun b => decide (b = 2)) T123.order = some 2 ↔
    List.find? (T123.test fun b => decide (b = 2 ∨ b = 4)) T123.order = some 2 :=
  T123.firstAccepted_iff_of_agreeOn_determinedCut _ _ 2 fun b hb => by
    obtain ⟨e, he, hbe⟩ := hb
    change b ∈ ({e} : Set ℕ) at hbe
    rw [Set.mem_singleton_iff] at hbe
    subst hbe
    have : b = 1 ∨ b = 2 := by
      simpa [T123, shb_OrderedLocalTests.testedThrough] using he
    rcases this with rfl | rfl <;> decide

-- Selection only depends on the trace cut.
example {D E B : Type*} [DecidableEq E] (X : shb_OrderedLocalExploration D E B) (ω : B → Bool)
    (d : D) (word : List E) : X.Selects ω d word ↔ X.Selects ω d word :=
  X.selects_iff_of_agreeOn_traceCut ω ω d word fun _ _ => rfl

-- Toggling path copies inside a cut preserves raw fiber masses of events outside it.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (m : G.edgeFinset → ℕ) (A C : Finset V) (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m)) (hP : RandomCurrent.sources (FluxEdgeCopy.endsM G m) P = C)
    (hcut : SupportedInCut G m cut P) (Q : (G.edgeFinset → ℕ) → Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m cut Q) :
    BackboneLabeledSwitching.rawFiberMass G β J m A Q =
      BackboneLabeledSwitching.rawFiberMass G β J m (symmDiff A C) Q :=
  rawFiberMass_eq_of_determinedCutToggle G β J m A C cut P hP hcut Q hQ

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCut
