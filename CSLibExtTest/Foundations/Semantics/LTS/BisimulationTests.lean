/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.Bisimulation

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS.BisimulationTests

/-- The complete two-state system: every state steps to every state under
the unit label, so any two states are bisimilar (via the total relation). -/
def completeLTS : LTS Bool Unit := ⟨fun _ _ _ => True⟩

theorem complete_bisimilar : HomBisimilarity completeLTS false true := by
  refine ⟨fun _ _ => True, trivial, ?_⟩
  intro s₁ s₂ _ μ
  exact ⟨fun s' _ => ⟨s', trivial, trivial⟩, fun s' _ => ⟨s', trivial, trivial⟩⟩

/-- Bisimilar states enable the same labels. -/
example (μ : Unit) :
    completeLTS.HasOutLabel false μ ↔ completeLTS.HasOutLabel true μ :=
  complete_bisimilar.hasOutLabel_iff μ

/-- Bisimilar states have equal ready sets. -/
example : completeLTS.outgoingLabels false = completeLTS.outgoingLabels true :=
  complete_bisimilar.outgoingLabels_eq

/-- Multistep transitions transfer across bisimilarity: the two-step run
from `false` is matched from `true`, ending in bisimilar states. -/
example : ∃ t, completeLTS.MTr true [(), ()] t ∧
    HomBisimilarity completeLTS false t :=
  complete_bisimilar.mtr
    (MTr.stepL (s1 := false) (s2 := false) trivial
      (MTr.stepL (s1 := false) trivial MTr.refl))

end Cslib.LTS.BisimulationTests
