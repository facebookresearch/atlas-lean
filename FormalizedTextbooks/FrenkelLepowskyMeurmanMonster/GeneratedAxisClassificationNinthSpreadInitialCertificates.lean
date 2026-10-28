/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCandidates

/-! Nine specified whole frame systems in the original selected E8 section. These finite
intersection checks do not identify the Ninth-axis short-vector marking. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The nine original candidate indices extracted from the proposed section spread. -/
def generatedNinthSpreadInitialIndex : Fin 9 → Fin 270 :=
  ![2, 45, 71, 119, 140, 155, 168, 210, 257]

/-- The initial list has nine different genuine candidate indices. -/
theorem generatedNinth_spread_initial_index_injective :
    Function.Injective generatedNinthSpreadInitialIndex := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check only the nine specified systems and their sixteen coefficient labels.
/-- Different initial systems have no common nonzero root-coordinate label. -/
theorem generatedNinth_spread_initial_label_intersection :
    ∀ i j : Fin 9, i ≠ j → ∀ a b : Fin 4 → ZMod 2,
      generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadInitialIndex i) a =
        generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadInitialIndex j) b →
          a = 0 ∧ b = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
