/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitEdges

/-! Explicit original source-letter words reach every vertex of both checked parent trees. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual initial candidate of each explicit parent tree. -/
def generatedAxisE8FrameSystemOrbitRoot (k : Fin 2) : Fin 270 := if k = 0 then 0 else 14

/-- An explicit word in original signs, selected permutations and Xi for each tree vertex. -/
def generatedAxisE8FrameSystemOrbitWord (k : Fin 2) (i : Fin 135) : List (Fin 18) :=
  if _hi : i = 0 then [] else
    generatedAxisE8FrameSystemOrbitGenerator k i ::
      generatedAxisE8FrameSystemOrbitWord k (generatedAxisE8FrameSystemOrbitParent k i)
termination_by i.val
decreasing_by exact generatedAxisE8FrameSystemOrbit_parent_lt k i _hi

/-- The explicit source word sends the actual root system to the displayed actual candidate. -/
theorem generatedAxisE8FrameSystemOrbit_word_action (k : Fin 2) (i : Fin 135) :
    ((generatedAxisE8FrameSystemOrbitWord k i).map generatedAxisE8FrameSystemOrbitLetter).prod •
      generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitRoot k) =
      generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      rw [generatedAxisE8FrameSystemOrbitWord]
      simp only [↓reduceDIte, List.map_nil, List.prod_nil, one_smul,
        generatedAxisE8FrameSystemOrbit_root, generatedAxisE8FrameSystemOrbitRoot]
    · rw [generatedAxisE8FrameSystemOrbitWord, dite_eq_right hi, List.map_cons, List.prod_cons,
        mul_smul, ih _ (generatedAxisE8FrameSystemOrbit_parent_lt k i hi)]
      exact generatedAxisE8FrameSystemOrbit_edge_actual k i

/-- Each of the270 displayed candidates has a genuine source-word witness in its tree-root orbit. -/
theorem generatedAxisE8FrameSystemOrbit_word_mem (k : Fin 2) (i : Fin 135) :
    generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k i) ∈
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitRoot k)) :=
  ⟨_, generatedAxisE8FrameSystemOrbit_word_action k i⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
