/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffTerminalOneMorphic

namespace MetaMathlibExt.WythoffTerminalOneMorphicTest

private abbrev subst : Fin 5 → List (Fin 5) := ![[0, 1], [2], [3, 4], [3, 1], [2]]

private abbrev code : Fin 5 → Bool := fun c => decide (c ∈ ({0, 1, 3} : Finset (Fin 5)))

-- The limit exists and codes the first mex pair (2, 4) at indices 0 and 2.
example : ∃ w : ℕ → Fin 5, IsOmegaLimit subst 0 w ∧ code (w 0) = true ∧ code (w 2) = false := by
  obtain ⟨⟨w, hw⟩, hc⟩ := wythoffTerminal_one_morphic 0
  exact ⟨w, hw, by simpa only [wythoffMexA_zero, wythoffMexB_zero] using hc w hw⟩

-- Every limit codes the second mex pair (3, 6) at indices 1 and 4.
example (w : ℕ → Fin 5) (hw : IsOmegaLimit subst 0 w) :
    code (w 1) = true ∧ code (w 4) = false := by
  have ha : wythoffMexA 1 1 = 3 := wythoffMexA_one 1 (by decide)
  have hb : wythoffMexB 1 1 = 6 := by rw [wythoffMexB, ha]
  simpa only [ha, hb] using (wythoffTerminal_one_morphic 1).2 w hw

end MetaMathlibExt.WythoffTerminalOneMorphicTest
