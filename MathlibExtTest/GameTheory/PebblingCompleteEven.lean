/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PebblingCompleteEven

open MetaMathlibExt

private theorem thresholdSix : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 6)) 1) 13 :=
  isLeast_pebblingAllNTotals_complete_even (n := 6) (hn := by decide) (heven := ⟨3, rfl⟩)

private theorem thresholdEight : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 8)) 1) 15 :=
  isLeast_pebblingAllNTotals_complete_even (n := 8) (hn := by decide) (heven := ⟨4, rfl⟩)

-- At the first two admissible widths, the threshold is attained and the previous total is not.
example : 13 ∈ pebblingAllNTotals (⊤ : SimpleGraph (Fin 6)) 1 := thresholdSix.1

example : 12 ∉ pebblingAllNTotals (⊤ : SimpleGraph (Fin 6)) 1 :=
  fun h => (by decide : ¬ 13 ≤ 12) (thresholdSix.2 h)

example : 15 ∈ pebblingAllNTotals (⊤ : SimpleGraph (Fin 8)) 1 := thresholdEight.1

example : 14 ∉ pebblingAllNTotals (⊤ : SimpleGraph (Fin 8)) 1 :=
  fun h => (by decide : ¬ 15 ≤ 14) (thresholdEight.2 h)
