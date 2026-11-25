/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Boundary tests for Kendall's tau and Spearman's footrule: the swap on
two items (upper-bound equality `F = 2K`) and the reversal on three
items (maximal Kendall tau).
-/

module

public import MathlibExt.Combinatorics.Enumerative.RankDistances

@[expose] public section

open scoped BigOperators
open Finset MetaMathlibExt

namespace MetaMathlibExt.Test.RankDistances

/-- The transposition of the two items of `Fin 2` has Kendall tau `1`
against the identity ranking: the single pair is discordant. -/
theorem kendallTau_swap_fin_two :
    kendallTau (Equiv.swap (0 : Fin 2) 1) 1 = 1 := by
  decide

/-- The transposition of the two items of `Fin 2` has footrule `2`
against the identity: each item moves by one rank. Hence the
Diaconis-Graham upper bound `F ≤ 2K` is tight. -/
theorem spearmanFootrule_swap_fin_two :
    spearmanFootrule (Equiv.swap (0 : Fin 2) 1) 1 = 2 := by
  decide

/-- The reversal permutation on `Fin 3` (`0 ↦ 2`, `1 ↦ 1`, `2 ↦ 0`) has
Kendall tau `3` against the identity: every pair is discordant. The
reversal is written as the swap of `0` and `2`. -/
theorem kendallTau_reverse_fin_three :
    kendallTau (Equiv.swap (0 : Fin 3) 2) 1 = 3 := by
  decide

/-- The reversal on `Fin 3` has footrule `4` against the identity:
displacements `2 + 0 + 2`. -/
theorem spearmanFootrule_reverse_fin_three :
    spearmanFootrule (Equiv.swap (0 : Fin 3) 2) 1 = 4 := by
  decide

/-- Non-vacuity: distinct rankings can have positive footrule with
Kendall tau strictly between the two bounds (`3 < 4 < 6` above), and
equal rankings give `0` for both distances on a nonempty type. -/
theorem distances_fin_three_bounds :
    kendallTau (Equiv.swap (0 : Fin 3) 2) 1 = 3 ∧
    spearmanFootrule (Equiv.swap (0 : Fin 3) 2) 1 = 4 ∧
    kendallTau (Equiv.swap (0 : Fin 3) 2) 1 <
      spearmanFootrule (Equiv.swap (0 : Fin 3) 2) 1 ∧
    spearmanFootrule (Equiv.swap (0 : Fin 3) 2) 1 <
      2 * kendallTau (Equiv.swap (0 : Fin 3) 2) 1 ∧
    kendallTau (1 : Equiv.Perm (Fin 3)) 1 = 0 ∧
    spearmanFootrule (1 : Equiv.Perm (Fin 3)) 1 = 0 := by
  rw [kendallTau_reverse_fin_three, spearmanFootrule_reverse_fin_three]
  exact ⟨rfl, rfl, by decide, by decide, kendallTau_self 1,
    spearmanFootrule_self 1⟩

end MetaMathlibExt.Test.RankDistances
