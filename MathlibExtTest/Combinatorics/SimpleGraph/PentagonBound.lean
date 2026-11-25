/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PentagonBound

open SimpleGraph MathlibExt.GraphTheory.ErdosProblem24Wanted

-- At zero vertices the upper bound is zero.
example (G : SimpleGraph (Fin 0)) : G.copyCount (cycleGraph 5) = 0 :=
  Nat.eq_zero_of_le_zero (conjecture_holds 0 G (G.cliqueFree_of_card_lt (by decide)))

-- A single pentagon attains the bound, including the factor for unlabelled copies.
example : (cycleGraph 5).copyCount (cycleGraph 5) = 1 := by
  have h : (cycleGraph 5).CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp hs
    have ht : ∀ i j k : Fin 5, (cycleGraph 5).Adj i j → (cycleGraph 5).Adj i k →
        ¬(cycleGraph 5).Adj j k := by decide
    exact ht a b c hab hac hbc
  apply Nat.le_antisymm (conjecture_holds 1 _ h)
  exact (copyCount_pos.mpr IsContained.rfl : 0 < (cycleGraph 5).copyCount (cycleGraph 5))
