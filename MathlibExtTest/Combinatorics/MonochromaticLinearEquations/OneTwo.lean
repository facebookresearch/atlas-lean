/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticLinearEquations.OneTwo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.isUncommonOverIntegers_one_two_neg_one_neg_two.Test

open Finset Filter

-- At the two-colour endpoint, get an actual count below one eighth on an interval
-- beyond any requested cutoff. The solution set includes repeated coordinates.
private def solutions (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (1 : ℤ) n).filter fun v => v 0 + 2 * v 1 = v 2 + 2 * v 3

example (N : ℕ) : ∃ n ≥ N, ∃ χ : ℤ → Fin 2,
    8 * ((solutions n).filter (fun v => ∀ i j, χ (v i) = χ (v j))).card < (solutions n).card := by
  obtain ⟨ε, hε, hf⟩ := isUncommonOverIntegers_one_two_neg_one_neg_two 2 (by decide)
  obtain ⟨n, hn, χ, hχ⟩ := frequently_atTop.mp hf N
  refine ⟨n, hn, χ, ?_⟩
  have eqn (v : Fin 4 → ℤ) :
      (∑ i, (![1, 2, -1, -2] : Fin 4 → ℤ) i * v i = 0) ↔ v 0 + 2 * v 1 = v 2 + 2 * v 3 := by
    simp [Fin.sum_univ_succ]
    omega
  simp only [eqn] at hχ
  have bound : (1 - ε) * (solutions n).card ≤ (solutions n).card := by
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)
  have h := hχ.trans_le bound
  norm_num at h
  simp only [solutions, filter_filter]
  exact_mod_cast h

example : IsUncommonOverIntegers (![1, 2, -1, -2] : Fin 4 → ℤ) 3 :=
  isUncommonOverIntegers_one_two_neg_one_neg_two 3 (by decide)

end MetaMathlibExt.isUncommonOverIntegers_one_two_neg_one_neg_two.Test
