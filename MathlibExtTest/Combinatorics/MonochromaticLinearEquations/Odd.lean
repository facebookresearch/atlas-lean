/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticLinearEquations.Odd
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.isUncommonOverIntegers_of_odd.Test

open Finset Filter

private def schur : Fin 3 → ℤ := ![1, 1, -1]

private def schurSolutions (n : ℕ) : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (1 : ℤ) n).filter fun x => x 0 + x 1 = x 2

-- At the three-colour endpoint the fraction is strictly below one ninth in arbitrarily large boxes.
example (N : ℕ) : ∃ n ≥ N, ∃ χ : ℤ → Fin 3,
    9 * ((schurSolutions n).filter (fun x => ∀ i j, χ (x i) = χ (x j))).card <
      (schurSolutions n).card := by
  obtain ⟨ε, hε, hf⟩ := isUncommonOverIntegers_of_odd 1 (by decide) schur (by decide)
    ⟨2, 0, by decide, by decide⟩ 3 (by decide)
  obtain ⟨n, hn, χ, hχ⟩ := frequently_atTop.mp hf N
  refine ⟨n, hn, χ, ?_⟩
  have eqn (x : Fin 3 → ℤ) : (∑ i, schur i * x i = 0) ↔ x 0 + x 1 = x 2 := by
    simp [schur, Fin.sum_univ_succ]
    omega
  simp only [eqn] at hχ
  have bound : (1 - ε) * (schurSolutions n).card ≤ (schurSolutions n).card :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (sub_le_self _ hε.le)
  have h := hχ.trans_le bound
  norm_num at h
  simp only [schurSolutions, filter_filter]
  exact_mod_cast h

-- A nonprimitive equation with a negative pivot; every constant tuple is a solution.
example : IsUncommonOverIntegers (![-8, 2, 2, 2, 2] : Fin 5 → ℤ) 4 :=
  isUncommonOverIntegers_of_odd 2 (by decide) _ (by decide) ⟨0, 1, by decide, by decide⟩ 4
    (by decide)

end MetaMathlibExt.isUncommonOverIntegers_of_odd.Test
