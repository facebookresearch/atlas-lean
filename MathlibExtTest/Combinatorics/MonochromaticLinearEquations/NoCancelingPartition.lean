/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticLinearEquations.NoCancelingPartition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.isUncommonOverIntegers_of_not_hasCancelingPartition.Test

open Finset Filter

-- Both signs of the same magnitude occur, but three positive copies cannot share one partner.
private def coeff : Fin 4 → ℤ := ![2, 2, 2, -2]

private lemma unpaired : ¬ HasCancelingPartition coeff := by
  rintro ⟨σ, -, -, h⟩
  have only_neg (j : Fin 4) (hj : 2 + coeff j = 0) : j = 3 := by
    fin_cases j <;> norm_num [coeff] at *
  have he : σ 0 = σ 1 := (only_neg _ (h 0)).trans (only_neg _ (h 1)).symm
  exact (by decide : (0 : Fin 4) ≠ 1) (σ.injective he)

private lemma uncommon (r : ℕ) (hr : 2 ≤ r) : IsUncommonOverIntegers coeff r :=
  isUncommonOverIntegers_of_not_hasCancelingPartition 2 (by decide) coeff (by decide)
    ⟨3, 0, by decide, by decide⟩ unpaired r hr

-- At the two-colour endpoint the proportion is strictly below one eighth for x + y + z = w.
private def triples (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (1 : ℤ) n).filter fun x => x 0 + x 1 + x 2 = x 3

example (N : ℕ) : ∃ n ≥ N, ∃ χ : ℤ → Fin 2,
    8 * ((triples n).filter (fun x => ∀ i j, χ (x i) = χ (x j))).card < (triples n).card := by
  obtain ⟨ε, hε, hf⟩ := uncommon 2 (by decide)
  obtain ⟨n, hn, χ, hχ⟩ := frequently_atTop.mp hf N
  refine ⟨n, hn, χ, ?_⟩
  have eqn (x : Fin 4 → ℤ) : (∑ i, coeff i * x i = 0) ↔ x 0 + x 1 + x 2 = x 3 := by
    simp [coeff, Fin.sum_univ_succ]
    omega
  simp only [eqn] at hχ
  have bound : (1 - ε) * (triples n).card ≤ (triples n).card :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (sub_le_self _ hε.le)
  have h := hχ.trans_le bound
  norm_num at h
  simp only [triples, filter_filter]
  exact_mod_cast h

example : IsUncommonOverIntegers coeff 3 := uncommon 3 (by decide)

end MetaMathlibExt.isUncommonOverIntegers_of_not_hasCancelingPartition.Test
