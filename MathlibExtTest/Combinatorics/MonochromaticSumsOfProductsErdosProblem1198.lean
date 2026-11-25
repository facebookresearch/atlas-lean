/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted

open Finset

-- Check the refutation against the expanded statement.
example :
    ¬ (∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
      ∀ (k : ℕ) (S : Fin k → Finset ℕ), 0 < k → (∀ j, (S j).Nonempty) →
        Pairwise (fun j j' => Disjoint (S j) (S j')) → ¬ (k = 1 ∧ ∀ j, (S j).card = 1) →
          c (∑ j, ∏ i ∈ S j, a i) = col) :=
  monochromaticSumsOfProducts_refuted

-- A single two-factor product is allowed, as is its sum with a disjoint singleton.
example (h : monochromaticSumsOfProducts) (c : ℕ → Fin 2) :
    ∃ (a : ℕ → ℕ) (col : Fin 2), StrictMono a ∧ 0 < a 0 ∧
      c (a 0 * a 1) = col ∧ c (a 0 * a 1 + a 2) = col := by
  obtain ⟨a, ha, hpos, col, hc⟩ := h c
  refine ⟨a, col, ha, hpos, ?_, ?_⟩
  · let S : Fin 1 → Finset ℕ := fun _ ↦ {0, 1}
    have hd : Pairwise (fun j j' ↦ Disjoint (S j) (S j')) := by
      intro j j' hne
      exact (hne (Subsingleton.elim _ _)).elim
    simpa [S, Finset.prod_pair] using hc 1 S (by decide) (by simp [S]) hd (by decide)
  · let S : Fin 2 → Finset ℕ := ![{0, 1}, {2}]
    have hne (j : Fin 2) : (S j).Nonempty := by fin_cases j <;> simp [S]
    have hd : Pairwise (fun j j' ↦ Disjoint (S j) (S j')) := by
      intro j j' hj
      fin_cases j <;> fin_cases j' <;> simp_all [S]
    simpa [S, Fin.sum_univ_two, Finset.prod_pair] using hc 2 S (by decide) hne hd (by decide)

end MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted
