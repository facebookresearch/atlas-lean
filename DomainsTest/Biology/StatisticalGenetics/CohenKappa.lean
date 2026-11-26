/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.CohenKappa
import Mathlib.Tactic.NormNum

/-!
# Tests for Cohen's kappa of independent raters

The uniform `2 × 2` table is the product of its margins, so its kappa is `0`; and on any
independent table the observed agreement equals the chance agreement.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

namespace DomainsTest.Biology.StatisticalGenetics.CohenKappa

/-- The uniform `2 × 2` table is a probability table. -/
private lemma isTable_uniform_two : IsTable (fun _ _ : Fin 2 => (1 / 4 : ℝ)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · show (0 : ℝ) ≤ 1 / 4
    norm_num
  · simp only [Fin.sum_univ_two]
    norm_num

/-- The uniform `2 × 2` table is the product of its margins. -/
private lemma independence_two (i j : Fin 2) :
    (fun _ _ : Fin 2 => (1 / 4 : ℝ)) i j =
      rowMargin (fun _ _ : Fin 2 => (1 / 4 : ℝ)) i *
        colMargin (fun _ _ : Fin 2 => (1 / 4 : ℝ)) j := by
  simp only [rowMargin, colMargin, Fin.sum_univ_two]
  norm_num

/-- The uniform `2 × 2` table has chance agreement below `1`. -/
private lemma chance_two : chance (fun _ _ : Fin 2 => (1 / 4 : ℝ)) < 1 := by
  simp only [chance, rowMargin, colMargin, Fin.sum_univ_two]
  norm_num

/-- The uniform `2 × 2` table has kappa `0`. -/
example : kappa (fun _ _ : Fin 2 => (1 / 4 : ℝ)) = 0 :=
  kappa_eq_zero_of_independent _ isTable_uniform_two independence_two chance_two

/-- On an independent table, observed agreement equals chance agreement. -/
example {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hind : ∀ i j, P i j = rowMargin P i * colMargin P j) :
    observed P = chance P := by
  simp only [observed, chance, hind]

end DomainsTest.Biology.StatisticalGenetics.CohenKappa
