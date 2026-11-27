/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.RischRecurrenceProdSubOneGeTwoMul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for under a multiplicative model `λ - 1` more than halves per degree

On two loci with first-degree ratios `(2, 3)` and second-degree ratios `(3 / 2, 2)`, the
multilocus ratios satisfy `2 (∏ λ₂ - 1) < ∏ λ₁ - 1`; on one locus the inequality is an equality.
-/

@[expose] public section

namespace DomainsTest.Biology.StatisticalGenetics.RischRecurrenceProdSubOneGeTwoMul

open Finset WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted

private noncomputable def lam₁₂ : Fin 2 → ℝ := fun i => if i = 0 then 2 else 3

private noncomputable def lam₂₂ : Fin 2 → ℝ := fun i => if i = 0 then 3 / 2 else 2

private lemma h₁₂ : ∀ i, 1 ≤ lam₁₂ i := by
  intro i
  fin_cases i <;> norm_num [lam₁₂]

private lemma hhalf₂ : ∀ i, lam₂₂ i - 1 = (lam₁₂ i - 1) / 2 := by
  intro i
  fin_cases i <;> norm_num [lam₁₂, lam₂₂]

example : ∏ i, lam₁₂ i = 6 := by
  rw [Fin.prod_univ_two]
  norm_num [lam₁₂]

example : ∏ i, lam₂₂ i = 3 := by
  rw [Fin.prod_univ_two]
  norm_num [lam₂₂]

example : 2 * (∏ i, lam₂₂ i - 1) ≤ ∏ i, lam₁₂ i - 1 :=
  (prod_sub_one_ge_two_mul lam₁₂ lam₂₂ h₁₂ hhalf₂).1

example : 2 * (∏ i, lam₂₂ i - 1) < ∏ i, lam₁₂ i - 1 :=
  (prod_sub_one_ge_two_mul lam₁₂ lam₂₂ h₁₂ hhalf₂).2
    ⟨0, 1, by decide, by norm_num [lam₁₂], by norm_num [lam₁₂]⟩

private noncomputable def lam₁₁ : Fin 1 → ℝ := fun _ => 2

private noncomputable def lam₂₁ : Fin 1 → ℝ := fun _ => 3 / 2

private lemma h₁₁ : ∀ i, 1 ≤ lam₁₁ i := by
  intro i
  norm_num [lam₁₁]

private lemma hhalf₁ : ∀ i, lam₂₁ i - 1 = (lam₁₁ i - 1) / 2 := by
  intro i
  norm_num [lam₁₁, lam₂₁]

example : 2 * (∏ i, lam₂₁ i - 1) = ∏ i, lam₁₁ i - 1 := le_antisymm
  (prod_sub_one_ge_two_mul lam₁₁ lam₂₁ h₁₁ hhalf₁).1
  (by rw [Fin.prod_univ_one, Fin.prod_univ_one]; norm_num [lam₁₁, lam₂₁])

end DomainsTest.Biology.StatisticalGenetics.RischRecurrenceProdSubOneGeTwoMul
