/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Domains.Economics.Finance.GlostenMilgrom

open MeasureTheory
open scoped unitInterval
open MathlibExt.Probability.Finance.GlostenMilgrom

private noncomputable def prior : I := ⟨1 / 3, by constructor <;> norm_num⟩
private noncomputable def informed : I := ⟨1 / 2, by constructor <;> norm_num⟩
private def emptyHistory : Fin 0 → Bool := Fin.elim0

private theorem snoc_empty (d : Bool) : Fin.snoc emptyHistory d = fun _ ↦ d := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ Fin.elim0 j) i
  simp only [Fin.snoc_last]

private theorem quote_buy : quote prior informed 2 12 emptyHistory true = 8 := by
  rw [quote, snoc_empty]
  norm_num [prefixPrice, posterior, jointWeight, likelihood, prior, informed]

-- With no informed traders both quotes agree with the prior mean, even after two trades.
example :
    let h := Fin.snoc (Fin.snoc emptyHistory true) false
    quote prior 0 2 12 h false = 16 / 3 ∧ quote prior 0 2 12 h true = 16 / 3 := by
  norm_num [quote, prefixPrice, posterior, jointWeight, likelihood, prior,
    Fin.prod_univ_castSucc, emptyHistory]

-- The asymmetric prior gives different buy and sell posterior odds and exact quotes.
example : quote prior informed 2 12 emptyHistory false = 24 / 7 ∧
    prefixPrice prior informed 2 12 emptyHistory = 16 / 3 ∧
    quote prior informed 2 12 emptyHistory true = 8 := by
  refine ⟨?_, ?_, quote_buy⟩
  · rw [quote, snoc_empty]
    norm_num [prefixPrice, posterior, jointWeight, likelihood, prior, informed]
  · norm_num [prefixPrice, posterior, jointWeight, prior]

-- At the ask, an inventory of four units falls to three and cash rises by the quote.
-- The expected change in terminal marked wealth, conditional on the first buy, is zero.
example :
    (∫ ω, (8 + 3 * value 2 12 ω) - 4 * value 2 12 ω
      ∂ProbabilityTheory.cond (law prior informed) (atom (Fin.snoc emptyHistory true))) = 0 := by
  obtain ⟨_, _, _, hPrefix, _⟩ := sequential_quotes_and_martingale prior informed 2 12
    (by norm_num) (by norm_num [prior]) (by norm_num [prior]) (by norm_num [informed])
  obtain ⟨_, _, _, _, _, _, hQuotes, _⟩ := hPrefix 0 emptyHistory
  obtain ⟨_, _, _, hProfit⟩ := hQuotes true
  have heq (ω : Sample) : (8 + 3 * value 2 12 ω) - 4 * value 2 12 ω = 8 - value 2 12 ω := by
    ring
  rw [show (fun ω ↦ (8 + 3 * value 2 12 ω) - 4 * value 2 12 ω) =
      (fun ω ↦ 8 - value 2 12 ω) from funext heq]
  exact (hProfit 8).2 quote_buy.symm

example : Martingale (transactionPrice prior 0 2 12) orderFiltration (law prior 0) := by
  obtain ⟨_, _, _, _, _, _, _, martingale⟩ := sequential_quotes_and_martingale prior 0 2 12
    (by norm_num) (by norm_num [prior]) (by norm_num [prior]) (by norm_num)
  exact martingale
