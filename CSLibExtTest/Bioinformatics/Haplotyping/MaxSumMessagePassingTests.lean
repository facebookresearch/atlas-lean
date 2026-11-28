/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.Haplotyping.MaxSumMessagePassing

/-!
# Tests for probabilistic haplotyping by max-sum message passing

`table3` is the `2 × 4` phasing matrix of Table 3 of the source (read `0` shows `0, 1, 0` at
sites `0`–`2`, read `1` shows `1, 0, 0` at sites `1`–`3`), with error probability `1/10`
everywhere. The tests check its spanning sets, coverage and cost, the number of allele flips,
and, through the main results, that the max-sum value at the root is `6 log (9/10)`: the
haplotype `0100` with both reads from it explains all six entries. Boundary cases: no reads and
no sites, and an error probability `0`, which makes a log-likelihood `⊥`.
-/

set_option autoImplicit false

namespace Cslib.Bioinformatics.Haplotyping.Tests

open Finset Cslib.Bioinformatics.Haplotyping.ReadData

private noncomputable def table3 : ReadData 2 4 where
  allele := ![![some false, some true, some false, none], ![none, some true, some false, some false]]
  err _ _ := 1 / 10
  err_nonneg _ _ := by norm_num
  err_lt_one _ _ := by norm_num
  covers := by decide

-- The reads spanning each site, empty past the last site.
example : table3.spanning 0 = {0} := by decide
example : table3.spanning 1 = {0, 1} := by decide
example : table3.spanning 2 = {0, 1} := by decide
example : table3.spanning 3 = {1} := by decide
example : table3.spanning 4 = ∅ := by decide

example : table3.coverage = 2 := by decide

-- The cost is `∑_j |R_j| 2^(|R_j| + 1) = 4 + 16 + 16 + 4`, below `m κ 2^(κ + 1) = 64`.
example : table3.maxSumTimed.time = 40 := by
  rw [maxSumTimed_time]
  decide

example : table3.maxSumTimed.time ≤ 4 * table3.coverage * 2 ^ (table3.coverage + 1) :=
  table3.maxSumTimed_time_le

private def h₀ : Fin 4 → Bool := ![false, true, false, false]

private def r₀ : Fin 2 → Bool := ![false, false]

-- Both reads from `h₀` need no flip; read `1` from its complement `1011` needs three.
example : table3.flips h₀ r₀ = 0 := by decide
example : table3.flips h₀ ![false, true] = 3 := by decide
example : table3.flips h₀ ![true, true] = 6 := by decide

private theorem isMEC_h₀ : table3.IsMEC h₀ r₀ := fun h' r' => by
  rw [show table3.flips h₀ r₀ = 0 by decide]
  exact Nat.zero_le _

private theorem err_eq (i : Fin 2) (j : Fin 4) : table3.err i j = 1 / 10 := rfl

-- With the constant error probability `1/10`, `h₀` and its reads maximize the likelihood.
private theorem isMax_h₀ (h' : Fin 4 → Bool) (r' : Fin 2 → Bool) :
    table3.logLikelihood h' r' ≤ table3.logLikelihood h₀ r₀ :=
  (table3.forall_logLikelihood_le_iff_isMEC (by norm_num) (by norm_num) err_eq h₀ _).2 isMEC_h₀ h' r'

private theorem logLikelihood_h₀ :
    table3.logLikelihood h₀ r₀ = ((6 * Real.log (9 / 10) : ℝ) : EReal) := by
  rw [table3.logLikelihood_eq_of_err_eq (by norm_num) (by norm_num) err_eq,
    show table3.flips h₀ r₀ = 0 by decide,
    show (∑ i, #(table3.covered i) : ℕ) = 6 by decide]
  norm_num

private theorem sup_logLikelihood :
    (univ : Finset ((Fin 4 → Bool) × (Fin 2 → Bool))).sup
      (fun p => table3.logLikelihood p.1 p.2) = ((6 * Real.log (9 / 10) : ℝ) : EReal) := by
  rw [← logLikelihood_h₀]
  exact le_antisymm (Finset.sup_le fun p _ => isMax_h₀ p.1 p.2)
    (le_sup (f := fun p : (Fin 4 → Bool) × (Fin 2 → Bool) => table3.logLikelihood p.1 p.2)
      (b := (h₀, r₀)) (mem_univ _))

-- The max-sum value at the root is the maximum log-likelihood, `6 log (9/10)`.
example : table3.message 4 ∅ = ((6 * Real.log (9 / 10) : ℝ) : EReal) := by
  rw [← table3.sup_logLikelihood_eq_message, sup_logLikelihood]

-- Backtracking through any stored argmaxes attains it, and stored argmaxes exist.
example (A : table3.ArgmaxTable) :
    table3.logLikelihood A.hap A.origin = ((6 * Real.log (9 / 10) : ℝ) : EReal) := by
  rw [table3.logLikelihood_backtrack, ← table3.sup_logLikelihood_eq_message, sup_logLikelihood]

example : Nonempty table3.ArgmaxTable := table3.nonempty_argmaxTable

-- Complementing the haplotype and the origins leaves the likelihood unchanged, and the prior
-- `P(h_0 = 0) = 1` gives the complemented solution joint probability `0`.
example : table3.likelihood ![true, false, true, true] ![true, true] =
    table3.likelihood h₀ r₀ :=
  table3.likelihood_not h₀ r₀

example : table3.jointProb ![true, false, true, true] ![true, true] = 0 := by
  rw [jointProb_eq]
  simp

-- The probabilities of the error model and the priors sum to one.
example (r b : Bool) : alleleProb (1 / 10) false r b + alleleProb (1 / 10) true r b = 1 :=
  alleleProb_false_add_true _ r b

example (j : Fin 4) : hapPrior j false + hapPrior j true = 1 := hapPrior_false_add_true j

/-! ## Boundary cases -/

private def empty : ReadData 0 0 where
  allele i _ := i.elim0
  err i _ := i.elim0
  err_nonneg i _ := i.elim0
  err_lt_one i _ := i.elim0
  covers i := i.elim0

-- With no sites, the root value `M_0 ≡ 0` is the log-likelihood `log 1` of the empty product.
example : empty.message 0 ∅ = 0 := rfl

example : (univ : Finset ((Fin 0 → Bool) × (Fin 0 → Bool))).sup
    (fun p => empty.logLikelihood p.1 p.2) = 0 := by
  rw [empty.sup_logLikelihood_eq_message]
  rfl

private noncomputable def exact : ReadData 1 1 where
  allele _ _ := some true
  err _ _ := 0
  err_nonneg _ _ := le_rfl
  err_lt_one _ _ := zero_lt_one
  covers _ := ⟨0, by simp⟩

-- An error probability `0` makes a mismatch impossible: its log-likelihood is `⊥`.
example : exact.logLikelihood ![false] ![false] = ⊥ := by
  simp [logLikelihood, likelihood, covered, obsProb, alleleProb, exact]

example : exact.logLikelihood ![true] ![false] = 0 := by
  simp [logLikelihood, likelihood, covered, obsProb, alleleProb, exact]

end Cslib.Bioinformatics.Haplotyping.Tests
