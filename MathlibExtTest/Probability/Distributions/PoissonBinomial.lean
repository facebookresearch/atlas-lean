/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonBinomial
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for the Poisson-binomial law

Masses for zero and two trials, the exact one-trial tail identity, tail and binomial
monotonicity at concrete parameters, Le Cam's bound for one and two trials, and the junk
(negative) mass outside the probability domain.
-/

@[expose] public section

open Finset ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.PoissonBinomial

/-- With no trials, `S = 0` surely. -/
example : poissonBinomialPMF (Fin.elim0 : Fin 0 → ℝ) 0 = 1 := by
  simp [poissonBinomialPMF]

/-- One trial with probability `a`: `P(S = 1) = a`. -/
example (a : ℝ) : poissonBinomialPMF (Fin.cons a Fin.elim0 : Fin 1 → ℝ) 1 = a := by
  refine (poissonBinomialPMF_cons_succ a Fin.elim0 0).trans ?_
  rw [poissonBinomialPMF_eq_zero_of_lt _ (by norm_num : 0 < 0 + 1)]
  simp [poissonBinomialPMF]

/-- Two trials `(1/2, 1/4)`: `P(S = 1) = 1/2 · 3/4 + 1/2 · 1/4 = 1/2`. -/
example : poissonBinomialPMF (Fin.cons (1 / 2) (Fin.cons (1 / 4) Fin.elim0) : Fin 2 → ℝ) 1 =
    1 / 2 := by
  refine (poissonBinomialPMF_cons_succ _ _ 0).trans ?_
  rw [poissonBinomialPMF_cons_zero, poissonBinomialPMF_cons_succ,
    poissonBinomialPMF_eq_zero_of_lt _ (by norm_num : 0 < 0 + 1)]
  simp [poissonBinomialPMF]
  norm_num

/-- With equal probabilities the law is binomial: three fair trials, two successes. -/
example : poissonBinomialPMF (fun _ : Fin 3 => (1 / 2 : ℝ)) 2 = 3 / 8 := by
  rw [poissonBinomialPMF_const]
  norm_num [Nat.choose]

/-- Raising one background rate cannot lower the burden p-value. -/
example (k : ℕ) :
    poissonBinomialTail (![1 / 10, 1 / 5] : Fin 2 → ℝ) k ≤
      poissonBinomialTail (![1 / 10, 1 / 2] : Fin 2 → ℝ) k := by
  refine poissonBinomialTail_mono (fun i => ?_) (fun i => ?_) (fun i => ?_) k <;>
    fin_cases i <;> norm_num

/-- The binomial upper tail `P(Bin(5, p) ≥ 3)` is larger at `p = 1/2` than at `p = 1/4`. -/
example : ∑ j ∈ Icc 3 5, (Nat.choose 5 j : ℝ) * (1 / 4) ^ j * (1 - 1 / 4) ^ (5 - j) ≤
    ∑ j ∈ Icc 3 5, (Nat.choose 5 j : ℝ) * (1 / 2) ^ j * (1 - 1 / 2) ^ (5 - j) :=
  binomialTail_mono (by norm_num) (by norm_num) (by norm_num)

/-- Le Cam's bound for two trials with probabilities `1/10`: total error at most `4/100`. -/
example : ∑' j : ℕ, |poissonBinomialPMF (![1 / 10, 1 / 10] : Fin 2 → ℝ) j -
      Real.exp (-∑ i, (![1 / 10, 1 / 10] : Fin 2 → ℝ) i) *
        (∑ i, (![1 / 10, 1 / 10] : Fin 2 → ℝ) i) ^ j / (j.factorial : ℝ)| ≤
    2 * ∑ i, (![1 / 10, 1 / 10] : Fin 2 → ℝ) i ^ 2 :=
  (tsum_abs_poissonBinomialPMF_sub_poisson_le (fun i => by fin_cases i <;> norm_num)).2

/-- Junk value: outside `[0, 1]` the formula is not a probability (one "trial" with `p = 2`
gives `P(S = 0) = -1`); the probabilistic theorems assume `p i ∈ [0, 1]`. -/
example : poissonBinomialPMF (Fin.cons 2 Fin.elim0 : Fin 1 → ℝ) 0 = -1 := by
  rw [poissonBinomialPMF_cons_zero]
  simp [poissonBinomialPMF]
  norm_num

end MathlibExtTest.Probability.Distributions.PoissonBinomial
