/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.BernsteinABOTwoLocusConstraint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

/-!
# Tests for the two-locus constraint

At allele frequencies `a = 1 / 2` and `b = 1 / 3` the carrier probabilities are `3 / 4` and
`5 / 9`, the phenotype frequencies are `A = 1 / 3`, `B = 5 / 36` and `AB = 5 / 12`, and the
two-locus constraint `(A + AB)(B + AB) = AB` holds. The marginal identities
`A + AB = carrierProb a` and `B + AB = carrierProb b` hold for all allele frequencies.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted

namespace DomainsTest.Biology.StatisticalGenetics.BernsteinABOTwoLocusConstraint

/-- Carrier probabilities at `a = 1 / 2` and `b = 1 / 3`. -/
example : carrierProb (1 / 2 : ℝ) = 3 / 4 ∧ carrierProb (1 / 3 : ℝ) = 5 / 9 := by
  constructor <;> simp only [carrierProb] <;> norm_num

/-- Phenotype frequencies at `a = 1 / 2` and `b = 1 / 3`. -/
example : twoLocusA (1 / 2 : ℝ) (1 / 3 : ℝ) = 1 / 3 ∧
    twoLocusB (1 / 2 : ℝ) (1 / 3 : ℝ) = 5 / 36 ∧
    twoLocusAB (1 / 2 : ℝ) (1 / 3 : ℝ) = 5 / 12 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [twoLocusA, twoLocusB, twoLocusAB, carrierProb] <;> norm_num

/-- The two-locus constraint at `a = 1 / 2` and `b = 1 / 3`. -/
example : (twoLocusA (1 / 2 : ℝ) (1 / 3 : ℝ) + twoLocusAB (1 / 2 : ℝ) (1 / 3 : ℝ)) *
    (twoLocusB (1 / 2 : ℝ) (1 / 3 : ℝ) + twoLocusAB (1 / 2 : ℝ) (1 / 3 : ℝ)) =
    twoLocusAB (1 / 2 : ℝ) (1 / 3 : ℝ) :=
  twoLocus_constraint _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Under the two-locus model, `A + AB` is the carrier probability of `A`. -/
private lemma add_AB_eq_carrierLeft (a b : ℝ) :
    twoLocusA a b + twoLocusAB a b = carrierProb a := by
  simp only [twoLocusA, twoLocusAB]
  ring

/-- Under the two-locus model, `B + AB` is the carrier probability of `B`. -/
private lemma add_AB_eq_carrierRight (a b : ℝ) :
    twoLocusB a b + twoLocusAB a b = carrierProb b := by
  simp only [twoLocusB, twoLocusAB]
  ring

end DomainsTest.Biology.StatisticalGenetics.BernsteinABOTwoLocusConstraint
