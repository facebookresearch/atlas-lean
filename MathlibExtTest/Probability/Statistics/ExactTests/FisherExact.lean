/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.FisherExact

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.ExactTests
open scoped unitInterval

namespace MathlibExtTest.Probability.Statistics.ExactTests.FisherExact

/-- Non-vacuity: the coordinates of `Bin(n₁, p) ⊗ Bin(n₂, p)` are independent binomial counts
with a common `p`, so the hypotheses of Fisher's theorem are satisfiable. -/
theorem witness (n₁ n₂ : ℕ) (p : I) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) Bin(n₁, p) (Bin(n₁, p).prod Bin(n₂, p)) ∧
      HasLaw (fun ω : ℕ × ℕ => ω.2) Bin(n₂, p) (Bin(n₁, p).prod Bin(n₂, p)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2) (Bin(n₁, p).prod Bin(n₂, p)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- On the witness, the conditional law of the first cell given the margin is
hypergeometric. With `p = 1/2`, `n₁ = 2`, `n₂ = 3` and margin `t = 2`:
`P(X = 1 | X + Y = 2) = C(2,1) C(3,1) / C(5,2) = 3/5`. -/
example :
    ((Bin(2, ⟨1 / 2, by norm_num, by norm_num⟩).prod Bin(3, ⟨1 / 2, by norm_num, by norm_num⟩))[|
      {ω : ℕ × ℕ | ω.1 + ω.2 = 2}]).real {ω | ω.1 = 1} = 3 / 5 := by
  have h := witness 2 3 ⟨1 / 2, by norm_num, by norm_num⟩
  rw [cond_measureReal_eq_hypergeometricReal (X := fun ω : ℕ × ℕ => ω.1)
    (Y := fun ω : ℕ × ℕ => ω.2) (by change (0 : ℝ) < 1 / 2; norm_num)
    (by change (1 / 2 : ℝ) < 1; norm_num) measurable_fst measurable_snd h.1 h.2.1 h.2.2
    (by norm_num) 1]
  norm_num [hypergeometricReal, Nat.choose]

/-- The sum of the two cells is binomial on the witness. -/
example (n₁ n₂ t : ℕ) (p : I) :
    (Bin(n₁, p).prod Bin(n₂, p)).real {ω : ℕ × ℕ | ω.1 + ω.2 = t} = Bin(n₁ + n₂, p).real {t} :=
  have h := witness n₁ n₂ p
  measureReal_add_eq_binomial measurable_fst measurable_snd h.1 h.2.1 h.2.2 t

/-- Non-vacuity of the Fisher validity theorem: on the witness with `n₁ = 2`, `n₂ = 3`,
`p = 1/2` and margin `t = 2`, the upper Fisher p-value of the first cell is valid given the
margin. -/
example : MathlibExt.Probability.Statistics.MultipleTesting.IsValidPValue
    ((Bin(2, ⟨1 / 2, by norm_num, by norm_num⟩).prod Bin(3, ⟨1 / 2, by norm_num, by norm_num⟩))[|
      {ω : ℕ × ℕ | ω.1 + ω.2 = 2}])
    (fisherUpperPValue 2 3 2 (by norm_num) fun ω : ℕ × ℕ => ω.1) := by
  have h := witness 2 3 ⟨1 / 2, by norm_num, by norm_num⟩
  exact isValidPValue_fisherUpper_cond (X := fun ω : ℕ × ℕ => ω.1) (Y := fun ω : ℕ × ℕ => ω.2)
    (by change (0 : ℝ) < 1 / 2; norm_num) (by change (1 / 2 : ℝ) < 1; norm_num)
    measurable_fst measurable_snd h.1 h.2.1 h.2.2 (by norm_num)

/-- Numeric value: with `n₁ = 2`, `n₂ = 3`, margin `t = 2` and observed cell `X = 1`, the upper
Fisher p-value is `P(X ≥ 1) = (C(2,1) C(3,1) + C(2,2) C(3,0)) / C(5,2) = 7/10`. -/
example : fisherUpperPValue 2 3 2 (by norm_num) (fun ω : ℕ × ℕ => ω.1) (1, 1) = 7 / 10 := by
  rw [fisherUpperPValue_eq_sum]
  norm_num [hypergeometricReal, Nat.choose, Finset.sum_Icc_succ_top]

/-- Boundary: with `n₁ = n₂ = 2` and margin `t = 2`, the largest possible cell is `X = 2`, and
its p-value is the single atom `C(2,2) C(2,0) / C(4,2) = 1/6`. -/
example : fisherUpperPValue 2 2 2 (by norm_num) (fun ω : ℕ × ℕ => ω.1) (2, 0) = 1 / 6 := by
  rw [fisherUpperPValue_eq_sum]
  norm_num [hypergeometricReal, Nat.choose]

end MathlibExtTest.Probability.Statistics.ExactTests.FisherExact
