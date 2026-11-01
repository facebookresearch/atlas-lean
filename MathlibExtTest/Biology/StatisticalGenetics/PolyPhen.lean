/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.PolyPhen

/-!
# Tests for profile log-odds scores and the naive-Bayes damage posterior

A two-letter alphabet profile, Gibbs' inequality on it, the PSIC difference of a substitution to
a depleted residue, a junk value at a zero background, and a concrete naive-Bayes model with
one binary feature (non-vacuity of `NaiveBayes`) whose posterior is computed and compared.
-/

open Real

namespace MathlibExtTest.Biology.StatisticalGenetics.PolyPhen

open MathlibExt.Biology.StatisticalGenetics.PolyPhen

/-- Profile `(3/4, 1/4)` against a uniform background on `Bool`. -/
noncomputable def p : Bool → ℝ := fun a => if a then 3 / 4 else 1 / 4

/-- The uniform background on `Bool`. -/
noncomputable def q : Bool → ℝ := fun _ => 1 / 2

example : profileScore p q true = log (3 / 2) := by
  norm_num [profileScore, p, q]

/-- Gibbs' inequality on the concrete profile. -/
example : 0 ≤ ∑ a, p a * profileScore p q a :=
  sum_mul_profileScore_nonneg (fun a => by cases a <;> norm_num [p]) (fun _ => by norm_num [q])
    (by norm_num [p]) (by norm_num [q])

/-- Substituting the enriched residue `true` by the depleted `false` has positive PSIC
difference `log 3`. -/
example : psicDifference p q true false = log 3 ∧ 0 < psicDifference p q true false := by
  have hp : ∀ a, 0 < p a := fun a => by cases a <;> norm_num [p]
  have hq : ∀ a, 0 < q a := fun _ => by norm_num [q]
  refine ⟨?_, (psicDifference_pos_iff hp hq).2 (by norm_num [p, q])⟩
  rw [psicDifference_eq_log hp hq]
  norm_num [p, q]

/-- The summed score of the sequence `(true, true)` is the log-likelihood ratio `log (9/4)`. -/
example : ∑ j : Fin 2, profileScore p q ((fun _ => true) j) = log (9 / 4) := by
  rw [sum_profileScore_eq_log_likelihood_ratio (fun _ => p) q _
    (fun _ a => by cases a <;> norm_num [p]) (fun _ => by norm_num [q])]
  norm_num [p, q]

/-- Junk value outside the domain: a zero background gives `log (p / 0) = log 0 = 0`. -/
example : profileScore p (fun _ => 0) true = 0 := by
  simp [profileScore]

/-- Non-vacuity witness: a naive-Bayes model with one binary feature, prior `1 / 2`, and a
feature value `true` three times as likely under *damaging* as under *benign*. -/
noncomputable def M : NaiveBayes Unit (fun _ => Bool) where
  prior := 1 / 2
  prior_pos := by norm_num
  prior_lt_one := by norm_num
  damaging := fun _ v => if v then 3 / 4 else 1 / 4
  benign := fun _ v => if v then 1 / 4 else 3 / 4
  damaging_pos := fun _ v => by cases v <;> norm_num
  benign_pos := fun _ v => by cases v <;> norm_num
  sum_damaging := fun _ => by norm_num
  sum_benign := fun _ => by norm_num

example : ∑ c, ∑ x, M.joint c x = 1 := M.sum_joint

/-- The posterior given the feature value `true` is `3 / 4`. -/
example : M.posterior (fun _ => true) = 3 / 4 := by
  norm_num [NaiveBayes.posterior, NaiveBayes.joint, M]

/-- The posterior is the logistic function of the score `log 3`. -/
example : M.posterior (fun _ => true) = sigmoid (log 3) := by
  rw [M.posterior_eq_sigmoid]
  norm_num [NaiveBayes.score, NaiveBayes.logLikelihoodRatio, M]

/-- The value `true` raises the posterior above that of `false`. -/
example : M.posterior (fun _ => false) < M.posterior (fun _ => true) := by
  rw [M.posterior_lt_posterior_iff]
  norm_num [NaiveBayes.score, NaiveBayes.logLikelihoodRatio, M]
  exact log_lt_log (by norm_num) (by norm_num)

/-- Monotonicity in a numerical feature value: ordering `false < true` through `g`, the
likelihood ratio increases, so does the posterior. -/
example (x : Unit → Bool) :
    M.posterior (Function.update x () false) ≤ M.posterior (Function.update x () true) :=
  M.posterior_update_le_of_monotone x () (fun v => if v then 1 else 0)
    (fun v w h => by revert h; cases v <;> cases w <;> norm_num [M]) (by norm_num)

end MathlibExtTest.Biology.StatisticalGenetics.PolyPhen
