/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
import MathlibExt.Analysis.SpecialFunctions.SigmoidLogOdds

/-!
# Profile log-odds scores and naive-Bayes damage prediction (PSIC, PolyPhen)

PolyPhen (Sunyaev et al. 2001) and PolyPhen-2 (Adzhubei et al. 2010) predict whether an amino
acid substitution damages a protein. One of their inputs is the PSIC profile score
(Sunyaev et al. 1999): from an alignment of homologous sequences one estimates, at each
position, the probability `p a` of amino acid `a` under the position-specific profile, and
compares it with its background probability `q a`. PolyPhen-2 then combines this and further
sequence and structure features with a naive Bayes classifier into a posterior probability that
the variant is damaging. The profiles, likelihood tables, priors and thresholds are estimated
from data; this file proves the probabilistic identities they rest on.

## Main results

* `profileScore p q a = log (p a / q a)`. `sum_profileScore_eq_log_likelihood_ratio`: summed
  over independent positions it is the log-likelihood ratio of a sequence under the profile
  model against the background model. `sum_mul_profileScore_nonneg` and
  `sum_mul_profileScore_nonpos`: its expectation is nonnegative under the profile and
  nonpositive under the background (Gibbs' inequality).
* `psicDifference p q wt mt`: the score difference between the wild-type and mutant residues,
  `psicDifference_eq_log` (the log of the ratio of their likelihood ratios) and
  `psicDifference_pos_iff` (positive iff the wild type is the more enriched residue).
* `NaiveBayes`: two classes (damaging, benign) with a prior and, for each feature, a finite
  class-conditional likelihood table; features are conditionally independent given the class.
  `NaiveBayes.sum_joint`: the joint law of class and features is a probability law.
* `NaiveBayes.posterior_eq_sigmoid`: the posterior probability of *damaging* given the feature
  values is the logistic function of the score `log (π / (1 - π)) + ∑_j log LR_j(x_j)`.
* `NaiveBayes.posterior_lt_posterior_iff`: the posterior is strictly monotone in the score;
  `NaiveBayes.posterior_update_le_of_monotone`: if one feature's likelihood ratio is monotone
  in a numerical value (such as a PSIC difference), the posterior is monotone in that value
  when the other features are held fixed.

## References

* S. R. Sunyaev et al., *PSIC: profile extraction from sequence alignments with
  position-specific counts of independent observations*, Protein Eng. 12 (1999) 387–394.
* S. Sunyaev et al., *Prediction of deleterious human alleles*, Hum. Mol. Genet. 10 (2001)
  591–597.
* I. A. Adzhubei et al., *A method and server for predicting damaging missense mutations*,
  Nat. Methods 7 (2010) 248–249.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.StatisticalGenetics.PolyPhen

/-! ### Profile log-odds scores -/

section Profile

variable {A : Type*}

/-- The profile log-odds score `log (p a / q a)` of residue `a`: `p` is the position-specific
profile probability (estimated from aligned homologs), `q` the background probability.
Meaningful for `p a, q a > 0`; otherwise Lean's `log 0 = 0` and `x / 0 = 0` give junk. -/
noncomputable def profileScore (p q : A → ℝ) (a : A) : ℝ :=
  log (p a / q a)

/-- **The score is a log-likelihood ratio.** For a sequence `s` over independent positions with
profiles `p j` and background `q` (all positive), the summed profile score is the log of the
likelihood ratio `∏ p_j(s_j) / ∏ q(s_j)` of the profile model against the background. -/
theorem sum_profileScore_eq_log_likelihood_ratio {ι : Type*} [Fintype ι] (p : ι → A → ℝ)
    (q : A → ℝ) (s : ι → A) (hp : ∀ j a, 0 < p j a) (hq : ∀ a, 0 < q a) :
    ∑ j, profileScore (p j) q (s j) = log ((∏ j, p j (s j)) / ∏ j, q (s j)) := by
  rw [log_div (Finset.prod_pos fun j _ => hp j (s j)).ne' (Finset.prod_pos fun j _ => hq (s j)).ne',
    log_prod (fun j _ => (hp j (s j)).ne'), log_prod (fun j _ => (hq (s j)).ne'),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => log_div (hp j (s j)).ne' (hq (s j)).ne'

/-- **Gibbs' inequality for the profile score.** If `p` and `q` are probability vectors and
`q` is positive, the expected score under the profile, `∑ p a log (p a / q a)` (the
Kullback–Leibler divergence), is nonnegative. -/
theorem sum_mul_profileScore_nonneg [Fintype A] {p q : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 < q a) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) :
    0 ≤ ∑ a, p a * profileScore p q a := by
  have h : ∀ a, p a - q a ≤ p a * profileScore p q a := by
    intro a
    rcases (hp a).eq_or_lt with h0 | hpos
    · rw [← h0]
      linarith [hq a]
    · have hlog := one_sub_inv_le_log_of_pos (div_pos hpos (hq a))
      rw [inv_div] at hlog
      calc p a - q a = p a * (1 - q a / p a) := by field_simp
        _ ≤ p a * profileScore p q a := mul_le_mul_of_nonneg_left hlog hpos.le
  calc (0 : ℝ) = ∑ a, (p a - q a) := by rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
    _ ≤ _ := Finset.sum_le_sum fun a _ => h a

/-- If `p` and `q` are probability vectors and `p` is positive, the expected score under the
background, `∑ q a log (p a / q a)`, is nonpositive. -/
theorem sum_mul_profileScore_nonpos [Fintype A] {p q : A → ℝ} (hp : ∀ a, 0 < p a)
    (hq : ∀ a, 0 ≤ q a) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) :
    ∑ a, q a * profileScore p q a ≤ 0 := by
  have h : ∀ a, q a * profileScore p q a ≤ p a - q a := by
    intro a
    rcases (hq a).eq_or_lt with h0 | hpos
    · rw [← h0]
      linarith [hp a]
    · have hlog := log_le_sub_one_of_pos (div_pos (hp a) hpos)
      calc q a * profileScore p q a ≤ q a * (p a / q a - 1) :=
            mul_le_mul_of_nonneg_left hlog hpos.le
        _ = p a - q a := by field_simp
  calc ∑ a, q a * profileScore p q a ≤ ∑ a, (p a - q a) := Finset.sum_le_sum fun a _ => h a
    _ = 0 := by rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]

/-- The PSIC score difference of a substitution from the wild-type residue `wt` to the mutant
residue `mt`: `profileScore p q wt - profileScore p q mt`. -/
noncomputable def psicDifference (p q : A → ℝ) (wt mt : A) : ℝ :=
  profileScore p q wt - profileScore p q mt

/-- The PSIC difference is the log of the ratio of the two residues' likelihood ratios. -/
theorem psicDifference_eq_log {p q : A → ℝ} {wt mt : A} (hp : ∀ a, 0 < p a)
    (hq : ∀ a, 0 < q a) :
    psicDifference p q wt mt = log ((p wt / q wt) / (p mt / q mt)) := by
  rw [psicDifference, profileScore, profileScore,
    log_div (div_pos (hp wt) (hq wt)).ne' (div_pos (hp mt) (hq mt)).ne']

/-- The PSIC difference is positive iff the wild type is more enriched in the profile, relative
to background, than the mutant. -/
theorem psicDifference_pos_iff {p q : A → ℝ} {wt mt : A} (hp : ∀ a, 0 < p a)
    (hq : ∀ a, 0 < q a) :
    0 < psicDifference p q wt mt ↔ p mt / q mt < p wt / q wt := by
  rw [psicDifference_eq_log hp hq,
    log_pos_iff (div_pos (div_pos (hp wt) (hq wt)) (div_pos (hp mt) (hq mt))).le,
    one_lt_div (div_pos (hp mt) (hq mt))]

end Profile

/-! ### Naive-Bayes combination of features -/

/-- A two-class naive Bayes model: class *damaging* has prior `prior ∈ (0, 1)`, class *benign*
the complement; each feature `j` takes values in the finite type `X j` with class-conditional
probabilities `damaging j` and `benign j`, assumed positive; features are conditionally
independent given the class. The tables are estimated from training data. -/
structure NaiveBayes (ι : Type*) (X : ι → Type*) [∀ j, Fintype (X j)] where
  /-- The prior probability of the class *damaging*. -/
  prior : ℝ
  prior_pos : 0 < prior
  prior_lt_one : prior < 1
  /-- The likelihood of each value of feature `j` given *damaging*. -/
  damaging : ∀ j, X j → ℝ
  /-- The likelihood of each value of feature `j` given *benign*. -/
  benign : ∀ j, X j → ℝ
  damaging_pos : ∀ j v, 0 < damaging j v
  benign_pos : ∀ j v, 0 < benign j v
  sum_damaging : ∀ j, ∑ v, damaging j v = 1
  sum_benign : ∀ j, ∑ v, benign j v = 1

namespace NaiveBayes

variable {ι : Type*} {X : ι → Type*} [∀ j, Fintype (X j)] [Fintype ι] (M : NaiveBayes ι X)

/-- The joint probability of class `c` (`true` = damaging) and feature values `x`:
`π ∏ P_D(x_j)` or `(1 - π) ∏ P_B(x_j)`. -/
noncomputable def joint (c : Bool) (x : ∀ j, X j) : ℝ :=
  if c then M.prior * ∏ j, M.damaging j (x j) else (1 - M.prior) * ∏ j, M.benign j (x j)

/-- The joint law of class and features is a probability law. -/
theorem sum_joint [DecidableEq ι] : ∑ c, ∑ x, M.joint c x = 1 := by
  simp only [Fintype.sum_bool, joint, Bool.false_eq_true, ↓reduceIte, ← Finset.mul_sum,
    ← Fintype.prod_sum, M.sum_damaging, M.sum_benign, Finset.prod_const_one]
  ring

/-- The posterior probability that the variant is damaging given feature values `x`
(Bayes' rule on the joint law). -/
noncomputable def posterior (x : ∀ j, X j) : ℝ :=
  M.joint true x / ∑ c, M.joint c x

/-- The log-likelihood ratio `log (P_D(v) / P_B(v))` of value `v` of feature `j`. -/
noncomputable def logLikelihoodRatio (j : ι) (v : X j) : ℝ :=
  log (M.damaging j v / M.benign j v)

/-- The naive-Bayes score: prior log-odds plus the features' log-likelihood ratios. -/
noncomputable def score (x : ∀ j, X j) : ℝ :=
  log (M.prior / (1 - M.prior)) + ∑ j, M.logLikelihoodRatio j (x j)

/-- **Naive-Bayes posterior.** The posterior probability of *damaging* is the logistic function
of the score. -/
theorem posterior_eq_sigmoid (x : ∀ j, X j) : M.posterior x = sigmoid (M.score x) := by
  have hd : 0 < ∏ j, M.damaging j (x j) := Finset.prod_pos fun j _ => M.damaging_pos j (x j)
  have hb : 0 < ∏ j, M.benign j (x j) := Finset.prod_pos fun j _ => M.benign_pos j (x j)
  have h1 : 0 < 1 - M.prior := sub_pos.2 M.prior_lt_one
  have hscore : M.score x = log (M.prior * ∏ j, M.damaging j (x j)) -
      log ((1 - M.prior) * ∏ j, M.benign j (x j)) := by
    simp only [score, logLikelihoodRatio]
    rw [log_div M.prior_pos.ne' h1.ne', log_mul M.prior_pos.ne' hd.ne', log_mul h1.ne' hb.ne',
      log_prod (fun j _ => (M.damaging_pos j (x j)).ne'),
      log_prod (fun j _ => (M.benign_pos j (x j)).ne'),
      Finset.sum_congr rfl
        (fun j _ => log_div (M.damaging_pos j (x j)).ne' (M.benign_pos j (x j)).ne'),
      Finset.sum_sub_distrib]
    ring
  rw [hscore, sigmoid_log_sub_log (mul_pos M.prior_pos hd) (mul_pos h1 hb), posterior,
    Fintype.sum_bool]
  simp [joint]

/-- The posterior is strictly monotone in the score. -/
theorem posterior_lt_posterior_iff (x y : ∀ j, X j) :
    M.posterior x < M.posterior y ↔ M.score x < M.score y := by
  rw [posterior_eq_sigmoid, posterior_eq_sigmoid, sigmoid_lt_iff]

/-- **Monotonicity in a feature value.** Let feature `j` carry a numerical value `g v` (for
example a PSIC-difference bin) such that its likelihood ratio `P_D(v) / P_B(v)` is monotone in
`g v`. With the other features fixed, the posterior is monotone in `g`. -/
theorem posterior_update_le_of_monotone [DecidableEq ι] (x : ∀ j, X j) (j : ι) (g : X j → ℝ)
    (hg : ∀ v w, g v ≤ g w → M.damaging j v / M.benign j v ≤ M.damaging j w / M.benign j w)
    {v w : X j} (hvw : g v ≤ g w) :
    M.posterior (Function.update x j v) ≤ M.posterior (Function.update x j w) := by
  rw [posterior_eq_sigmoid, posterior_eq_sigmoid, sigmoid_le_iff, score, score,
    add_le_add_iff_left]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, logLikelihoodRatio]
    exact log_le_log (div_pos (M.damaging_pos i v) (M.benign_pos i v)) (hg v w hvw)
  · simp only [Function.update_of_ne hij, le_refl]

end NaiveBayes

end MathlibExt.Biology.StatisticalGenetics.PolyPhen
