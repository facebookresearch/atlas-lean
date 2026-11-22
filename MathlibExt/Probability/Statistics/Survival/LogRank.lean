/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Distributions.Hypergeometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The tied log-rank variance term

At one distinct event time of a two-sample survival comparison, `Y` subjects are at risk, `Y₁`
of them in group 1, and `d` of them fail. Conditionally on the margins, the number of group-1
failures is hypergeometric (draw `d` of the `Y` subjects without replacement, `Y₁` marked), with
variance

  `d Y₁ (Y - Y₁) (Y - d) / (Y² (Y - 1))`

(Mantel 1966). Summing these over the event times gives the log-rank variance with ties.

## Main results

* `tiedLogRankVarianceTerm_nonneg`: the term is non-negative when `Y₁ ≤ Y` and `d ≤ Y`.
* `tiedLogRankVarianceTerm_eq_mul`: the algebraic identity
  `term = d · (Y₁ (Y - Y₁) / Y²) · ((Y - d) / (Y - 1))` for every `Y > 1` (no domain
  hypotheses; it carries no statistical meaning outside `Y₁ ≤ Y`, `d ≤ Y`).
* `tiedLogRankVarianceTerm_one`: on the domain `Y₁ ≤ Y`, a single failure (`d = 1`) gives the
  Breslow (Cox information) summand `Y₁ (Y - Y₁) / Y²`, as in
  `CoxPartialLikelihood.breslowInformation`.
* `tiedLogRankVarianceTerm_le`: on the domain `Y₁ ≤ Y`, `1 ≤ d ≤ Y`, the tied variance is at
  most the Breslow contribution `d Y₁ (Y - Y₁) / Y²` of the `d` tied events, since the
  finite-population factor `(Y - d) / (Y - 1)` lies in `[0, 1]`.

For example, with `Y = 4`, `Y₁ = 2` and `d = 2` the tied variance is `1 / 3`, while the Breslow
information of the two tied events is `2 · (2 · 2 / 4²) = 1 / 2`.

* `tiedLogRankVarianceTerm_eq_variance`: for `Y > 1` the term is the variance of the
  hypergeometric law of the number of group-1 failures
  (`ProbabilityTheory.sum_sq_sub_mean_mul_hypergeometricReal`).

## Scope

This file covers one event time. The log-rank statistic, its sum of these terms over the event
times, and its asymptotic normality are not formalized here.

## References

* N. Mantel, *Evaluation of survival data and two new rank order statistics arising in its
  consideration*, Cancer Chemother. Rep. 50 (1966), 163–170.
* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Section 7.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.LogRank

/-- The **tied log-rank variance term** `d Y₁ (Y - Y₁) (Y - d) / (Y² (Y - 1))` at one event time
with `Y` at risk, `Y₁` of them in group 1, and `d` failures. It is the conditional
(hypergeometric) variance of the number of group-1 failures given the margins (Mantel 1966); for
`Y ≤ 1` that number is deterministic and the term is `0`. All subtractions are taken in `ℝ`, so
under `Y₁ ≤ Y` and `d ≤ Y` they agree with the natural-number differences. -/
noncomputable def tiedLogRankVarianceTerm (Y Y₁ d : ℕ) : ℝ :=
  if Y ≤ 1 then 0 else
    (d : ℝ) * Y₁ * ((Y : ℝ) - Y₁) * ((Y : ℝ) - d) / ((Y : ℝ) ^ 2 * ((Y : ℝ) - 1))

/-- The tied log-rank variance term is non-negative when `Y₁ ≤ Y` and `d ≤ Y`. -/
theorem tiedLogRankVarianceTerm_nonneg {Y Y₁ d : ℕ} (h₁ : Y₁ ≤ Y) (hd : d ≤ Y) :
    0 ≤ tiedLogRankVarianceTerm Y Y₁ d := by
  unfold tiedLogRankVarianceTerm
  split_ifs with hY
  · exact le_rfl
  have h₁' : (Y₁ : ℝ) ≤ Y := by exact_mod_cast h₁
  have hd' : (d : ℝ) ≤ Y := by exact_mod_cast hd
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
  refine div_nonneg (mul_nonneg (mul_nonneg (by positivity) ?_) ?_) (mul_nonneg ?_ ?_) <;>
    nlinarith

/-- Algebraic identity: for `1 < Y` and any naturals `Y₁`, `d`, the term equals
`d · (Y₁ (Y - Y₁) / Y²) · ((Y - d) / (Y - 1))`, with all subtractions in `ℝ`. Only on the domain
`Y₁ ≤ Y`, `d ≤ Y` do the factors read as the Breslow contribution of the `d` tied events and the
finite-population correction (see `tiedLogRankVarianceTerm_one`, `tiedLogRankVarianceTerm_le`);
outside it the factors can be negative. -/
theorem tiedLogRankVarianceTerm_eq_mul {Y : ℕ} (hY : 1 < Y) (Y₁ d : ℕ) :
    tiedLogRankVarianceTerm Y Y₁ d =
      d * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) * (((Y : ℝ) - d) / ((Y : ℝ) - 1)) := by
  have hY0 : (Y : ℝ) ≠ 0 := by positivity
  have hY1 : (Y : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hY.ne')
  unfold tiedLogRankVarianceTerm
  split_ifs with h
  · omega
  field_simp

/-- **A single failure gives the Breslow term**: on the domain `Y₁ ≤ Y`, for `d = 1` the tied
log-rank variance term is `Y₁ (Y - Y₁) / Y²`, the summand of the Cox information
`breslowInformation` at one risk set. The hypothesis `Y₁ ≤ Y` only restricts to valid counts; the
underlying algebra is `tiedLogRankVarianceTerm_eq_mul`. -/
theorem tiedLogRankVarianceTerm_one {Y Y₁ : ℕ} (hY : 1 < Y) (_h₁ : Y₁ ≤ Y) :
    tiedLogRankVarianceTerm Y Y₁ 1 = (Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2 := by
  have hY1 : (Y : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hY.ne')
  rw [tiedLogRankVarianceTerm_eq_mul hY, Nat.cast_one, div_self hY1, one_mul, mul_one]

/-- On the domain `Y₁ ≤ Y`, `1 ≤ d ≤ Y`, the tied variance is at most the Breslow contribution
`d Y₁ (Y - Y₁) / Y²` of the `d` tied events; Breslow's information overstates it under ties.
The hypothesis `d ≤ Y` only restricts to valid counts (the inequality itself does not need
it). -/
theorem tiedLogRankVarianceTerm_le {Y Y₁ d : ℕ} (h₁ : Y₁ ≤ Y) (hd1 : 1 ≤ d) (_hd : d ≤ Y) :
    tiedLogRankVarianceTerm Y Y₁ d ≤ d * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) := by
  have hB : 0 ≤ (d : ℝ) * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) := by
    have : (Y₁ : ℝ) ≤ Y := by exact_mod_cast h₁
    have : 0 ≤ (Y : ℝ) - Y₁ := by linarith
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) this)
      (sq_nonneg _))
  rcases Nat.lt_or_ge 1 Y with hY | hY
  · rw [tiedLogRankVarianceTerm_eq_mul hY]
    have hY' : (1 : ℝ) < Y := by exact_mod_cast hY
    have hf : ((Y : ℝ) - d) / ((Y : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    exact mul_le_of_le_one_right hB hf
  · unfold tiedLogRankVarianceTerm
    split_ifs with h
    · exact hB
    · omega

/-- **The tied term is the hypergeometric variance** (Mantel 1966): for `1 < Y`, `Y₁ ≤ Y` and
`d ≤ Y`, it is `∑ₖ (k - d Y₁ / Y)² h(k)`, where `h` is the law of the number of group-1 subjects
among `d` drawn without replacement from `Y` subjects of which `Y₁` are in group 1, and
`d Y₁ / Y` is its mean (`ProbabilityTheory.sum_mul_hypergeometricReal`). -/
theorem tiedLogRankVarianceTerm_eq_variance {Y Y₁ d : ℕ} (hY : 1 < Y) (h₁ : Y₁ ≤ Y)
    (hd : d ≤ Y) :
    tiedLogRankVarianceTerm Y Y₁ d = ∑ k ∈ Finset.range (d + 1),
      ((k : ℝ) - d * Y₁ / Y) ^ 2 * ProbabilityTheory.hypergeometricReal Y Y₁ d k := by
  rw [ProbabilityTheory.sum_sq_sub_mean_mul_hypergeometricReal hY h₁ hd]
  unfold tiedLogRankVarianceTerm
  split_ifs with h
  · omega
  · rfl

end MathlibExt.Probability.Statistics.LogRank
