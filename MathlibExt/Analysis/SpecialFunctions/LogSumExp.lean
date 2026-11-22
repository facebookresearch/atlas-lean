/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.StdSimplexWeights
public import MathlibExt.Analysis.SpecialFunctions.Softplus
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import MathlibExt.Analysis.Calculus.DotProductGradient

/-!
# Log-sum-exp, softmax and softplus

On a nonempty finite index type, the log-sum-exp function `logSumExp z = log ∑ i, exp (z i)` is the
log-partition function of the categorical distribution with natural parameters `z`; its gradient is
the softmax `softmax z i = exp (z i) / ∑ j, exp (z j)`, and it is convex. (On an empty index type
the sum is `0`, Lean's `Real.log 0 = 0`, and the softmax is not a distribution; the results below
assume `[Nonempty ι]` where needed.) With two coordinates `0` and `z` it
is the softplus `log (1 + exp z)`, whose derivative is the logistic function `Real.sigmoid`.

## Main results

* `convexOn_log_sum_mul_exp`: for nonnegative weights `h` with a positive entry,
  `z ↦ log ∑ i, h i * exp (z i)` is convex (Hölder's inequality in the form of the weighted
  AM-GM inequality `p ^ a * q ^ b ≤ a * p + b * q`, summed over normalized terms). In particular
  `convexOn_logSumExp` (and `convexOn_softplus`, from
  `MathlibExt/Analysis/SpecialFunctions/Softplus.lean`).
* `sum_softmax`, `softmaxDist`, `log_softmax`: the softmax is a categorical distribution (a point
  of Mathlib's `Convexity.StdSimplex`), and `log (softmax z i) = z i - logSumExp z`.
* `hasFDerivAt_logSumExp`, `hasGradientAt_logSumExp`, `hasDerivAt_logSumExp_line`: the gradient
  of log-sum-exp is the softmax (a Fréchet derivative on `ι → ℝ` with gradients represented by
  `dotL g : v ↦ v ⬝ᵥ g`, and Mathlib's `HasGradientAt` on `EuclideanSpace ℝ ι`; the helpers are in
  `MathlibExt/Analysis/Calculus/DotProductGradient.lean`).
* `logSumExp_add_const`, `softmax_add_const`: on a nonempty index type, adding a constant to all
  scores shifts log-sum-exp by that constant, and it always leaves the softmax unchanged.
* `hasDerivAt_softplus` (from `Softplus.lean`): the derivative of the softplus is the logistic function;
  `softmax_pair`: the softmax of two scores is the logistic function of their difference;
  `softplus_neg`, `neg_log_sigmoid`: `softplus (-z) = softplus z - z` and
  `-log (sigmoid z) = softplus (-z)`; `unitInterval.coe_sigmoid`: Mathlib's
  `unitInterval.sigmoid` coerces to `Real.sigmoid`.

These are the log-partition calculus of categorical and Bernoulli models used by logistic and
softmax regression (`CSLibExt/MachineLearning/Discriminative/`). Everything is in the `Real`
namespace, next to Mathlib's `Real.sigmoid`.
-/

@[expose] public section

namespace Real

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Convexity of weighted log-sum-exp**: for nonnegative weights `h` with a positive entry,
`z ↦ log ∑ i, h i * exp (z i)` is convex. -/
theorem convexOn_log_sum_mul_exp {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) (hpos : 0 < ∑ i, h i) :
    ConvexOn ℝ Set.univ fun z : ι → ℝ => log (∑ i, h i * exp (z i)) := by
  have hsum : ∀ z : ι → ℝ, 0 < ∑ i, h i * exp (z i) := fun z => by
    refine lt_of_le_of_ne (sum_nonneg fun i _ => mul_nonneg (hh i) (exp_pos _).le) fun h0 => ?_
    have h0' := (sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hh i) (exp_pos _).le).1 h0.symm
    have hz : ∀ i, h i = 0 := fun i =>
      (mul_eq_zero.1 (h0' i (mem_univ i))).resolve_right (exp_pos _).ne'
    simp [hz] at hpos
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set A := ∑ i, h i * exp (x i)
  set B := ∑ i, h i * exp (y i)
  have hA : 0 < A := hsum x
  have hB : 0 < B := hsum y
  have hterm : ∀ i, h i * exp ((a • x + b • y) i) =
      A ^ a * B ^ b * ((h i * exp (x i) / A) ^ a * (h i * exp (y i) / B) ^ b) := fun i => by
    have h1 : 0 ≤ h i * exp (x i) := mul_nonneg (hh i) (exp_pos _).le
    have h2 : 0 ≤ h i * exp (y i) := mul_nonneg (hh i) (exp_pos _).le
    have hAa : A ^ a ≠ 0 := (rpow_pos_of_pos hA a).ne'
    have hBb : B ^ b ≠ 0 := (rpow_pos_of_pos hB b).ne'
    rw [div_rpow h1 hA.le, div_rpow h2 hB.le,
      show A ^ a * B ^ b * ((h i * exp (x i)) ^ a / A ^ a * ((h i * exp (y i)) ^ b / B ^ b)) =
        (h i * exp (x i)) ^ a * (h i * exp (y i)) ^ b by field_simp,
      mul_rpow (hh i) (exp_pos _).le, mul_rpow (hh i) (exp_pos _).le, ← exp_mul, ← exp_mul,
      show h i ^ a * exp (x i * a) * (h i ^ b * exp (y i * b)) =
        (h i ^ a * h i ^ b) * (exp (x i * a) * exp (y i * b)) by ring,
      ← rpow_add' (hh i) (by rw [hab]; exact one_ne_zero), hab, rpow_one, ← exp_add]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
  have key : ∑ i, h i * exp ((a • x + b • y) i) ≤ A ^ a * B ^ b := by
    rw [sum_congr rfl fun i _ => hterm i, ← mul_sum]
    refine (mul_le_mul_of_nonneg_left ?_ (by positivity)).trans (mul_one _).le
    calc ∑ i, (h i * exp (x i) / A) ^ a * (h i * exp (y i) / B) ^ b
        ≤ ∑ i, (a * (h i * exp (x i) / A) + b * (h i * exp (y i) / B)) :=
          sum_le_sum fun i _ => geom_mean_le_arith_mean2_weighted ha hb
            (div_nonneg (mul_nonneg (hh i) (exp_pos _).le) hA.le)
            (div_nonneg (mul_nonneg (hh i) (exp_pos _).le) hB.le) hab
      _ = 1 := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_div, ← sum_div, div_self hA.ne',
            div_self hB.ne', mul_one, mul_one, hab]
  calc log (∑ i, h i * exp ((a • x + b • y) i)) ≤ log (A ^ a * B ^ b) :=
        log_le_log (hsum _) key
    _ = a * log A + b * log B := by
        rw [log_mul (rpow_pos_of_pos hA a).ne' (rpow_pos_of_pos hB b).ne', log_rpow hA,
          log_rpow hB]
    _ = _ := by simp only [smul_eq_mul]; rfl

/-- `log ∑ i, exp (z i)`. -/
noncomputable def logSumExp (z : ι → ℝ) : ℝ :=
  log (∑ i, exp (z i))

/-- The softmax `exp (z i) / ∑ j, exp (z j)`. -/
noncomputable def softmax (z : ι → ℝ) (i : ι) : ℝ :=
  exp (z i) / ∑ j, exp (z j)

theorem convexOn_logSumExp [Nonempty ι] : ConvexOn ℝ Set.univ (logSumExp (ι := ι)) := by
  have h := convexOn_log_sum_mul_exp (h := fun _ : ι => (1 : ℝ)) (fun _ => zero_le_one)
    (by simp [Fintype.card_pos])
  change ConvexOn ℝ Set.univ fun z : ι → ℝ => log (∑ i, exp (z i))
  simpa using h

theorem sum_exp_pos [Nonempty ι] (z : ι → ℝ) : 0 < ∑ i, exp (z i) :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

theorem softmax_pos [Nonempty ι] (z : ι → ℝ) (i : ι) : 0 < softmax z i :=
  div_pos (exp_pos _) (sum_exp_pos z)

theorem sum_softmax [Nonempty ι] (z : ι → ℝ) : ∑ i, softmax z i = 1 := by
  simp only [softmax, ← sum_div]
  exact div_self (sum_exp_pos z).ne'

/-- The softmax as a categorical distribution, a point of Mathlib's standard simplex. -/
noncomputable def softmaxDist [Nonempty ι] (z : ι → ℝ) : Convexity.StdSimplex ℝ ι :=
  Convexity.StdSimplex.ofWeights (softmax z) (fun i => (softmax_pos z i).le) (sum_softmax z)

@[simp]
theorem softmaxDist_weights [Nonempty ι] (z : ι → ℝ) (i : ι) :
    (softmaxDist z).weights i = softmax z i :=
  Convexity.StdSimplex.ofWeights_weights _ _ _ i

theorem log_softmax [Nonempty ι] (z : ι → ℝ) (i : ι) :
    log (softmax z i) = z i - logSumExp z := by
  rw [softmax, log_div (exp_pos _).ne' (sum_exp_pos z).ne', log_exp, logSumExp]

/-! ### Derivatives

The gradient of log-sum-exp is stated as a Fréchet derivative `dotL g` on `ι → ℝ` and transferred to
Mathlib's `HasGradientAt` on `EuclideanSpace ℝ ι`, using the helpers of
`MathlibExt/Analysis/Calculus/DotProductGradient.lean`.
-/

/-- **The gradient of log-sum-exp is the softmax.** -/
theorem hasFDerivAt_logSumExp [Nonempty ι] (z : ι → ℝ) :
    HasFDerivAt logSumExp (dotL (softmax z)) z := by
  have hsum : HasFDerivAt (fun z : ι → ℝ => ∑ i, exp (z i))
      (∑ i, exp (z i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) z :=
    HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_apply i z).exp
  convert hsum.log (sum_exp_pos z).ne' using 1
  · rfl
  · ext v
    simp [dotL, softmax, Finset.smul_sum, div_eq_inv_mul, mul_assoc, mul_comm]

/-- **The gradient of log-sum-exp is the softmax**, in Mathlib's gradient API. -/
theorem hasGradientAt_logSumExp [Nonempty ι] (z : ι → ℝ) :
    HasGradientAt (fun w : EuclideanSpace ℝ ι => logSumExp (WithLp.ofLp w))
      (WithLp.toLp 2 (softmax z)) (WithLp.toLp 2 z) :=
  hasGradientAt_ofLp (hasFDerivAt_logSumExp z)

/-- The derivative of `logSumExp` at `z` in the direction `v` is `v ⬝ᵥ softmax z`. -/
theorem hasDerivAt_logSumExp_line [Nonempty ι] (z v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => logSumExp (z + t • v)) (v ⬝ᵥ softmax z) 0 :=
  hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_logSumExp z) v

/-! ### Translation invariance -/

theorem logSumExp_add_const [Nonempty ι] (z : ι → ℝ) (c : ℝ) :
    logSumExp (fun i => z i + c) = logSumExp z + c := by
  rw [logSumExp, logSumExp]
  simp only [exp_add, ← sum_mul]
  rw [log_mul (sum_exp_pos z).ne' (exp_pos c).ne', log_exp]

/-- The softmax is invariant under adding a constant to all scores. -/
theorem softmax_add_const (z : ι → ℝ) (c : ℝ) (i : ι) :
    softmax (fun j => z j + c) i = softmax z i := by
  simp only [softmax, exp_add, ← sum_mul]
  by_cases h : exp c = 0
  · exact absurd h (exp_pos c).ne'
  · rw [mul_div_mul_right _ _ h]

theorem softplus_eq_logSumExp (z : ℝ) : softplus z = logSumExp ![0, z] := by
  simp [softplus, logSumExp, Fin.sum_univ_two]

/-- The softmax of two scores is the logistic function of their difference. -/
theorem softmax_pair (z₀ z₁ : ℝ) : softmax ![z₀, z₁] 1 = sigmoid (z₁ - z₀) := by
  rw [softmax, Fin.sum_univ_two, sigmoid_def, neg_sub, exp_sub]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

theorem softplus_neg (z : ℝ) : softplus (-z) = softplus z - z := by
  rw [softplus, softplus, eq_sub_iff_add_eq, ← log_exp z, ← log_mul (by positivity)
    (exp_pos z).ne', log_exp, add_mul, one_mul, ← exp_add, neg_add_cancel, exp_zero, add_comm]

theorem neg_log_sigmoid (z : ℝ) : -log (sigmoid z) = softplus (-z) := by
  rw [sigmoid_def, log_inv, neg_neg, softplus]

end Real

/-- Mathlib's `unitInterval.sigmoid` is `Real.sigmoid` as a point of the unit interval. -/
theorem unitInterval.coe_sigmoid (z : ℝ) : (unitInterval.sigmoid z : ℝ) = Real.sigmoid z :=
  rfl
