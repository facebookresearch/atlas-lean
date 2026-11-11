/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The Cox partial likelihood and the log-rank test

`n` subjects have observed times `Tᵢ`, event indicators `δᵢ` (`true` = event observed, `false` =
right-censored) and covariate vectors `xᵢ ∈ ℝᵖ`. Under Cox's proportional-hazards model the
hazard of subject `i` is `λ₀(t) exp ⟪β, xᵢ⟫`, and Cox's partial likelihood is

  `L(β) = ∏_{i : δᵢ} exp ⟪β, xᵢ⟫ / ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫`,

where `R(t) = {l : T_l ≥ t}` is the risk set. With tied event times each event uses the full
risk set at its time (Breslow 1974), which is Cox's formula when the event times are distinct.

## Main results

* `log_partialLikelihood`, `concaveOn_logPartialLikelihood`: the log partial likelihood
  `ℓ(β) = ∑_{i : δᵢ} (⟪β, xᵢ⟫ - log ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫)` is concave on `ℝᵖ` (each
  log-sum-exp term is convex), so every critical point is a global maximizer.
* For a scalar covariate `zᵢ`: `hasDerivAt_logPartialLikelihood`, the score
  `ℓ'(b) = ∑_{i : δᵢ} (zᵢ - z̄ᵢ(b))` with `z̄ᵢ(b)` the `exp (b z)`-weighted mean of `z` over
  `R(Tᵢ)`; `hasDerivAt_coxScore`, `ℓ''(b) = -∑_{i : δᵢ} Varᵢ(b)` with the weighted variance.
* For covariate vectors: `hasFDerivAt_logPartialLikelihood`, the Fréchet derivative of `ℓ` at
  `β` is `v ↦ ⟪U(β), v⟫` with the score vector `U(β) = ∑_{i : δᵢ} (xᵢ - x̄ᵢ(β))`
  (`coxGradient`, `riskMeanVec`), and `hasGradientAt_logPartialLikelihood` states that `U(β)`
  is the gradient of `ℓ` on `EuclideanSpace ℝ (Fin p)`. `coxGradient_one` recovers the scalar
  `coxScore` at `p = 1`. `hasDerivAt_coxGradient_dotProduct`: the Hessian quadratic form
  `d/dt ⟪U(β + t u), u⟫ |_{t=0}` is `-∑_{i : δᵢ} Varᵢ(⟪x, u⟫)` (`riskVarAlong`).
* **The log-rank test is the score test** (Mantel 1966; Cox 1972): for a group
  indicator `zᵢ = 1` (group 1) or `0`, `coxScore_zero` gives `ℓ'(0) = O - E`, the observed minus
  the expected number of group-1 events, `∑_{i : δᵢ} (zᵢ - n₁(Tᵢ) / n(Tᵢ))`, and
  `coxInformation_zero` gives `-ℓ''(0) = ∑_{i : δᵢ} n₁ n₀ / n²` at the risk sets of the events,
  the Breslow information (`breslowInformation`).
  When the event times are distinct this equals Mantel's hypergeometric variance
  `∑ dᵢ n₁ n₀ (n - dᵢ) / (n² (n - 1))` with `dᵢ = 1`; with ties the Breslow information differs
  from the hypergeometric variance, which this file does not cover. In particular this
  quantity must not be called the (tied) log-rank variance: for one tied risk set with
  `n = 4`, `n₁ = 2` and `d = 2` events it gives `1 / 2`, while the hypergeometric log-rank
  variance is `1 / 3`.

## References

* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
* N. Breslow, *Covariance analysis of censored survival data*, Biometrics 30 (1974), 89–99.
* N. Mantel, *Evaluation of survival data and two new rank order statistics arising in its
  consideration*, Cancer Chemother. Rep. 50 (1966), 163–170.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxPartialLikelihood

open Finset Real

variable {n p : ℕ}

/-- The risk set at the observed time of subject `i`: subjects still under observation,
`{l : T_l ≥ Tᵢ}`. -/
noncomputable def riskSet (T : Fin n → ℝ) (i : Fin n) : Finset (Fin n) := {l | T i ≤ T l}

/-- Subject `i` is in its own risk set. -/
theorem mem_riskSet (T : Fin n → ℝ) (i : Fin n) : i ∈ riskSet T i := by
  simp [riskSet]

/-- The risk set of subject `i` is nonempty. -/
theorem riskSet_nonempty (T : Fin n → ℝ) (i : Fin n) : (riskSet T i).Nonempty :=
  ⟨i, mem_riskSet T i⟩

private lemma sum_pos_exp (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) :
    0 < ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) :=
  sum_pos (fun _ _ => exp_pos _) (riskSet_nonempty T i)

/-- Cox's partial likelihood `∏_{i : δᵢ} exp ⟪β, xᵢ⟫ / ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫`. -/
noncomputable def partialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) : ℝ :=
  ∏ i with δ i = true, exp (β ⬝ᵥ x i) / ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)

/-- The log partial likelihood `∑_{i : δᵢ} (⟪β, xᵢ⟫ - log ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫)`. -/
noncomputable def logPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i with δ i = true, (β ⬝ᵥ x i - log (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)))

/-- The logarithm of the partial likelihood is the log partial likelihood. -/
theorem log_partialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) : log (partialLikelihood T δ x β) = logPartialLikelihood T δ x β := by
  rw [partialLikelihood, logPartialLikelihood, log_prod]
  · refine sum_congr rfl fun i _ => ?_
    rw [log_div (exp_pos _).ne' (sum_pos_exp T x β i).ne', log_exp]
  · exact fun i _ => (div_pos (exp_pos _) (sum_pos_exp T x β i)).ne'

/-- Log-sum-exp is convex: `log ∑ exp (a u + b v) ≤ a log ∑ exp u + b log ∑ exp v`. -/
private lemma log_sum_exp_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (u v : ι → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    log (∑ l ∈ s, exp (a * u l + b * v l)) ≤
      a * log (∑ l ∈ s, exp (u l)) + b * log (∑ l ∈ s, exp (v l)) := by
  set X := ∑ l ∈ s, exp (u l)
  set Y := ∑ l ∈ s, exp (v l)
  have hX : 0 < X := sum_pos (fun _ _ => exp_pos _) hs
  have hY : 0 < Y := sum_pos (fun _ _ => exp_pos _) hs
  have hnorm : ∀ (w : ι → ℝ) (Z : ℝ), 0 < Z → Z = ∑ l ∈ s, exp (w l) →
      ∑ l ∈ s, exp (w l - log Z) = 1 := fun w Z hZ hZw => by
    simp_rw [exp_sub, exp_log hZ, ← Finset.sum_div, ← hZw, div_self hZ.ne']
  have key : ∑ l ∈ s, exp (a * u l + b * v l) ≤ exp (a * log X + b * log Y) := by
    calc ∑ l ∈ s, exp (a * u l + b * v l)
        = ∑ l ∈ s, exp (a * log X + b * log Y) *
            exp (a * (u l - log X) + b * (v l - log Y)) := by
          refine sum_congr rfl fun l _ => ?_
          rw [← exp_add]; ring_nf
      _ ≤ ∑ l ∈ s, exp (a * log X + b * log Y) *
            (a * exp (u l - log X) + b * exp (v l - log Y)) := by
          refine sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          simpa [smul_eq_mul] using
            convexOn_exp.2 (Set.mem_univ (u l - log X)) (Set.mem_univ (v l - log Y)) ha hb hab
      _ = exp (a * log X + b * log Y) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum, hnorm u X hX rfl,
            hnorm v Y hY rfl, mul_one, mul_one, hab, mul_one]
  calc log (∑ l ∈ s, exp (a * u l + b * v l)) ≤ log (exp (a * log X + b * log Y)) :=
        log_le_log (sum_pos (fun _ _ => exp_pos _) hs) key
    _ = _ := log_exp _

/-- **Concavity of the Cox log partial likelihood** on `ℝᵖ`. -/
theorem concaveOn_logPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) : ConcaveOn ℝ Set.univ (logPartialLikelihood T δ x) := by
  refine ⟨convex_univ, fun β _ γ _ a b ha hb hab => ?_⟩
  simp only [logPartialLikelihood, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have h := log_sum_exp_le (riskSet_nonempty T i) (fun l => β ⬝ᵥ x l) (fun l => γ ⬝ᵥ x l)
    ha hb hab
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  linarith

/-- The `exp (b z)`-weighted mean of a scalar covariate `z` over the risk set of subject `i`. -/
noncomputable def riskMean (T : Fin n → ℝ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n) : ℝ :=
  (∑ l ∈ riskSet T i, z l * exp (b * z l)) / ∑ l ∈ riskSet T i, exp (b * z l)

/-- The `exp (b z)`-weighted variance of a scalar covariate over the risk set of subject `i`. -/
noncomputable def riskVar (T : Fin n → ℝ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n) : ℝ :=
  (∑ l ∈ riskSet T i, z l ^ 2 * exp (b * z l)) / (∑ l ∈ riskSet T i, exp (b * z l)) -
    riskMean T z b i ^ 2

/-- The Cox score for a scalar covariate: `∑_{i : δᵢ} (zᵢ - z̄ᵢ(b))`. -/
noncomputable def coxScore (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∑ i with δ i = true, (z i - riskMean T z b i)

/-- The Cox observed information for a scalar covariate: `∑_{i : δᵢ} Varᵢ(b)`. -/
noncomputable def coxInformation (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ) :
    ℝ :=
  ∑ i with δ i = true, riskVar T z b i

/-- The log partial likelihood of a scalar covariate `z` as a function of `b ∈ ℝ`. -/
noncomputable def logPartialLikelihood₁ (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ)
    (b : ℝ) : ℝ :=
  logPartialLikelihood T δ (fun i _ => z i) (fun _ : Fin 1 => b)

private lemma hasDerivAt_sum_exp (s : Finset (Fin n)) (z w : Fin n → ℝ) (b : ℝ) :
    HasDerivAt (fun b => ∑ l ∈ s, w l * exp (b * z l)) (∑ l ∈ s, w l * z l * exp (b * z l)) b := by
  refine HasDerivAt.fun_sum fun l _ => ?_
  convert ((hasDerivAt_mul_const (z l)).exp).const_mul (w l) using 1
  ring

private lemma sum_pos_exp₁ (T : Fin n → ℝ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    0 < ∑ l ∈ riskSet T i, exp (b * z l) :=
  sum_pos (fun _ _ => exp_pos _) (riskSet_nonempty T i)

/-- The derivative of the scalar log partial likelihood is the Cox score. -/
theorem hasDerivAt_logPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ)
    (b : ℝ) : HasDerivAt (logPartialLikelihood₁ T δ z) (coxScore T δ z b) b := by
  have hfun : logPartialLikelihood₁ T δ z = fun b => ∑ i with δ i = true,
      (b * z i - log (∑ l ∈ riskSet T i, exp (b * z l))) := by
    funext b
    simp [logPartialLikelihood₁, logPartialLikelihood, dotProduct]
  rw [hfun, coxScore]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hS := hasDerivAt_sum_exp (riskSet T i) z (fun _ => 1) b
  simp only [one_mul] at hS
  convert (hasDerivAt_mul_const (z i)).fun_sub (hS.log (sum_pos_exp₁ T z b i).ne') using 1
  simp [riskMean]

/-- The derivative of the Cox score is minus the observed information. -/
theorem hasDerivAt_coxScore (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ) :
    HasDerivAt (coxScore T δ z) (-coxInformation T δ z b) b := by
  unfold coxScore coxInformation
  rw [← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hS := hasDerivAt_sum_exp (riskSet T i) z (fun _ => 1) b
  have hN := hasDerivAt_sum_exp (riskSet T i) z z b
  simp only [one_mul] at hS
  simp only [← sq] at hN
  have hpos := sum_pos_exp₁ T z b i
  convert (hasDerivAt_const b (z i)).fun_sub (hN.fun_div hS hpos.ne') using 1
  · rfl
  · have hc : ∀ x, exp (z x * b) = exp (b * z x) := fun x => by rw [mul_comm]
    unfold riskVar riskMean
    field_simp
    simp only [hc]
    ring

/-- The number at risk at the time of subject `i`. -/
noncomputable def numAtRisk (T : Fin n → ℝ) (i : Fin n) : ℕ := #(riskSet T i)

/-- The number of group-1 subjects at risk at the time of subject `i`. -/
noncomputable def numAtRiskIn (T : Fin n → ℝ) (g : Fin n → Bool) (i : Fin n) : ℕ :=
  #{l ∈ riskSet T i | g l = true}

/-- The group indicator `zᵢ = 1` for group 1 (`g i = true`) and `0` otherwise. -/
def groupIndicator (g : Fin n → Bool) (i : Fin n) : ℝ := if g i = true then 1 else 0

/-- The log-rank numerator `O - E`: observed minus expected group-1 events,
`∑_{i : δᵢ} (zᵢ - n₁(Tᵢ) / n(Tᵢ))`. -/
noncomputable def observedMinusExpected (T : Fin n → ℝ) (δ : Fin n → Bool) (g : Fin n → Bool) :
    ℝ :=
  ∑ i with δ i = true, (groupIndicator g i - (numAtRiskIn T g i : ℝ) / numAtRisk T i)

/-- The Breslow (Cox) information `∑_{i : δᵢ} n₁ n₀ / n²` at the risk sets of the events.
This is `-ℓ''(0)` for a group indicator, not the tied log-rank variance: for one tied
risk set with `n = 4`, `n₁ = 2` and `d = 2` events it gives `1 / 2`, while the
hypergeometric log-rank variance is `1 / 3`. It equals the log-rank variance only when
the event times are distinct (so each risk set contributes at most one event). -/
noncomputable def breslowInformation (T : Fin n → ℝ) (δ : Fin n → Bool) (g : Fin n → Bool) :
    ℝ :=
  ∑ i with δ i = true,
    (numAtRiskIn T g i : ℝ) * ((numAtRisk T i : ℝ) - numAtRiskIn T g i) / (numAtRisk T i) ^ 2

/-- **The log-rank statistic is the Cox score at `β = 0`**: `ℓ'(0) = O - E`. -/
theorem coxScore_zero (T : Fin n → ℝ) (δ : Fin n → Bool) (g : Fin n → Bool) :
    coxScore T δ (groupIndicator g) 0 = observedMinusExpected T δ g := by
  refine sum_congr rfl fun i _ => ?_
  simp [riskMean, numAtRiskIn, numAtRisk, groupIndicator, sum_boole]

/-- **The Cox information at `β = 0` is the Breslow information** `∑ n₁ n₀ / n²`
(not the tied log-rank variance; see `breslowInformation`). -/
theorem coxInformation_zero (T : Fin n → ℝ) (δ : Fin n → Bool) (g : Fin n → Bool) :
    coxInformation T δ (groupIndicator g) 0 = breslowInformation T δ g := by
  refine sum_congr rfl fun i _ => ?_
  have hn : (0 : ℝ) < #(riskSet T i) := by exact_mod_cast (riskSet_nonempty T i).card_pos
  have hsq : ∀ l, groupIndicator g l ^ 2 = groupIndicator g l := fun l => by
    unfold groupIndicator; split_ifs <;> norm_num
  simp only [riskVar, riskMean, zero_mul, exp_zero, mul_one, hsq]
  simp only [sum_const, nsmul_eq_mul, groupIndicator, sum_boole, numAtRiskIn, numAtRisk]
  field_simp

/-! ### The vector score: gradient of the log partial likelihood -/

/-- The `exp ⟪β, x⟫`-weighted mean covariate vector over the risk set of subject `i`,
`x̄ᵢ(β) = (∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫ x_l) / ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l⟫`. -/
noncomputable def riskMeanVec (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ)
    (i : Fin n) : Fin p → ℝ :=
  (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l))⁻¹ • ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) • x l

/-- Component `j` of the weighted mean vector is the `exp ⟪β, x⟫`-weighted mean of the `j`-th
covariate over the risk set. -/
theorem riskMeanVec_apply (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n)
    (j : Fin p) :
    riskMeanVec T x β i j =
      (∑ l ∈ riskSet T i, x l j * exp (β ⬝ᵥ x l)) / ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) := by
  simp only [riskMeanVec, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [inv_mul_eq_div]
  simp_rw [mul_comm (exp _)]

/-- Along a coordinate axis, `β = b eⱼ`, component `j` of the weighted mean vector is the scalar
weighted mean `riskMean` of the `j`-th covariate at `b`. -/
theorem riskMeanVec_single_apply (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (j : Fin p) (b : ℝ)
    (i : Fin n) :
    riskMeanVec T x (Pi.single j b) i j = riskMean T (fun l => x l j) b i := by
  simp [riskMeanVec_apply, riskMean, single_dotProduct]

/-- The Cox score vector `∑_{i : δᵢ} (xᵢ - x̄ᵢ(β))`. -/
noncomputable def coxGradient (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (β : Fin p → ℝ) : Fin p → ℝ :=
  ∑ i with δ i = true, (x i - riskMeanVec T x β i)

/-- For one covariate (`p = 1`) the score vector has the scalar Cox score `coxScore` as its
single component. -/
theorem coxGradient_one (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ) :
    coxGradient T δ (fun i (_ : Fin 1) => z i) (fun _ => b) = fun _ => coxScore T δ z b := by
  funext j
  have hj : (fun _ : Fin 1 => b) = Pi.single j b := by
    funext k; rw [Subsingleton.elim k j, Pi.single_eq_same]
  simp only [coxGradient, coxScore, Finset.sum_apply, Pi.sub_apply, hj]
  exact sum_congr rfl fun i _ => by rw [riskMeanVec_single_apply]

/-- The continuous linear functional `w ↦ ⟪v, w⟫` on `Fin p → ℝ`. -/
private noncomputable def dotCLM (v : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ j, v j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) j

private lemma dotCLM_apply (v w : Fin p → ℝ) : dotCLM v w = v ⬝ᵥ w := by
  simp [dotCLM, dotProduct]

private lemma hasFDerivAt_dotProduct (v β : Fin p → ℝ) :
    HasFDerivAt (fun β => β ⬝ᵥ v) (dotCLM v) β := by
  have h : (fun β => β ⬝ᵥ v) = dotCLM v := funext fun β => by
    rw [dotCLM_apply, dotProduct_comm]
  rw [h]
  exact (dotCLM v).hasFDerivAt

private lemma hasFDerivAt_logSumExp (s : Finset (Fin n)) (hs : s.Nonempty)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    HasFDerivAt (fun β => log (∑ l ∈ s, exp (β ⬝ᵥ x l)))
      (dotCLM ((∑ l ∈ s, exp (β ⬝ᵥ x l))⁻¹ • ∑ l ∈ s, exp (β ⬝ᵥ x l) • x l)) β := by
  have hS : HasFDerivAt (fun β => ∑ l ∈ s, exp (β ⬝ᵥ x l))
      (∑ l ∈ s, exp (β ⬝ᵥ x l) • dotCLM (x l)) β :=
    HasFDerivAt.fun_sum fun l _ => (hasFDerivAt_dotProduct (x l) β).exp
  convert hS.log (sum_pos (fun l _ => exp_pos (β ⬝ᵥ x l)) hs).ne' using 1
  ext v
  simp [dotCLM_apply, smul_dotProduct, sum_dotProduct]

/-- The Fréchet derivative of the Cox log partial likelihood at `β` is `v ↦ ⟪U(β), v⟫`, written
as `∑ⱼ U(β)ⱼ • projⱼ`, where `U = coxGradient` is the Cox score vector. -/
theorem hasFDerivAt_logPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    HasFDerivAt (logPartialLikelihood T δ x)
      (∑ j, coxGradient T δ x β j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j) β := by
  change HasFDerivAt _ (dotCLM (coxGradient T δ x β)) β
  have h : HasFDerivAt (logPartialLikelihood T δ x)
      (∑ i with δ i = true, (dotCLM (x i) - dotCLM (riskMeanVec T x β i))) β := by
    unfold logPartialLikelihood
    exact HasFDerivAt.fun_sum fun i _ =>
      (hasFDerivAt_dotProduct (x i) β).sub (hasFDerivAt_logSumExp _ (riskSet_nonempty T i) x β)
  convert h using 1
  ext v
  simp [dotCLM_apply, coxGradient, sum_dotProduct, sub_dotProduct]

/-- **The Cox score vector is the gradient of the log partial likelihood.** The gradient needs an
inner product, which `Fin p → ℝ` (sup norm) lacks, so the statement transports `ℓ` to Euclidean
space `EuclideanSpace ℝ (Fin p)` along `WithLp.ofLp`. -/
theorem hasGradientAt_logPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ (Fin p) => logPartialLikelihood T δ x b.ofLp)
      (WithLp.toLp 2 (coxGradient T δ x β)) (WithLp.toLp 2 β) := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine ((hasFDerivAt_logPartialLikelihood T δ x β).comp (WithLp.toLp 2 β)
    (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (WithLp.toLp 2 β))).congr_fderiv ?_
  ext v
  simp [PiLp.inner_apply, mul_comm]

/-! ### The Hessian quadratic form -/

/-- The `exp ⟪β, x⟫`-weighted variance of the linear covariate `⟪x, u⟫` over the risk set of
subject `i`. -/
noncomputable def riskVarAlong (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β u : Fin p → ℝ)
    (i : Fin n) : ℝ :=
  (∑ l ∈ riskSet T i, (x l ⬝ᵥ u) ^ 2 * exp (β ⬝ᵥ x l)) / (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l)) -
    (riskMeanVec T x β i ⬝ᵥ u) ^ 2

private lemma riskMeanVec_dotProduct (T : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β u : Fin p → ℝ)
    (i : Fin n) :
    riskMeanVec T x β i ⬝ᵥ u =
      (∑ l ∈ riskSet T i, (x l ⬝ᵥ u) * exp (β ⬝ᵥ x l)) / ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l) := by
  simp only [riskMeanVec, smul_dotProduct, sum_dotProduct, smul_eq_mul]
  rw [inv_mul_eq_div]
  simp_rw [mul_comm (exp _)]

private lemma hasDerivAt_sum_exp_add (s : Finset (Fin n)) (a z w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ l ∈ s, w l * exp (a l + t * z l))
      (∑ l ∈ s, w l * z l * exp (a l + t * z l)) t := by
  refine HasDerivAt.fun_sum fun l _ => ?_
  convert (((hasDerivAt_mul_const (z l)).const_add (a l)).exp).const_mul (w l) using 1
  ring

/-- **The Hessian quadratic form of the Cox log partial likelihood is minus the observed
information along `u`**: the derivative at `t = 0` of `t ↦ ⟪U(β + t u), u⟫` is
`-∑_{i : δᵢ} Varᵢ(⟪x, u⟫)`, the weighted variances being taken at `β`. -/
theorem hasDerivAt_coxGradient_dotProduct (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (β u : Fin p → ℝ) :
    HasDerivAt (fun t : ℝ => coxGradient T δ x (β + t • u) ⬝ᵥ u)
      (-∑ i with δ i = true, riskVarAlong T x β u i) 0 := by
  set a : Fin n → ℝ := fun l => β ⬝ᵥ x l
  set z : Fin n → ℝ := fun l => x l ⬝ᵥ u
  have hdot : ∀ (t : ℝ) (l : Fin n), (β + t • u) ⬝ᵥ x l = a l + t * z l := fun t l => by
    simp [a, z, add_dotProduct, smul_dotProduct, dotProduct_comm u]
  have hfun : (fun t : ℝ => coxGradient T δ x (β + t • u) ⬝ᵥ u) = fun t => ∑ i with δ i = true,
      (z i - (∑ l ∈ riskSet T i, z l * exp (a l + t * z l)) /
        ∑ l ∈ riskSet T i, 1 * exp (a l + t * z l)) := by
    funext t
    simp only [coxGradient, sum_dotProduct, sub_dotProduct, riskMeanVec_dotProduct, hdot,
      one_mul]
    rfl
  rw [hfun, ← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hN := hasDerivAt_sum_exp_add (riskSet T i) a z z 0
  have hD := hasDerivAt_sum_exp_add (riskSet T i) a z (fun _ => 1) 0
  have hpos : (∑ l ∈ riskSet T i, 1 * exp (a l + 0 * z l)) ≠ 0 :=
    (sum_pos (fun l _ => by positivity) (riskSet_nonempty T i)).ne'
  convert (hasDerivAt_const (0 : ℝ) (z i)).fun_sub (hN.fun_div hD hpos) using 1
  have hZ : (∑ l ∈ riskSet T i, exp (a l)) ≠ 0 :=
    (sum_pos (fun l _ => exp_pos (a l)) (riskSet_nonempty T i)).ne'
  simp only [riskVarAlong, riskMeanVec_dotProduct, zero_mul, add_zero, one_mul, a, z] at hZ ⊢
  field_simp
  ring

/-- For one covariate (`p = 1`) and the unit direction, the directional variance is the scalar
weighted variance `riskVar`. -/
theorem riskVarAlong_one (T : Fin n → ℝ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    riskVarAlong T (fun i (_ : Fin 1) => z i) (fun _ => b) (fun _ => 1) i = riskVar T z b i := by
  simp [riskVarAlong, riskVar, riskMean, riskMeanVec_apply, dotProduct, mul_comm b]

end MathlibExt.Probability.Statistics.CoxPartialLikelihood
