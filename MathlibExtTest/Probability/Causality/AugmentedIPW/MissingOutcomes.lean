/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.MissingOutcomes

/-!
# Tests for AIPW with missing outcomes

* Smoke test of the API: the score off and on the response event, and its dependence on the
  outcome through responders only.
* A finite example under MAR (`Ω = Bool × Bool × Bool`, points `(x, r, y)`, eight weighted
  points): the response propensity depends on the covariate, so the complete-case mean is biased.
  The AIPW score is computed explicitly and is unbiased with a correct propensity and a wrong
  regression, and with a correct regression and a wrong propensity; the same values follow from
  the theorems. With both nuisances wrong it is biased.
* The average treatment effect on the same space, with `R` as the treatment, control outcome
  `Y` and treated outcome `Yt = 2Y + 1` (ATE `3/2`, asymmetric arms): the ATE score is computed
  explicitly in the propensity branch (wrong, distinct constant regressions) and the regression
  branch (wrong propensity `1/3`), and both values also follow from `integral_aipwATEScore`.
  Swapping the two correct regressions under the wrong propensity gives a biased value.
* An MNAR counterexample: responders are exactly the units with `Y = 1`. Positivity holds and
  both nuisances are correct, yet the score has mean `1` while `E[Y] = 1/2`; MAR fails.
* A positivity boundary case: nobody responds. MAR holds, the propensity `0` is correct, and
  the score with a wrong regression is biased.
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingOutcomes

namespace MathlibExtTest.Probability.Causality.AugmentedIPW

/-! ### Smoke test -/

/-- Off the response event the score is the regression value. -/
example (X : Bool → Unit) (π m : Unit → ℝ) (Y : Bool → ℝ) :
    aipwScore {true} X π m Y false = m (X false) := by
  simp [aipwScore]

/-- On the response event the score is the inverse-propensity-corrected residual. -/
example (X : Bool → Unit) (π m : Unit → ℝ) (Y : Bool → ℝ) :
    aipwScore {true} X π m Y true = m (X true) + (Y true - m (X true)) / π (X true) := by
  simp [aipwScore]

/-- The score ignores the outcome of nonresponders. -/
example (X : Bool → Unit) (π m : Unit → ℝ) :
    aipwScore {true} X π m (fun b => if b then 1 else 7) =
      aipwScore {true} X π m (fun b => if b then 1 else -3) :=
  aipwScore_congr fun b hb => by simp_all

/-! ### Finite measures with explicit weights -/

/-- The measure with nonnegative weight `w a` at each point `a`. -/
noncomputable def wmeas {α : Type*} [Fintype α] [MeasurableSpace α] (w : α → ℝ) : Measure α :=
  ∑ a, ENNReal.ofReal (w a) • Measure.dirac a

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

instance (w : α → ℝ) : IsFiniteMeasure (wmeas w) := by
  constructor
  simp [wmeas, ENNReal.sum_lt_top]

lemma wmeas_real {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (S : Set α) :
    (wmeas w).real S = ∑ a, S.indicator w a := by
  classical
  rw [measureReal_def, wmeas, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a ∈ S <;> simp [h, Measure.dirac_apply, hw a]

lemma isProbabilityMeasure_wmeas {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1) :
    IsProbabilityMeasure (wmeas w) := by
  constructor
  have h := wmeas_real hw Set.univ
  simp only [Set.indicator_univ, h1, measureReal_def] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

lemma integral_wmeas {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (f : α → ℝ) :
    ∫ a, f a ∂(wmeas w) = ∑ a, w a * f a := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wmeas_real hw, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single a (fun b _ hb => Set.indicator_of_notMem (by simpa using hb) _)
    (by simp)]
  simp

/-! ### A finite example under MAR -/

/-- A point is `(x, r, y)`: covariate, response, outcome bit. -/
abbrev Pt := Bool × Bool × Bool

/-- Weights: `P(X = x) = 1/2`; `P(R | X = false) = 1/2`, `P(R | X = true) = 3/4`;
`P(Y = 1 | X = false) = 1/4`, `P(Y = 1 | X = true) = 3/4`; `R ⊥ Y | X`. -/
noncomputable def w : Pt → ℝ
  | (false, _, true) => 4 / 64
  | (false, _, false) => 12 / 64
  | (true, true, true) => 18 / 64
  | (true, true, false) => 6 / 64
  | (true, false, true) => 6 / 64
  | (true, false, false) => 2 / 64

lemma w_nonneg (p : Pt) : 0 ≤ w p := by
  obtain ⟨x, r, y⟩ := p
  cases x <;> cases r <;> cases y <;> norm_num [w]

/-- The probability measure of the example. -/
noncomputable abbrev μ : Measure Pt := wmeas w

/-- The covariate. -/
def X (p : Pt) : Bool := p.1

/-- The response event. -/
def R : Set Pt := {p | p.2.1 = true}

/-- The outcome. -/
def Y (p : Pt) : ℝ := if p.2.2 then 1 else 0

lemma sum_pt (f : Pt → ℝ) :
    ∑ p, f p = f (false, false, false) + f (false, false, true) + f (false, true, false) +
      f (false, true, true) + f (true, false, false) + f (true, false, true) +
      f (true, true, false) + f (true, true, true) := by
  simp [Fintype.sum_prod_type]
  ring

instance : IsProbabilityMeasure μ :=
  isProbabilityMeasure_wmeas w_nonneg (by rw [sum_pt]; norm_num [w])

lemma μ_real (S : Set Pt) : μ.real S = ∑ p, S.indicator w p := wmeas_real w_nonneg S

lemma integral_μ (f : Pt → ℝ) : ∫ p, f p ∂μ = ∑ p, w p * f p := integral_wmeas w_nonneg f

lemma hR : MeasurableSet R := (Set.toFinite R).measurableSet

lemma hX : Measurable X := measurable_of_countable X

lemma hY : Measurable Y := measurable_of_countable Y

/-- The outcome mean is `1/2`. -/
lemma integral_Y : ∫ p, Y p ∂μ = 1 / 2 := by
  rw [integral_μ, sum_pt]; norm_num [w, Y]

/-- The complete-case mean `E[Y | R] = 11/20` is biased: responders over-represent `X = true`. -/
example : (∫ p, R.indicator Y p ∂μ) / μ.real R = 11 / 20 := by
  rw [integral_μ, μ_real, sum_pt, sum_pt]; norm_num [w, Y, R]

/-- MAR holds. -/
lemma mar : MissingAtRandom μ R Y X := by
  intro B _ x
  simp only [μ_real, sum_pt]
  by_cases h0 : (0 : ℝ) ∈ B <;> by_cases h1 : (1 : ℝ) ∈ B <;> cases x <;>
    simp [Set.indicator, R, X, Y, h0, h1, w] <;> norm_num

lemma propensity_eq (x : Bool) : propensity μ R X x = if x then 3 / 4 else 1 / 2 := by
  cases x <;> simp only [propensity, μ_real, sum_pt] <;>
    simp [Set.indicator, R, X, w] <;> norm_num

lemma regression_eq (x : Bool) : outcomeRegression μ Y X x = if x then 3 / 4 else 1 / 4 := by
  rw [outcomeRegression, ← integral_indicator (hX (measurableSet_singleton _)), integral_μ,
    μ_real, sum_pt, sum_pt]
  cases x <;> simp [Set.indicator, X, Y, w] <;> norm_num

lemma pos : ResponsePositivity μ R X :=
  ⟨1 / 2, by norm_num, fun x _ => by cases x <;> norm_num [propensity_eq]⟩

/-- Correct propensity, wrong regression `m = 0`: the score `1_R Y / π(X)`, computed point by
point, has mean `1/2 = E[Y]`. -/
example : ∫ p, aipwScore R X (fun x => if x then 3 / 4 else 1 / 2) (fun _ => 0) Y p ∂μ =
    1 / 2 := by
  rw [integral_μ, sum_pt]; norm_num [aipwScore, w, Y, R, X, Set.indicator]

/-- The same value from the propensity branch of double robustness. -/
example : ∫ p, aipwScore R X (fun x => if x then 3 / 4 else 1 / 2) (fun _ => 0) Y p ∂μ =
    1 / 2 := by
  rw [integral_aipwScore_of_propensity hR hX hY Integrable.of_finite mar pos _
    fun x _ => (propensity_eq x).symm, integral_Y]

/-- Correct regression, wrong propensity `π = 1` (no reweighting): the score, computed point by
point, has mean `1/2 = E[Y]`. -/
example : ∫ p, aipwScore R X (fun _ => 1) (fun x => if x then 3 / 4 else 1 / 4) Y p ∂μ =
    1 / 2 := by
  rw [integral_μ, sum_pt]; norm_num [aipwScore, w, Y, R, X, Set.indicator]

/-- The same value from the regression branch of double robustness. -/
example : ∫ p, aipwScore R X (fun _ => 1) (fun x => if x then 3 / 4 else 1 / 4) Y p ∂μ =
    1 / 2 := by
  rw [integral_aipwScore_of_regression hR hX hY Integrable.of_finite mar _
    fun x _ => (regression_eq x).symm, integral_Y]

/-- Both nuisances wrong (`π = 1`, `m = 0`, the complete-case sum `E[1_R Y]`): biased. -/
example : ∫ p, aipwScore R X (fun _ => 1) (fun _ => 0) Y p ∂μ = 11 / 32 := by
  rw [integral_μ, sum_pt]; norm_num [aipwScore, w, Y, R, X, Set.indicator]

/-- The same value from the exact-bias identity, where the bias is nonzero:
`E[Y] + (1/2 - 1)(1/8) + (3/4 - 1)(3/8) = 1/2 - 5/32 = 11/32`. -/
example : ∫ p, aipwScore R X (fun _ => 1) (fun _ => 0) Y p ∂μ = 1 / 2 - 5 / 32 := by
  rw [(integral_aipwScore_eq hR hX hY Integrable.of_finite mar _ _).2, integral_Y,
    Fintype.sum_bool, ← integral_indicator (hX (measurableSet_singleton true)),
    ← integral_indicator (hX (measurableSet_singleton false)), integral_μ, integral_μ, sum_pt,
    sum_pt]
  simp only [propensity_eq]
  norm_num [Set.indicator, X, Y, w]

/-! ### Average treatment effect -/

/-- The treated potential outcome; the control potential outcome is `Y`. -/
def Yt (p : Pt) : ℝ := if p.2.2 then 3 else 1

lemma hYt : Measurable Yt := measurable_of_countable Yt

lemma integral_Yt : ∫ p, Yt p ∂μ = 2 := by
  rw [integral_μ, sum_pt]; norm_num [w, Yt]

/-- The ATE is `E[Yt - Y] = 2 - 1/2 = 3/2`. -/
lemma ate_eq : ∫ p, (Yt p - Y p) ∂μ = 3 / 2 := by
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_Yt, integral_Y]
  norm_num

lemma regressionT_eq (x : Bool) : outcomeRegression μ Yt X x = if x then 5 / 2 else 3 / 2 := by
  rw [outcomeRegression, ← integral_indicator (hX (measurableSet_singleton _)), integral_μ,
    μ_real, sum_pt, sum_pt]
  cases x <;> simp [Set.indicator, X, Yt, w] <;> norm_num

/-- Strong ignorability of the treatment `R` given `X` for the pair `(Y, Yt)`. -/
lemma ign : StronglyIgnorable μ R (fun p => (Y p, Yt p)) X := by
  refine ⟨fun B _ x => ?_, fun x _ => ?_⟩
  · simp only [μ_real, sum_pt]
    by_cases h0 : ((0 : ℝ), (1 : ℝ)) ∈ B <;> by_cases h1 : ((1 : ℝ), (3 : ℝ)) ∈ B <;>
      cases x <;> simp [Set.indicator, R, X, Y, Yt, h0, h1, w] <;> norm_num
  · cases x <;> norm_num [propensity_eq]

/-- Propensity branch, computed point by point: correct `e`, wrong and distinct regressions
`m₀ = 5`, `m₁ = -2`. -/
example : ∫ p, aipwATEScore R X (fun x => if x then 3 / 4 else 1 / 2) (fun _ => 5) (fun _ => -2)
    (observed R Y Yt) p ∂μ = 3 / 2 := by
  rw [integral_μ, sum_pt]
  norm_num [aipwATEScore, aipwScore, observed, w, Y, Yt, R, X, Set.indicator]

/-- The same value from the propensity branch of `integral_aipwATEScore`. -/
example : ∫ p, aipwATEScore R X (fun x => if x then 3 / 4 else 1 / 2) (fun _ => 5) (fun _ => -2)
    (observed R Y Yt) p ∂μ = 3 / 2 := by
  rw [integral_aipwATEScore hR hX hY hYt Integrable.of_finite Integrable.of_finite ign _ _ _
    (Or.inl fun x _ => (propensity_eq x).symm), ate_eq]

/-- Regression branch, computed point by point: wrong propensity `e = 1/3`, correct regressions
`m₀ = E[Y | X]`, `m₁ = E[Yt | X]`. -/
example : ∫ p, aipwATEScore R X (fun _ => 1 / 3) (fun x => if x then 3 / 4 else 1 / 4)
    (fun x => if x then 5 / 2 else 3 / 2) (observed R Y Yt) p ∂μ = 3 / 2 := by
  rw [integral_μ, sum_pt]
  norm_num [aipwATEScore, aipwScore, observed, w, Y, Yt, R, X, Set.indicator]

/-- The same value from the regression branch of `integral_aipwATEScore`. -/
example : ∫ p, aipwATEScore R X (fun _ => 1 / 3) (fun x => if x then 3 / 4 else 1 / 4)
    (fun x => if x then 5 / 2 else 3 / 2) (observed R Y Yt) p ∂μ = 3 / 2 := by
  rw [integral_aipwATEScore hR hX hY hYt Integrable.of_finite Integrable.of_finite ign _ _ _
    (Or.inr ⟨fun x _ => (regression_eq x).symm, fun x _ => (regressionT_eq x).symm⟩), ate_eq]

/-- Swapping the two correct regressions under the wrong propensity is biased: the arms are
not interchangeable. -/
example : ∫ p, aipwATEScore R X (fun _ => 1 / 3) (fun x => if x then 5 / 2 else 3 / 2)
    (fun x => if x then 3 / 4 else 1 / 4) (observed R Y Yt) p ∂μ ≠ 3 / 2 := by
  rw [integral_μ, sum_pt]
  norm_num [aipwATEScore, aipwScore, observed, w, Y, Yt, R, X, Set.indicator]

/-! ### MNAR counterexample: MAR is needed -/

/-- A fair coin for the outcome bit; the covariate is constant. -/
noncomputable abbrev ν : Measure Bool := wmeas fun _ => 1 / 2

lemma ν_nonneg : ∀ b : Bool, (0 : ℝ) ≤ (fun _ => 1 / 2) b := fun _ => by norm_num

instance : IsProbabilityMeasure ν :=
  isProbabilityMeasure_wmeas ν_nonneg (by simp)

/-- The outcome bit. -/
def Yb (b : Bool) : ℝ := if b then 1 else 0

/-- The response propensity of `R = {Y = 1}` given the constant covariate is `1/2`. -/
lemma mnar_propensity : propensity ν {true} (fun _ => ()) () = 1 / 2 := by
  simp only [propensity, wmeas_real ν_nonneg]
  simp [Set.indicator]

/-- The regression `E[Y | X = ()] = 1/2`. -/
lemma mnar_regression : outcomeRegression ν Yb (fun _ => ()) () = 1 / 2 := by
  simp only [outcomeRegression, Set.preimage_const, Set.mem_singleton_iff, ↓reduceIte,
    Measure.restrict_univ, integral_wmeas ν_nonneg, wmeas_real ν_nonneg]
  simp [Yb]

/-- Missing not at random: responders are exactly the units with `Y = 1`. Positivity holds. -/
example : ¬ MissingAtRandom ν {true} Yb (fun _ => ()) := by
  intro h
  have := h {1} (measurableSet_singleton 1) ()
  simp only [Set.preimage_const, Set.mem_singleton_iff, ↓reduceIte, Set.inter_univ,
    wmeas_real ν_nonneg] at this
  simp [Set.indicator, Yb] at this

example : ResponsePositivity ν {true} (fun _ => ()) :=
  ⟨1 / 2, by norm_num, fun _ _ => by rw [mnar_propensity]⟩

/-- With both nuisances correct the score has mean `1`, while `E[Y] = 1/2`. -/
example : ∫ b, aipwScore {true} (fun _ => ()) (fun _ => 1 / 2) (fun _ => 1 / 2) Yb b ∂ν = 1 ∧
    ∫ b, Yb b ∂ν = 1 / 2 := by
  simp only [integral_wmeas ν_nonneg]
  constructor <;> norm_num [aipwScore, Yb]

/-- Both nuisances used above are the correct ones. -/
example : (fun _ : Unit => (1 / 2 : ℝ)) () = propensity ν {true} (fun _ => ()) () ∧
    (fun _ : Unit => (1 / 2 : ℝ)) () = outcomeRegression ν Yb (fun _ => ()) () :=
  ⟨mnar_propensity.symm, mnar_regression.symm⟩

/-! ### Positivity boundary: nobody responds -/

/-- With no responders MAR holds trivially. -/
lemma mar_empty : MissingAtRandom ν ∅ Yb (fun _ => ()) := by
  intro B _ _; simp

/-- Positivity fails: the response propensity is `0` on the only covariate value. -/
example : ¬ ResponsePositivity ν ∅ (fun _ => ()) := by
  rintro ⟨ε, hε, h⟩
  have hne : ν (Set.univ) ≠ 0 := by simp [wmeas]
  have := h () (by simpa using hne)
  simp [propensity] at this
  linarith

/-- The propensity `0` is correct, the regression `m = 0` is wrong, and the score has mean
`0 ≠ 1/2 = E[Y]`: the propensity branch needs positivity. Since `R = ∅`, the residual term is
never evaluated, so no division by `π = 0` takes place. -/
example : propensity ν ∅ (fun _ => ()) () = 0 ∧
    ∫ b, aipwScore ∅ (fun _ => ()) (fun _ => 0) (fun _ => 0) Yb b ∂ν = 0 := by
  constructor
  · simp [propensity]
  · simp [aipwScore]

end MathlibExtTest.Probability.Causality.AugmentedIPW
