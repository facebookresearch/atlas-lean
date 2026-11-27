/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ConditionalProbability

/-!
# Predictive parity versus error-rate balance

A binary classifier `Ŷ` of a binary label `Y` is assessed in a group through the joint law of
`(Y, Ŷ)` in that group, a probability measure `μ` on `Bool × Bool` (first coordinate the label,
second the prediction, `true` for `1`). This file defines the group's prevalence
`Pr(Y = 1)` and, as conditional probabilities (`ProbabilityTheory.cond`), its false-positive rate
`Pr(Ŷ = 1 | Y = 0)`, false-negative rate `Pr(Ŷ = 0 | Y = 1)` and positive predictive value
`Pr(Y = 1 | Ŷ = 1)`. Conditioning on an event of probability zero gives the zero measure, so a
rate whose conditioning event is null is `0`.

## Main definitions

* `prevalence μ`: the prevalence `Pr(Y = 1)`.
* `falsePositiveRate μ`, `falseNegativeRate μ`, `positivePredictiveValue μ`: the false-positive
  rate, the false-negative rate and the positive predictive value.

## Main statements

* `falsePositiveRate_eq_mul`: Chouldechova's identity
  `FPR = p / (1 - p) * (1 - PPV) / PPV * (1 - FNR)` when `0 < p < 1` and `PPV > 0`.
* `falseNegativeRate_eq_one_iff`: `FNR = 1` exactly when `PPV = 0`, when `p > 0` and the
  predicted-positive event has positive probability.
* `falseNegativeRate_eq_one_or_positivePredictiveValue_eq_one`: two groups with equal positive
  predictive values and different prevalences have equal false-positive and equal false-negative
  rates only if `FNR = 1` in both or `PPV = 1` in both.
* `falsePositiveRate_eq_zero_of_positivePredictiveValue_eq_one`: `PPV = 1` forces `FPR = 0`.
* `exists_positivePredictiveValue_eq_one`, `exists_positivePredictiveValue_eq_zero`: both
  exceptions occur for every prevalence `p ∈ (0, 1)`.
* `predictiveParity_errorRateBalance_tradeoff`: the statements above together.

The rates of a general population are those of the law of `(Y, Ŷ)`: for random variables
`Y Ŷ : Ω → Bool` on a probability space, `falsePositiveRate_map` and its companions identify the
rates of `μ.map fun ω ↦ (Y ω, Ŷ ω)` with the conditional probabilities computed in `μ`.

## References

* A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
  prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3, equation (2.6).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Fairness

open MeasureTheory ProbabilityTheory Set

/-- **Prevalence.** For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's `Bool × Bool`, with
`true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the second. The prevalence of
$\mu$ is the real number $\mu(\{Y = 1\})$, the mass of the event $\{Y = 1\}$, taken as $0$ when
that mass is infinite. When $\mu$ is a probability measure, the joint law of a binary label $Y$
and a binary prediction $\hat Y$ in a group, it is the prevalence $p = \Pr(Y = 1)$ of the group.

Source: A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3 (the recidivism
prevalence $P(Y = 1 \mid R = r)$ of group $r$). -/
noncomputable def prevalence (μ : Measure (Bool × Bool)) : ℝ :=
  μ.real {z | z.1 = true}

/-- **False-positive rate.** For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's
`Bool × Bool`, with `true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the
second. The false-positive rate of $\mu$ is the real number $\mu(\{\hat Y = 1\} \mid Y = 0)$, the
mass of $\{\hat Y = 1\}$ under the conditional measure
$\mu(\cdot \mid Y = 0) = \mu(\{Y = 0\})^{-1} \, \mu(\cdot \cap \{Y = 0\})$; that measure is zero,
and the rate $0$, when $\mu(\{Y = 0\})$ is $0$ or infinite. When $\mu$ is a probability measure,
the joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a group, the rate is
$\mathrm{FPR} = \Pr(\hat Y = 1 \mid Y = 0)$, which is $0$ when $\Pr(Y = 0) = 0$.

Source: A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 3,
equation (2.3). -/
noncomputable def falsePositiveRate (μ : Measure (Bool × Bool)) : ℝ :=
  (μ[|{z | z.1 = false}]).real {z | z.2 = true}

/-- **False-negative rate.** For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's
`Bool × Bool`, with `true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the
second. The false-negative rate of $\mu$ is the real number $\mu(\{\hat Y = 0\} \mid Y = 1)$, the
mass of $\{\hat Y = 0\}$ under the conditional measure
$\mu(\cdot \mid Y = 1) = \mu(\{Y = 1\})^{-1} \, \mu(\cdot \cap \{Y = 1\})$; that measure is zero,
and the rate $0$, when $\mu(\{Y = 1\})$ is $0$ or infinite. When $\mu$ is a probability measure,
the joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a group, the rate is
$\mathrm{FNR} = \Pr(\hat Y = 0 \mid Y = 1)$, which is $0$ when $\Pr(Y = 1) = 0$.

Source: A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 3,
equation (2.4). -/
noncomputable def falseNegativeRate (μ : Measure (Bool × Bool)) : ℝ :=
  (μ[|{z | z.1 = true}]).real {z | z.2 = false}

/-- **Positive predictive value.** For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's
`Bool × Bool`, with `true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the
second. The positive predictive value of $\mu$ is the real number
$\mu(\{Y = 1\} \mid \hat Y = 1)$, the mass of $\{Y = 1\}$ under the conditional measure
$\mu(\cdot \mid \hat Y = 1) = \mu(\{\hat Y = 1\})^{-1} \, \mu(\cdot \cap \{\hat Y = 1\})$; that
measure is zero, and the value $0$, when $\mu(\{\hat Y = 1\})$ is $0$ or infinite. When $\mu$ is a
probability measure, the joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a
group, the value is $\mathrm{PPV} = \Pr(Y = 1 \mid \hat Y = 1)$, which is $0$ when
$\Pr(\hat Y = 1) = 0$.

Source: A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 2,
equation (2.2) and the remark after it. -/
noncomputable def positivePredictiveValue (μ : Measure (Bool × Bool)) : ℝ :=
  (μ[|{z | z.2 = true}]).real {z | z.1 = true}

section Cells

variable (μ : Measure (Bool × Bool))

private lemma real_cond {α : Type*} [MeasurableSpace α] (ν : Measure α) {s : Set α}
    (hs : MeasurableSet s) (t : Set α) : (ν[|s]).real t = ν.real (s ∩ t) / ν.real s := by
  rw [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul,
    measureReal_def, measureReal_def]

private lemma measurableSet_bool_prod (s : Set (Bool × Bool)) : MeasurableSet s :=
  (Set.toFinite s).measurableSet

private lemma real_pair [IsFiniteMeasure μ] {s : Set (Bool × Bool)} {x y : Bool × Bool}
    (hxy : x ≠ y) (hs : s = ({x, y} : Finset (Bool × Bool))) :
    μ.real s = μ.real {x} + μ.real {y} := by
  rw [hs, ← sum_measureReal_singleton, Finset.sum_pair hxy]

lemma prevalence_eq [IsFiniteMeasure μ] :
    prevalence μ = μ.real {(true, true)} + μ.real {(true, false)} :=
  real_pair μ (by decide) (by ext ⟨x, y⟩; cases x <;> cases y <;> simp)

lemma measureReal_fst_eq_false [IsFiniteMeasure μ] :
    μ.real {z : Bool × Bool | z.1 = false} = μ.real {(false, true)} + μ.real {(false, false)} :=
  real_pair μ (by decide) (by ext ⟨x, y⟩; cases x <;> cases y <;> simp)

lemma measureReal_snd_eq_true [IsFiniteMeasure μ] :
    μ.real {z : Bool × Bool | z.2 = true} = μ.real {(true, true)} + μ.real {(false, true)} :=
  real_pair μ (by decide) (by ext ⟨x, y⟩; cases x <;> cases y <;> simp)

lemma measureReal_cells_sum [IsProbabilityMeasure μ] :
    μ.real {(true, true)} + μ.real {(false, true)} + μ.real {(true, false)} +
      μ.real {(false, false)} = 1 := by
  have h := sum_measureReal_singleton (μ := μ) Finset.univ
  rw [Finset.coe_univ, probReal_univ, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool] at h
  linarith

lemma falsePositiveRate_eq [IsFiniteMeasure μ] :
    falsePositiveRate μ =
      μ.real {(false, true)} / (μ.real {(false, true)} + μ.real {(false, false)}) := by
  rw [falsePositiveRate, real_cond μ (measurableSet_bool_prod _), ← measureReal_fst_eq_false]
  congr 2
  ext ⟨x, y⟩; cases x <;> cases y <;> simp

lemma falseNegativeRate_eq [IsFiniteMeasure μ] :
    falseNegativeRate μ =
      μ.real {(true, false)} / (μ.real {(true, true)} + μ.real {(true, false)}) := by
  rw [falseNegativeRate, real_cond μ (measurableSet_bool_prod _), ← prevalence_eq, prevalence]
  congr 2
  ext ⟨x, y⟩; cases x <;> cases y <;> simp

lemma positivePredictiveValue_eq [IsFiniteMeasure μ] :
    positivePredictiveValue μ =
      μ.real {(true, true)} / (μ.real {(true, true)} + μ.real {(false, true)}) := by
  rw [positivePredictiveValue, real_cond μ (measurableSet_bool_prod _),
    ← measureReal_snd_eq_true]
  congr 2
  ext ⟨x, y⟩; cases x <;> cases y <;> simp

lemma positivePredictiveValue_nonneg : 0 ≤ positivePredictiveValue μ :=
  measureReal_nonneg

end Cells

section Map

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Y Yhat : Ω → Bool}

private lemma real_map (hY : Measurable Y) (hYhat : Measurable Yhat) (s : Set (Bool × Bool)) :
    (μ.map fun ω ↦ (Y ω, Yhat ω)).real s = μ.real ((fun ω ↦ (Y ω, Yhat ω)) ⁻¹' s) :=
  map_measureReal_apply (hY.prodMk hYhat) (measurableSet_bool_prod s)

lemma prevalence_map (hY : Measurable Y) (hYhat : Measurable Yhat) :
    prevalence (μ.map fun ω ↦ (Y ω, Yhat ω)) = μ.real {ω | Y ω = true} :=
  real_map μ hY hYhat _

lemma falsePositiveRate_map (hY : Measurable Y) (hYhat : Measurable Yhat) :
    falsePositiveRate (μ.map fun ω ↦ (Y ω, Yhat ω)) =
      (μ[|{ω | Y ω = false}]).real {ω | Yhat ω = true} := by
  rw [falsePositiveRate, real_cond _ (measurableSet_bool_prod _), real_map μ hY hYhat,
    real_map μ hY hYhat, real_cond μ (s := {ω | Y ω = false}) (hY (measurableSet_singleton _))]
  rfl

lemma falseNegativeRate_map (hY : Measurable Y) (hYhat : Measurable Yhat) :
    falseNegativeRate (μ.map fun ω ↦ (Y ω, Yhat ω)) =
      (μ[|{ω | Y ω = true}]).real {ω | Yhat ω = false} := by
  rw [falseNegativeRate, real_cond _ (measurableSet_bool_prod _), real_map μ hY hYhat,
    real_map μ hY hYhat, real_cond μ (s := {ω | Y ω = true}) (hY (measurableSet_singleton _))]
  rfl

lemma positivePredictiveValue_map (hY : Measurable Y) (hYhat : Measurable Yhat) :
    positivePredictiveValue (μ.map fun ω ↦ (Y ω, Yhat ω)) =
      (μ[|{ω | Yhat ω = true}]).real {ω | Y ω = true} := by
  rw [positivePredictiveValue, real_cond _ (measurableSet_bool_prod _), real_map μ hY hYhat,
    real_map μ hY hYhat,
    real_cond μ (s := {ω | Yhat ω = true}) (hYhat (measurableSet_singleton _))]
  rfl

end Map

section Tradeoff

variable (μ ν : Measure (Bool × Bool))

theorem falsePositiveRate_eq_mul [IsProbabilityMeasure μ] (hp₀ : 0 < prevalence μ)
    (hp₁ : prevalence μ < 1) (hppv : 0 < positivePredictiveValue μ) :
    falsePositiveRate μ = prevalence μ / (1 - prevalence μ) *
      ((1 - positivePredictiveValue μ) / positivePredictiveValue μ) *
        (1 - falseNegativeRate μ) := by
  have hsum := measureReal_cells_sum μ
  rw [prevalence_eq] at hp₀ hp₁ ⊢
  rw [positivePredictiveValue_eq] at hppv ⊢
  rw [falsePositiveRate_eq, falseNegativeRate_eq]
  set a := μ.real {(true, true)}
  set b := μ.real {(false, true)}
  set c := μ.real {(true, false)}
  set d := μ.real {(false, false)}
  have ha : 0 ≤ a := measureReal_nonneg
  have hb : 0 ≤ b := measureReal_nonneg
  have hab : 0 < a + b := by
    by_contra h
    rw [show a + b = 0 by linarith, div_zero] at hppv
    exact lt_irrefl 0 hppv
  have ha' : 0 < a := by
    rcases ha.lt_or_eq with ha | ha
    · exact ha
    · rw [← ha, zero_div] at hppv; exact absurd hppv (lt_irrefl 0)
  have hbd : b + d = 1 - (a + c) := by linarith
  have hbd' : 0 < b + d := by linarith
  rw [← hbd]
  field_simp
  ring

theorem falseNegativeRate_eq_one_iff [IsFiniteMeasure μ] (hp₀ : 0 < prevalence μ)
    (hpos : 0 < μ.real {z | z.2 = true}) :
    falseNegativeRate μ = 1 ↔ positivePredictiveValue μ = 0 := by
  rw [prevalence_eq] at hp₀
  rw [measureReal_snd_eq_true] at hpos
  rw [falseNegativeRate_eq, positivePredictiveValue_eq, div_eq_one_iff_eq hp₀.ne',
    div_eq_zero_iff, or_iff_left hpos.ne']
  constructor <;> intro h <;> linarith

theorem falsePositiveRate_eq_zero_of_positivePredictiveValue_eq_one [IsFiniteMeasure μ]
    (h : positivePredictiveValue μ = 1) : falsePositiveRate μ = 0 := by
  rw [positivePredictiveValue_eq] at h
  have hab : μ.real {(true, true)} + μ.real {(false, true)} ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; exact zero_ne_one h
  rw [div_eq_one_iff_eq hab] at h
  rw [falsePositiveRate_eq, show μ.real {(false, true)} = 0 by linarith, zero_div]

theorem falseNegativeRate_eq_one_or_positivePredictiveValue_eq_one
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ₀ : 0 < prevalence μ) (hμ₁ : prevalence μ < 1) (hμ : 0 < μ.real {z | z.2 = true})
    (hν₀ : 0 < prevalence ν) (hν₁ : prevalence ν < 1)
    (hppv : positivePredictiveValue μ = positivePredictiveValue ν)
    (hprev : prevalence μ ≠ prevalence ν)
    (hfpr : falsePositiveRate μ = falsePositiveRate ν)
    (hfnr : falseNegativeRate μ = falseNegativeRate ν) :
    (falseNegativeRate μ = 1 ∧ falseNegativeRate ν = 1) ∨
      (positivePredictiveValue μ = 1 ∧ positivePredictiveValue ν = 1) := by
  by_cases hf : falseNegativeRate μ = 1
  · exact Or.inl ⟨hf, hfnr ▸ hf⟩
  by_cases hv : positivePredictiveValue μ = 1
  · exact Or.inr ⟨hv, hppv ▸ hv⟩
  exfalso
  have hv₀ : positivePredictiveValue μ ≠ 0 := fun h ↦
    hf ((falseNegativeRate_eq_one_iff μ hμ₀ hμ).2 h)
  have hvpos : 0 < positivePredictiveValue μ :=
    (positivePredictiveValue_nonneg μ).lt_of_ne' hv₀
  have hμe := falsePositiveRate_eq_mul μ hμ₀ hμ₁ hvpos
  have hνe := falsePositiveRate_eq_mul ν hν₀ hν₁ (hppv ▸ hvpos)
  rw [← hppv, ← hfnr, ← hfpr, hμe] at hνe
  have hK : (1 - positivePredictiveValue μ) / positivePredictiveValue μ *
      (1 - falseNegativeRate μ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (sub_ne_zero.2 (Ne.symm hv)) hv₀) (sub_ne_zero.2 (Ne.symm hf))
  rw [mul_assoc, mul_assoc] at hνe
  have hodds := mul_right_cancel₀ hK hνe
  rw [div_eq_div_iff (by linarith) (by linarith)] at hodds
  exact hprev (by linarith)

end Tradeoff

section Exceptions

/-- For nonnegative weights `a`, `b`, `c`, `d`, the measure on `Bool × Bool` with masses `a`,
`b`, `c`, `d` at `(true, true)`, `(false, true)`, `(true, false)` and `(false, false)`
(`ENNReal.ofReal` clips a negative weight to `0`). -/
private noncomputable def cellMeasure (a b c d : ℝ) : Measure (Bool × Bool) :=
  ENNReal.ofReal a • Measure.dirac (true, true) + ENNReal.ofReal b • Measure.dirac (false, true) +
    ENNReal.ofReal c • Measure.dirac (true, false) +
      ENNReal.ofReal d • Measure.dirac (false, false)

private lemma isProbabilityMeasure_cellMeasure {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    IsProbabilityMeasure (cellMeasure a b c d) := by
  constructor
  simp only [cellMeasure, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (by positivity) hc,
    ← ENNReal.ofReal_add (by positivity) hd, h, ENNReal.ofReal_one]

private lemma cellMeasure_real {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    (cellMeasure a b c d).real {(true, true)} = a ∧
      (cellMeasure a b c d).real {(false, true)} = b ∧
        (cellMeasure a b c d).real {(true, false)} = c ∧
          (cellMeasure a b c d).real {(false, false)} = d := by
  simp [cellMeasure, measureReal_def, ha, hb, hc, hd]

theorem exists_positivePredictiveValue_eq_one {p f : ℝ} (hp : p ∈ Ioo 0 1) (hf : f ∈ Ico 0 1) :
    ∃ μ : Measure (Bool × Bool), IsProbabilityMeasure μ ∧ prevalence μ = p ∧
      0 < μ.real {z | z.2 = true} ∧ positivePredictiveValue μ = 1 ∧ falseNegativeRate μ = f ∧
        falsePositiveRate μ = 0 := by
  obtain ⟨hp₀, hp₁⟩ := hp
  obtain ⟨hf₀, hf₁⟩ := hf
  have ha : 0 ≤ p * (1 - f) := by nlinarith
  have hc : 0 ≤ p * f := by positivity
  have hd : 0 ≤ 1 - p := by linarith
  have := isProbabilityMeasure_cellMeasure ha le_rfl hc hd (by ring)
  obtain ⟨h1, h2, h3, h4⟩ := cellMeasure_real ha le_rfl hc hd
  have hpos : 0 < p * (1 - f) := mul_pos hp₀ (by linarith)
  refine ⟨cellMeasure (p * (1 - f)) 0 (p * f) (1 - p), this, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prevalence_eq, h1, h3]; ring
  · rw [measureReal_snd_eq_true, h1, h2, add_zero]; exact hpos
  · rw [positivePredictiveValue_eq, h1, h2, add_zero, div_self hpos.ne']
  · rw [falseNegativeRate_eq, h1, h3, show p * (1 - f) + p * f = p by ring]
    field_simp
  · rw [falsePositiveRate_eq, h2, zero_div]

theorem exists_positivePredictiveValue_eq_zero {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Ioc 0 1) :
    ∃ μ : Measure (Bool × Bool), IsProbabilityMeasure μ ∧ prevalence μ = p ∧
      0 < μ.real {z | z.2 = true} ∧ positivePredictiveValue μ = 0 ∧ falseNegativeRate μ = 1 ∧
        falsePositiveRate μ = r := by
  obtain ⟨hp₀, hp₁⟩ := hp
  obtain ⟨hr₀, hr₁⟩ := hr
  have hb : 0 ≤ (1 - p) * r := mul_nonneg (by linarith) hr₀.le
  have hd : 0 ≤ (1 - p) * (1 - r) := mul_nonneg (by linarith) (by linarith)
  have := isProbabilityMeasure_cellMeasure le_rfl hb hp₀.le hd (by ring)
  obtain ⟨h1, h2, h3, h4⟩ := cellMeasure_real le_rfl hb hp₀.le hd
  have hpos : 0 < (1 - p) * r := mul_pos (by linarith) hr₀
  refine ⟨cellMeasure 0 ((1 - p) * r) p ((1 - p) * (1 - r)), this, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prevalence_eq, h1, h3, zero_add]
  · rw [measureReal_snd_eq_true, h1, h2, zero_add]; exact hpos
  · rw [positivePredictiveValue_eq, h1, zero_div]
  · rw [falseNegativeRate_eq, h1, h3, zero_add, div_self hp₀.ne']
  · rw [falsePositiveRate_eq, h2, h4, show (1 - p) * r + (1 - p) * (1 - r) = 1 - p by ring]
    field_simp [show (1 - p) ≠ 0 by linarith]

end Exceptions

/-- **Predictive parity versus error-rate balance.** Model a group by the joint law $\mu$ of a
binary label $Y$ and a binary classifier's prediction $\hat Y$ in it, a probability measure on
$\{0,1\} \times \{0,1\}$ (Lean's `Bool × Bool`, with `true` for $1$; the first coordinate is
$Y$). Call the group admissible when its prevalence $p = \Pr(Y = 1)$ lies in $(0, 1)$ and
$\Pr(\hat Y = 1) > 0$, and write $\mathrm{FPR} = \Pr(\hat Y = 1 \mid Y = 0)$,
$\mathrm{FNR} = \Pr(\hat Y = 0 \mid Y = 1)$ and $\mathrm{PPV} = \Pr(Y = 1 \mid \hat Y = 1)$,
conditional probabilities under $\mu$. Then:

1. in an admissible group with $\mathrm{PPV} > 0$,
   $\mathrm{FPR} = \frac{p}{1-p} \cdot \frac{1-\mathrm{PPV}}{\mathrm{PPV}} \cdot (1-\mathrm{FNR})$;
2. if two admissible groups have equal PPV, different prevalences, equal FPR and equal FNR, then
   $\mathrm{FNR} = 1$ and $\mathrm{PPV} = 0$ in both, or $\mathrm{PPV} = 1$ in both;
3. in an admissible group, $\mathrm{FNR} = 1$ if and only if $\mathrm{PPV} = 0$;
4. in an admissible group, $\mathrm{PPV} = 1$ implies $\mathrm{FPR} = 0$;
5. for every $p \in (0, 1)$ and $f \in [0, 1)$, some admissible group has prevalence $p$,
   $\mathrm{PPV} = 1$, $\mathrm{FNR} = f$ and $\mathrm{FPR} = 0$;
6. for every $p \in (0, 1)$ and $r \in (0, 1]$, some admissible group has prevalence $p$,
   $\mathrm{PPV} = 0$, $\mathrm{FNR} = 1$ and $\mathrm{FPR} = r$.

In an admissible group every conditioning event has positive probability.

Source: A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism
prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3: part 1 is equation
(2.6), and the remark after it states part 2 without its exceptions. The exceptions in part 2
follow from (2.6) and part 3, parts 3 and 4 follow from the definitions of the rates, and parts 5
and 6 from laws given by explicit cell masses; none of these is stated there. -/
theorem predictiveParity_errorRateBalance_tradeoff :
    (∀ (μ : Measure (Bool × Bool)) [IsProbabilityMeasure μ], 0 < prevalence μ →
      prevalence μ < 1 → 0 < μ.real {z | z.2 = true} → 0 < positivePredictiveValue μ →
      falsePositiveRate μ = prevalence μ / (1 - prevalence μ) *
        ((1 - positivePredictiveValue μ) / positivePredictiveValue μ) *
          (1 - falseNegativeRate μ)) ∧
    (∀ (μ ν : Measure (Bool × Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      0 < prevalence μ → prevalence μ < 1 → 0 < μ.real {z | z.2 = true} →
      0 < prevalence ν → prevalence ν < 1 → 0 < ν.real {z | z.2 = true} →
      positivePredictiveValue μ = positivePredictiveValue ν → prevalence μ ≠ prevalence ν →
      falsePositiveRate μ = falsePositiveRate ν → falseNegativeRate μ = falseNegativeRate ν →
      (falseNegativeRate μ = 1 ∧ falseNegativeRate ν = 1 ∧
          positivePredictiveValue μ = 0 ∧ positivePredictiveValue ν = 0) ∨
        (positivePredictiveValue μ = 1 ∧ positivePredictiveValue ν = 1)) ∧
    (∀ (μ : Measure (Bool × Bool)) [IsProbabilityMeasure μ], 0 < prevalence μ →
      prevalence μ < 1 → 0 < μ.real {z | z.2 = true} →
      (falseNegativeRate μ = 1 ↔ positivePredictiveValue μ = 0)) ∧
    (∀ (μ : Measure (Bool × Bool)) [IsProbabilityMeasure μ], 0 < prevalence μ →
      prevalence μ < 1 → 0 < μ.real {z | z.2 = true} → positivePredictiveValue μ = 1 →
      falsePositiveRate μ = 0) ∧
    (∀ p ∈ Ioo (0 : ℝ) 1, ∀ f ∈ Ico (0 : ℝ) 1, ∃ μ : Measure (Bool × Bool),
      IsProbabilityMeasure μ ∧ prevalence μ = p ∧ 0 < μ.real {z | z.2 = true} ∧
        positivePredictiveValue μ = 1 ∧ falseNegativeRate μ = f ∧ falsePositiveRate μ = 0) ∧
    (∀ p ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioc (0 : ℝ) 1, ∃ μ : Measure (Bool × Bool),
      IsProbabilityMeasure μ ∧ prevalence μ = p ∧ 0 < μ.real {z | z.2 = true} ∧
        positivePredictiveValue μ = 0 ∧ falseNegativeRate μ = 1 ∧ falsePositiveRate μ = r) := by
  refine ⟨fun μ _ hp₀ hp₁ _ hppv ↦ falsePositiveRate_eq_mul μ hp₀ hp₁ hppv,
    fun μ ν _ _ hμ₀ hμ₁ hμ hν₀ hν₁ hν hppv hprev hfpr hfnr ↦ ?_,
    fun μ _ hp₀ _ hpos ↦ falseNegativeRate_eq_one_iff μ hp₀ hpos,
    fun μ _ _ _ _ h ↦ falsePositiveRate_eq_zero_of_positivePredictiveValue_eq_one μ h,
    fun _ hp _ hf ↦ exists_positivePredictiveValue_eq_one hp hf,
    fun _ hp _ hr ↦ exists_positivePredictiveValue_eq_zero hp hr⟩
  rcases falseNegativeRate_eq_one_or_positivePredictiveValue_eq_one μ ν hμ₀ hμ₁ hμ hν₀ hν₁
    hppv hprev hfpr hfnr with ⟨h, h'⟩ | h
  · exact Or.inl ⟨h, h', (falseNegativeRate_eq_one_iff μ hμ₀ hμ).1 h,
      (falseNegativeRate_eq_one_iff ν hν₀ hν).1 h'⟩
  · exact Or.inr h

end Cslib.MachineLearning.Fairness
