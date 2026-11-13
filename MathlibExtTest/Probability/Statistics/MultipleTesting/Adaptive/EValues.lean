/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.EValues

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.EValues

/-! ### A likelihood-ratio e-value: simple null versus simple alternative

Null: a fair coin, `P₀ {true} = 1/2`. Alternative: `P₁ {true} = 3/4`. The likelihood ratio
`P₁ / P₀` takes the values `3/2` and `1/2`, and its null expectation is exactly `1`. -/

/-- The fair-coin null law on `Bool`. -/
noncomputable def coin : Measure Bool :=
  ENNReal.ofReal (1 / 2) • Measure.dirac true + ENNReal.ofReal (1 / 2) • Measure.dirac false

/-- Null probability mass function. -/
noncomputable def nullPmf (_b : Bool) : ℝ := 1 / 2

/-- Alternative probability mass function. -/
noncomputable def altPmf (b : Bool) : ℝ := if b then 3 / 4 else 1 / 4

/-- The likelihood ratio `P₁ / P₀`. -/
noncomputable def lr (b : Bool) : ℝ := altPmf b / nullPmf b

theorem lr_true : lr true = 3 / 2 := by norm_num [lr, altPmf, nullPmf]

theorem lr_false : lr false = 1 / 2 := by norm_num [lr, altPmf, nullPmf]

instance : IsProbabilityMeasure coin := by
  constructor
  simp only [coin, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Lebesgue integral over the fair coin: the average of the two values. -/
theorem lintegral_coin (f : Bool → ENNReal) :
    ∫⁻ b, f b ∂coin = ENNReal.ofReal (1 / 2) * f true + ENNReal.ofReal (1 / 2) * f false := by
  simp [coin, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

/-- **The likelihood ratio has null expectation exactly `1`**, computed from the definition. -/
theorem lintegral_lr : ∫⁻ b, ENNReal.ofReal (lr b) ∂coin = 1 := by
  rw [lintegral_coin, lr_true, lr_false, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem lr_nonneg (b : Bool) : 0 ≤ lr b := by
  cases b <;> norm_num [lr_true, lr_false]

/-- The likelihood ratio is an e-value under the null. -/
theorem isEValue_lr : IsEValue coin lr where
  nonneg := lr_nonneg
  measurable := measurable_of_countable _
  lintegral_le_one := lintegral_lr.le

/-- The rejection event `{lr ≥ 3/2}` is `{true}`. -/
theorem setOf_le_lr : {b : Bool | (3 / 2 : ℝ) ≤ lr b} = {true} := by
  ext b
  cases b <;> norm_num [lr_true, lr_false]

/-- Computed from the definition: `P₀ {lr ≥ 3/2} = 1/2`. -/
theorem coin_setOf_le_lr : coin {b : Bool | (3 / 2 : ℝ) ≤ lr b} = ENNReal.ofReal (1 / 2) := by
  rw [setOf_le_lr]
  simp [coin]

/-- Markov's bound `1 / c = 2/3` from the theorem, consistent with the exact value `1/2`. -/
example : coin {b : Bool | (3 / 2 : ℝ) ≤ lr b} ≤ ENNReal.ofReal (2 / 3) := by
  simpa using isEValue_lr.measure_ge_le (c := 3 / 2) (by norm_num)

example : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (2 / 3) :=
  ENNReal.ofReal_le_ofReal (by norm_num)

/-- The calibrated p-value `(max lr 1)⁻¹` is valid. -/
example : IsValidPValue coin (fun b => (max (lr b) 1)⁻¹) := isEValue_lr.isValidPValue

/-! ### A stopped likelihood-ratio process: Ville's bound checked numerically

Two independent fair-coin flips under the null; `E 0 = 1`, `E 1 = lr ω₁`,
`E n = lr ω₁ · lr ω₂` for `n ≥ 2`. All quantities below are computed from the definitions,
not through the theorems under test. -/

/-- Two independent fair flips: uniform on `Bool × Bool`. -/
noncomputable def coin2 : Measure (Bool × Bool) :=
  ENNReal.ofReal (1 / 4) • (Measure.dirac (true, true) + Measure.dirac (true, false) +
    Measure.dirac (false, true) + Measure.dirac (false, false))

/-- The likelihood-ratio process. -/
noncomputable def lrProc (n : ℕ) (ω : Bool × Bool) : ℝ :=
  if n = 0 then 1 else if n = 1 then lr ω.1 else lr ω.1 * lr ω.2

/-- Lebesgue integral over two fair flips. -/
theorem lintegral_coin2 (f : Bool × Bool → ENNReal) :
    ∫⁻ ω, f ω ∂coin2 = ENNReal.ofReal (1 / 4) *
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) := by
  simp [coin2, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, mul_add]

/-- Measure of a set under two fair flips. -/
theorem coin2_apply (s : Set (Bool × Bool)) :
    coin2 s = ENNReal.ofReal (1 / 4) *
      (s.indicator 1 (true, true) + s.indicator 1 (true, false) +
        s.indicator 1 (false, true) + s.indicator 1 (false, false)) := by
  simp [coin2, Measure.dirac_apply, mul_add]

/-- Stop at look `1` after heads (where `E 1 = 3/2`), otherwise at look `2`: the hitting time of
`[3/2, ∞)` capped at `2`. -/
def τ (ω : Bool × Bool) : WithTop ℕ := if ω.1 then (1 : ℕ) else (2 : ℕ)

/-- The stopped value: `E 1 = lr ω₁` after heads, `E 2 = lr ω₁ · lr ω₂` after tails. -/
theorem stoppedValue_lrProc_τ (a b : Bool) :
    stoppedValue lrProc τ (a, b) = if a then lr a else lr a * lr b := by
  cases a
  · show lrProc 2 (false, b) = _
    simp [lrProc]
  · show lrProc 1 (true, b) = _
    simp [lrProc]

/-- **Optional stopping, numerically**: `E[E_τ] = (3/2 + 3/2 + 3/4 + 1/4) / 4 = 1`. -/
theorem lintegral_stoppedValue_lrProc :
    ∫⁻ ω, ENNReal.ofReal (stoppedValue lrProc τ ω) ∂coin2 = 1 := by
  rw [lintegral_coin2]
  simp only [stoppedValue_lrProc_τ, ite_true, Bool.false_eq_true, ite_false, lr_true, lr_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem exists_le_lrProc_iff (c : ℝ) (ω : Bool × Bool) :
    (∃ n, c ≤ lrProc n ω) ↔ c ≤ 1 ∨ c ≤ lr ω.1 ∨ c ≤ lr ω.1 * lr ω.2 := by
  constructor
  · rintro ⟨n, hn⟩
    unfold lrProc at hn
    split_ifs at hn
    · exact Or.inl hn
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr hn)
  · rintro (h | h | h)
    · exact ⟨0, by simpa [lrProc] using h⟩
    · exact ⟨1, by simpa [lrProc] using h⟩
    · exact ⟨2, by simpa [lrProc] using h⟩

/-- The path ever reaches `3/2` exactly when the first flip is heads. -/
theorem crossing_three_halves :
    {ω : Bool × Bool | ∃ n, (3 / 2 : ℝ) ≤ lrProc n ω} = {(true, true), (true, false)} := by
  ext ⟨a, b⟩
  rw [Set.mem_ofPred_eq, exists_le_lrProc_iff]
  cases a <;> cases b <;> norm_num [lr_true, lr_false]

/-- The path ever reaches `9/4` exactly on two heads. -/
theorem crossing_nine_quarters :
    {ω : Bool × Bool | ∃ n, (9 / 4 : ℝ) ≤ lrProc n ω} = {(true, true)} := by
  ext ⟨a, b⟩
  rw [Set.mem_ofPred_eq, exists_le_lrProc_iff]
  cases a <;> cases b <;> norm_num [lr_true, lr_false]

/-- **Ville at `c = 3/2`, numerically**: the crossing probability is `1/2 ≤ 2/3 = 1/c`. -/
theorem ville_three_halves :
    coin2 {ω | ∃ n, (3 / 2 : ℝ) ≤ lrProc n ω} = ENNReal.ofReal (1 / 2) ∧
      ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (3 / 2)⁻¹ := by
  refine ⟨?_, ENNReal.ofReal_le_ofReal (by norm_num)⟩
  rw [crossing_three_halves, coin2_apply]
  simp [Set.indicator]
  rw [one_add_one_eq_two, show (4 : ENNReal) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by simp) (by simp), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one]

/-- **Ville at `c = 9/4`, numerically**: the crossing probability is `1/4 ≤ 4/9 = 1/c`. -/
theorem ville_nine_quarters :
    coin2 {ω | ∃ n, (9 / 4 : ℝ) ≤ lrProc n ω} = ENNReal.ofReal (1 / 4) ∧
      ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (9 / 4)⁻¹ := by
  refine ⟨?_, ENNReal.ofReal_le_ofReal (by norm_num)⟩
  rw [crossing_nine_quarters, coin2_apply]
  simp [Set.indicator]

/-! ### A statistic with expectation above one is not an e-value -/

/-- A statistic with values `3` and `1`: null expectation `2`. -/
noncomputable def bad (b : Bool) : ℝ := if b then 3 else 1

theorem lintegral_bad : ∫⁻ b, ENNReal.ofReal (bad b) ∂coin = 2 := by
  rw [lintegral_coin]
  simp only [bad, ite_true, Bool.false_eq_true, ite_false]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- `bad` has expectation `2 > 1`, so it is not an e-value. -/
theorem not_isEValue_bad : ¬ IsEValue coin bad := by
  intro h
  have := h.lintegral_le_one
  rw [lintegral_bad] at this
  norm_num at this

/-- The conclusion of Markov's bound fails for `bad`: `P₀ {bad ≥ 3} = 1/2 > 1/3`. So the
hypothesis `E[E] ≤ 1` cannot be dropped from `IsEValue.measure_ge_le`. -/
theorem markov_fails_bad :
    ENNReal.ofReal (3 : ℝ)⁻¹ < coin {b : Bool | (3 : ℝ) ≤ bad b} := by
  have hset : {b : Bool | (3 : ℝ) ≤ bad b} = {true} := by
    ext b
    cases b <;> norm_num [bad]
  rw [hset]
  simp only [coin, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply, Set.indicator, Set.mem_singleton_iff]
  simp only [ite_true, Bool.false_eq_true, ite_false, Pi.one_apply, mul_one, mul_zero, add_zero]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-! ### e-BH versus e-Bonferroni on concrete e-values

`m = 3`, `α = 1/2`, e-values `(4, 1/2, 3)`. e-Bonferroni needs `e ≥ m / α = 6`: no rejection.
e-BH: `k = 3` needs `e ≥ 2` (two qualify, fewer than 3); `k = 2` needs `e ≥ 3` (two qualify), so
`k̂ = 2` and e-BH rejects hypotheses `0` and `2`. -/

/-- Three concrete e-values. -/
noncomputable def ev : Fin 3 → ℝ := ![4, 1 / 2, 3]

theorem eBonferroniRejections_ev : eBonferroniRejections (1 / 2) ev = ∅ := by
  ext i
  fin_cases i <;> norm_num [eBonferroniRejections, ev]

theorem filter_ev (k : ℕ) (hk : k = 2 ∨ k = 3) :
    (Finset.univ.filter fun i : Fin 3 => ((3 : ℕ) : ℝ) ≤ 1 / 2 * k * ev i) = {0, 2} := by
  ext i
  rcases hk with rfl | rfl <;> fin_cases i <;> norm_num [ev]

theorem eBHCount_ev_two : eBHCount (1 / 2) ev 2 = 2 := by
  rw [eBHCount, filter_ev 2 (Or.inl rfl)]
  rfl

theorem eBHCount_ev_three : eBHCount (1 / 2) ev 3 = 2 := by
  rw [eBHCount, filter_ev 3 (Or.inr rfl)]
  rfl

theorem eBHIndex_ev : eBHIndex (1 / 2) ev = 2 := by
  have h2 : 2 ≤ eBHIndex (1 / 2) ev :=
    le_eBHIndex (by norm_num) (by rw [eBHCount_ev_two])
  have h3 : eBHIndex (1 / 2) ev ≤ 3 := eBHIndex_le _ _
  have hne : eBHIndex (1 / 2) ev ≠ 3 := by
    intro h
    have hc := eBHIndex_le_card_eBHRejections (1 / 2) ev
    have hcard : (eBHRejections (1 / 2) ev).card = eBHCount (1 / 2) ev 3 := by
      rw [eBHRejections, eBHCount, h]
    rw [hcard, eBHCount_ev_three, h] at hc
    omega
  omega

theorem eBHRejections_ev : eBHRejections (1 / 2) ev = {0, 2} := by
  rw [eBHRejections, eBHIndex_ev]
  exact filter_ev 2 (Or.inl rfl)

/-- Self-consistency of `{0, 2}` checked from the definition: `3 ≤ (1/2) · 2 · e i`. -/
example : IsEBHSelfConsistent (1 / 2) ev {0, 2} := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num [ev]

/-- If hypothesis `2` is a true null, the e-BH FDP is `1/2`. -/
example : falseDiscoveryProportion {2} (eBHRejections (1 / 2) ev) = 1 / 2 := by
  rw [eBHRejections_ev]
  norm_num [falseDiscoveryProportion]

/-! ### API usage on the likelihood-ratio e-value -/

/-- The constant filtration on `Bool`. -/
noncomputable def constFiltration : Filtration ℕ (inferInstance : MeasurableSpace Bool) :=
  Filtration.const ℕ _ le_rfl

/-- Every function on `Bool` is measurable for each slice of the constant filtration. -/
theorem sm_const (n : ℕ) (f : Bool → ℝ) : StronglyMeasurable[constFiltration n] f := by
  unfold constFiltration
  exact (measurable_of_countable f).stronglyMeasurable

/-- Under the constant filtration on `Bool`, conditional expectation is the identity. -/
theorem condExp_constFiltration (n : ℕ) (f : Bool → ℝ) : coin[f | constFiltration n] = f :=
  condExp_of_stronglyMeasurable (constFiltration.le n) (sm_const n f) (Integrable.of_finite)

/-! ### A test supermartingale: the likelihood ratio decaying in time -/

/-- `lr / (n + 1)` is a test supermartingale: it is nonincreasing in `n` and starts at the
likelihood ratio, whose null expectation is `1`. -/
theorem isTestSupermartingale_lrDecay :
    IsTestSupermartingale coin constFiltration (fun n b => lr b / (n + 1)) where
  supermartingale := by
    refine ⟨fun n => sm_const n _, fun i j hij => ?_, fun _ => Integrable.of_finite⟩
    rw [condExp_constFiltration]
    refine Filter.Eventually.of_forall fun b => ?_
    exact div_le_div_of_nonneg_left (lr_nonneg b) (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)
  nonneg n b := div_nonneg (lr_nonneg b) (by positivity)
  integral_zero_le_one := by
    have h := ofReal_integral_eq_lintegral_ofReal (μ := coin) (f := lr) Integrable.of_finite
      (Filter.Eventually.of_forall lr_nonneg)
    rw [lintegral_lr] at h
    simp only [CharP.cast_eq_zero, zero_add, div_one]
    exact ENNReal.ofReal_le_one.1 h.le

/-- Through `IsTestSupermartingale.isEProcess`, the decaying likelihood ratio is an
e-process. -/
example : IsEProcess coin constFiltration (fun n b => lr b / (n + 1)) :=
  isTestSupermartingale_lrDecay.isEProcess

/-! ### An e-process that is not a supermartingale -/

/-- A deterministic process rising from `1/2` to `1`. -/
noncomputable def risingProc (n : ℕ) (_ : Bool) : ℝ := if n = 0 then 1 / 2 else 1

theorem risingProc_le_one (n : ℕ) (b : Bool) : risingProc n b ≤ 1 := by
  unfold risingProc
  split_ifs <;> norm_num

/-- `risingProc` is an e-process: its value at any time is at most `1`. -/
theorem isEProcess_risingProc : IsEProcess coin constFiltration risingProc where
  nonneg n b := by unfold risingProc; split_ifs <;> norm_num
  stronglyAdapted n := sm_const n _
  lintegral_stoppedValue_le_one τ _ _ _ := by
    calc ∫⁻ b, ENNReal.ofReal (stoppedValue risingProc τ b) ∂coin
        ≤ ∫⁻ _, 1 ∂coin := lintegral_mono fun b => ENNReal.ofReal_le_one.2 (risingProc_le_one _ b)
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]

/-- `risingProc` is not a supermartingale: from time `0` to time `1` it rises from `1/2` to `1`.
So Ville's inequality for e-processes covers processes outside `Supermartingale.ville_maximal_ineq`.
-/
theorem not_supermartingale_risingProc : ¬ Supermartingale risingProc constFiltration coin := by
  intro h
  have h01 := h.2.1 0 1 zero_le_one
  rw [condExp_constFiltration] at h01
  have : (ae coin).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero coin)
  obtain ⟨b, hb⟩ := h01.exists
  norm_num [risingProc] at hb

/-- The likelihood ratio held constant in time is an e-process. -/
theorem isEProcess_lr_const : IsEProcess coin constFiltration (fun _ => lr) :=
  isEValue_lr.isEProcess_const isEValue_lr.measurable

/-- Its time-uniform crossing probability at `c = 3/2` is at most `2/3`. -/
example : coin {b | ∃ n : ℕ, (3 / 2 : ℝ) ≤ (fun _ => lr) n b} ≤ ENNReal.ofReal (3 / 2)⁻¹ :=
  isEProcess_lr_const.measure_exists_ge_le (by norm_num)

/-- e-Bonferroni FWER over all looks for two endpoints carrying the constant e-process. -/
example :
    coin {b | ∃ i ∈ (Finset.univ : Finset (Fin 2)), ∃ n : ℕ,
      i ∈ eBonferroniRejections (1 / 2) (fun j => (fun (_ : Fin 2) (_ : ℕ) => lr) j n b)} ≤
      ENNReal.ofReal (1 / 2) :=
  measure_exists_mem_exists_eBonferroniRejections_le_alpha (by norm_num)
    (fun _ _ => lr) _ fun _ _ => isEProcess_lr_const

end MathlibExtTest.Probability.Statistics.MultipleTesting.EValues
