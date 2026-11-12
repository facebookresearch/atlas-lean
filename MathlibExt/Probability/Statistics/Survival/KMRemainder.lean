/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.StochasticIntegral

/-!
# The vanishing-risk remainder of the Kaplan–Meier martingale representation

Gill's representation (`kaplanMeierProcess_div_sub_one`) on the time grid `0, 1, 2, …` reads
`Ŝ/S - 1 = -∫ Ŝ₋ / (S Y) dM + Rₙ` with the **vanishing-risk remainder**
`Rₙ = ∫ Ŝ₋ / S · 1{Y = 0} dα = ∑_{k < n} Ŝ_k / S_{k+1} · 1{Y_{k+1} = 0} · Δα_{k+1}`.
This file shows when `R` vanishes and when it does not.

* With **one subject and no censoring** the subject leaves the risk set only by dying, which makes
  `Ŝ` zero; so `Ŝ₋ · 1{Y = 0} ≡ 0` and the remainder is identically `0`
  (`stochasticIntegral_kaplanMeierRemainder_eq_zero_of_uncensored`).
* **Censoring** removes the subject from the risk set while `Ŝ` stays positive, and every later
  hazard increment then adds to `R`. Under the hypotheses of Gill's martingale the remainder is
  nonnegative (`stochasticIntegral_kaplanMeierRemainder_nonneg`), and one such step makes it
  positive (`stochasticIntegral_kaplanMeierRemainder_pos`). If this happens with positive
  probability, no conditional expectation of `R` given any sub-σ-algebra is a.e. zero
  (`not_condExp_kaplanMeierRemainder_ae_eq_zero`), and the remainder is exactly the mean bias of
  `Ŝ/S` (`integral_kaplanMeierProcess_div_sub_one`).
* **Censoring known at an intermediate time** (`CensoredAtOne`): one subject, two independent fair
  coins `(c, d)`. The censoring coin `c` is revealed at time `1`, so `ℱ₁ = σ(c)` is neither
  trivial nor everything (`CensoredAtOne.filtration_one_ne_bot`,
  `CensoredAtOne.filtration_one_ne_top`). An uncensored subject dies at step `2` iff `d`, with
  hazard `Δα₂ = 1/2`. All hypotheses of `martingale_kaplanMeierProcess` hold
  (`CensoredAtOne.martingale_aalen` and its neighbours), and
  `E[R₂ | ℱ₁] = R₂ = 1{c}` (`CensoredAtOne.condExp_remainder_two`), which is not a.e. zero
  (`CensoredAtOne.condExp_remainder_two_ne_zero`). The mean bias is
  `E[Ŝ₂/S₂] - 1 = E[R₂] = 1/2` (`CensoredAtOne.integral_kaplanMeierProcess_div_sub_one`).

## Reused API (source receipts)

* `kaplanMeierProcess`, `kaplanMeierProcess_succ`, `kaplanMeierProcess_mem_Icc`,
  `kaplanMeierRemainder`, `kaplanMeierProcess_div_sub_one`, `martingale_kaplanMeierProcess`,
  `stronglyAdapted_kaplanMeierProcess`, `prodIntegral`, `aalenCompensator`, `stochasticIntegral`
  (`MathlibExt/Probability/Statistics/Survival/StochasticIntegral.lean`).
* `MeasureTheory.integral_condExp`, `condExp_of_stronglyMeasurable`,
  `ae_eq_condExp_of_forall_setIntegral_eq`, `martingale_of_condExp_sub_eq_zero_nat`
  (Mathlib).

## References

* R. D. Gill, *Censoring and Stochastic Integrals*, Mathematical Centre Tracts 124, Amsterdam
  (1980), Theorem 3.2.1 and Section 3.2 (the bias of the Kaplan–Meier estimator).
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section IV.3.1.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess

open MeasureTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### When the remainder vanishes: no censoring -/

/-- The remainder `Rₙ ω` vanishes if at every step `k < n` where the risk set is empty the
Kaplan–Meier process is already `0`. -/
theorem stochasticIntegral_kaplanMeierRemainder_eq_zero_of_forall (N Y : ℕ → Ω → ℝ)
    (α : ℕ → ℝ) {n : ℕ} {ω : Ω}
    (h : ∀ k < n, Y (k + 1) ω = 0 → kaplanMeierProcess N Y k ω = 0) :
    stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω = 0 := by
  refine sum_eq_zero fun k hk => ?_
  simp only [kaplanMeierRemainder, Nat.add_sub_cancel]
  by_cases hY : Y (k + 1) ω = 0
  · simp [h k (mem_range.1 hk) hY]
  · simp [hY]

/-- **One uncensored subject.** If the subject starts alive (`N₀ = 0`), dies at most once
(unit jumps, `ΔN ≤ Y`) and is at risk exactly while alive (`Y_{k+1} = 1 - N_k`), then at every
time either it is alive and `Ŝ = 1`, or it is dead and `Ŝ = 0`. -/
theorem kaplanMeierProcess_of_uncensored {N Y : ℕ → Ω → ℝ} {ω : Ω} (hN0 : N 0 ω = 0)
    (hjump : ∀ k, N (k + 1) ω - N k ω = 0 ∨ N (k + 1) ω - N k ω = 1)
    (hNY : ∀ k, N (k + 1) ω - N k ω ≤ Y (k + 1) ω) (hY : ∀ k, Y (k + 1) ω = 1 - N k ω) (k : ℕ) :
    (N k ω = 0 ∧ kaplanMeierProcess N Y k ω = 1) ∨
      (N k ω = 1 ∧ kaplanMeierProcess N Y k ω = 0) := by
  induction k with
  | zero => exact Or.inl ⟨hN0, by simp [kaplanMeierProcess]⟩
  | succ k ih =>
    rw [kaplanMeierProcess_succ, hY k]
    have hle := hNY k
    rw [hY k] at hle
    rcases ih with ⟨hN, hS⟩ | ⟨hN, hS⟩ <;> rcases hjump k with hj | hj
    · left; constructor <;> [linarith; (rw [hS, hj, hN]; norm_num)]
    · right; constructor <;> [linarith; (rw [hS, hj, hN]; norm_num)]
    · right; constructor <;> [linarith; (rw [hS]; ring)]
    · exfalso; linarith

/-- **The remainder vanishes for one uncensored subject** (the phenomenon behind the single-subject
examples of `StochasticIntegral.lean`): the subject leaves the risk set only by dying, at which
point `Ŝ` drops to `0`, so `Ŝ₋ · 1{Y = 0} ≡ 0`. -/
theorem stochasticIntegral_kaplanMeierRemainder_eq_zero_of_uncensored {N Y : ℕ → Ω → ℝ}
    (α : ℕ → ℝ) {ω : Ω} (hN0 : N 0 ω = 0)
    (hjump : ∀ k, N (k + 1) ω - N k ω = 0 ∨ N (k + 1) ω - N k ω = 1)
    (hNY : ∀ k, N (k + 1) ω - N k ω ≤ Y (k + 1) ω) (hY : ∀ k, Y (k + 1) ω = 1 - N k ω) (n : ℕ) :
    stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω = 0 := by
  refine stochasticIntegral_kaplanMeierRemainder_eq_zero_of_forall N Y α fun k _ hY0 => ?_
  rcases kaplanMeierProcess_of_uncensored hN0 hjump hNY hY k with ⟨hN, -⟩ | ⟨-, hS⟩
  · rw [hY k, hN] at hY0; norm_num at hY0
  · exact hS

/-! ### When the remainder is positive: censoring -/

private lemma prodIntegral_pos {α : ℕ → ℝ} (hα : ∀ k, α (k + 1) - α k < 1) (n : ℕ) :
    0 < prodIntegral α n :=
  prod_pos fun k _ => by linarith [hα k]

/-- Each summand `Ŝ_k / S_{k+1} · 1{Y_{k+1} = 0} · Δα_{k+1}` of the remainder is nonnegative. -/
private lemma kaplanMeierRemainder_term_nonneg {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, 0 ≤ α (k + 1) - α k ∧ α (k + 1) - α k < 1) (k : ℕ) (ω : Ω) :
    0 ≤ kaplanMeierRemainder N Y α (k + 1) ω * (α (k + 1) - α k) := by
  refine mul_nonneg ?_ (hα k).1
  simp only [kaplanMeierRemainder, Nat.add_sub_cancel]
  refine mul_nonneg (div_nonneg (kaplanMeierProcess_mem_Icc hY1 hNY k ω).1
    (prodIntegral_pos (fun j => (hα j).2) _).le) ?_
  split_ifs <;> norm_num

/-- **The remainder is nonnegative** under the hypotheses of Gill's Kaplan–Meier martingale, with
hazard increments in `[0, 1)`. -/
theorem stochasticIntegral_kaplanMeierRemainder_nonneg {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, 0 ≤ α (k + 1) - α k ∧ α (k + 1) - α k < 1) (n : ℕ) (ω : Ω) :
    0 ≤ stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω :=
  sum_nonneg fun k _ => kaplanMeierRemainder_term_nonneg hY1 hNY hα k ω

/-- **The remainder is positive after a censoring step**: if at some step `k < n` the risk set is
empty while `Ŝ_k > 0` (the subject left by censoring, not by death) and the hazard still
increases (`Δα_{k+1} > 0`), then `Rₙ > 0`. -/
theorem stochasticIntegral_kaplanMeierRemainder_pos {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, 0 ≤ α (k + 1) - α k ∧ α (k + 1) - α k < 1) {n k : ℕ} {ω : Ω} (hk : k < n)
    (hYk : Y (k + 1) ω = 0) (hSk : 0 < kaplanMeierProcess N Y k ω)
    (hαk : 0 < α (k + 1) - α k) :
    0 < stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω := by
  refine sum_pos' (fun j _ => kaplanMeierRemainder_term_nonneg hY1 hNY hα j ω)
    ⟨k, mem_range.2 hk, mul_pos ?_ hαk⟩
  simp only [kaplanMeierRemainder, Nat.add_sub_cancel, hYk, ite_true, mul_one]
  exact div_pos hSk (prodIntegral_pos (fun j => (hα j).2) _)

/-- A nonnegative integrable function that is positive on a set of positive measure has a
conditional expectation, given any sub-σ-algebra, with positive integral. -/
theorem integral_condExp_pos_of_nonneg [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {f : Ω → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) (hpos : 0 < μ (Function.support f)) :
    0 < ∫ ω, (μ[f | m]) ω ∂μ := by
  rw [integral_condExp hm]
  exact (integral_pos_iff_support_of_nonneg hf hfi).2 hpos

/-- **No conditional expectation of the remainder vanishes.** Under the hypotheses of
`stochasticIntegral_kaplanMeierRemainder_nonneg`, if `Rₙ` is integrable and positive with positive
probability, then `E[Rₙ | 𝒢]` is not a.e. zero for any sub-σ-algebra `𝒢`. -/
theorem not_condExp_kaplanMeierRemainder_ae_eq_zero [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ}
    {α : ℕ → ℝ} (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, 0 ≤ α (k + 1) - α k ∧ α (k + 1) - α k < 1) {n : ℕ}
    (hint : Integrable (stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n) μ)
    (hpos : 0 < μ {ω | 0 < stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω})
    {m : MeasurableSpace Ω} (hm : m ≤ m0) :
    ¬ μ[stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n | m] =ᵐ[μ] 0 := by
  intro h0
  have hnn := stochasticIntegral_kaplanMeierRemainder_nonneg (N := N) hY1 hNY hα n
  have hsupp : {ω | 0 < stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω} =
      Function.support (stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n) := by
    ext ω; exact (hnn ω).lt_iff_ne.trans ne_comm
  have hlt := integral_condExp_pos_of_nonneg hm hnn hint (hsupp ▸ hpos)
  rw [integral_congr_ae h0] at hlt
  simp at hlt

/-- **The remainder is the mean bias of `Ŝ/S`.** Under the hypotheses of Gill's Kaplan–Meier
martingale (`martingale_kaplanMeierProcess`), `E[Ŝₙ/Sₙ - 1] = E[Rₙ]`. -/
theorem integral_kaplanMeierProcess_div_sub_one [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ}
    {α : ℕ → ℝ} (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hN : StronglyAdapted ℱ N) (hY : IsStronglyPredictable ℱ Y)
    (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, α (k + 1) - α k ≠ 1) (n : ℕ) :
    ∫ ω, (kaplanMeierProcess N Y n ω / prodIntegral α n - 1) ∂μ =
      ∫ ω, stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω ∂μ := by
  have hmart := martingale_kaplanMeierProcess hM hN hY hY1 hNY hα
  have hS : Integrable (fun ω => kaplanMeierProcess N Y n ω / prodIntegral α n - 1) μ := by
    refine Integrable.of_bound ((((stronglyAdapted_kaplanMeierProcess hN hY n).mono
      (ℱ.le n)).measurable.div_const _).sub measurable_const).aestronglyMeasurable
      (|(prodIntegral α n)⁻¹| + 1) (ae_of_all _ fun ω => ?_)
    have h1 := kaplanMeierProcess_mem_Icc hY1 hNY n ω
    calc ‖kaplanMeierProcess N Y n ω / prodIntegral α n - 1‖
        ≤ |kaplanMeierProcess N Y n ω| * |(prodIntegral α n)⁻¹| + |1| := by
          rw [Real.norm_eq_abs, div_eq_mul_inv, ← abs_mul]; exact abs_sub _ _
      _ ≤ 1 * |(prodIntegral α n)⁻¹| + 1 := by
          gcongr
          · rw [abs_of_nonneg h1.1]; exact h1.2
          · simp
      _ = |(prodIntegral α n)⁻¹| + 1 := by ring
  have h0 := hmart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
  simp only [setIntegral_univ] at h0
  have hX0 : ∫ ω, (kaplanMeierProcess N Y 0 ω / prodIntegral α 0 - 1 -
      stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) 0 ω) ∂μ = 0 := by
    simp [kaplanMeierProcess]
  rw [hX0] at h0
  have hR : Integrable
      (stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n) μ := by
    have h := hS.sub (hmart.integrable n)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [integral_sub hS hR] at h0
  linarith

/-! ### Censoring known at an intermediate time -/

namespace CensoredAtOne

open scoped ENNReal

/-- The sample space: a censoring coin `c` (`true` = censored at time `1`) and a death coin `d`
(`true` = an uncensored subject dies at step `2`). -/
abbrev Ω₀ : Type := Bool × Bool

/-- Two independent fair coins: the uniform probability on `Bool × Bool`. -/
noncomputable def μ₀ : Measure Ω₀ := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ₀ :=
  ⟨by
    simp only [μ₀, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
    rw [show (ENat.card Ω₀ : ℝ≥0∞) = 4 by simp [ENat.card_eq_coe_fintype_card]]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

lemma μ₀_real_singleton (ω : Ω₀) : μ₀.real {ω} = 1 / 4 := by
  simp [μ₀, Measure.real]

/-- The history: nothing is known at time `0`, the censoring coin is revealed at time `1`, and
everything is known from time `2` on. -/
def ℱ₀ : Filtration ℕ (inferInstance : MeasurableSpace Ω₀) where
  seq n := if n = 0 then ⊥ else if n = 1 then MeasurableSpace.comap Prod.fst inferInstance
    else inferInstance
  mono' i j hij := by
    dsimp only
    split_ifs <;> first | omega | exact bot_le | exact le_rfl | exact measurable_fst.comap_le
  le' n := by
    split_ifs
    · exact bot_le
    · exact measurable_fst.comap_le
    · exact le_rfl

lemma ℱ₀_zero : ℱ₀ 0 = ⊥ := rfl

lemma ℱ₀_one : ℱ₀ 1 = MeasurableSpace.comap Prod.fst inferInstance := rfl

lemma ℱ₀_of_two_le {n : ℕ} (hn : 2 ≤ n) : ℱ₀ n = (inferInstance : MeasurableSpace Ω₀) := by
  change (if n = 0 then _ else _) = _
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- **The intermediate σ-algebra is not trivial**: the censoring event is known at time `1`. -/
theorem filtration_one_ne_bot : ℱ₀ 1 ≠ ⊥ := by
  intro h
  have hs : MeasurableSet[ℱ₀ 1] {ω : Ω₀ | ω.1 = true} :=
    ⟨{true}, MeasurableSet.of_discrete, by ext ω; simp⟩
  rw [h, MeasurableSpace.measurableSet_bot_iff] at hs
  rcases hs with hs | hs
  · exact (Set.ext_iff.1 hs (true, true)).1 rfl
  · exact absurd ((Set.ext_iff.1 hs (false, true)).2 trivial) (by simp)

/-- **The intermediate σ-algebra is not everything**: the death coin is not known at time `1`. -/
theorem filtration_one_ne_top : ℱ₀ 1 ≠ (inferInstance : MeasurableSpace Ω₀) := by
  intro h
  have hs : MeasurableSet[ℱ₀ 1] {ω : Ω₀ | ω.2 = true} := by
    rw [h]; exact MeasurableSet.of_discrete
  rw [ℱ₀_one, MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t, -, ht⟩ := hs
  have h1 : (false, true) ∈ Prod.fst ⁻¹' t := ht ▸ rfl
  have h2 : (false, false) ∈ Prod.fst ⁻¹' t := h1
  rw [ht] at h2
  simp at h2

/-- The death counting process: `N_n = 1` from step `2` on iff the subject was not censored and
the death coin came up. -/
def deaths : ℕ → Ω₀ → ℝ := fun n ω => if 2 ≤ n ∧ ω.1 = false ∧ ω.2 = true then 1 else 0

/-- The at-risk process: at risk at step `1`, at step `2` only if not censored at time `1`,
never afterwards. -/
def atRisk : ℕ → Ω₀ → ℝ := fun n ω => if n = 1 ∨ (n = 2 ∧ ω.1 = false) then 1 else 0

/-- The cumulative hazard: `Δα₁ = 0`, `Δα₂ = 1/2`, no hazard afterwards. -/
noncomputable def hazard : ℕ → ℝ := fun n => if n ≤ 1 then 0 else 1 / 2

lemma hazard_increment (k : ℕ) : hazard (k + 1) - hazard k = if k = 1 then 1 / 2 else 0 := by
  unfold hazard; split_ifs <;> first | omega | norm_num

lemma hazard_increment_mem (k : ℕ) :
    0 ≤ hazard (k + 1) - hazard k ∧ hazard (k + 1) - hazard k < 1 := by
  rw [hazard_increment]; split_ifs <;> norm_num

lemma hazard_increment_ne_one (k : ℕ) : hazard (k + 1) - hazard k ≠ 1 :=
  (hazard_increment_mem k).2.ne

lemma atRisk_mem (n : ℕ) (ω : Ω₀) : atRisk n ω = 0 ∨ 1 ≤ atRisk n ω := by
  unfold atRisk; split_ifs <;> simp

lemma deaths_le_atRisk (n : ℕ) (ω : Ω₀) :
    0 ≤ deaths (n + 1) ω - deaths n ω ∧ deaths (n + 1) ω - deaths n ω ≤ atRisk (n + 1) ω := by
  obtain ⟨c, d⟩ := ω
  rcases n with _ | _ | n <;> cases c <;> cases d <;> simp [deaths, atRisk]

lemma stronglyAdapted_deaths : StronglyAdapted ℱ₀ deaths := fun n => by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : deaths n = fun _ => 0 := by funext ω; simp [deaths]; omega
    rw [this]; exact stronglyMeasurable_const
  · rw [ℱ₀_of_two_le hn]; exact (measurable_of_countable _).stronglyMeasurable

lemma isStronglyPredictable_atRisk : IsStronglyPredictable ℱ₀ atRisk := by
  refine .of_measurable_add_one ?_ fun n => ?_
  · have : atRisk 0 = fun _ => 0 := by funext ω; simp [atRisk]
    rw [this]; exact stronglyMeasurable_const
  · rcases n with _ | _ | n
    · have : atRisk (0 + 1) = fun _ => 1 := by funext ω; simp [atRisk]
      rw [this]; exact stronglyMeasurable_const
    · have : atRisk (1 + 1) = (fun c : Bool => if c = false then (1 : ℝ) else 0) ∘ Prod.fst := by
        funext ω; simp [atRisk]
      rw [this, ℱ₀_one]
      exact ((measurable_of_countable _).comp (comap_measurable _)).stronglyMeasurable
    · rw [ℱ₀_of_two_le (by omega)]; exact (measurable_of_countable _).stronglyMeasurable

/-- The martingale increment `ΔN_{k+1} - Y_{k+1} Δα_{k+1}` of the Aalen model. -/
private lemma aalen_increment (k : ℕ) (ω : Ω₀) :
    (deaths (k + 1) ω - aalenCompensator atRisk hazard (k + 1) ω) -
      (deaths k ω - aalenCompensator atRisk hazard k ω) =
      (deaths (k + 1) ω - deaths k ω) - atRisk (k + 1) ω * (hazard (k + 1) - hazard k) := by
  rw [aalenCompensator, stochasticIntegral_succ]; ring

/-- **Aalen's multiplicative intensity model holds**: `N - ∫ Y dα` is a martingale. At step `2`
the conditional death probability given the censoring coin is `1{c = false} · 1/2 = Y₂ Δα₂`. -/
theorem martingale_aalen :
    Martingale (fun n ω => deaths n ω - aalenCompensator atRisk hazard n ω) ℱ₀ μ₀ := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_) (fun _ => Integrable.of_finite)
    fun k => ?_
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · have : (fun ω => deaths n ω - aalenCompensator atRisk hazard n ω) = fun _ => 0 := by
        funext ω
        rcases n with _ | _ | n
        · simp [deaths, aalenCompensator]
        · simp [deaths, aalenCompensator, stochasticIntegral, hazard]
        · omega
      rw [this]; exact stronglyMeasurable_const
    · rw [ℱ₀_of_two_le hn]; exact (measurable_of_countable _).stronglyMeasurable
  · have hfun : ((fun n ω => deaths n ω - aalenCompensator atRisk hazard n ω) (k + 1) -
        (fun n ω => deaths n ω - aalenCompensator atRisk hazard n ω) k) =
        fun ω => (deaths (k + 1) ω - deaths k ω) - atRisk (k + 1) ω * (hazard (k + 1) - hazard k) :=
      funext fun ω => aalen_increment k ω
    rw [hfun]
    rcases k with _ | _ | k
    · have h0 : (fun ω : Ω₀ => (deaths (0 + 1) ω - deaths 0 ω) -
          atRisk (0 + 1) ω * (hazard (0 + 1) - hazard 0)) = 0 := by
        funext ω; simp [deaths, hazard]
      rw [h0, condExp_zero]
    · -- the step where the censoring coin is known but the death coin is not
      refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ₀.le 1) Integrable.of_finite
        (fun _ _ _ => integrableOn_zero) (fun s hs _ => ?_)
        aestronglyMeasurable_zero).symm
      rw [ℱ₀_one, MeasurableSpace.measurableSet_comap] at hs
      obtain ⟨t, -, rfl⟩ := hs
      have hf : (fun ω : Ω₀ => (deaths (1 + 1) ω - deaths 1 ω) -
          atRisk (1 + 1) ω * (hazard (1 + 1) - hazard 1)) =
          fun ω => if ω.1 = false then (if ω.2 = true then 1 / 2 else -(1 / 2)) else 0 := by
        funext ω
        obtain ⟨c, d⟩ := ω
        cases c <;> cases d <;> norm_num [deaths, atRisk, hazard]
      rw [hf, integral_zero, ← integral_indicator (measurable_fst (MeasurableSet.of_discrete)),
        integral_fintype Integrable.of_finite]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, μ₀_real_singleton, Set.indicator,
        Set.mem_preimage]
      by_cases ht : true ∈ t <;> by_cases hf : false ∈ t <;> simp [ht, hf]
    · have h0 : (fun ω : Ω₀ => (deaths (k + 2 + 1) ω - deaths (k + 2) ω) -
          atRisk (k + 2 + 1) ω * (hazard (k + 2 + 1) - hazard (k + 2))) = 0 := by
        funext ω
        obtain ⟨c, d⟩ := ω
        cases c <;> cases d <;> simp [deaths, atRisk, hazard]
      rw [h0, condExp_zero]

/-- **The remainder at time `2` is the censoring indicator**: `R₂ = Ŝ₁ / S₂ · 1{Y₂ = 0} · Δα₂
= 1 / (1/2) · 1{c} · 1/2 = 1{c}`. -/
theorem remainder_two (ω : Ω₀) :
    stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 2 ω =
      if ω.1 = true then 1 else 0 := by
  obtain ⟨c, d⟩ := ω
  cases c <;> cases d <;>
    simp [stochasticIntegral, kaplanMeierRemainder, kaplanMeierProcess, prodIntegral,
      nelsonAalenProcess, deaths, atRisk, hazard, sum_range_succ, prod_range_succ] <;> norm_num

/-- The remainder is `ℱ₁`-measurable: censoring known at time `1` determines it. -/
lemma stronglyMeasurable_remainder_two :
    StronglyMeasurable[ℱ₀ 1]
      (stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 2) := by
  have : stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 2 =
      (fun c : Bool => if c = true then (1 : ℝ) else 0) ∘ Prod.fst := funext remainder_two
  rw [this, ℱ₀_one]
  exact ((measurable_of_countable _).comp (comap_measurable _)).stronglyMeasurable

/-- **Conditional expectation given the intermediate σ-algebra**:
`E[R₂ | ℱ₁] = 1{c}`, the indicator of censoring at time `1`. -/
theorem condExp_remainder_two :
    μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 2 |
      ℱ₀ 1] = fun ω => if ω.1 = true then 1 else 0 := by
  rw [condExp_of_stronglyMeasurable (ℱ₀.le 1) stronglyMeasurable_remainder_two
    Integrable.of_finite]
  exact funext remainder_two

/-- **The Kaplan–Meier remainder is genuinely nonzero**: `E[R₂ | ℱ₁]` is not a.e. zero. -/
theorem condExp_remainder_two_ne_zero :
    ¬ μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 2 |
      ℱ₀ 1] =ᵐ[μ₀] 0 := by
  rw [condExp_remainder_two, Filter.EventuallyEq, ae_iff]
  intro h
  have hsub : ({(true, true)} : Set Ω₀) ⊆
      {ω | ¬ (if ω.1 = true then (1 : ℝ) else 0) = (0 : Ω₀ → ℝ) ω} := by simp
  have := measure_mono_null hsub h
  simp [μ₀] at this

/-- The model satisfies every hypothesis of Gill's Kaplan–Meier martingale
`martingale_kaplanMeierProcess`; hence `Ŝ/S - 1 - R` is a martingale here. -/
theorem martingale_kaplanMeier :
    Martingale (fun n ω => kaplanMeierProcess deaths atRisk n ω / prodIntegral hazard n - 1 -
      stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) n ω)
      ℱ₀ μ₀ :=
  martingale_kaplanMeierProcess martingale_aalen stronglyAdapted_deaths
    isStronglyPredictable_atRisk atRisk_mem deaths_le_atRisk hazard_increment_ne_one

/-- **The mean bias is the remainder**: `E[Ŝ₂/S₂] - 1 = E[R₂] = P(c) = 1/2`. -/
theorem integral_kaplanMeierProcess_div_sub_one :
    ∫ ω, (kaplanMeierProcess deaths atRisk 2 ω / prodIntegral hazard 2 - 1) ∂μ₀ = 1 / 2 := by
  rw [CountingProcess.integral_kaplanMeierProcess_div_sub_one martingale_aalen
    stronglyAdapted_deaths isStronglyPredictable_atRisk atRisk_mem deaths_le_atRisk
    hazard_increment_ne_one, integral_fintype Integrable.of_finite]
  simp only [remainder_two, Fintype.sum_prod_type, Fintype.sum_bool, μ₀_real_singleton]
  norm_num

end CensoredAtOne

end MathlibExt.Probability.Statistics.CountingProcess
