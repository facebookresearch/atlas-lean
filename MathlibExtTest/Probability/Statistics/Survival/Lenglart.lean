/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Lenglart

/-!
# Tests for `Lenglart`

* **Sharpness of Lenglart's bound.** For the deterministic process `X = A = k` on `Fin 4`, all
  hypotheses of `measure_le_sup_le` hold, and with `K = 1`, `ε = 1`, `η = 2` both sides equal `1`,
  each computed from the definitions.
* **Predictability cannot be dropped.** On the uniform `Fin 4` with the filtration that is trivial
  at step `0`, `X₁ = 1{ω ≠ 3}` and `A₁ = 3 · 1{ω = 3}` satisfy every hypothesis of
  `measure_le_sup_le` except predictability (`A₁` is not `F₀`-measurable): `X` is dominated by
  `A` at every stopping time `τ ≤ 1`. Yet `P(max X ≥ 1) = 3/4` while
  `E[A₁ ∧ 1] + P(A₁ ≥ 1) = 1/2`.
* **The normalized variance.** `wVar` of two subjects with covariates `1, 0` and `limVar` of the
  normalized sums are both `1/4`, computed separately.
* **Non-vacuity of `IsAndersenGillRegular`.** All conditions hold for the deterministic family
  in which `n` subjects with covariate `0` stay at risk for `n` steps, `Δα = 1/n` (limit `i = 0`).
  The deterministic part (`lower_le`, `sum_hazard_le`, `tendsto_det`) also holds with a
  positive limit: constant limits `s⁽⁰⁾ = 1`, `s⁽¹⁾ = s⁽²⁾ = 1/2` and `Δα = 1/n` give the
  deterministic compensator `1/4` for every `n ≥ 1`.

No fixture exhibits `IsCoxCountingProcess` and `IsAndersenGillRegular` jointly with `v > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxCountingProcessConditions
open MathlibExt.Probability.Statistics.Lenglart
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.Lenglart

/-! ### A uniform probability on `Fin 4` and a filtration trivial at step `0` -/

/-- The uniform probability on `Fin 4`. -/
noncomputable def unif4 : Measure (Fin 4) :=
  ENNReal.ofReal (1 / 4) • (Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2 + Measure.dirac 3)

theorem unif4_apply (s : Set (Fin 4)) :
    unif4 s = ENNReal.ofReal (1 / 4) * (s.indicator 1 0 + s.indicator 1 1 + s.indicator 1 2 +
      s.indicator 1 3) := by
  simp only [unif4, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, smul_eq_mul]

instance : IsProbabilityMeasure unif4 := by
  constructor
  rw [unif4_apply]
  simp only [Set.indicator_univ, Pi.one_apply]
  rw [show (1 : ℝ≥0∞) + 1 + 1 + 1 = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem integral_unif4 (f : Fin 4 → ℝ) :
    ∫ ω, f ω ∂unif4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  rw [unif4, integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_add_measure Integrable.of_finite Integrable.of_finite, integral_dirac, integral_dirac,
    integral_dirac, integral_dirac]
  rw [ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
  ring

/-- The σ-algebras of the `Fin 4` filtration: trivial at step `0`, everything from step `1` on. -/
abbrev seq4 (k : ℕ) : MeasurableSpace (Fin 4) := if k = 0 then ⊥ else ⊤

theorem monotone_seq4 : Monotone seq4 := by
  intro i j hij
  by_cases hi : i = 0
  · simp only [seq4, hi, ↓reduceIte]
    exact bot_le
  · have hj : j ≠ 0 := by omega
    simp only [seq4, hi, hj, ↓reduceIte, le_refl]

theorem seq4_le (k : ℕ) : seq4 k ≤ Fin.instMeasurableSpace 4 := by
  unfold seq4
  split_ifs
  · exact bot_le
  · exact le_top

/-- Nothing is known at step `0`; everything is known from step `1` on. -/
def filtration4 : Filtration ℕ (Fin.instMeasurableSpace 4) := ⟨seq4, monotone_seq4, seq4_le⟩

theorem filtration4_zero : (filtration4 0 : MeasurableSpace (Fin 4)) = ⊥ := rfl

theorem filtration4_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    (filtration4 k : MeasurableSpace (Fin 4)) = ⊤ := by
  change seq4 k = _
  simp only [seq4, hk, ↓reduceIte]

theorem measurable_filtration4 {k : ℕ} (hk : k ≠ 0) (f : Fin 4 → ℝ) :
    Measurable[filtration4 k] f := by
  rw [filtration4_of_ne_zero hk]
  exact measurable_from_top

/-! ### Sharpness: a deterministic process attains the bound -/

/-- The deterministic process `k ↦ k`. -/
def detProc (k : ℕ) (_ω : Fin 4) : ℝ := k

/-- All hypotheses of `measure_le_sup_le` hold for `X = A = detProc` (with predictability). -/
theorem lenglart_detProc :
    unif4 {ω | (1 : ℝ) ≤ (range (1 + 1)).sup' nonempty_range_add_one fun k => detProc k ω} ≤
      ENNReal.ofReal ((∫ ω, min (detProc 1 ω) 2 ∂unif4) / 1) + unif4 {ω | (2 : ℝ) ≤ detProc 1 ω} :=
  measure_le_sup_le (F := filtration4) 1 (fun _ => measurable_const) (fun _ => measurable_const)
    (Eventually.of_forall fun _ k => Nat.cast_nonneg k)
    (Eventually.of_forall fun _ => by simp)
    (Eventually.of_forall fun _ => fun a b hab => by simpa [detProc] using hab)
    (fun _ => integrable_const _) (fun _ => integrable_const _)
    (fun _ _ _ => le_rfl) one_pos two_pos

/-- The left side of Lenglart's bound for `detProc`, computed directly: `1`. -/
theorem lhs_detProc :
    unif4 {ω | (1 : ℝ) ≤ (range (1 + 1)).sup' nonempty_range_add_one fun k => detProc k ω} = 1 := by
  have h : {ω : Fin 4 | (1 : ℝ) ≤ (range (1 + 1)).sup' nonempty_range_add_one
      fun k => detProc k ω} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_sup'_of_le (fun k => detProc k ω) (b := 1) (by simp) (by simp [detProc])
  rw [h, measure_univ]

/-- The right side of Lenglart's bound for `detProc`, computed directly: also `1`. -/
theorem rhs_detProc :
    ENNReal.ofReal ((∫ ω, min (detProc 1 ω) 2 ∂unif4) / 1) +
      unif4 {ω | (2 : ℝ) ≤ detProc 1 ω} = 1 := by
  have h : {ω : Fin 4 | (2 : ℝ) ≤ detProc 1 ω} = ∅ := by
    ext ω
    simp only [detProc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    norm_num
  rw [h, measure_empty, add_zero, integral_unif4]
  norm_num [detProc]

/-! ### Predictability of the dominating process is needed -/

/-- `X₁ = 1{ω ≠ 3}` from step `1` on. -/
noncomputable def cX (k : ℕ) (ω : Fin 4) : ℝ := if 1 ≤ k ∧ ω ≠ 3 then 1 else 0

/-- `A₁ = 3 · 1{ω = 3}` from step `1` on: adapted, nondecreasing, but not predictable. -/
noncomputable def cA (k : ℕ) (ω : Fin 4) : ℝ := if 1 ≤ k ∧ ω = 3 then 3 else 0

theorem cX_zero : cX 0 = fun _ => 0 := by funext ω; simp [cX]

theorem cA_zero : cA 0 = fun _ => 0 := by funext ω; simp [cA]

theorem adapted_cX : Adapted filtration4 cX := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [cX_zero]
    exact measurable_const
  · exact measurable_filtration4 hk _

/-- `A₁` is not `F₀`-measurable. -/
theorem not_measurable_cA_one : ¬ Measurable[filtration4 0] (cA 1) := by
  intro hm
  have hs : MeasurableSet[filtration4 0] (cA 1 ⁻¹' {3}) := hm (measurableSet_singleton 3)
  rw [filtration4_zero, MeasurableSpace.measurableSet_bot_iff] at hs
  have h3 : (3 : Fin 4) ∈ cA 1 ⁻¹' {3} := by simp [cA]
  have h0 : (0 : Fin 4) ∉ cA 1 ⁻¹' {3} := by simp [cA]
  rcases hs with h | h
  · rw [h] at h3
    exact h3
  · rw [h] at h0
    exact h0 (Set.mem_univ _)

/-- A stopping time `τ ≤ 1` for the filtration trivial at `0` is constant, so `X` is dominated
by `A` (with equality) at every such `τ`. -/
theorem dom_cX_cA (τ : Fin 4 → WithTop ℕ) (hτ : IsStoppingTime filtration4 τ)
    (hτK : ∀ ω, τ ω ≤ (1 : ℕ)) :
    ∫ ω, stoppedValue cX τ ω ∂unif4 ≤ ∫ ω, stoppedValue cA τ ω ∂unif4 := by
  have hs := hτ 0
  rw [filtration4_zero, MeasurableSpace.measurableSet_bot_iff] at hs
  rcases hs with h | h
  · -- `τ = 1` everywhere
    have h1 : ∀ ω, τ ω = (1 : ℕ) := by
      intro ω
      have hω := Set.eq_empty_iff_forall_notMem.1 h ω
      simp only [Set.mem_ofPred_eq, not_le] at hω
      have hle := hτK ω
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
      rw [← hm] at hω hle ⊢
      have hm1 : m ≤ 1 := WithTop.coe_le_coe.1 hle
      have hm0 : 0 < m := WithTop.coe_lt_coe.1 hω
      have : m = 1 := by omega
      subst this
      rfl
    have hX : stoppedValue cX τ = cX 1 := by
      funext ω; simp only [stoppedValue, h1 ω]; rfl
    have hA : stoppedValue cA τ = cA 1 := by
      funext ω; simp only [stoppedValue, h1 ω]; rfl
    rw [hX, hA, integral_unif4, integral_unif4]
    norm_num [cX, cA]
  · -- `τ = 0` everywhere
    have h0 : ∀ ω, τ ω = (0 : ℕ) := by
      intro ω
      have hω := Set.eq_univ_iff_forall.1 h ω
      simp only [Set.mem_ofPred_eq] at hω
      exact le_antisymm hω (by simp)
    have hX : stoppedValue cX τ = cX 0 := by
      funext ω; simp only [stoppedValue, h0 ω]; rfl
    have hA : stoppedValue cA τ = cA 0 := by
      funext ω; simp only [stoppedValue, h0 ω]; rfl
    rw [hX, hA, cX_zero, cA_zero]

/-- The remaining hypotheses of `measure_le_sup_le` hold for `cX` and `cA`. -/
theorem hyps_cX_cA :
    (∀ᵐ ω ∂unif4, ∀ k, 0 ≤ cX k ω) ∧ (∀ᵐ ω ∂unif4, cA 0 ω = 0) ∧
      (∀ᵐ ω ∂unif4, Monotone fun k => cA k ω) ∧ (∀ k, Integrable (cX k) unif4) ∧
      (∀ k, Integrable (cA k) unif4) := by
  refine ⟨Eventually.of_forall fun ω k => ?_, Eventually.of_forall fun ω => by simp [cA],
    Eventually.of_forall fun ω => ?_, fun _ => Integrable.of_finite, fun _ => Integrable.of_finite⟩
  · unfold cX; split_ifs <;> norm_num
  · intro a b hab
    simp only [cA]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd ⟨h1.1.trans hab, h1.2⟩ h2
    · norm_num
    · exact le_rfl

/-- Without predictability the conclusion of Lenglart's inequality fails:
`P(max_{k ≤ 1} X_k ≥ 1) = 3/4 > 1/2 = E[A₁ ∧ 1] + P(A₁ ≥ 1)`. -/
theorem not_lenglart_cX_cA :
    ¬ unif4 {ω | (1 : ℝ) ≤ (range (1 + 1)).sup' nonempty_range_add_one fun k => cX k ω} ≤
      ENNReal.ofReal ((∫ ω, min (cA 1 ω) 1 ∂unif4) / 1) + unif4 {ω | (1 : ℝ) ≤ cA 1 ω} := by
  have hL : {ω : Fin 4 | (1 : ℝ) ≤ (range (1 + 1)).sup' nonempty_range_add_one
      fun k => cX k ω} = {ω | ω ≠ 3} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hle h3
      have : (range (1 + 1)).sup' nonempty_range_add_one (fun k => cX k ω) = 0 := by
        refine le_antisymm (sup'_le _ _ fun k _ => by simp [cX, h3]) ?_
        exact le_sup'_of_le (fun k => cX k ω) (b := 0) (by simp) (by simp [cX])
      linarith
    · intro h3
      exact le_sup'_of_le (fun k => cX k ω) (b := 1) (by simp) (by simp [cX, h3])
  have hR : {ω : Fin 4 | (1 : ℝ) ≤ cA 1 ω} = {3} := by
    ext ω
    simp only [cA, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    by_cases h3 : ω = 3 <;> simp [h3]
  rw [hL, hR, integral_unif4, unif4_apply, unif4_apply]
  norm_num [cA, Set.indicator]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-! ### The normalized weighted variance -/

/-- Covariates `1, 0`. -/
def z₂ : Fin 2 → ℝ := ![1, 0]

/-- `V(0)` of two at-risk subjects with covariates `1, 0`, from the definition: `1/4`. -/
theorem wVar_z₂ : wVar (fun _ => 1) z₂ 0 = 1 / 4 := by
  simp [wVar, wMean, wSum, z₂, Fin.sum_univ_two]
  norm_num

/-- `v(S⁽⁰⁾/2, S⁽¹⁾/2, S⁽²⁾/2) = v(1, 1/2, 1/2)`, from the definition: also `1/4`. -/
theorem limVar_z₂ : limVar 1 (1 / 2) (1 / 2) = 1 / 4 := by
  norm_num [limVar]

example : wVar (fun _ => 1) z₂ 0 = limVar 1 (1 / 2) (1 / 2) := by
  rw [wVar_z₂, limVar_z₂]

/-! ### Non-vacuity of `IsAndersenGillRegular` -/

/-- Everybody is at risk through grid time `n`. -/
def tAll (n : ℕ) (_ω : Fin 4) (_l : Fin n) : ℕ := n

/-- Zero covariates. -/
def zZero (n : ℕ) (_ω : Fin 4) (_l : Fin n) : ℝ := 0

/-- Baseline hazard increments `1/n`. -/
noncomputable def dαInv (n _k : ℕ) : ℝ := 1 / n

/-- Deterministic limits `s⁽⁰⁾ = 1`, `s⁽¹⁾ = s⁽²⁾ = 0`. -/
def sZero (_n j _k : ℕ) (_b : ℝ) : ℝ := if j = 0 then 1 else 0

theorem wSum_tAll_div {n k : ℕ} (hk : k < n) (j : ℕ) (b : ℝ) (ω : Fin 4) :
    wSum (atRiskInd (tAll n ω) k) (zZero n ω) j b / n = sZero n j k b := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hY : ∀ l, atRiskInd (tAll n ω) k l = 1 := fun l => by
    simp [atRiskInd, tAll, Nat.succ_le_of_lt hk]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp [wSum, hY, zZero, sZero, hn]
  · simp [wSum, hY, zZero, sZero, zero_pow hj.ne', hj.ne']

theorem sum_dαInv_le (n : ℕ) : ∑ k ∈ range n, dαInv n k ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [dαInv, hn']

theorem detInfoCompensator_sZero (n : ℕ) (b : ℝ) :
    detInfoCompensator (sZero n) (dαInv n) 0 b n = 0 := by
  simp [detInfoCompensator, sZero, limVar]

/-- All conditions of `IsAndersenGillRegular` hold for the deterministic family. -/
theorem isAndersenGillRegular_tAll :
    IsAndersenGillRegular unif4 tAll zZero dαInv (fun n => n) 0 1 sZero 1 1 (fun _ => 0) where
  radius_nonneg := zero_le_one
  lower_pos := one_pos
  tendsto_wSum j _ η hη := by
    have h : ∀ n : ℕ, {ω : Fin 4 | ∃ k < n, ∃ b ∈ Set.Icc ((0 : ℝ) - 1) (0 + 1),
        η ≤ |wSum (atRiskInd (tAll n ω) k) (zZero n ω) j b / n - sZero n j k b|} = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro k hk b _
      rw [wSum_tAll_div hk, sub_self, abs_zero]
      exact hη
    simp only [h, measure_empty]
    exact tendsto_const_nhds
  lower_le _ _ _ _ _ := by simp [sZero]
  sum_hazard_le n := sum_dαInv_le n
  tendsto_det ε hε := Eventually.of_forall fun n b _ => by
    rw [detInfoCompensator_sZero, sub_zero, abs_zero]
    exact hε

/-- Constant limits with a nonzero variance: `s⁽⁰⁾ = 1`, `s⁽¹⁾ = s⁽²⁾ = 1/2`. -/
noncomputable def sHalf (_n j _k : ℕ) (_b : ℝ) : ℝ := if j = 0 then 1 else 1 / 2

/-- The deterministic compensator of `sHalf` with `Δα = 1/n` is `1/4` for `n ≥ 1`. -/
theorem detInfoCompensator_sHalf {n : ℕ} (hn : 1 ≤ n) (β₀ b : ℝ) :
    detInfoCompensator (sHalf n) (dαInv n) β₀ b n = 1 / 4 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [detInfoCompensator, sHalf, limVar, dαInv, sum_const, card_range, nsmul_eq_mul]
  norm_num
  field_simp

/-- The deterministic conditions of `IsAndersenGillRegular` (`lower_le`, `sum_hazard_le`,
`tendsto_det`) hold for `sHalf` with the positive limit `i = 1/4`. -/
theorem det_conditions_sHalf (β₀ r : ℝ) :
    (∀ n, ∀ k < n, ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r), (1 : ℝ) ≤ sHalf n 0 k b) ∧
    (∀ n, ∑ k ∈ range n, dαInv n k ≤ 1) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      |detInfoCompensator (sHalf n) (dαInv n) β₀ b n - 1 / 4| < ε) := by
  refine ⟨fun _ _ _ _ _ => by simp [sHalf], sum_dαInv_le, fun ε hε => ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn b _
  rw [detInfoCompensator_sHalf hn, sub_self, abs_zero]
  exact hε

end MathlibExtTest.Probability.Statistics.Lenglart
