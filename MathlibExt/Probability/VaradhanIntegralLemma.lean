/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LargeDeviationPrinciple
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Varadhan's integral lemma

Let `μₙ` satisfy a large deviation principle with rate function `I` (not necessarily good),
and let `F : X → ℝ` be continuous and bounded. Then
`(1/n) log ∫ exp (n F) dμₙ → sup_x (F x - I x)` in `EReal`.

## Proof idea

* Lower bound: for `x` and `ε > 0`, the set `U = {y | F x - ε < F y}` is open and contains
  `x`, and `∫ exp (n F) dμₙ ≥ exp (n (F x - ε)) μₙ(U)`; the LDP lower bound on `U` gives
  `liminf ≥ F x - ε - I x`. Only lower semicontinuity of `F` is used.
* Upper bound: split `[-C, C]` into finitely many intervals `[aⱼ, aⱼ₊₁]` of length `δ`.
  The closed sets `Kⱼ = F⁻¹' [aⱼ, aⱼ₊₁]` cover `X` and
  `∫ exp (n F) dμₙ ≤ ∑ⱼ exp (n aⱼ₊₁) μₙ(Kⱼ)`. The LDP upper bound on each `Kⱼ` together
  with `aⱼ₊₁ ≤ F + δ` on `Kⱼ` gives `limsup ≤ sup_x (F x - I x) + O(δ)`.
  No goodness (tightness) of the rate function is needed.

All asymptotic statements are reduced to finite-`n` inequalities between `ℝ≥0∞` values
through `coe_le_inv_mul_log_iff` and `inv_mul_log_le_coe_iff`.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 2, Theorem 2.8 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf). The upper bound follows
the finite-partition argument of A. Dembo and O. Zeitouni, *Large Deviations Techniques and
Applications*, 2nd ed., Section 4.3.

## Main results

* `coe_le_inv_mul_log_iff`, `inv_mul_log_le_coe_iff`: translate bounds on
  `(1/n) log a` into bounds `a` versus `exp (n t)`.
* `le_liminf_log_lintegral_exp`: the lower bound, for lower semicontinuous `F`.
* `limsup_log_lintegral_exp_le`: the upper bound, for continuous bounded `F`.
* `tendsto_log_lintegral_exp`: Varadhan's integral lemma.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.Probability.VaradhanIntegralLemma

open MathlibExt.Probability.LargeDeviationPrinciple

/-- **Comparing a real number with a log-scaled mass from below.** For `n > 0`, a real number
`t` satisfies `t ≤ (1/n) log a` if and only if `exp (n t) ≤ a`. -/
theorem coe_le_inv_mul_log_iff {n : ℕ} (hn : 0 < n) (t : ℝ) (a : ℝ≥0∞) :
    (t : EReal) ≤ ((n : ℕ) : EReal)⁻¹ * ENNReal.log a ↔
      ENNReal.ofReal (Real.exp (n * t)) ≤ a := by
  have h0 : (0 : EReal) < (n : EReal) := by exact_mod_cast hn
  rw [← EReal.div_eq_inv_mul, EReal.le_div_iff_mul_le h0 (EReal.natCast_ne_top n),
    ← ENNReal.log_le_log_iff, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have : (t : EReal) * (n : EReal) = ((n * t : ℝ) : EReal) := by
    rw [mul_comm, EReal.coe_mul]; rfl
  rw [this]

/-- **Comparing a real number with a log-scaled mass from above.** For `n > 0` and a real
number `t`, `(1/n) log a ≤ t` if and only if `a ≤ exp (n t)`. -/
theorem inv_mul_log_le_coe_iff {n : ℕ} (hn : 0 < n) (t : ℝ) (a : ℝ≥0∞) :
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log a ≤ t ↔
      a ≤ ENNReal.ofReal (Real.exp (n * t)) := by
  have h0 : (0 : EReal) < (n : EReal) := by exact_mod_cast hn
  rw [← EReal.div_eq_inv_mul, EReal.div_le_iff_le_mul h0 (EReal.natCast_ne_top n),
    ← ENNReal.log_le_log_iff, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have : (n : EReal) * (t : EReal) = ((n * t : ℝ) : EReal) := by
    rw [EReal.coe_mul]; rfl
  rw [this]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Lower bound in Varadhan's integral lemma.** If `μₙ` satisfies an LDP with rate
function `I` and `F` is lower semicontinuous (no boundedness is needed), then
`sup_x (F x - I x) ≤ liminf (1/n) log ∫ exp (n F) dμₙ`. -/
theorem le_liminf_log_lintegral_exp {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : LowerSemicontinuous F) :
    (⨆ x, ((F x : EReal) - (I x : EReal))) ≤
      liminf (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))) atTop := by
  refine iSup_le fun x => ?_
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  obtain ⟨t, hbt, htx⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  refine hbt.le.trans ?_
  have hIx : I x ≠ ⊤ := by
    rintro h
    rw [h, EReal.coe_ennreal_top] at htx
    simp at htx
  set r := (I x).toReal with hr_def
  have hr : ((I x : ℝ≥0∞) : EReal) = (r : EReal) := (EReal.coe_ennreal_toReal hIx).symm
  rw [hr, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at htx
  set ε := (F x - r - t) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set U := F ⁻¹' Set.Ioi (F x - ε) with hU_def
  have hU : IsOpen U := hF.isOpen_preimage (F x - ε)
  have hxU : x ∈ U := by
    rw [hU_def, Set.mem_preimage, Set.mem_Ioi]
    linarith
  have hinf : (⨅ y ∈ U, (I y : EReal)) ≤ r := hr ▸ iInf₂_le x hxU
  have hs : ((-r - ε : ℝ) : EReal) <
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop := by
    refine lt_of_lt_of_le ?_ (hμ.lower_bound U hU)
    calc ((-r - ε : ℝ) : EReal) < ((-r : ℝ) : EReal) := by
          exact_mod_cast (show -r - ε < -r by linarith)
      _ = -(r : EReal) := by rw [EReal.coe_neg]
      _ ≤ -(⨅ y ∈ U, (I y : EReal)) := EReal.neg_le_neg_iff.2 hinf
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_lt_of_lt_liminf hs, eventually_gt_atTop 0] with n hn hn0
  rw [coe_le_inv_mul_log_iff hn0]
  have hμU : ENNReal.ofReal (Real.exp (n * (-r - ε))) < μ n U := by
    rw [← not_le, ← inv_mul_log_le_coe_iff hn0]
    exact not_le.2 hn
  calc ENNReal.ofReal (Real.exp (n * t))
      = ENNReal.ofReal (Real.exp (n * (F x - ε))) * ENNReal.ofReal (Real.exp (n * (-r - ε))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hε_def]
        ring
    _ ≤ ENNReal.ofReal (Real.exp (n * (F x - ε))) * μ n U := by gcongr
    _ = ∫⁻ y, U.indicator (fun _ => ENNReal.ofReal (Real.exp (n * (F x - ε)))) y ∂(μ n) :=
        (lintegral_indicator_const hU.measurableSet _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ U
        · rw [Set.indicator_of_mem hy]
          have hy' : F x - ε < F y := hy
          gcongr
        · rw [Set.indicator_of_notMem hy]
          exact zero_le

/-- **Upper bound in Varadhan's integral lemma.** If `μₙ` satisfies an LDP with rate
function `I` (not necessarily good) and `F` is continuous with `|F| ≤ C`, then
`limsup (1/n) log ∫ exp (n F) dμₙ ≤ sup_x (F x - I x)`. -/
theorem limsup_log_lintegral_exp_le {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    limsup (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))) atTop ≤
      ⨆ x, ((F x : EReal) - (I x : EReal)) := by
  set S := ⨆ x, ((F x : EReal) - (I x : EReal)) with hS_def
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨t, hSt, htc⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  refine le_trans ?_ htc.le
  obtain ⟨t₀, hSt₀, ht₀t⟩ := EReal.lt_iff_exists_real_btwn.1 hSt
  rw [EReal.coe_lt_coe_iff] at ht₀t
  set δ := (t - t₀) / 3 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set k := ⌊2 * C / δ⌋₊ + 1 with hk_def
  set a : ℕ → ℝ := fun j => -C + j * δ with ha_def
  set K : ℕ → Set X := fun j => F ⁻¹' Set.Icc (a j) (a (j + 1)) with hK_def
  have hKc : ∀ j, IsClosed (K j) := fun j => isClosed_Icc.preimage hF
  have hpiece : ∀ j, ∀ᶠ n : ℕ in atTop,
      μ n (K j) < ENNReal.ofReal (Real.exp (n * (t₀ + 2 * δ - a (j + 1)))) := by
    intro j
    have hle : -(⨅ y ∈ K j, (I y : EReal)) ≤ ((t₀ + δ - a (j + 1) : ℝ) : EReal) := by
      rw [EReal.neg_le]
      refine le_iInf₂ fun y hy => ?_
      have hy1 : a j ≤ F y := hy.1
      have hFI : (F y : EReal) - I y < t₀ :=
        (le_iSup (fun x => (F x : EReal) - I x) y).trans_lt hSt₀
      by_cases hIy : I y = ⊤
      · rw [hIy, EReal.coe_ennreal_top]
        exact le_top
      · rw [← EReal.coe_ennreal_toReal hIy, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hFI
        rw [← EReal.coe_ennreal_toReal hIy, ← EReal.coe_neg, EReal.coe_le_coe_iff]
        simp only [ha_def] at hy1 ⊢
        push_cast at hy1 ⊢
        linarith
    have hlt : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n (K j))) atTop <
        ((t₀ + 2 * δ - a (j + 1) : ℝ) : EReal) :=
      (hμ.upper_bound _ (hKc j)).trans_lt
        (hle.trans_lt (by exact_mod_cast (show t₀ + δ - a (j + 1) < t₀ + 2 * δ - a (j + 1) by
          linarith)))
    filter_upwards [eventually_lt_of_limsup_lt hlt, eventually_gt_atTop 0] with n hn hn0
    rw [← not_le, ← coe_le_inv_mul_log_iff hn0]
    exact not_le.2 hn
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range k,
      μ n (K j) < ENNReal.ofReal (Real.exp (n * (t₀ + 2 * δ - a (j + 1)))) :=
    (eventually_all_finset _).2 fun j _ => hpiece j
  have hk : ∀ᶠ n : ℕ in atTop, (k : ℝ) ≤ Real.exp (n * δ) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) * δ) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hδ
    filter_upwards [this.eventually_ge_atTop (k : ℝ)] with n hn
    linarith [Real.add_one_le_exp ((n : ℝ) * δ)]
  have hcover : ∀ (n : ℕ) (y : X), ENNReal.ofReal (Real.exp (n * F y)) ≤
      ∑ j ∈ Finset.range k,
        (K j).indicator (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y := by
    intro n y
    have hFy := abs_le.1 (hC y)
    have hnn : 0 ≤ (F y + C) / δ := div_nonneg (by linarith) hδ.le
    set j := ⌊(F y + C) / δ⌋₊ with hj_def
    have hj : j ∈ Finset.range k := by
      rw [Finset.mem_range, hk_def]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right
        (by linarith) hδ.le))
    have hyK : y ∈ K j := by
      have h1 := Nat.floor_le hnn
      have h2 := Nat.lt_floor_add_one ((F y + C) / δ)
      rw [← hj_def, le_div_iff₀ hδ] at h1
      rw [← hj_def, div_lt_iff₀ hδ] at h2
      simp only [hK_def, ha_def, Set.mem_preimage, Set.mem_Icc]
      push_cast
      constructor <;> linarith
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun j => (K j).indicator (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y)
      (fun _ _ => zero_le) hj)
    simp only [Set.indicator_of_mem hyK]
    have := hyK.2
    gcongr
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hall, hk, eventually_gt_atTop 0] with n hn hkn hn0
  rw [inv_mul_log_le_coe_iff hn0]
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n)
      ≤ ∫⁻ y, ∑ j ∈ Finset.range k,
          (K j).indicator (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y ∂(μ n) :=
        lintegral_mono fun y => hcover n y
    _ = ∑ j ∈ Finset.range k, ENNReal.ofReal (Real.exp (n * a (j + 1))) * μ n (K j) := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          exact lintegral_indicator_const (hKc j).measurableSet _
        · intro j _
          exact measurable_const.indicator (hKc j).measurableSet
    _ ≤ ∑ j ∈ Finset.range k, ENNReal.ofReal (Real.exp (n * (t₀ + 2 * δ))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        calc ENNReal.ofReal (Real.exp (n * a (j + 1))) * μ n (K j)
            ≤ ENNReal.ofReal (Real.exp (n * a (j + 1))) *
                ENNReal.ofReal (Real.exp (n * (t₀ + 2 * δ - a (j + 1)))) := by
              gcongr
              exact (hn j hj).le
          _ = ENNReal.ofReal (Real.exp (n * (t₀ + 2 * δ))) := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
              ring_nf
    _ = ENNReal.ofReal (k * Real.exp (n * (t₀ + 2 * δ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (n * t)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (k : ℝ) * Real.exp (n * (t₀ + 2 * δ))
            ≤ Real.exp (n * δ) * Real.exp (n * (t₀ + 2 * δ)) := by gcongr
          _ = Real.exp (n * t) := by
              rw [← Real.exp_add]
              congr 1
              rw [hδ_def]
              ring

/-- **Varadhan's integral lemma.** If a sequence of measures `μₙ` satisfies a large
deviation principle with rate function `I` and `F : X → ℝ` is continuous and bounded, then
`(1/n) log ∫ exp (n F) dμₙ → sup_x (F x - I x)` in `EReal`.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 2, Theorem 2.8 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).
The upper bound follows the finite-partition argument of A. Dembo and O. Zeitouni,
*Large Deviations Techniques and Applications*, 2nd ed., Section 4.3.

As in Varadhan's Remarks 2.9–2.10, the lower bound (`le_liminf_log_lintegral_exp`) needs only
lower semicontinuity of `F` and no boundedness. This version does not need a good rate
function: the finite partition of the range of `F` replaces the tightness argument. -/
theorem tendsto_log_lintegral_exp {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n)))
      atTop (𝓝 (⨆ x, ((F x : EReal) - (I x : EReal)))) :=
  tendsto_of_le_liminf_of_limsup_le (le_liminf_log_lintegral_exp hμ hF.lowerSemicontinuous)
    (limsup_log_lintegral_exp_le hμ hF hC)

end MathlibExt.Probability.VaradhanIntegralLemma
