/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.VaradhanIntegralLemma
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The tilted large deviation principle

Let probability measures `μₙ` satisfy a large deviation principle with rate function `I`, and
let `F : X → ℝ` be continuous and bounded. The tilted measures

`Qₙ = (∫ exp (n F) dμₙ)⁻¹ • exp (n F) μₙ`

satisfy a large deviation principle with rate function `J x = S - (F x - I x)`, where
`S = sup_x (F x - I x)` (a finite number).

## Proof idea

For a measurable set `A`, `Qₙ(A) = (∫_A exp (n F) dμₙ) / ∫ exp (n F) dμₙ`. The denominator
behaves like `exp (n S)` by Varadhan's integral lemma (`tendsto_log_lintegral_exp`). The
numerator is controlled by local versions of the two halves of Varadhan's lemma:

* for an open set `U` and `x ∈ U`, `∫_U exp (n F) dμₙ ≳ exp (n (F x - I x))`
  (`eventually_ofReal_exp_le_setLIntegral_exp`);
* for a closed set `K`, `∫_K exp (n F) dμₙ ≲ exp (n sup_K (F - I))`, by the finite partition of
  the range of `F` (`eventually_setLIntegral_exp_le_ofReal_exp`).

All asymptotic statements are reduced to finite-`n` inequalities between `ℝ≥0∞` values.
The rate function `J` is lower semicontinuous because `F` is continuous and `I` is lower
semicontinuous.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 2, Theorem 2.11 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).

## Main results

* `tiltedMeasure`: the tilted measures `Qₙ`.
* `le_liminf_log_setLIntegral_exp`, `limsup_log_setLIntegral_exp_le`: the two bounds of
  Varadhan's integral lemma for integrals over open, respectively closed, sets.
* `tiltedRate_eq_zero_iff`: the tilted rate function vanishes exactly at the maximisers of
  `F - I`.
* `satisfiesLDP_tiltedMeasure`: the tilted large deviation principle.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.Probability.TiltedLDP

open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.VaradhanIntegralLemma

/-- **Inverse of an exponential mass.** `(exp a)⁻¹ = exp (-a)` in `ℝ≥0∞`. -/
theorem inv_ofReal_exp (a : ℝ) :
    (ENNReal.ofReal (Real.exp a))⁻¹ = ENNReal.ofReal (Real.exp (-a)) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos a), Real.exp_neg]

/-- **Product of exponential masses.** `exp a * exp b = exp (a + b)` in `ℝ≥0∞`. -/
theorem ofReal_exp_mul_ofReal_exp (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-- **Zeros of the tilted rate function.** The rate function `J x = S - (F x - I x)`, with
`S = sup_y (F y - I y)`, vanishes exactly at the maximisers of `F - I`. -/
theorem tiltedRate_eq_zero_iff {X : Type*} (F : X → ℝ) (I : X → ℝ≥0∞) (x : X) :
    ((⨆ y, ((F y : EReal) - (I y : EReal))) - ((F x : EReal) - (I x : EReal))).toENNReal = 0 ↔
      (F x : EReal) - (I x : EReal) = ⨆ y, ((F y : EReal) - (I y : EReal)) := by
  rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
  exact ⟨fun h => le_antisymm (le_iSup (fun y => (F y : EReal) - (I y : EReal)) x) h,
    fun h => h.ge⟩

section Def

variable {X : Type*} [MeasurableSpace X]

/-- **Tilted measures.** The measure `Qₙ = (∫ exp (n F) dμₙ)⁻¹ • exp (n F) μₙ`, the `n`-th
measure `μₙ` reweighted by the density `exp (n F)` and renormalised. It is a probability measure
when the normaliser `Zₙ = ∫ exp (n F) dμₙ` is positive and finite, for example for a probability
measure `μₙ` and a bounded `F`, the setting of `satisfiesLDP_tiltedMeasure`. Otherwise it is the
zero measure: for `Zₙ = ∞` because `∞⁻¹ = 0`, and for `Zₙ = 0` because then the reweighted
measure is zero. -/
noncomputable def tiltedMeasure (μ : ℕ → Measure X) (F : X → ℝ) (n : ℕ) : Measure X :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))⁻¹ •
    (μ n).withDensity fun x => ENNReal.ofReal (Real.exp (n * F x))

/-- **Mass of a measurable set under a tilted measure.**
`Qₙ(A) = (∫ exp (n F) dμₙ)⁻¹ * ∫_A exp (n F) dμₙ`. -/
theorem tiltedMeasure_apply (μ : ℕ → Measure X) (F : X → ℝ) (n : ℕ) {A : Set X}
    (hA : MeasurableSet A) :
    tiltedMeasure μ F n A = (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))⁻¹ *
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n) := by
  rw [tiltedMeasure, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul]

end Def

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Local lower bound for a restricted exponential integral.** If `μₙ` satisfies an LDP with
rate function `I`, `F` is lower semicontinuous, `U` is open, `x ∈ U` and `I x < ∞`, then for
every `ε > 0`, eventually `exp (n (F x - I x - ε)) ≤ ∫_U exp (n F) dμₙ`. -/
theorem eventually_ofReal_exp_le_setLIntegral_exp {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : LowerSemicontinuous F) {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) (hIx : I x ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * (F x - (I x).toReal - ε))) ≤
      ∫⁻ y in U, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n) := by
  set r := (I x).toReal with hr_def
  have hr : ((I x : ℝ≥0∞) : EReal) = (r : EReal) := (EReal.coe_ennreal_toReal hIx).symm
  set V := U ∩ F ⁻¹' Set.Ioi (F x - ε / 2) with hV_def
  have hV : IsOpen V := hU.inter (hF.isOpen_preimage _)
  have hxV : x ∈ V := ⟨hx, by rw [Set.mem_preimage, Set.mem_Ioi]; linarith⟩
  have hinf : (⨅ y ∈ V, (I y : EReal)) ≤ r := hr ▸ iInf₂_le x hxV
  have hs : ((-r - ε / 2 : ℝ) : EReal) <
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n V)) atTop := by
    refine lt_of_lt_of_le ?_ (hμ.lower_bound V hV)
    calc ((-r - ε / 2 : ℝ) : EReal) < ((-r : ℝ) : EReal) := by
          exact_mod_cast (show -r - ε / 2 < -r by linarith)
      _ = -(r : EReal) := by rw [EReal.coe_neg]
      _ ≤ -(⨅ y ∈ V, (I y : EReal)) := EReal.neg_le_neg_iff.2 hinf
  filter_upwards [eventually_lt_of_lt_liminf hs, eventually_gt_atTop 0] with n hn hn0
  have hμV : ENNReal.ofReal (Real.exp (n * (-r - ε / 2))) < μ n V := by
    rw [← not_le, ← inv_mul_log_le_coe_iff hn0]
    exact not_le.2 hn
  calc ENNReal.ofReal (Real.exp (n * (F x - r - ε)))
      = ENNReal.ofReal (Real.exp (n * (F x - ε / 2))) *
          ENNReal.ofReal (Real.exp (n * (-r - ε / 2))) := by
        rw [ofReal_exp_mul_ofReal_exp]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (Real.exp (n * (F x - ε / 2))) * μ n V := by gcongr
    _ = ∫⁻ y in V, ENNReal.ofReal (Real.exp (n * (F x - ε / 2))) ∂(μ n) :=
        (setLIntegral_const V _).symm
    _ ≤ ∫⁻ y in V, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n) := by
        refine setLIntegral_mono' hV.measurableSet fun y hy => ?_
        have hy' : F x - ε / 2 < F y := hy.2
        gcongr
    _ ≤ ∫⁻ y in U, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n) :=
        lintegral_mono_set Set.inter_subset_left

/-- **Upper bound for a restricted exponential integral.** If `μₙ` satisfies an LDP with rate
function `I` (not necessarily good), `F` is continuous with `|F| ≤ C`, `K` is closed and
`F x - I x ≤ u` on `K`, then for every `t > u`, eventually `∫_K exp (n F) dμₙ ≤ exp (n t)`.
The proof is the finite-partition argument applied to the closed sets `K ∩ F⁻¹' [aⱼ, aⱼ₊₁]`. -/
theorem eventually_setLIntegral_exp_le_ofReal_exp {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    {K : Set X} (hK : IsClosed K) {u : ℝ} (hu : ∀ x ∈ K, (F x : EReal) - I x ≤ u) {t : ℝ}
    (hut : u < t) :
    ∀ᶠ n : ℕ in atTop, ∫⁻ y in K, ENNReal.ofReal (Real.exp (n * F y)) ∂(μ n) ≤
      ENNReal.ofReal (Real.exp (n * t)) := by
  set δ := (t - u) / 3 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set k := ⌊2 * C / δ⌋₊ + 1 with hk_def
  set a : ℕ → ℝ := fun j => -C + j * δ with ha_def
  set Kp : ℕ → Set X := fun j => K ∩ F ⁻¹' Set.Icc (a j) (a (j + 1)) with hKp_def
  have hKc : ∀ j, IsClosed (Kp j) := fun j => hK.inter (isClosed_Icc.preimage hF)
  have hpiece : ∀ j, ∀ᶠ n : ℕ in atTop,
      μ n (Kp j) < ENNReal.ofReal (Real.exp (n * (u + 2 * δ - a (j + 1)))) := by
    intro j
    have hle : -(⨅ y ∈ Kp j, (I y : EReal)) ≤ ((u + δ - a (j + 1) : ℝ) : EReal) := by
      rw [EReal.neg_le]
      refine le_iInf₂ fun y hy => ?_
      have hy1 : a j ≤ F y := hy.2.1
      have hFI : (F y : EReal) - I y ≤ u := hu y hy.1
      by_cases hIy : I y = ⊤
      · rw [hIy, EReal.coe_ennreal_top]
        exact le_top
      · rw [← EReal.coe_ennreal_toReal hIy, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hFI
        rw [← EReal.coe_ennreal_toReal hIy, ← EReal.coe_neg, EReal.coe_le_coe_iff]
        simp only [ha_def] at hy1 ⊢
        push_cast at hy1 ⊢
        linarith
    have hlt : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n (Kp j))) atTop <
        ((u + 2 * δ - a (j + 1) : ℝ) : EReal) :=
      (hμ.upper_bound _ (hKc j)).trans_lt
        (hle.trans_lt (by exact_mod_cast (show u + δ - a (j + 1) < u + 2 * δ - a (j + 1) by
          linarith)))
    filter_upwards [eventually_lt_of_limsup_lt hlt, eventually_gt_atTop 0] with n hn hn0
    rw [← not_le, ← coe_le_inv_mul_log_iff hn0]
    exact not_le.2 hn
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range k,
      μ n (Kp j) < ENNReal.ofReal (Real.exp (n * (u + 2 * δ - a (j + 1)))) :=
    (eventually_all_finset _).2 fun j _ => hpiece j
  have hk : ∀ᶠ n : ℕ in atTop, (k : ℝ) ≤ Real.exp (n * δ) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) * δ) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hδ
    filter_upwards [this.eventually_ge_atTop (k : ℝ)] with n hn
    linarith [Real.add_one_le_exp ((n : ℝ) * δ)]
  have hcover : ∀ (n : ℕ) (y : X),
      K.indicator (fun y => ENNReal.ofReal (Real.exp (n * F y))) y ≤
      ∑ j ∈ Finset.range k,
        (Kp j).indicator (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y := by
    intro n y
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
      have hFy := abs_le.1 (hC y)
      have hnn : 0 ≤ (F y + C) / δ := div_nonneg (by linarith) hδ.le
      set j := ⌊(F y + C) / δ⌋₊ with hj_def
      have hj : j ∈ Finset.range k := by
        rw [Finset.mem_range, hk_def]
        exact Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right
          (by linarith) hδ.le))
      have hyK' : y ∈ Kp j := by
        have h1 := Nat.floor_le hnn
        have h2 := Nat.lt_floor_add_one ((F y + C) / δ)
        rw [← hj_def, le_div_iff₀ hδ] at h1
        rw [← hj_def, div_lt_iff₀ hδ] at h2
        refine ⟨hyK, ?_⟩
        simp only [ha_def, Set.mem_preimage, Set.mem_Icc]
        push_cast
        constructor <;> linarith
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun j => (Kp j).indicator
          (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y)
        (fun _ _ => zero_le) hj)
      simp only [Set.indicator_of_mem hyK']
      have := hyK'.2.2
      gcongr
    · rw [Set.indicator_of_notMem hyK]
      exact zero_le
  filter_upwards [hall, hk] with n hn hkn
  rw [← lintegral_indicator hK.measurableSet]
  calc ∫⁻ y, K.indicator (fun y => ENNReal.ofReal (Real.exp (n * F y))) y ∂(μ n)
      ≤ ∫⁻ y, ∑ j ∈ Finset.range k,
          (Kp j).indicator (fun _ => ENNReal.ofReal (Real.exp (n * a (j + 1)))) y ∂(μ n) :=
        lintegral_mono fun y => hcover n y
    _ = ∑ j ∈ Finset.range k, ENNReal.ofReal (Real.exp (n * a (j + 1))) * μ n (Kp j) := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          exact lintegral_indicator_const (hKc j).measurableSet _
        · intro j _
          exact measurable_const.indicator (hKc j).measurableSet
    _ ≤ ∑ j ∈ Finset.range k, ENNReal.ofReal (Real.exp (n * (u + 2 * δ))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        calc ENNReal.ofReal (Real.exp (n * a (j + 1))) * μ n (Kp j)
            ≤ ENNReal.ofReal (Real.exp (n * a (j + 1))) *
                ENNReal.ofReal (Real.exp (n * (u + 2 * δ - a (j + 1)))) := by
              gcongr
              exact (hn j hj).le
          _ = ENNReal.ofReal (Real.exp (n * (u + 2 * δ))) := by
              rw [ofReal_exp_mul_ofReal_exp]
              ring_nf
    _ = ENNReal.ofReal (k * Real.exp (n * (u + 2 * δ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (n * t)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (k : ℝ) * Real.exp (n * (u + 2 * δ))
            ≤ Real.exp (n * δ) * Real.exp (n * (u + 2 * δ)) := by gcongr
          _ = Real.exp (n * t) := by
              rw [← Real.exp_add]
              congr 1
              rw [hδ_def]
              ring

/-- **Varadhan's lower bound on an open set.** If `μₙ` satisfies an LDP with rate function `I`,
`F` is lower semicontinuous and `U` is open, then
`sup_{x ∈ U} (F x - I x) ≤ liminf (1/n) log ∫_U exp (n F) dμₙ`. -/
theorem le_liminf_log_setLIntegral_exp {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : LowerSemicontinuous F) {U : Set X}
    (hU : IsOpen U) :
    (⨆ x ∈ U, ((F x : EReal) - (I x : EReal))) ≤
      liminf (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x in U, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))) atTop := by
  refine iSup₂_le fun x hx => ?_
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  obtain ⟨t, hbt, htx⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  refine hbt.le.trans ?_
  have hIx : I x ≠ ⊤ := by
    rintro h
    rw [h, EReal.coe_ennreal_top] at htx
    simp at htx
  rw [← EReal.coe_ennreal_toReal hIx, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at htx
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ofReal_exp_le_setLIntegral_exp hμ hF hU hx hIx
    (ε := F x - (I x).toReal - t) (by linarith), eventually_gt_atTop 0] with n hn hn0
  rw [coe_le_inv_mul_log_iff hn0]
  convert hn using 4
  ring

/-- **Varadhan's upper bound on a closed set.** If `μₙ` satisfies an LDP with rate function `I`
(not necessarily good), `F` is continuous with `|F| ≤ C` and `K` is closed, then
`limsup (1/n) log ∫_K exp (n F) dμₙ ≤ sup_{x ∈ K} (F x - I x)`. -/
theorem limsup_log_setLIntegral_exp_le {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    {K : Set X} (hK : IsClosed K) :
    limsup (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x in K, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))) atTop ≤
      ⨆ x ∈ K, ((F x : EReal) - (I x : EReal)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨t, hβt, htc⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨u, hβu, hut⟩ := EReal.lt_iff_exists_real_btwn.1 hβt
  rw [EReal.coe_lt_coe_iff] at hut
  refine le_trans ?_ htc.le
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_setLIntegral_exp_le_ofReal_exp hμ hF hC hK
    (fun x hx => (le_iSup₂ (f := fun x (_ : x ∈ K) => (F x : EReal) - I x) x hx).trans hβu.le)
    hut, eventually_gt_atTop 0] with n hn hn0
  rw [inv_mul_log_le_coe_iff hn0]
  exact hn

/-- **Tilted large deviation principle.** Let probability measures `μₙ` satisfy a large
deviation principle with rate function `I` (not necessarily good), and let `F : X → ℝ` be
continuous with `|F| ≤ C`. Then the tilted measures
`Qₙ = (∫ exp (n F) dμₙ)⁻¹ • exp (n F) μₙ` satisfy a large deviation principle with rate function
`J x = S - (F x - I x)`, where `S = sup_x (F x - I x)` is finite.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 2, Theorem 2.11 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf). -/
theorem satisfiesLDP_tiltedMeasure {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)]
    {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I) {F : X → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) :
    SatisfiesLDP (tiltedMeasure μ F)
      (fun x => ((⨆ y, ((F y : EReal) - (I y : EReal))) -
        ((F x : EReal) - (I x : EReal))).toENNReal) := by
  set S := ⨆ y, ((F y : EReal) - (I y : EReal)) with hS_def
  have hle : ∀ x, (F x : EReal) - I x ≤ S := fun x => le_iSup (fun y => (F y : EReal) - I y) x
  obtain ⟨x₀, hx₀⟩ : ∃ x, I x ≠ ⊤ := by
    by_contra h
    push Not at h
    have hub := hμ.upper_bound Set.univ isClosed_univ
    have h1 : (⨅ x ∈ Set.univ, (I x : EReal)) = ⊤ := by simp [h]
    have h2 : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Set.univ)) atTop = 0 := by
      simp
    rw [h1, h2, EReal.neg_top] at hub
    simp at hub
  have hS_ne_bot : S ≠ ⊥ := by
    refine (lt_of_lt_of_le (?_ : (⊥ : EReal) < _) (hle x₀)).ne'
    rw [← EReal.coe_ennreal_toReal hx₀, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  have hS_le : S ≤ C := iSup_le fun x => by
    by_cases hIx : I x = ⊤
    · rw [hIx, EReal.coe_ennreal_top]
      simp
    · rw [← EReal.coe_ennreal_toReal hIx, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := (abs_le.1 (hC x)).2
      have := ENNReal.toReal_nonneg (a := I x)
      linarith
  have hS_ne_top : S ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) hS_le
  set s := S.toReal with hs_def
  have hS : S = (s : EReal) := (EReal.coe_toReal hS_ne_top hS_ne_bot).symm
  have hJtop : ∀ x, I x = ⊤ → (S - ((F x : EReal) - I x)).toENNReal = ⊤ := by
    intro x hx
    rw [hx, EReal.coe_ennreal_top, hS]
    simp
  have hJfin : ∀ x, I x ≠ ⊤ → (S - ((F x : EReal) - I x)).toENNReal =
      ENNReal.ofReal (s - F x + (I x).toReal) ∧ F x - (I x).toReal ≤ s := by
    intro x hx
    have h1 := hle x
    rw [← EReal.coe_ennreal_toReal hx, ← EReal.coe_sub, hS] at h1 ⊢
    rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
    exact ⟨by congr 1; ring, EReal.coe_le_coe_iff.1 h1⟩
  have hden : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n))) atTop
      (𝓝 (s : EReal)) := by
    rw [← hS]
    exact tendsto_log_lintegral_exp hμ hF hC
  have hDup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n) ≤
        ENNReal.ofReal (Real.exp (n * (s + ε))) := by
    intro ε hε
    filter_upwards [hden.eventually (gt_mem_nhds (show (s : EReal) < ((s + ε : ℝ) : EReal) by
      exact_mod_cast (show s < s + ε by linarith))), eventually_gt_atTop 0] with n hn hn0
    exact (inv_mul_log_le_coe_iff hn0 _ _).1 hn.le
  have hDlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (n * (s - ε))) ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp (n * F x)) ∂(μ n) := by
    intro ε hε
    filter_upwards [hden.eventually (lt_mem_nhds (show ((s - ε : ℝ) : EReal) < (s : EReal) by
      exact_mod_cast (show s - ε < s by linarith))), eventually_gt_atTop 0] with n hn hn0
    exact (coe_le_inv_mul_log_iff hn0 _ _).1 hn.le
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · -- lower semicontinuity of the rate function
    intro x y hy
    beta_reduce at hy ⊢
    have hy_top : y ≠ ⊤ := ne_top_of_lt hy
    set y' := y.toReal with hy'_def
    have hyy : y = ENNReal.ofReal y' := (ENNReal.ofReal_toReal hy_top).symm
    have hy0 : 0 ≤ y' := ENNReal.toReal_nonneg
    obtain ⟨w, hw, hFw⟩ : ∃ w : ℝ, ((w : EReal) < I x) ∧
        ∀ᶠ x' in 𝓝 x, y' + F x' - s < w := by
      by_cases hIx : I x = ⊤
      · refine ⟨C + y' - s + 1, by rw [hIx, EReal.coe_ennreal_top]; exact EReal.coe_lt_top _,
          Filter.Eventually.of_forall fun x' => ?_⟩
        have := (abs_le.1 (hC x')).2
        linarith
      · rw [(hJfin x hIx).1, hyy, gt_iff_lt, ENNReal.ofReal_lt_ofReal_iff'] at hy
        refine ⟨y' + F x - s + (s - F x + (I x).toReal - y') / 2, ?_, ?_⟩
        · rw [← EReal.coe_ennreal_toReal hIx, EReal.coe_lt_coe_iff]
          linarith [hy.1]
        · filter_upwards [hF.continuousAt.eventually (gt_mem_nhds (show F x <
            F x + (s - F x + (I x).toReal - y') / 2 by linarith [hy.1]))] with x' hx'
          linarith
    have hIev : ∀ᶠ x' in 𝓝 x, (w : EReal) < I x' := by
      by_cases hw0 : w < 0
      · refine Filter.Eventually.of_forall fun x' => ?_
        exact lt_of_lt_of_le (by exact_mod_cast hw0) (EReal.coe_ennreal_nonneg _)
      · push Not at hw0
        have hcoe : ((ENNReal.ofReal w : ℝ≥0∞) : EReal) = (w : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left hw0]
        rw [← hcoe, EReal.coe_ennreal_lt_coe_ennreal_iff] at hw
        filter_upwards [hμ.isRateFunction.lowerSemicontinuous x _ hw] with x' hx'
        rw [← hcoe, EReal.coe_ennreal_lt_coe_ennreal_iff]
        exact hx'
    filter_upwards [hIev, hFw] with x' hx'1 hx'2
    by_cases hIx' : I x' = ⊤
    · rw [hJtop x' hIx']
      exact lt_top_iff_ne_top.2 hy_top
    · rw [(hJfin x' hIx').1, hyy, gt_iff_lt, ENNReal.ofReal_lt_ofReal_iff']
      rw [← EReal.coe_ennreal_toReal hIx', EReal.coe_lt_coe_iff] at hx'1
      constructor <;> linarith
  · -- lower bound on open sets
    intro U hU
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    rw [EReal.lt_neg_comm] at hb
    obtain ⟨x, hxU, hJx⟩ : ∃ x ∈ U,
        (((S - ((F x : EReal) - I x)).toENNReal : ℝ≥0∞) : EReal) < -b := by
      rw [iInf_lt_iff] at hb
      obtain ⟨x, hx⟩ := hb
      rw [iInf_lt_iff] at hx
      obtain ⟨hxU, h⟩ := hx
      exact ⟨x, hxU, h⟩
    have hIx : I x ≠ ⊤ := by
      intro h
      rw [hJtop x h, EReal.coe_ennreal_top] at hJx
      exact not_top_lt hJx
    obtain ⟨hJ, hle'⟩ := hJfin x hIx
    rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (by linarith), EReal.lt_neg_comm,
      ← EReal.coe_neg] at hJx
    obtain ⟨t, hbt, htx⟩ := EReal.lt_iff_exists_real_btwn.1 hJx
    rw [EReal.coe_lt_coe_iff] at htx
    refine hbt.le.trans ?_
    set ε := (F x - (I x).toReal - s - t) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ofReal_exp_le_setLIntegral_exp hμ hF.lowerSemicontinuous hU hxU
      hIx hε, hDup ε hε, eventually_gt_atTop 0] with n hZ hD hn0
    rw [coe_le_inv_mul_log_iff hn0, tiltedMeasure_apply μ F n hU.measurableSet]
    calc ENNReal.ofReal (Real.exp (n * t))
        = (ENNReal.ofReal (Real.exp (n * (s + ε))))⁻¹ *
            ENNReal.ofReal (Real.exp (n * (F x - (I x).toReal - ε))) := by
          rw [inv_ofReal_exp, ofReal_exp_mul_ofReal_exp]
          congr 2
          rw [hε_def]
          ring
      _ ≤ _ := mul_le_mul' (ENNReal.inv_le_inv.2 hD) hZ
  · -- upper bound on closed sets
    intro K hK
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    rw [EReal.neg_lt_comm] at hc
    obtain ⟨w, hcw, hwm⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    have hcw' : ((-w : ℝ) : EReal) < c := by
      rw [EReal.coe_neg]
      exact EReal.neg_lt_comm.1 hcw
    obtain ⟨t', hwt, htc⟩ := EReal.lt_iff_exists_real_btwn.1 hcw'
    rw [EReal.coe_lt_coe_iff] at hwt
    refine le_trans ?_ htc.le
    have hu : ∀ x ∈ K, (F x : EReal) - I x ≤ ((s - w : ℝ) : EReal) := by
      intro x hx
      have hJx : (w : EReal) < (((S - ((F x : EReal) - I x)).toENNReal : ℝ≥0∞) : EReal) :=
        hwm.trans_le (iInf₂_le (f := fun x (_ : x ∈ K) =>
          (((S - ((F x : EReal) - I x)).toENNReal : ℝ≥0∞) : EReal)) x hx)
      by_cases hIx : I x = ⊤
      · rw [hIx, EReal.coe_ennreal_top]
        simp
      · obtain ⟨hJ, hle'⟩ := hJfin x hIx
        rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (by linarith), EReal.coe_lt_coe_iff]
          at hJx
        rw [← EReal.coe_ennreal_toReal hIx, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        linarith
    set ε := (t' + w) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_setLIntegral_exp_le_ofReal_exp hμ hF hC hK hu
      (show s - w < s - w + ε by linarith), hDlow ε hε, eventually_gt_atTop 0]
      with n hZ hD hn0
    rw [inv_mul_log_le_coe_iff hn0, tiltedMeasure_apply μ F n hK.measurableSet]
    calc _ ≤ (ENNReal.ofReal (Real.exp (n * (s - ε))))⁻¹ *
            ENNReal.ofReal (Real.exp (n * (s - w + ε))) :=
          mul_le_mul' (ENNReal.inv_le_inv.2 hD) hZ
      _ = ENNReal.ofReal (Real.exp (n * t')) := by
          rw [inv_ofReal_exp, ofReal_exp_mul_ofReal_exp]
          congr 2
          rw [hε_def]
          ring

end MathlibExt.Probability.TiltedLDP
