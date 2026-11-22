/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Goldbeter–Koshland zero-order ultrasensitivity

A protein `W` is converted to its modified form `W*` by a converter enzyme `E₁` (for example a
kinase) and back by `E₂` (a phosphatase), both with Michaelis–Menten kinetics. Let `W*` also
denote the steady-state mole fraction of modified protein, `V₁, V₂` the maximal rates and
`K₁ = K_{m1} / W_T`, `K₂ = K_{m2} / W_T` the Michaelis constants divided by the total protein
concentration. When the enzyme–substrate complexes are negligible, the steady state balances
modification and demodification (Goldbeter–Koshland 1981, the condition preceding Eq. 7):

  `V₁ (1 - W*) / (K₁ + 1 - W*) = V₂ W* / (K₂ + W*)`.

Equivalently `V₁ / V₂ = W* (1 - W* + K₁) / ((1 - W*) (W* + K₂))` (their Eq. 8). For
`V₁, V₂, K₁, K₂ > 0` there is exactly one steady state in `(0, 1)`, given by the
**Goldbeter–Koshland function** (their Eq. 7), written here in the rationalized form

  `G(v, K₁, K₂) = 2 v K₂ / (√(b² + 4 (v - 1) v K₂) - b)`,   `b = v - 1 - K₁ - K₂ v`,

`v = V₁ / V₂`, which agrees with Eq. 7 for `v ≠ 1` and also covers `v = 1` (their Eq. 9,
`W* = K₂ / (K₁ + K₂)`).

The steepness of the switch is measured by the **response coefficient** `R_v`, the ratio of the
values of `V₁ / V₂` that give 90% and 10% modification. By Eq. 8 it equals (their Eq. 10)

  `R_v = 81 (K₁ + 0.1) (K₂ + 0.1) / ((K₁ + 0.9) (K₂ + 0.9))`,

which lies strictly between `1` and `81`, tends to `81` (the Michaelis–Menten value) when both
enzymes work in the first-order regime `K₁, K₂ → ∞`, and tends to `1` (infinite sensitivity)
when both are saturated, `K₁, K₂ → 0` (zero-order ultrasensitivity). For comparison, a Hill
response `Sⁿ / (Kⁿ + Sⁿ)` has `S_{0.9} / S_{0.1} = 81^{1/n}` (their Eq. 11), so `81` for a
Michaelis–Menten response (`n = 1`).

## Main results

* `steadyState_iff`: the steady-state condition is Eq. 8.
* `goldbeterKoshland_mem_Ioo`, `rateRatio_goldbeterKoshland`, `eq_goldbeterKoshland`: the
  Goldbeter–Koshland function is the unique steady state in `(0, 1)` (Eq. 7).
* `goldbeterKoshland_one`: Eq. 9.
* `responseCoefficient_eq`: Eq. 10; `one_lt_responseCoefficient`,
  `responseCoefficient_lt_81`; `tendsto_responseCoefficient_atTop`,
  `tendsto_responseCoefficient_zero`.
* `hill_ratio_eq`: Eq. 11, and `michaelisMenten_ratio_eq`: `R = 81` for `n = 1`.

## References

* A. Goldbeter and D. E. Koshland Jr., *An amplified sensitivity arising from covalent
  modification in biological systems*, Proc. Natl. Acad. Sci. USA 78 (1981) 6840–6844,
  Eqs. 7–11.
-/

@[expose] public section

open Filter Real Set
open scoped Topology

namespace MathlibExt.Biology.Dynamics.GoldbeterKoshland

/-- The value of `V₁ / V₂` for which the mole fraction `W` of modified protein is at steady
state (Goldbeter–Koshland 1981, Eq. 8): `W (1 - W + K₁) / ((1 - W) (W + K₂))`. Meaningful for
`0 < W < 1` and `K₁, K₂ > 0`; at `W = 1` Lean's `a / 0 = 0` gives the junk value `0`. -/
noncomputable def rateRatio (K₁ K₂ W : ℝ) : ℝ :=
  W * (1 - W + K₁) / ((1 - W) * (W + K₂))

/-- The **Goldbeter–Koshland function**: the steady-state mole fraction of modified protein
when `V₁ / V₂ = v` (Goldbeter–Koshland 1981, Eq. 7, rationalized so that it also covers
`v = 1`, Eq. 9). Meaningful for `v, K₁, K₂ > 0`. -/
noncomputable def goldbeterKoshland (v K₁ K₂ : ℝ) : ℝ :=
  2 * v * K₂ / (√((v - 1 - K₁ - K₂ * v) ^ 2 + 4 * (v - 1) * v * K₂) - (v - 1 - K₁ - K₂ * v))

/-- The **response coefficient** `R_v`: the ratio of the values of `V₁ / V₂` giving 90% and 10%
modified protein at steady state (Goldbeter–Koshland 1981). -/
noncomputable def responseCoefficient (K₁ K₂ : ℝ) : ℝ :=
  rateRatio K₁ K₂ 0.9 / rateRatio K₁ K₂ 0.1

/-- The fraction of a Hill response `Sⁿ / (Kⁿ + Sⁿ)` with half-saturation constant `K` and
Hill coefficient `n` (meaningful for `S, K > 0`, `n > 0`). -/
noncomputable def hill (n K S : ℝ) : ℝ :=
  S ^ n / (K ^ n + S ^ n)

/-- **Steady state of the modification cycle** (Goldbeter–Koshland 1981, Eq. 8). For
`V₂ > 0`, `K₁, K₂ > 0` and `0 < W < 1`, modification and demodification balance,
`V₁ (1 - W) / (K₁ + 1 - W) = V₂ W / (K₂ + W)`, iff `V₁ / V₂ = rateRatio K₁ K₂ W`. -/
theorem steadyState_iff {V₁ V₂ K₁ K₂ W : ℝ} (hV₂ : 0 < V₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hW0 : 0 < W) (hW1 : W < 1) :
    V₁ * (1 - W) / (K₁ + (1 - W)) = V₂ * W / (K₂ + W) ↔ V₁ / V₂ = rateRatio K₁ K₂ W := by
  have h1 : 0 < 1 - W := by linarith
  have h2 : 0 < K₁ + (1 - W) := by linarith
  have h3 : 0 < K₂ + W := by linarith
  unfold rateRatio
  rw [div_eq_div_iff h2.ne' h3.ne', div_eq_div_iff hV₂.ne' (by positivity)]
  constructor <;> intro h <;> nlinarith [h]

/-- `rateRatio K₁ K₂` is strictly increasing on `(0, 1)` for `K₁, K₂ > 0`: it is the product
of the positive increasing functions `W / (W + K₂)` and `1 + K₁ / (1 - W)`. -/
theorem strictMonoOn_rateRatio {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    StrictMonoOn (rateRatio K₁ K₂) (Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have e : ∀ W, 0 < W → W < 1 → rateRatio K₁ K₂ W = W / (W + K₂) * (1 + K₁ / (1 - W)) := by
    intro W h0 h1
    have : (1 - W) ≠ 0 := by linarith
    have : W + K₂ ≠ 0 := by linarith
    unfold rateRatio
    field_simp
  rw [e a ha0 ha1, e b hb0 hb1]
  have f1 : a / (a + K₂) < b / (b + K₂) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have f2 : 1 + K₁ / (1 - a) < 1 + K₁ / (1 - b) := by
    have := div_lt_div_of_pos_left hK₁ (by linarith : (0 : ℝ) < 1 - b)
      (by linarith : 1 - b < 1 - a)
    linarith
  have p1 : 0 < a / (a + K₂) := by positivity
  have p2 : 0 < 1 + K₁ / (1 - a) := by
    have : 0 < K₁ / (1 - a) := div_pos hK₁ (by linarith)
    linarith
  calc a / (a + K₂) * (1 + K₁ / (1 - a)) < b / (b + K₂) * (1 + K₁ / (1 - a)) :=
        mul_lt_mul_of_pos_right f1 p2
    _ < b / (b + K₂) * (1 + K₁ / (1 - b)) :=
        mul_lt_mul_of_pos_left f2 (lt_trans p1 f1)

/-- The discriminant in the Goldbeter–Koshland function is
`(v - 1 + K₂ v - K₁)² + 4 K₁ K₂ v`. -/
private theorem disc_eq (v K₁ K₂ : ℝ) :
    (v - 1 - K₁ - K₂ * v) ^ 2 + 4 * (v - 1) * v * K₂ =
      (v - 1 + K₂ * v - K₁) ^ 2 + 4 * K₁ * K₂ * v := by
  ring

private theorem disc_pos {v K₁ K₂ : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    0 < (v - 1 - K₁ - K₂ * v) ^ 2 + 4 * (v - 1) * v * K₂ := by
  rw [disc_eq]
  positivity

private theorem lt_sqrt_disc {v K₁ K₂ : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    v - 1 - K₁ - K₂ * v < √((v - 1 - K₁ - K₂ * v) ^ 2 + 4 * (v - 1) * v * K₂) := by
  rcases lt_or_ge (v - 1 - K₁ - K₂ * v) 0 with hb | hb
  · exact hb.trans_le (Real.sqrt_nonneg _)
  · have hv1 : 1 < v := by nlinarith [mul_pos hK₂ hv]
    rw [Real.lt_sqrt hb]
    nlinarith [mul_pos (mul_pos (sub_pos.2 hv1) hv) hK₂]

private theorem denom_pos {v K₁ K₂ : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    0 < √((v - 1 - K₁ - K₂ * v) ^ 2 + 4 * (v - 1) * v * K₂) - (v - 1 - K₁ - K₂ * v) :=
  sub_pos.2 (lt_sqrt_disc hv hK₁ hK₂)

/-- For `v, K₁, K₂ > 0` the Goldbeter–Koshland function lies in `(0, 1)`. -/
theorem goldbeterKoshland_mem_Ioo {v K₁ K₂ : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    goldbeterKoshland v K₁ K₂ ∈ Ioo 0 1 := by
  have hd := denom_pos hv hK₁ hK₂
  unfold goldbeterKoshland
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hd, lt_sub_iff_add_lt]
  -- `√D > b + 2 v K₂`, since `D - (b + 2 v K₂)² = 4 K₁ K₂ v > 0`
  rcases lt_or_ge (2 * v * K₂ + (v - 1 - K₁ - K₂ * v)) 0 with h | h
  · exact h.trans_le (Real.sqrt_nonneg _)
  · rw [Real.lt_sqrt h]
    nlinarith [mul_pos (mul_pos hK₁ hK₂) hv]

/-- **The Goldbeter–Koshland function is a steady state** (Goldbeter–Koshland 1981, Eq. 7):
for `v, K₁, K₂ > 0`, `rateRatio K₁ K₂ (goldbeterKoshland v K₁ K₂) = v`. -/
theorem rateRatio_goldbeterKoshland {v K₁ K₂ : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    rateRatio K₁ K₂ (goldbeterKoshland v K₁ K₂) = v := by
  obtain ⟨hG0, hG1⟩ := goldbeterKoshland_mem_Ioo hv hK₁ hK₂
  have hd := denom_pos hv hK₁ hK₂
  set G := goldbeterKoshland v K₁ K₂ with hGdef
  set b := v - 1 - K₁ - K₂ * v
  set D := b ^ 2 + 4 * (v - 1) * v * K₂
  set s := √D
  have hD : 0 < D := disc_pos hv hK₁ hK₂
  have hs : s ^ 2 = D := Real.sq_sqrt hD.le
  have hG : G * (s - b) = 2 * v * K₂ := by
    simp only [hGdef, goldbeterKoshland]
    exact div_mul_cancel₀ _ hd.ne'
  -- `G` is a root of `(1 - v) W² + b W + v K₂`
  have hq : (1 - v) * G ^ 2 + b * G + v * K₂ = 0 := by
    have h4 : ((1 - v) * G ^ 2 + b * G + v * K₂) * (s - b) ^ 2 = 0 := by
      have : ((1 - v) * G ^ 2 + b * G + v * K₂) * (s - b) ^ 2 =
          (1 - v) * (G * (s - b)) ^ 2 + b * (G * (s - b)) * (s - b) + v * K₂ * (s - b) ^ 2 := by
        ring
      rw [this, hG]
      linear_combination (v * K₂) * hs
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hd.ne')
  have h1 : 1 - G ≠ 0 := by linarith
  have h2 : G + K₂ ≠ 0 := by linarith
  unfold rateRatio
  rw [div_eq_iff (mul_ne_zero h1 h2)]
  simp only [b] at hq
  linarith [hq]

/-- **Uniqueness of the steady state** (Goldbeter–Koshland 1981, Eq. 7). For `K₁, K₂ > 0`, if
`0 < W < 1` and `rateRatio K₁ K₂ W = v` with `v > 0`, then `W` is the Goldbeter–Koshland
function. -/
theorem eq_goldbeterKoshland {v K₁ K₂ W : ℝ} (hv : 0 < v) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hW : W ∈ Ioo 0 1) (h : rateRatio K₁ K₂ W = v) : W = goldbeterKoshland v K₁ K₂ :=
  (strictMonoOn_rateRatio hK₁ hK₂).injOn hW (goldbeterKoshland_mem_Ioo hv hK₁ hK₂)
    (h.trans (rateRatio_goldbeterKoshland hv hK₁ hK₂).symm)

/-- **Equal maximal rates** (Goldbeter–Koshland 1981, Eq. 9): for `V₁ = V₂` and `K₁, K₂ > 0`
the steady-state modified fraction is `K₂ / (K₁ + K₂)`. -/
theorem goldbeterKoshland_one {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    goldbeterKoshland 1 K₁ K₂ = K₂ / (K₁ + K₂) := by
  symm
  refine eq_goldbeterKoshland one_pos hK₁ hK₂ ⟨by positivity, ?_⟩ ?_
  · rw [div_lt_one (by positivity)]; linarith
  · have h1 : K₁ + K₂ ≠ 0 := by positivity
    have h2 : 1 - K₂ / (K₁ + K₂) = K₁ / (K₁ + K₂) := by field_simp; ring
    unfold rateRatio
    rw [h2]
    field_simp

/-- **The response coefficient** (Goldbeter–Koshland 1981, Eq. 10): for `K₁, K₂ > -0.1`,
`R_v = 81 (K₁ + 0.1)(K₂ + 0.1) / ((K₁ + 0.9)(K₂ + 0.9))`. -/
theorem responseCoefficient_eq {K₁ K₂ : ℝ} (hK₁ : -0.1 < K₁) (hK₂ : -0.1 < K₂) :
    responseCoefficient K₁ K₂ = 81 * (K₁ + 0.1) * (K₂ + 0.1) / ((K₁ + 0.9) * (K₂ + 0.9)) := by
  have a1 : K₁ + 0.1 ≠ 0 := by linarith
  have a2 : K₂ + 0.1 ≠ 0 := by linarith
  have a3 : K₁ + 0.9 ≠ 0 := by linarith
  have a4 : K₂ + 0.9 ≠ 0 := by linarith
  have r9 : rateRatio K₁ K₂ 0.9 = 9 * (K₁ + 0.1) / (K₂ + 0.9) := by
    unfold rateRatio
    rw [div_eq_div_iff (by norm_num; linarith) a4]
    ring
  have r1 : rateRatio K₁ K₂ 0.1 = (K₁ + 0.9) / (9 * (K₂ + 0.1)) := by
    unfold rateRatio
    rw [div_eq_div_iff (by norm_num; linarith) (by positivity)]
    ring
  unfold responseCoefficient
  rw [r9, r1, div_div_div_eq, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- For `K₁, K₂ > 0` the response coefficient exceeds `1`: the switch is never infinitely
sharp. -/
theorem one_lt_responseCoefficient {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    1 < responseCoefficient K₁ K₂ := by
  rw [responseCoefficient_eq (by linarith) (by linarith), one_lt_div (by positivity)]
  nlinarith [mul_pos hK₁ hK₂]

/-- For `K₁, K₂ > 0` the response coefficient is below the Michaelis–Menten value `81`. -/
theorem responseCoefficient_lt_81 {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    responseCoefficient K₁ K₂ < 81 := by
  rw [responseCoefficient_eq (by linarith) (by linarith), div_lt_iff₀ (by positivity)]
  nlinarith

/-- **First-order limit**: as both `K₁, K₂ → ∞` the response coefficient tends to `81`, the
value of a Michaelis–Menten response. -/
theorem tendsto_responseCoefficient_atTop :
    Tendsto (fun p : ℝ × ℝ => responseCoefficient p.1 p.2) (atTop ×ˢ atTop) (𝓝 81) := by
  set φ : ℝ → ℝ := fun K => 1 - 0.8 * (K + 0.9)⁻¹
  have hφ : Tendsto φ atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ (0.9 : ℝ) tendsto_id)).const_mul (0.8 : ℝ))
    simpa [φ, Function.comp_def] using h
  have hlim : Tendsto (fun p : ℝ × ℝ => 81 * φ p.1 * φ p.2) (atTop ×ˢ atTop) (𝓝 81) := by
    simpa using ((hφ.comp tendsto_fst).const_mul 81).mul (hφ.comp tendsto_snd)
  refine hlim.congr' ?_
  filter_upwards [(eventually_gt_atTop (0 : ℝ)).prod_mk (eventually_gt_atTop (0 : ℝ))] with p hp
  obtain ⟨h1, h2⟩ := hp
  rw [responseCoefficient_eq (by linarith) (by linarith)]
  have a3 : p.1 + 0.9 ≠ 0 := by linarith
  have a4 : p.2 + 0.9 ≠ 0 := by linarith
  simp only [φ]
  field_simp
  ring

/-- **Zero-order ultrasensitivity**: as both `K₁, K₂ → 0` the response coefficient tends to
`1`. -/
theorem tendsto_responseCoefficient_zero :
    Tendsto (fun p : ℝ × ℝ => responseCoefficient p.1 p.2) (𝓝 (0, 0)) (𝓝 1) := by
  have hc : ContinuousAt
      (fun p : ℝ × ℝ => 81 * (p.1 + 0.1) * (p.2 + 0.1) / ((p.1 + 0.9) * (p.2 + 0.9))) (0, 0) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    norm_num
  have hlim := hc.tendsto
  norm_num at hlim
  refine hlim.congr' ?_
  have e1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), -0.1 < p.1 :=
    (continuous_fst.tendsto (0, 0)).eventually (eventually_gt_nhds (by norm_num))
  have e2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), -0.1 < p.2 :=
    (continuous_snd.tendsto (0, 0)).eventually (eventually_gt_nhds (by norm_num))
  filter_upwards [e1, e2] with p h1 h2
  rw [responseCoefficient_eq h1 h2]
  norm_num

/-- **Hill response coefficient** (Goldbeter–Koshland 1981, Eq. 11). For a Hill response with
`n > 0` and `K > 0`, if `S₉, S₁ > 0` give 90% and 10% response, then
`S₉ / S₁ = 81 ^ (1 / n)`. -/
theorem hill_ratio_eq {n K S₉ S₁ : ℝ} (hn : 0 < n) (hK : 0 < K) (hS₉ : 0 < S₉) (hS₁ : 0 < S₁)
    (h₉ : hill n K S₉ = 0.9) (h₁ : hill n K S₁ = 0.1) : S₉ / S₁ = 81 ^ (1 / n) := by
  have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
  have h9n : 0 < S₉ ^ n := Real.rpow_pos_of_pos hS₉ n
  have h1n : 0 < S₁ ^ n := Real.rpow_pos_of_pos hS₁ n
  unfold hill at h₉ h₁
  rw [div_eq_iff (by positivity)] at h₉ h₁
  have hq : (S₉ / S₁) ^ n = 81 := by
    rw [Real.div_rpow hS₉.le hS₁.le, div_eq_iff h1n.ne']
    linarith
  rw [← hq, one_div, Real.rpow_rpow_inv (div_pos hS₉ hS₁).le hn.ne']

/-- **Michaelis–Menten response** (`n = 1`): going from 10% to 90% of the response takes an
81-fold increase of the stimulus. -/
theorem michaelisMenten_ratio_eq {K S₉ S₁ : ℝ} (hK : 0 < K) (hS₉ : 0 < S₉) (hS₁ : 0 < S₁)
    (h₉ : hill 1 K S₉ = 0.9) (h₁ : hill 1 K S₁ = 0.1) : S₉ / S₁ = 81 := by
  rw [hill_ratio_eq one_pos hK hS₉ hS₁ h₉ h₁]
  norm_num

end MathlibExt.Biology.Dynamics.GoldbeterKoshland
