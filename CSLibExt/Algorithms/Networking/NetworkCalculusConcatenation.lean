/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Network calculus: concatenation of service curves (Le Boudec-Thiran)
-/

module

public import CSLibExt.Algorithms.Networking.NetworkCalculus
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Monotone.Defs

/-!
## Source

J.-Y. Le Boudec and P. Thiran, Network Calculus (LNCS 2050), Section 1.4.3:
Theorem 1.4.6 (concatenation of nodes), the rate-latency convolution
`β_{R₁,T₁} ⊗ β_{R₂,T₂} = β_{min R₁ R₂, T₁+T₂}`, the pay-bursts-only-once
end-to-end delay bound, and order independence of that bound.

## Conventions

The provider's frozen conventions carry over unchanged (continuous time,
monotone finite curves, `ℝ≥0∞`-valued deviations, no continuity hypotheses).
Since the provider's `minPlusConv` is `ℝ≥0∞`-valued while service curves are
`ℝ≥0`-valued, the concatenated curve `convCurve` bridges the two through
`ENNReal.toNNReal`; the coercion identity holds because every convolution
value is finite (the `s = 0` term is a finite upper bound). Associativity is
stated with `(R ⊗ β₁) ⊗ β₂` unfolded, since `minPlusConv` only accepts
`ℝ≥0`-valued functions and the `ℝ≥0∞`-valued `R ⊗ β₁` cannot be nested.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal

/-- Concatenated service curve `β₁ ⊗ β₂`: the `ℝ≥0∞`-valued `minPlusConv`
rounded back to a finite curve through `ENNReal.toNNReal`. -/
noncomputable def convCurve (β₁ β₂ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => (minPlusConv β₁ β₂ t).toNNReal

/-- Coercion identity: the concatenated curve coerced back to `ℝ≥0∞` is the
`minPlusConv` value. Finiteness comes from the `s = 0` term. -/
theorem convCurve_coe (β₁ β₂ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((convCurve β₁ β₂ t : ℝ≥0) : ℝ≥0∞) = minPlusConv β₁ β₂ t := by
  have hle : minPlusConv β₁ β₂ t ≤ ((β₁ (t - 0) + β₂ 0 : ℝ≥0) : ℝ≥0∞) :=
    minPlusConv_le zero_le
  have hne : minPlusConv β₁ β₂ t ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle ENNReal.coe_lt_top)
  unfold convCurve
  exact ENNReal.coe_toNNReal hne

/-- The concatenated curve vanishes at `0` when both factors do. -/
theorem convCurve_zero (β₁ β₂ : ℝ≥0 → ℝ≥0) (h₁ : β₁ 0 = 0) (h₂ : β₂ 0 = 0) :
    convCurve β₁ β₂ 0 = 0 := by
  have h : minPlusConv β₁ β₂ 0 = ((0 : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · have h0 := minPlusConv_le (f := β₁) (g := β₂) (t := 0) (s := 0) le_rfl
      rwa [tsub_zero, h₁, h₂, add_zero] at h0
    · rw [ENNReal.coe_zero]
      exact zero_le
  have hc := convCurve_coe β₁ β₂ 0
  rw [h] at hc
  exact WithTop.coe_eq_coe.mp hc

/-- Monotonicity of the concatenated curve when both factors are monotone
and vanish at `0`. -/
theorem convCurve_mono (β₁ β₂ : ℝ≥0 → ℝ≥0) (h₁ : Monotone β₁)
    (h₁₀ : β₁ 0 = 0) (h₂ : Monotone β₂) (h₂₀ : β₂ 0 = 0) :
    Monotone (convCurve β₁ β₂) := by
  intro a b hab
  apply ENNReal.coe_le_coe.mp
  rw [convCurve_coe, convCurve_coe]
  apply le_iInf
  intro v
  have h1 := minPlusConv_le (f := β₁) (g := β₂) (t := a)
    (s := min v.val a) (min_le_right v.val a)
  refine le_trans h1 ?_
  show ((β₁ (a - min v.val a) + β₂ (min v.val a) : ℝ≥0) : ℝ≥0∞)
    ≤ ((β₁ (b - v.val) + β₂ v.val : ℝ≥0) : ℝ≥0∞)
  apply ENNReal.coe_le_coe.mpr
  apply add_le_add
  · apply h₁
    by_cases h : v.val ≤ a
    · have hs : min v.val a = v.val := min_eq_left h
      rw [hs]
      exact tsub_le_tsub_right hab _
    · push Not at h
      have hs : min v.val a = a := min_eq_right (le_of_lt h)
      rw [hs, tsub_self]
      exact zero_le
  · apply h₂
    exact min_le_left v.val a

/-- Associativity of min-plus convolution at flow level: `(R ⊗ β₁) ⊗ β₂` in
unfolded `ℝ≥0∞` form equals `R ⊗ (β₁ ⊗ β₂)`. This is the final step of the
Theorem 1.4.6 chain `R* ≥ R₁ ⊗ β₂ ≥ (R ⊗ β₁) ⊗ β₂ = R ⊗ (β₁ ⊗ β₂)`. -/
theorem minPlusConv_assoc (R β₁ β₂ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    (⨅ v : { v : ℝ≥0 // v ≤ t },
      (minPlusConv R β₁ (t - v.val) + (β₂ v.val : ℝ≥0∞)))
      = minPlusConv R (convCurve β₁ β₂) t := by
  apply le_antisymm
  · apply le_iInf
    intro s
    show (⨅ v : { v : ℝ≥0 // v ≤ t },
        (minPlusConv R β₁ (t - v.val) + (β₂ v.val : ℝ≥0∞)))
        ≤ ((R (t - s.val) + convCurve β₁ β₂ s.val : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_add, convCurve_coe, ← tsub_le_iff_left]
    apply le_iInf
    intro w
    rw [tsub_le_iff_left]
    have hwt : w.val ≤ t := le_trans w.property s.property
    have hle : (⨅ v : { v : ℝ≥0 // v ≤ t },
          (minPlusConv R β₁ (t - v.val) + (β₂ v.val : ℝ≥0∞)))
        ≤ minPlusConv R β₁ (t - w.val) + ((β₂ w.val : ℝ≥0) : ℝ≥0∞) :=
      iInf_le _ (⟨w.val, hwt⟩ : { v : ℝ≥0 // v ≤ t })
    refine le_trans hle ?_
    have hsw : s.val - w.val ≤ t - w.val := tsub_le_tsub_right s.property _
    have hFu : minPlusConv R β₁ (t - w.val)
        ≤ ((R (t - w.val - (s.val - w.val)) + β₁ (s.val - w.val) : ℝ≥0) : ℝ≥0∞) :=
      minPlusConv_le hsw
    refine le_trans (add_le_add hFu le_rfl) ?_
    show ((R (t - w.val - (s.val - w.val)) + β₁ (s.val - w.val) : ℝ≥0) : ℝ≥0∞)
        + ((β₂ w.val : ℝ≥0) : ℝ≥0∞)
      ≤ ((R (t - s.val) : ℝ≥0) : ℝ≥0∞)
        + ((β₁ (s.val - w.val) + β₂ w.val : ℝ≥0) : ℝ≥0∞)
    have e1 : t - w.val - (s.val - w.val) = t - s.val := by
      rw [tsub_tsub, add_tsub_cancel_of_le w.property]
    rw [ENNReal.coe_add, ENNReal.coe_add, e1]
    apply le_of_eq
    ac_rfl
  · apply le_iInf
    intro v
    show minPlusConv R (convCurve β₁ β₂) t
      ≤ minPlusConv R β₁ (t - v.val) + (β₂ v.val : ℝ≥0∞)
    rw [← tsub_le_iff_right]
    apply le_iInf
    intro u
    rw [tsub_le_iff_right]
    have huv : u.val + v.val ≤ t := by
      calc u.val + v.val ≤ (t - v.val) + v.val :=
            add_le_add u.property le_rfl
        _ = t := tsub_add_cancel_of_le v.property
    have hle : minPlusConv R (convCurve β₁ β₂) t
        ≤ ((R (t - (u.val + v.val)) + convCurve β₁ β₂ (u.val + v.val) : ℝ≥0) : ℝ≥0∞) :=
      iInf_le _ (⟨u.val + v.val, huv⟩ : { s : ℝ≥0 // s ≤ t })
    refine le_trans hle ?_
    rw [ENNReal.coe_add, convCurve_coe]
    have hwv : v.val ≤ u.val + v.val := le_add_left le_rfl
    have hle2 : minPlusConv β₁ β₂ (u.val + v.val)
        ≤ ((β₁ (u.val + v.val - v.val) + β₂ v.val : ℝ≥0) : ℝ≥0∞) :=
      minPlusConv_le hwv
    refine le_trans (add_le_add le_rfl hle2) ?_
    show ((R (t - (u.val + v.val)) : ℝ≥0) : ℝ≥0∞)
        + ((β₁ (u.val + v.val - v.val) + β₂ v.val : ℝ≥0) : ℝ≥0∞)
      ≤ ((R (t - v.val - u.val) + β₁ u.val : ℝ≥0) : ℝ≥0∞)
        + ((β₂ v.val : ℝ≥0) : ℝ≥0∞)
    have e_a : t - (u.val + v.val) = t - v.val - u.val := by
      rw [add_comm u.val v.val, tsub_tsub]
    have e_b : u.val + v.val - v.val = u.val := add_tsub_cancel_right _ _
    rw [ENNReal.coe_add, ENNReal.coe_add, e_a, e_b]
    apply le_of_eq
    ac_rfl

/-- Commutativity of the curve convolution, by reindexing `s ↦ t - s`. -/
theorem convCurve_comm (β₁ β₂ : ℝ≥0 → ℝ≥0) :
    convCurve β₁ β₂ = convCurve β₂ β₁ := by
  funext t
  unfold convCurve
  refine congrArg ENNReal.toNNReal ?_
  apply le_antisymm
  · apply le_iInf
    intro u
    refine le_trans (iInf_le _ (⟨t - u.val, tsub_le_self⟩ : { s : ℝ≥0 // s ≤ t })) ?_
    show ((β₁ (t - (t - u.val)) + β₂ (t - u.val) : ℝ≥0) : ℝ≥0∞)
      ≤ ((β₂ (t - u.val) + β₁ u.val : ℝ≥0) : ℝ≥0∞)
    have e : β₁ (t - (t - u.val)) + β₂ (t - u.val) = β₂ (t - u.val) + β₁ u.val := by
      rw [tsub_tsub_cancel_of_le u.property]
      exact add_comm _ _
    exact le_of_eq (by rw [e])
  · apply le_iInf
    intro u
    refine le_trans (iInf_le _ (⟨t - u.val, tsub_le_self⟩ : { s : ℝ≥0 // s ≤ t })) ?_
    show ((β₂ (t - (t - u.val)) + β₁ (t - u.val) : ℝ≥0) : ℝ≥0∞)
      ≤ ((β₁ (t - u.val) + β₂ u.val : ℝ≥0) : ℝ≥0∞)
    have e : β₂ (t - (t - u.val)) + β₁ (t - u.val) = β₁ (t - u.val) + β₂ u.val := by
      rw [tsub_tsub_cancel_of_le u.property]
      exact add_comm _ _
    exact le_of_eq (by rw [e])

/-- Concatenation of service curves (Theorem 1.4.6): if a flow traverses two
systems in sequence offering `β₁` and `β₂`, the tandem offers `β₁ ⊗ β₂`. -/
theorem serviceCurve_concat {R R₁ R' β₁ β₂ : ℝ≥0 → ℝ≥0}
    (hR : IsCumulativeFlow R) (hR₁ : IsCumulativeFlow R₁)
    (hR' : IsCumulativeFlow R') (h₁ : IsServiceCurve R R₁ β₁)
    (h₂ : IsServiceCurve R₁ R' β₂) :
    IsServiceCurve R R' (convCurve β₁ β₂) := by
  refine ⟨convCurve_mono β₁ β₂ h₁.1 h₁.2.1 h₂.1 h₂.2.1,
    convCurve_zero β₁ β₂ h₁.2.1 h₂.2.1, ?_⟩
  intro t
  rw [← minPlusConv_assoc R β₁ β₂ t]
  refine le_trans ?_ (h₂.2.2 t)
  apply le_iInf
  intro v
  refine le_trans (iInf_le _ v) ?_
  show minPlusConv R β₁ (t - v.val) + ((β₂ v.val : ℝ≥0) : ℝ≥0∞)
    ≤ ((R₁ (t - v.val) + β₂ v.val : ℝ≥0) : ℝ≥0∞)
  have h := h₁.2.2 (t - v.val)
  rw [ENNReal.coe_add]
  exact add_le_add h le_rfl

private theorem cc_rl_eq (R T s : ℝ≥0) :
    rateLatency R T s = R * (s - T) := by
  show R * max (s - T) 0 = R * (s - T)
  rw [max_eq_left zero_le]

private theorem cc_le_tsub_add (x y : ℝ≥0) : x ≤ (x - y) + y := by
  by_cases h : y ≤ x
  · exact le_of_eq (tsub_add_cancel_of_le h).symm
  · push Not at h
    have hz : x - y = 0 := tsub_eq_zero_of_le (le_of_lt h)
    rw [hz, zero_add]
    exact le_of_lt h

private theorem cc_tsub_key (t s T₁ T₂ : ℝ≥0) (hs : s ≤ t) :
    t - (T₁ + T₂) ≤ ((t - s) - T₁) + (s - T₂) := by
  by_cases hC : T₁ + T₂ ≤ t
  · have hP1a : (t - s) ≤ ((t - s) - T₁) + T₁ := cc_le_tsub_add _ _
    have hP1b : s ≤ (s - T₂) + T₂ := cc_le_tsub_add _ _
    have hP2 : (t - s) + s = t := tsub_add_cancel_of_le hs
    have hle : t ≤ (((t - s) - T₁) + (s - T₂)) + (T₁ + T₂) := by
      calc t = (t - s) + s := hP2.symm
        _ ≤ (((t - s) - T₁) + T₁) + ((s - T₂) + T₂) := add_le_add hP1a hP1b
        _ = (((t - s) - T₁) + (s - T₂)) + (T₁ + T₂) := by ac_rfl
    have heq : (t - (T₁ + T₂)) + (T₁ + T₂) = t := tsub_add_cancel_of_le hC
    have hle' : (t - (T₁ + T₂)) + (T₁ + T₂)
        ≤ (((t - s) - T₁) + (s - T₂)) + (T₁ + T₂) := by
      rw [heq]
      exact hle
    exact le_of_add_le_add_right hle'
  · push Not at hC
    have hz : t - (T₁ + T₂) = 0 := tsub_eq_zero_of_le (le_of_lt hC)
    rw [hz]
    exact zero_le

/-- Rate-latency convolution: `β_{R₁,T₁} ⊗ β_{R₂,T₂} = β_{min R₁ R₂, T₁+T₂}`
as functions. -/
theorem convCurve_rateLatency (R₁ R₂ T₁ T₂ : ℝ≥0) :
    convCurve (rateLatency R₁ T₁) (rateLatency R₂ T₂)
      = rateLatency (min R₁ R₂) (T₁ + T₂) := by
  funext t
  have hconv : minPlusConv (rateLatency R₁ T₁) (rateLatency R₂ T₂) t
      = (((min R₁ R₂) * (t - (T₁ + T₂)) : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · by_cases ht : t ≤ T₁ + T₂
      · have h0 : t - (T₁ + T₂) = 0 := tsub_eq_zero_of_le ht
        have hs : t - T₁ ≤ t := tsub_le_self
        have hle := minPlusConv_le (f := rateLatency R₁ T₁)
          (g := rateLatency R₂ T₂) (t := t) (s := t - T₁) hs
        rw [cc_rl_eq, cc_rl_eq] at hle
        have g1 : t - (t - T₁) ≤ T₁ := by
          by_cases hT : T₁ ≤ t
          · exact le_of_eq (tsub_tsub_cancel_of_le hT)
          · push Not at hT
            have hz : t - T₁ = 0 := tsub_eq_zero_of_le (le_of_lt hT)
            rw [hz, tsub_zero]
            exact le_of_lt hT
        have eβ1 : R₁ * ((t - (t - T₁)) - T₁) = 0 := by
          rw [tsub_eq_zero_of_le g1, mul_zero]
        have eβ2 : R₂ * ((t - T₁) - T₂) = 0 := by
          have e : (t - T₁) - T₂ = t - (T₁ + T₂) := by rw [tsub_tsub]
          rw [e, h0, mul_zero]
        rw [h0, mul_zero]
        rw [eβ1, eβ2, add_zero] at hle
        exact hle
      · push Not at ht
        by_cases hR : R₁ ≤ R₂
        · have hT2le : T₂ ≤ T₁ + T₂ := le_add_left le_rfl
          have hle2t : T₁ + T₂ ≤ t := le_of_lt ht
          have hT2t : T₂ ≤ t := le_trans hT2le hle2t
          have hle := minPlusConv_le (f := rateLatency R₁ T₁)
            (g := rateLatency R₂ T₂) (t := t) (s := T₂) hT2t
          rw [cc_rl_eq, cc_rl_eq] at hle
          have e1 : (t - T₂) - T₁ = t - (T₁ + T₂) := by
            rw [tsub_tsub, add_comm T₂ T₁]
          have hmin : min R₁ R₂ = R₁ := min_eq_left hR
          rw [hmin]
          rw [e1, tsub_self, mul_zero, add_zero] at hle
          exact hle
        · push Not at hR
          have hT1le : T₁ ≤ T₁ + T₂ := le_add_right le_rfl
          have hle2t : T₁ + T₂ ≤ t := le_of_lt ht
          have hT1t : T₁ ≤ t := le_trans hT1le hle2t
          have hs : t - T₁ ≤ t := tsub_le_self
          have hle := minPlusConv_le (f := rateLatency R₁ T₁)
            (g := rateLatency R₂ T₂) (t := t) (s := t - T₁) hs
          rw [cc_rl_eq, cc_rl_eq] at hle
          have e1 : t - (t - T₁) = T₁ := tsub_tsub_cancel_of_le hT1t
          have e2 : (t - T₁) - T₂ = t - (T₁ + T₂) := by rw [tsub_tsub]
          have hmin : min R₁ R₂ = R₂ := min_eq_right (le_of_lt hR)
          rw [hmin]
          rw [e1, tsub_self, mul_zero, zero_add, e2] at hle
          exact hle
    · apply le_iInf
      intro s
      show (((min R₁ R₂) * (t - (T₁ + T₂)) : ℝ≥0) : ℝ≥0∞)
        ≤ ((rateLatency R₁ T₁ (t - s.val) + rateLatency R₂ T₂ s.val : ℝ≥0) : ℝ≥0∞)
      rw [cc_rl_eq, cc_rl_eq]
      apply ENNReal.coe_le_coe.mpr
      have hm1 : min R₁ R₂ ≤ R₁ := min_le_left _ _
      have hm2 : min R₁ R₂ ≤ R₂ := min_le_right _ _
      have g1 : (min R₁ R₂) * ((t - s.val) - T₁) ≤ R₁ * ((t - s.val) - T₁) :=
        mul_le_mul_of_nonneg_right hm1 zero_le
      have g2 : (min R₁ R₂) * (s.val - T₂) ≤ R₂ * (s.val - T₂) :=
        mul_le_mul_of_nonneg_right hm2 zero_le
      have hkey : t - (T₁ + T₂) ≤ ((t - s.val) - T₁) + (s.val - T₂) :=
        cc_tsub_key t s.val T₁ T₂ s.property
      have g3 : (min R₁ R₂) * (t - (T₁ + T₂))
          ≤ (min R₁ R₂) * (((t - s.val) - T₁) + (s.val - T₂)) :=
        mul_le_mul_of_nonneg_left hkey zero_le
      calc (min R₁ R₂) * (t - (T₁ + T₂))
          ≤ (min R₁ R₂) * (((t - s.val) - T₁) + (s.val - T₂)) := g3
        _ = (min R₁ R₂) * ((t - s.val) - T₁) + (min R₁ R₂) * (s.val - T₂) := by
            rw [mul_add]
        _ ≤ R₁ * ((t - s.val) - T₁) + R₂ * (s.val - T₂) := add_le_add g1 g2
  have hc := convCurve_coe (rateLatency R₁ T₁) (rateLatency R₂ T₂) t
  rw [hconv] at hc
  have hr : rateLatency (min R₁ R₂) (T₁ + T₂) t
      = (min R₁ R₂) * (t - (T₁ + T₂)) :=
    cc_rl_eq _ _ _
  rw [hr]
  exact WithTop.coe_eq_coe.mp hc

private theorem cc_tokenBucket_zero_zero (w : ℝ≥0) :
    tokenBucket 0 0 w = 0 := by
  unfold tokenBucket
  split <;> simp

private theorem cc_flow_zero_of_zero_bucket {R : ℝ≥0 → ℝ≥0}
    (hR : IsCumulativeFlow R) (hα : IsArrivalCurve R (tokenBucket 0 0))
    (u : ℝ≥0) : R u = 0 := by
  have h := hα.2 0 u zero_le
  rw [hR.2] at h
  simp only [tsub_zero] at h
  rw [cc_tokenBucket_zero_zero] at h
  exact le_antisymm h zero_le

private theorem cc_delay_zero_of_flow_zero {R R' : ℝ≥0 → ℝ≥0}
    (hR0 : ∀ u, R u = 0) (t : ℝ≥0) : delay R R' t = 0 := by
  have h0 : R t ≤ R' (t + 0) := by
    rw [hR0 t]
    exact zero_le
  unfold delay
  refine le_antisymm ?_ zero_le
  calc (⨅ u : { τ : ℝ≥0 // R t ≤ R' (t + τ) }, (u.val : ℝ≥0∞))
        ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
          iInf_le _ (⟨0, h0⟩ : { τ : ℝ≥0 // R t ≤ R' (t + τ) })
    _ = 0 := ENNReal.coe_zero

/-- End-to-end delay bound through two rate-latency nodes, paying bursts
only once: a `γ_{r,b}`-constrained flow with `r ≤ min R₁ R₂` has virtual
delay at most `T₁ + T₂ + b / min R₁ R₂` at every time. -/
theorem delay_concat_rateLatency {R Rmid R' : ℝ≥0 → ℝ≥0} {r b : ℝ≥0}
    {R₁ R₂ T₁ T₂ : ℝ≥0} (hR : IsCumulativeFlow R)
    (hRmid : IsCumulativeFlow Rmid) (hR' : IsCumulativeFlow R')
    (hα : IsArrivalCurve R (tokenBucket r b))
    (hβ₁ : IsServiceCurve R Rmid (rateLatency R₁ T₁))
    (hβ₂ : IsServiceCurve Rmid R' (rateLatency R₂ T₂))
    (hr : r ≤ min R₁ R₂) (hRpos : 0 < min R₁ R₂)
    (t : ℝ≥0) :
    delay R R' t ≤ ((T₁ + T₂ + b / min R₁ R₂ : ℝ≥0) : ℝ≥0∞) := by
  by_cases hpos : 0 < r ∨ 0 < b
  · have hβ : IsServiceCurve R R' (convCurve (rateLatency R₁ T₁) (rateLatency R₂ T₂)) :=
      serviceCurve_concat hR hRmid hR' hβ₁ hβ₂
    rw [convCurve_rateLatency] at hβ
    have h := delay_le_hdev hR hR' hα hβ t
    rw [hdev_tokenBucket_rateLatency hr hRpos hpos] at h
    exact h
  · push Not at hpos
    obtain ⟨hr0, hb0⟩ := hpos
    have hr0' : r = 0 := le_antisymm hr0 zero_le
    have hb0' : b = 0 := le_antisymm hb0 zero_le
    subst hr0'
    subst hb0'
    have hR0 : ∀ u, R u = 0 := cc_flow_zero_of_zero_bucket hR hα
    rw [cc_delay_zero_of_flow_zero hR0 t]
    exact zero_le

/-- Order independence: the same end-to-end bound holds with the two
rate-latency nodes swapped. -/
theorem delay_concat_rateLatency_swap {R Rmid R' : ℝ≥0 → ℝ≥0} {r b : ℝ≥0}
    {R₁ R₂ T₁ T₂ : ℝ≥0} (hR : IsCumulativeFlow R)
    (hRmid : IsCumulativeFlow Rmid) (hR' : IsCumulativeFlow R')
    (hα : IsArrivalCurve R (tokenBucket r b))
    (hβ₁ : IsServiceCurve R Rmid (rateLatency R₂ T₂))
    (hβ₂ : IsServiceCurve Rmid R' (rateLatency R₁ T₁))
    (hr : r ≤ min R₁ R₂) (hRpos : 0 < min R₁ R₂)
    (t : ℝ≥0) :
    delay R R' t ≤ ((T₁ + T₂ + b / min R₁ R₂ : ℝ≥0) : ℝ≥0∞) := by
  by_cases hpos : 0 < r ∨ 0 < b
  · have hβ : IsServiceCurve R R' (convCurve (rateLatency R₂ T₂) (rateLatency R₁ T₁)) :=
      serviceCurve_concat hR hRmid hR' hβ₁ hβ₂
    rw [convCurve_comm, convCurve_rateLatency] at hβ
    have h := delay_le_hdev hR hR' hα hβ t
    rw [hdev_tokenBucket_rateLatency hr hRpos hpos] at h
    exact h
  · push Not at hpos
    obtain ⟨hr0, hb0⟩ := hpos
    have hr0' : r = 0 := le_antisymm hr0 zero_le
    have hb0' : b = 0 := le_antisymm hb0 zero_le
    subst hr0'
    subst hb0'
    have hR0 : ∀ u, R u = 0 := cc_flow_zero_of_zero_bucket hR hα
    rw [cc_delay_zero_of_flow_zero hR0 t]
    exact zero_le

end Cslib.Algorithms.Networking.NetworkCalculus
