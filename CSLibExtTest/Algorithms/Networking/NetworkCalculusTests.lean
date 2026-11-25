/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for network calculus bounds
-/

module

public import CSLibExt.Algorithms.Networking.NetworkCalculus
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.Order.Star.Real

/-!
Tests for the network calculus backlog and delay bounds. Equality tests
assert equality of the deviation values in `ℝ≥0∞`, never pointwise equality
at `0`: suprema need not be attained (see `constRate_vdiff_zero`). The
horizontal-value tests carry the non-degeneracy hypothesis `0 < r ∨ 0 < b`
from the `NetworkCalculus` module note: a degenerate `γ 0 0` gives `h = 0`.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal

private theorem gamma_zero (r b : ℝ≥0) : tokenBucket r b 0 = 0 :=
  ite_eq_left rfl

private theorem gamma_ne_zero (r b s : ℝ≥0) (hs : s ≠ 0) :
    tokenBucket r b s = r * s + b :=
  ite_eq_right hs

private theorem beta_eq (R T s : ℝ≥0) :
    rateLatency R T s = R * (s - T) := by
  show R * max (s - T) 0 = R * (s - T)
  rw [max_eq_left zero_le]

/-- Constant-rate server (`T = 0`): vertical deviation is `b`. -/
theorem constRate_vdev {r b R : ℝ≥0} (hr : 0 < r) (h : r ≤ R) :
    vdev (tokenBucket r b) (rateLatency R 0) = (b : ℝ≥0∞) := by
  have hT := vdev_tokenBucket_rateLatency (r := r) (b := b) (R := R) (T := 0) h
  rw [mul_zero, add_zero] at hT
  exact hT

/-- Constant-rate server (`T = 0`): horizontal deviation is `b / R`. -/
theorem constRate_hdev {r b R : ℝ≥0} (hr : 0 < r) (h : r ≤ R) :
    hdev (tokenBucket r b) (rateLatency R 0) = ((b / R : ℝ≥0) : ℝ≥0∞) := by
  have hR : 0 < R := by
    by_contra hcon
    push Not at hcon
    have hR0 : R = 0 := le_zero_iff.mp hcon
    rw [hR0] at h
    have hr0 : r = 0 := le_zero_iff.mp h
    rw [hr0] at hr
    exact (lt_irrefl 0) hr
  have hT := hdev_tokenBucket_rateLatency (r := r) (b := b) (R := R) (T := 0) h
    hR (Or.inl hr)
  rw [zero_add] at hT
  exact hT

/-- The `T = 0` supremum is not attained: the vertical difference at `0`
is `0`, while the deviation value is `b`. -/
theorem constRate_vdiff_zero {r b R : ℝ≥0} :
    (tokenBucket r b 0 : ℝ≥0∞) - (rateLatency R 0 0 : ℝ≥0∞) = 0 := by
  rw [gamma_zero, beta_eq, tsub_zero, mul_zero, ENNReal.coe_zero, tsub_self]

/-- Latency `T > 0`: vertical deviation is `b + r * T`. -/
theorem latency_vdev {r b R T : ℝ≥0} (h : r ≤ R) (hT : 0 < T) :
    vdev (tokenBucket r b) (rateLatency R T) = ((b + r * T : ℝ≥0) : ℝ≥0∞) :=
  vdev_tokenBucket_rateLatency h

/-- Latency `T > 0`: horizontal deviation is `T + b / R`. -/
theorem latency_hdev {r b R T : ℝ≥0} (h : r ≤ R) (hR : 0 < R) (hT : 0 < T)
    (hpos : 0 < r ∨ 0 < b) :
    hdev (tokenBucket r b) (rateLatency R T) = ((T + b / R : ℝ≥0) : ℝ≥0∞) :=
  hdev_tokenBucket_rateLatency h hR hpos

/-- For `r > R` the vertical deviation is top. -/
theorem rate_vdev_top {r b R T : ℝ≥0} (h : R < r) :
    vdev (tokenBucket r b) (rateLatency R T) = ⊤ :=
  vdev_top_of_rate h

/-- For `r > R` the horizontal deviation is top. -/
theorem rate_hdev_top {r b R T : ℝ≥0} (h : R < r) :
    hdev (tokenBucket r b) (rateLatency R T) = ⊤ :=
  hdev_top_of_rate h

/-- The token bucket constrains itself as a flow. -/
theorem gamma_self_arrival {r b : ℝ≥0} :
    IsArrivalCurve (tokenBucket r b) (tokenBucket r b) := by
  constructor
  · intro a c hac
    by_cases ha : a = 0
    · rw [ha, gamma_zero]
      exact zero_le
    · have hc : c ≠ 0 := by
        intro hcon
        rw [hcon] at hac
        exact ha (le_zero_iff.mp hac)
      rw [gamma_ne_zero _ _ _ ha, gamma_ne_zero _ _ _ hc]
      exact add_le_add (mul_le_mul_of_nonneg_left hac zero_le) le_rfl
  · intro s t hst
    by_cases hs : s = 0
    · rw [hs, gamma_zero, tsub_zero, tsub_zero]
    · have ht : t ≠ 0 := by
        intro hcon
        rw [hcon] at hst
        exact hs (le_zero_iff.mp hst)
      rw [gamma_ne_zero _ _ _ ht, gamma_ne_zero _ _ _ hs]
      by_cases hts : t - s = 0
      · have hle : t ≤ s := tsub_eq_zero_iff_le.mp hts
        have hts' : t = s := le_antisymm hle hst
        rw [hts, gamma_zero, hts', tsub_self]
      · rw [gamma_ne_zero _ _ _ hts]
        have hYX : r * s ≤ r * t := mul_le_mul_of_nonneg_left hst zero_le
        have hsub : (r * t + b) - (r * s + b) = r * (t - s) := by
          have hdecomp : r * t = (r * t - r * s) + r * s :=
            (tsub_add_cancel_of_le hYX).symm
          calc (r * t + b) - (r * s + b)
              = ((r * t - r * s) + r * s + b) - (r * s + b) := by
                conv_lhs => rw [hdecomp]
            _ = ((r * t - r * s) + (r * s + b)) - (r * s + b) := by
                rw [add_assoc]
            _ = r * t - r * s := add_tsub_cancel_right _ _
            _ = r * (t - s) := (mul_tsub _ _ _).symm
        rw [hsub]
        exact le_add_right le_rfl

/-- The token bucket is exact on windows from `0`. -/
theorem gamma_window_zero {r b : ℝ≥0} (t : ℝ≥0) :
    tokenBucket r b t - tokenBucket r b 0 = tokenBucket r b (t - 0) := by
  rw [gamma_zero, tsub_zero, tsub_zero]

/-- The identity system has zero backlog. -/
theorem backlog_identity (R : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    backlog R R t = 0 := by
  unfold backlog
  exact tsub_self _

/-- The identity system has zero delay. -/
theorem delay_identity (R : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    delay R R t = 0 := by
  apply le_antisymm
  · have h0 : R t ≤ R (t + 0) := by rw [add_zero]
    calc delay R R t ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
          iInf_le _ (⟨0, h0⟩ : { τ : ℝ≥0 // R t ≤ R (t + τ) })
      _ = 0 := ENNReal.coe_zero
  · exact zero_le

/-- A pure-delay system delays by at most the delay parameter. -/
theorem delay_pureDelay_le (R : ℝ≥0 → ℝ≥0) (D : ℝ≥0) (t : ℝ≥0) :
    delay R (fun t => R (t - D)) t ≤ (D : ℝ≥0∞) := by
  have hD : R t ≤ (fun t => R (t - D)) (t + D) := by
    show R t ≤ R (t + D - D)
    rw [add_tsub_cancel_right]
  exact iInf_le _ (⟨D, hD⟩ : { τ : ℝ≥0 // R t ≤ (fun t => R (t - D)) (t + τ) })

/-- Latency separates horizontal from vertical deviation: `v = 1`, `h = 2`. -/
theorem latency_separates_vdev_hdev :
    vdev (tokenBucket 0 1) (rateLatency 1 1) = 1 ∧
      hdev (tokenBucket 0 1) (rateLatency 1 1) = 2 := by
  constructor
  · have hT := vdev_tokenBucket_rateLatency (r := (0 : ℝ≥0)) (b := 1) (R := 1)
      (T := 1) zero_le
    rw [hT]
    simp
  · have hT := hdev_tokenBucket_rateLatency (r := (0 : ℝ≥0)) (b := 1) (R := 1)
      (T := 1) zero_le zero_lt_one (Or.inr zero_lt_one)
    rw [hT]
    simp [one_add_one_eq_two]

/-- Zero service gives top horizontal deviation against a somewhere-positive
arrival curve. -/
theorem hdev_zero_service_top (α : ℝ≥0 → ℝ≥0) (hα : ∃ s, α s ≠ 0) :
    hdev α (fun _ => 0) = ⊤ := by
  obtain ⟨s, hs⟩ := hα
  haveI hempty : IsEmpty { τ : ℝ≥0 // α s ≤ (fun _ => 0) (s + τ) } :=
    ⟨fun u => hs (le_zero_iff.mp (show α s ≤ 0 from u.property))⟩
  have htop : (⨅ u : { τ : ℝ≥0 // α s ≤ (fun _ => 0) (s + τ) },
      (u.val : ℝ≥0∞)) = ⊤ := iInf_of_empty _
  have hle : (⊤ : ℝ≥0∞) ≤ hdev α (fun _ => 0) := by
    rw [← htop]
    exact le_iSup (fun s : ℝ≥0 => ⨅ u : { τ : ℝ≥0 //
      α s ≤ (fun _ => 0) (s + τ) }, (u.val : ℝ≥0∞)) s
  exact top_le_iff.mp hle

/-- Empty-infimum delay is top. -/
theorem delay_empty_top (R R' : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (h : ∀ τ : ℝ≥0, R' (t + τ) < R t) : delay R R' t = ⊤ := by
  haveI hempty : IsEmpty { τ : ℝ≥0 // R t ≤ R' (t + τ) } :=
    ⟨fun u => absurd u.property (not_le_of_gt (h u.val))⟩
  exact iInf_of_empty _

/-- Convolution at `0` is the sum of the endpoint values. -/
theorem conv_at_zero (f g : ℝ≥0 → ℝ≥0) :
    minPlusConv f g 0 = ((f 0 + g 0 : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · calc minPlusConv f g 0 ≤ ((f (0 - 0) + g 0 : ℝ≥0) : ℝ≥0∞) :=
          minPlusConv_le le_rfl
      _ = ((f 0 + g 0 : ℝ≥0) : ℝ≥0∞) := by rw [tsub_self]
  · apply le_iInf
    intro u
    have hu : u.val = 0 := le_zero_iff.mp u.property
    rw [hu, tsub_self]

/-- Convolution is bounded by its `s = 0` endpoint term. -/
theorem conv_upper_left (f g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minPlusConv f g t ≤ ((f t + g 0 : ℝ≥0) : ℝ≥0∞) := by
  have h0 := minPlusConv_le (f := f) (g := g) (t := t) (s := 0) zero_le
  rw [tsub_zero] at h0
  exact h0

/-- Convolution is bounded by its `s = t` endpoint term. -/
theorem conv_upper_right (f g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minPlusConv f g t ≤ ((f 0 + g t : ℝ≥0) : ℝ≥0∞) := by
  have ht := minPlusConv_le (f := f) (g := g) (t := t) (s := t) le_rfl
  rw [tsub_self] at ht
  exact ht

/-- Convolution of monotone functions is monotone in time. -/
theorem conv_mono_time (f g : ℝ≥0 → ℝ≥0) (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun t => minPlusConv f g t) := by
  intro a b hab
  apply le_iInf
  intro u
  by_cases hua : u.val ≤ a
  · calc minPlusConv f g a
        ≤ ((f (a - u.val) + g u.val : ℝ≥0) : ℝ≥0∞) := minPlusConv_le hua
      _ ≤ ((f (b - u.val) + g u.val : ℝ≥0) : ℝ≥0∞) := by
          apply ENNReal.coe_le_coe.mpr
          exact add_le_add (hf (tsub_le_tsub_right hab _)) le_rfl
  · push Not at hua
    have hau : a ≤ u.val := le_of_lt hua
    calc minPlusConv f g a ≤ ((f (a - a) + g a : ℝ≥0) : ℝ≥0∞) :=
          minPlusConv_le le_rfl
      _ = ((f 0 + g a : ℝ≥0) : ℝ≥0∞) := by rw [tsub_self]
      _ ≤ ((f (b - u.val) + g u.val : ℝ≥0) : ℝ≥0∞) := by
          apply ENNReal.coe_le_coe.mpr
          exact add_le_add (hf zero_le) (hg hau)

/-- Half-rate service: backlog at each time is `t / 2`. -/
theorem half_backlog_value (t : ℝ≥0) :
    backlog (fun t => t) (fun t => t / 2) t = ((t / 2 : ℝ≥0) : ℝ≥0∞) := by
  unfold backlog
  show (t : ℝ≥0∞) - ((t / 2 : ℝ≥0) : ℝ≥0∞) = ((t / 2 : ℝ≥0) : ℝ≥0∞)
  rw [← ENNReal.coe_sub]
  congr 1
  nth_rewrite 1 [← add_halves t]
  exact add_tsub_cancel_right _ _

/-- Half-rate service: backlog is finite at each time. -/
theorem half_backlog_finite (t : ℝ≥0) :
    backlog (fun t => t) (fun t => t / 2) t ≠ ⊤ := by
  rw [half_backlog_value]
  exact ENNReal.coe_ne_top

/-- Half-rate service: backlog is uniformly unbounded over time. -/
theorem half_backlog_unbounded :
    ⨆ t : ℝ≥0, backlog (fun t => t) (fun t => t / 2) t = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro M
  have hM : (2 * M / 2 : ℝ≥0) = M := mul_div_cancel_left₀ M two_ne_zero
  calc (M : ℝ≥0∞) = backlog (fun t => t) (fun t => t / 2) (2 * M) := by
        rw [half_backlog_value, hM]
    _ ≤ ⨆ t : ℝ≥0, backlog (fun t => t) (fun t => t / 2) t := le_iSup _ (2 * M)

/-- Half-rate service: delay at each time is `t`. -/
theorem half_delay_value (t : ℝ≥0) :
    delay (fun t => t) (fun t => t / 2) t = (t : ℝ≥0∞) := by
  apply le_antisymm
  · have hmem : (fun t => t) t ≤ (fun t => t / 2) (t + t) := by
      show t ≤ (t + t) / 2
      rw [add_div, add_halves]
    exact iInf_le _ (⟨t, hmem⟩ : { τ : ℝ≥0 //
      (fun t => t) t ≤ (fun t => t / 2) (t + τ) })
  · apply le_iInf
    intro w
    obtain ⟨τ, hτ⟩ := w
    show (t : ℝ≥0∞) ≤ (τ : ℝ≥0∞)
    apply ENNReal.coe_le_coe.mpr
    have hτ' : t ≤ (t + τ) / 2 := hτ
    rw [add_div] at hτ'
    have htt : t = t / 2 + t / 2 := (add_halves t).symm
    have hle : t / 2 ≤ τ / 2 := by
      have h3 : t / 2 + t / 2 ≤ t / 2 + τ / 2 := by
        conv_lhs => rw [← htt]
        exact hτ'
      exact le_of_add_le_add_left h3
    have h2 : (t / 2) * 2 ≤ (τ / 2) * 2 :=
      mul_le_mul_of_nonneg_right hle zero_le
    rw [div_mul_cancel₀ _ two_ne_zero, div_mul_cancel₀ _ two_ne_zero] at h2
    exact h2

/-- Zero service rate with positive burst gives top horizontal deviation. -/
theorem zeroRate_hdev_top {r b T : ℝ≥0} (hb : 0 < b) :
    hdev (tokenBucket r b) (rateLatency 0 T) = ⊤ := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hγ : tokenBucket r b 1 = r * 1 + b := gamma_ne_zero _ _ _ h1
  have hγpos : 0 < tokenBucket r b 1 := by
    rw [hγ]
    exact lt_of_lt_of_le hb (le_add_left le_rfl)
  have hβ : ∀ τ : ℝ≥0, rateLatency 0 T (1 + τ) = 0 := by
    intro τ
    rw [beta_eq, zero_mul]
  haveI hempty : IsEmpty { τ : ℝ≥0 //
      tokenBucket r b 1 ≤ rateLatency 0 T (1 + τ) } :=
    ⟨fun u => by
      have hprop := u.property
      rw [hβ u.val] at hprop
      exact absurd hprop (not_le_of_gt hγpos)⟩
  have htop : (⨅ u : { τ : ℝ≥0 //
      tokenBucket r b 1 ≤ rateLatency 0 T (1 + τ) }, (u.val : ℝ≥0∞)) = ⊤ :=
    iInf_of_empty _
  have hle : (⊤ : ℝ≥0∞) ≤ hdev (tokenBucket r b) (rateLatency 0 T) := by
    rw [← htop]
    exact le_iSup (fun s : ℝ≥0 => ⨅ u : { τ : ℝ≥0 //
      tokenBucket r b s ≤ rateLatency 0 T (s + τ) }, (u.val : ℝ≥0∞)) 1
  exact top_le_iff.mp hle

/-- Zero service rate with zero arrival rate keeps vertical deviation at `b`. -/
theorem zeroRate_vdev_value {b T : ℝ≥0} :
    vdev (tokenBucket 0 b) (rateLatency 0 T) = (b : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    show ((tokenBucket 0 b s : ℝ≥0∞) - (rateLatency 0 T s : ℝ≥0∞)) ≤ (b : ℝ≥0∞)
    rw [beta_eq, zero_mul, ENNReal.coe_zero, tsub_zero]
    by_cases hs : s = 0
    · rw [hs, gamma_zero, ENNReal.coe_zero]
      exact zero_le
    · rw [gamma_ne_zero _ _ _ hs, zero_mul, zero_add]
  · have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have hterm : ((tokenBucket 0 b 1 : ℝ≥0∞) - (rateLatency 0 T 1 : ℝ≥0∞))
        = (b : ℝ≥0∞) := by
      rw [gamma_ne_zero _ _ _ h1, beta_eq, zero_mul, zero_mul,
        ENNReal.coe_zero, tsub_zero, zero_add]
    calc (b : ℝ≥0∞)
        = ((tokenBucket 0 b 1 : ℝ≥0∞) - (rateLatency 0 T 1 : ℝ≥0∞)) :=
          hterm.symm
      _ ≤ vdev (tokenBucket 0 b) (rateLatency 0 T) :=
          le_iSup (fun s : ℝ≥0 => ((tokenBucket 0 b s : ℝ≥0∞)
            - (rateLatency 0 T s : ℝ≥0∞))) 1

/-- The zero flow has zero delay against any service. -/
theorem zeroFlow_delay (R' : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    delay (fun _ => 0) R' t = 0 := by
  apply le_antisymm
  · have h0 : (fun _ : ℝ≥0 => 0) t ≤ R' (t + 0) := by
      show (0 : ℝ≥0) ≤ R' (t + 0)
      exact zero_le
    calc delay (fun _ => 0) R' t ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
          iInf_le _ (⟨0, h0⟩ : { τ : ℝ≥0 // (fun _ => 0) t ≤ R' (t + τ) })
      _ = 0 := ENNReal.coe_zero
  · exact zero_le

/-- The zero flow has zero backlog against any service. -/
theorem zeroFlow_backlog (R' : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    backlog (fun _ => 0) R' t = 0 := by
  have hbb : backlog (fun _ => 0) R' t
      = ((0 : ℝ≥0) : ℝ≥0∞) - (R' t : ℝ≥0∞) := rfl
  rw [hbb, ENNReal.coe_zero, zero_tsub]

end Cslib.Algorithms.Networking.NetworkCalculus
