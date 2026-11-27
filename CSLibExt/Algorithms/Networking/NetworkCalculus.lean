/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Network calculus: backlog and delay bounds (Le Boudec-Thiran)
-/

module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.Order.Star.Real

/-!
## Source

J.-Y. Le Boudec and P. Thiran, Network Calculus (LNCS 2050), Chapter 1
(Sections 1.1-1.4), plus Definition 3.1.15 (Equations 3.20-3.21) for the
vertical and horizontal deviations, exactly as Chapter 1 itself imports it.

## Frozen conventions

- Continuous time `ℝ≥0`. Flows and curves are finite-valued monotone
  (`Monotone`) functions into nonnegative reals.
- Cumulative flows `R`, `R*` and service curves `β` vanish at `0`; arrival
  curves `α` are monotone with no `α 0 = 0` requirement.
- No continuity hypotheses anywhere (deliberate strengthening over the book's
  left-continuous convention; attainment statements are out of scope).
- Virtual delay, vertical deviation, and horizontal deviation take values in
  `ℝ≥0∞`, so infinite bounds and empty-infimum delays are honest top values.
- Min-plus convolution is the total infimum over `[0, t]` in that extended
  setting (see `minPlusConv`); this uniform `ℝ≥0∞` encoding is used for every
  extended quantity below, and encodings are never mixed.
- Causality `R* ≤ R` is part of the flow-pair predicate `IsFlowPair`
  (lossless system, Def. 1.1.1), but the bound theorems take the two
  `IsCumulativeFlow` hypotheses separately and do not consume causality.
- Token bucket `γ r b`: `γ 0 = 0` and `γ t = r * t + b` for `t > 0`.
- Rate latency `β R T`: `β R T t = R * max (t - T) 0`.

## Out of scope for this leaf

`+∞`-valued curve inputs such as `δ_T` service curves, deconvolution,
pseudo-inverse, the full convolution algebra (associativity, commutativity,
distributivity), Theorem 1.4.3, concatenation, greedy shapers, and the
discrete-time variant.

## Note on the horizontal closed form

The book's Figure 1.10 equality `h (γ r b) (β R T) = T + b / R` (for `r ≤ R`
and `R > 0`) is false as stated: for `r = b = 0` and `R = T = 1` the left
side is `0` while the right side is `1`. It is therefore not stated here. It
becomes true under a non-degeneracy hypothesis such as `0 < r ∨ 0 < b`.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal

/-- A cumulative flow: a finite-valued monotone function of continuous time
vanishing at `0`. No continuity is assumed. -/
def IsCumulativeFlow (R : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone R ∧ R 0 = 0

/-- A lossless flow pair (system): two cumulative flows with pointwise
causality `R* ≤ R` (Def. 1.1.1). The bound theorems below do not consume
causality; they take the two `IsCumulativeFlow` hypotheses separately. -/
def IsFlowPair (R R' : ℝ≥0 → ℝ≥0) : Prop :=
  IsCumulativeFlow R ∧ IsCumulativeFlow R' ∧ ∀ t, R' t ≤ R t

/-- Backlog at time `t`: `R t - R' t` as an extended value. -/
def backlog (R R' : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  (R t : ℝ≥0∞) - (R' t : ℝ≥0∞)

/-- Virtual delay at time `t`: `inf {τ ≥ 0 | R t ≤ R' (t + τ)}` in `ℝ≥0∞`.
The infimum is total: an empty set gives `⊤`. -/
noncomputable def delay (R R' : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ u : { τ : ℝ≥0 // R t ≤ R' (t + τ) }, (u.val : ℝ≥0∞)

/-- Arrival-curve constraint: `α` is monotone and
`R t - R s ≤ α (t - s)` for `s ≤ t`. No `α 0 = 0` is required. -/
def IsArrivalCurve (R α : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone α ∧ ∀ s t : ℝ≥0, s ≤ t → R t - R s ≤ α (t - s)

/-- Min-plus convolution: `(f ⊗ g) t` is the infimum over `0 ≤ s ≤ t` of
`f (t - s) + g s`, as a total `iInf` in `ℝ≥0∞` over the subtype. -/
noncomputable def minPlusConv (f g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ s : { s : ℝ≥0 // s ≤ t }, ((f (t - s.val) + g s.val : ℝ≥0) : ℝ≥0∞)

/-- Service-curve offer: `β` is monotone, vanishes at `0`, and
`R' t ≥ (R ⊗ β) t` for all `t` (compared in `ℝ≥0∞`). -/
def IsServiceCurve (R R' β : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone β ∧ β 0 = 0 ∧ ∀ t, minPlusConv R β t ≤ (R' t : ℝ≥0∞)

/-- Vertical deviation: `v α β = sup over s ≥ 0 of (α s - β s)` in `ℝ≥0∞`. -/
noncomputable def vdev (α β : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  ⨆ s : ℝ≥0, ((α s : ℝ≥0∞) - (β s : ℝ≥0∞))

/-- Horizontal deviation per Def. 3.1.15:
`h α β = sup over s ≥ 0 of inf {τ ≥ 0 | α s ≤ β (s + τ)}` in `ℝ≥0∞`. -/
noncomputable def hdev (α β : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  ⨆ s : ℝ≥0, ⨅ u : { τ : ℝ≥0 // α s ≤ β (s + τ) }, (u.val : ℝ≥0∞)

/-- Token-bucket arrival curve `γ r b`: `0` at `0`, `r * t + b` for `t > 0`. -/
noncomputable def tokenBucket (r b : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => if t = 0 then 0 else r * t + b

/-- Rate-latency service curve `β R T`: `R * max (t - T) 0`. -/
def rateLatency (R T : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => R * max (t - T) 0

/-- Backlog bound (Thm. 1.4.1): a flow arrival-constrained by `α` in a system
offering service curve `β` has backlog at most `v α β` at every time.
Causality is not consumed. -/
theorem backlog_le_vdev {R R' α β : ℝ≥0 → ℝ≥0}
    (hR : IsCumulativeFlow R) (hR' : IsCumulativeFlow R')
    (hα : IsArrivalCurve R α) (hβ : IsServiceCurve R R' β) (t : ℝ≥0) :
    backlog R R' t ≤ vdev α β := by
  unfold backlog
  rw [tsub_le_iff_left]
  have hserv : minPlusConv R β t ≤ (R' t : ℝ≥0∞) := hβ.2.2 t
  have hconv : (R t : ℝ≥0∞) - vdev α β ≤ minPlusConv R β t := by
    apply le_iInf
    intro u
    rw [tsub_le_iff_right]
    have hle : t - u.val ≤ t := tsub_le_self
    have harr := hα.2 (t - u.val) t hle
    rw [tsub_tsub_cancel_of_le u.property] at harr
    have hRt : R t ≤ R (t - u.val) + α u.val := tsub_le_iff_left.mp harr
    have hαu : (α u.val : ℝ≥0∞) ≤ (β u.val : ℝ≥0∞) + vdev α β :=
      tsub_le_iff_left.mp
        (le_iSup (fun s : ℝ≥0 => ((α s : ℝ≥0∞) - (β s : ℝ≥0∞))) u.val)
    calc (R t : ℝ≥0∞)
        ≤ ((R (t - u.val) + α u.val : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hRt
      _ = (R (t - u.val) : ℝ≥0∞) + (α u.val : ℝ≥0∞) := ENNReal.coe_add _ _
      _ ≤ (R (t - u.val) : ℝ≥0∞) + ((β u.val : ℝ≥0∞) + vdev α β) :=
          add_le_add le_rfl hαu
      _ = ((R (t - u.val) + β u.val : ℝ≥0) : ℝ≥0∞) + vdev α β := by
          rw [ENNReal.coe_add, add_assoc]
  have hconv' : (R t : ℝ≥0∞) ≤ minPlusConv R β t + vdev α β :=
    tsub_le_iff_right.mp hconv
  calc (R t : ℝ≥0∞) ≤ minPlusConv R β t + vdev α β := hconv'
    _ ≤ (R' t : ℝ≥0∞) + vdev α β := add_le_add hserv le_rfl

/-- Delay bound (Thm. 1.4.2): under the same hypotheses, virtual delay at
every time is at most `h α β`. Causality is not consumed. -/
theorem delay_le_hdev {R R' α β : ℝ≥0 → ℝ≥0}
    (hR : IsCumulativeFlow R) (hR' : IsCumulativeFlow R')
    (hα : IsArrivalCurve R α) (hβ : IsServiceCurve R R' β) (t : ℝ≥0) :
    delay R R' t ≤ hdev α β := by
  have key : ∀ τ : ℝ≥0, (∀ s, α s ≤ β (s + τ)) → delay R R' t ≤ (τ : ℝ≥0∞) := by
    intro τ hunif
    have hRt : R t ≤ R' (t + τ) := by
      apply ENNReal.coe_le_coe.mp
      calc (R t : ℝ≥0∞) ≤ minPlusConv R β (t + τ) := by
            apply le_iInf
            intro u
            show (R t : ℝ≥0∞)
              ≤ ((R (t + τ - u.val) + β u.val : ℝ≥0) : ℝ≥0∞)
            apply ENNReal.coe_le_coe.mpr
            by_cases hcase : t ≤ t + τ - u.val
            · calc R t ≤ R (t + τ - u.val) := hR.1 hcase
                _ ≤ R (t + τ - u.val) + β u.val := le_add_right le_rfl
            · have hvt : t + τ - u.val ≤ t := le_of_lt (lt_of_not_ge hcase)
              have harr : R t - R (t + τ - u.val) ≤ α (t - (t + τ - u.val)) :=
                hα.2 _ _ hvt
              have hRle : R t ≤ R (t + τ - u.val) + α (t - (t + τ - u.val)) :=
                tsub_le_iff_left.mp harr
              have huv : t + τ - u.val + u.val = t + τ :=
                tsub_add_cancel_of_le u.property
              have hgoal : t - (t + τ - u.val) + τ ≤ u.val := by
                have htv : t - (t + τ - u.val) + (t + τ - u.val) = t :=
                  tsub_add_cancel_of_le hvt
                have h1 : t - (t + τ - u.val) + τ + (t + τ - u.val) ≤
                    u.val + (t + τ - u.val) := by
                  have heq : t - (t + τ - u.val) + τ + (t + τ - u.val)
                      = t + τ := by
                    calc t - (t + τ - u.val) + τ + (t + τ - u.val)
                        = (t - (t + τ - u.val) + (t + τ - u.val)) + τ := by
                          ac_rfl
                      _ = t + τ := by rw [htv]
                  rw [heq, add_comm u.val _, huv]
                exact le_of_add_le_add_right h1
              calc R t ≤ R (t + τ - u.val) + α (t - (t + τ - u.val)) := hRle
                _ ≤ R (t + τ - u.val) + β (t - (t + τ - u.val) + τ) :=
                    add_le_add le_rfl (hunif _)
                _ ≤ R (t + τ - u.val) + β u.val :=
                    add_le_add le_rfl (hβ.1 hgoal)
        _ ≤ (R' (t + τ) : ℝ≥0∞) := hβ.2.2 (t + τ)
    exact iInf_le
      (fun u : { τ' : ℝ≥0 // R t ≤ R' (t + τ') } => (u.val : ℝ≥0∞))
      (⟨τ, hRt⟩ : { τ' : ℝ≥0 // R t ≤ R' (t + τ') })
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcl, hcr⟩ := exists_between hcon
  have hc_top : c ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hcr le_top)
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = c :=
    ⟨c.toNNReal, ENNReal.coe_toNNReal hc_top⟩
  subst hr
  have hunif : ∀ s, α s ≤ β (s + r) := by
    intro s
    have hs : (⨅ u : { τ : ℝ≥0 // α s ≤ β (s + τ) }, (u.val : ℝ≥0∞)) <
        (r : ℝ≥0∞) :=
      lt_of_le_of_lt
        (le_iSup (fun s : ℝ≥0 =>
          ⨅ u : { τ : ℝ≥0 // α s ≤ β (s + τ) }, (u.val : ℝ≥0∞)) s) hcl
    have hwit : ∃ (τ : ℝ≥0) (_ : α s ≤ β (s + τ)),
        (τ : ℝ≥0∞) < (r : ℝ≥0∞) := by
      by_contra hcon2
      have hle : (r : ℝ≥0∞) ≤
          ⨅ u : { τ : ℝ≥0 // α s ≤ β (s + τ) }, (u.val : ℝ≥0∞) := by
        apply le_iInf
        intro u
        by_contra hlt
        push Not at hlt
        exact hcon2 ⟨u.val, u.property, hlt⟩
      exact absurd hle (not_le_of_gt hs)
    obtain ⟨τ, hτ, hτr⟩ := hwit
    calc α s ≤ β (s + τ) := hτ
      _ ≤ β (s + r) :=
          hβ.1 (add_le_add le_rfl (ENNReal.coe_le_coe.mp (le_of_lt hτr)))
  exact absurd (key r hunif) (not_le_of_gt hcr)

/-- Upper-bound direction for convolution: every `s ≤ t` term bounds it. -/
theorem minPlusConv_le {f g : ℝ≥0 → ℝ≥0} {t s : ℝ≥0} (h : s ≤ t) :
    minPlusConv f g t ≤ ((f (t - s) + g s : ℝ≥0) : ℝ≥0∞) :=
  iInf_le _ (⟨s, h⟩ : { s : ℝ≥0 // s ≤ t })

/-- Strict lower-bound direction: if the convolution at `t` is below `c`, some term with
`s ≤ t` is below `c` (no attainment is claimed). -/
theorem exists_lt_of_minPlusConv_lt {f g : ℝ≥0 → ℝ≥0} {t : ℝ≥0} {c : ℝ≥0∞}
    (h : minPlusConv f g t < c) :
    ∃ (s : ℝ≥0) (_ : s ≤ t), ((f (t - s) + g s : ℝ≥0) : ℝ≥0∞) < c := by
  by_contra hc
  have hc' : ∀ (s : ℝ≥0) (_ : s ≤ t),
      c ≤ ((f (t - s) + g s : ℝ≥0) : ℝ≥0∞) := by
    intro s hs
    by_contra hlt
    push Not at hlt
    exact hc ⟨s, hs, hlt⟩
  have hle : c ≤ minPlusConv f g t := le_iInf fun s => hc' s.val s.property
  exact (not_le_of_gt h) hle

/-- Monotonicity of convolution in its first argument. -/
theorem minPlusConv_mono_left {f f' g : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (h : ∀ u, f u ≤ f' u) : minPlusConv f g t ≤ minPlusConv f' g t := by
  apply le_iInf
  intro s
  calc minPlusConv f g t
      ≤ ((f (t - s.val) + g s.val : ℝ≥0) : ℝ≥0∞) := iInf_le _ s
    _ ≤ ((f' (t - s.val) + g s.val : ℝ≥0) : ℝ≥0∞) := by
        apply ENNReal.coe_le_coe.mpr
        exact add_le_add (h _) le_rfl

/-- Monotonicity of convolution in its second argument. -/
theorem minPlusConv_mono_right {f g g' : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (h : ∀ u, g u ≤ g' u) : minPlusConv f g t ≤ minPlusConv f g' t := by
  apply le_iInf
  intro s
  calc minPlusConv f g t
      ≤ ((f (t - s.val) + g s.val : ℝ≥0) : ℝ≥0∞) := iInf_le _ s
    _ ≤ ((f (t - s.val) + g' s.val : ℝ≥0) : ℝ≥0∞) := by
        apply ENNReal.coe_le_coe.mpr
        exact add_le_add le_rfl (h _)

private theorem tokenBucket_zero (r b : ℝ≥0) : tokenBucket r b 0 = 0 :=
  ite_eq_left rfl

private theorem tokenBucket_ne_zero (r b s : ℝ≥0) (hs : s ≠ 0) :
    tokenBucket r b s = r * s + b :=
  ite_eq_right hs

private theorem rateLatency_eq (R T s : ℝ≥0) :
    rateLatency R T s = R * (s - T) := by
  show R * max (s - T) 0 = R * (s - T)
  rw [max_eq_left zero_le]

private theorem vdev_T0_wit (r b R y s : ℝ≥0) (h : r ≤ R) (hyb : y < b)
    (hsne : s ≠ 0) (hsmall : (R - r) * s ≤ b - y) :
    (y : ℝ≥0∞) ≤ ((tokenBucket r b s : ℝ≥0∞)
      - (rateLatency R 0 s : ℝ≥0∞)) := by
  rw [tokenBucket_ne_zero _ _ _ hsne, rateLatency_eq, tsub_zero,
    ← ENNReal.coe_sub]
  apply ENNReal.coe_le_coe.mpr
  have hRdecomp : ∀ t : ℝ≥0, R * t = r * t + (R - r) * t := by
    intro t
    have hRR : r + (R - r) = R := add_tsub_cancel_of_le h
    conv_lhs => rw [← hRR]
    exact add_mul _ _ _
  have hside : R * s ≤ r * s + b := by
    calc R * s = r * s + (R - r) * s := hRdecomp s
      _ ≤ r * s + (b - y) := add_le_add le_rfl hsmall
      _ ≤ r * s + b := add_le_add le_rfl tsub_le_self
  apply (le_tsub_iff_left hside).mpr
  calc R * s + y = r * s + (R - r) * s + y := by rw [hRdecomp]
    _ = r * s + ((R - r) * s + y) := add_assoc _ _ _
    _ ≤ r * s + ((b - y) + y) := add_le_add le_rfl (add_le_add hsmall le_rfl)
    _ = r * s + b := by
        rw [add_comm (b - y) y, add_tsub_cancel_of_le (le_of_lt hyb)]

/-- Closed form (Fig. 1.10): vertical deviation of token bucket against
rate latency with `r ≤ R` is `b + r * T`. -/
theorem vdev_tokenBucket_rateLatency {r b R T : ℝ≥0} (h : r ≤ R) :
    vdev (tokenBucket r b) (rateLatency R T) = ((b + r * T : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    show ((tokenBucket r b s : ℝ≥0∞) - (rateLatency R T s : ℝ≥0∞)) ≤ _
    by_cases hs : s = 0
    · subst hs
      rw [tokenBucket_zero, rateLatency_eq, zero_tsub, mul_zero]
      simp
    · rw [tokenBucket_ne_zero r b s hs, rateLatency_eq, tsub_le_iff_left]
      by_cases hsT : s ≤ T
      · rw [tsub_eq_zero_of_le hsT, mul_zero, ENNReal.coe_zero, zero_add]
        apply ENNReal.coe_le_coe.mpr
        calc r * s + b = b + r * s := add_comm _ _
          _ ≤ b + r * T :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hsT zero_le)
      · push Not at hsT
        have hRT : r * (s - T) ≤ R * (s - T) :=
          mul_le_mul_of_nonneg_right h zero_le
        have hdecomp : r * s = r * (s - T) + r * T := by
          have hle : T ≤ s := le_of_lt hsT
          calc r * s = r * ((s - T) + T) := by rw [tsub_add_cancel_of_le hle]
            _ = r * (s - T) + r * T := mul_add _ _ _
        rw [← ENNReal.coe_add]
        apply ENNReal.coe_le_coe.mpr
        calc r * s + b = r * (s - T) + r * T + b := by rw [hdecomp]
          _ = r * (s - T) + (r * T + b) := add_assoc _ _ _
          _ = r * (s - T) + (b + r * T) := by rw [add_comm (r * T) b]
          _ ≤ R * (s - T) + (b + r * T) := add_le_add hRT le_rfl
  · by_cases hT0 : T = 0
    · subst hT0
      rw [mul_zero, add_zero]
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hcl, hcr⟩ := exists_between hcon
      have hc_top : c ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hcr le_top)
      obtain ⟨y, hy⟩ : ∃ y : ℝ≥0, (y : ℝ≥0∞) = c :=
        ⟨c.toNNReal, ENNReal.coe_toNNReal hc_top⟩
      subst hy
      have hyb : y < b := ENNReal.coe_lt_coe.mp hcr
      have hδpos : (0 : ℝ≥0) < b - y := tsub_pos_of_lt hyb
      have hRr : (0 : ℝ≥0) < R - r + 1 := by positivity
      have hspos : (0 : ℝ≥0) < (b - y) / (R - r + 1) := div_pos hδpos hRr
      have hsne : (b - y) / (R - r + 1) ≠ 0 := ne_of_gt hspos
      have hsmall : (R - r) * ((b - y) / (R - r + 1)) ≤ b - y := by
        rw [← mul_div_assoc, div_le_iff₀ hRr]
        calc (R - r) * (b - y) = (b - y) * (R - r) := mul_comm _ _
          _ ≤ (b - y) * (R - r + 1) :=
              mul_le_mul_of_nonneg_left (le_add_right le_rfl) zero_le
      have hwit : (y : ℝ≥0∞) ≤ ((tokenBucket r b ((b - y) / (R - r + 1)) : ℝ≥0∞)
          - (rateLatency R 0 ((b - y) / (R - r + 1)) : ℝ≥0∞)) :=
        vdev_T0_wit r b R y _ h hyb hsne hsmall
      have hle : (y : ℝ≥0∞) ≤ vdev (tokenBucket r b) (rateLatency R 0) :=
        le_trans hwit (le_iSup (fun s : ℝ≥0 =>
          ((tokenBucket r b s : ℝ≥0∞) - (rateLatency R 0 s : ℝ≥0∞)))
          ((b - y) / (R - r + 1)))
      exact (not_le_of_gt hcl) hle
    · have hterm : ((tokenBucket r b T : ℝ≥0∞) - (rateLatency R T T : ℝ≥0∞))
          = ((b + r * T : ℝ≥0) : ℝ≥0∞) := by
        rw [tokenBucket_ne_zero _ _ _ hT0, rateLatency_eq, tsub_self, mul_zero,
          ENNReal.coe_zero, tsub_zero, add_comm (r * T) b]
      calc ((b + r * T : ℝ≥0) : ℝ≥0∞)
          = ((tokenBucket r b T : ℝ≥0∞) - (rateLatency R T T : ℝ≥0∞)) :=
            hterm.symm
        _ ≤ vdev (tokenBucket r b) (rateLatency R T) :=
            le_iSup (fun s : ℝ≥0 =>
              ((tokenBucket r b s : ℝ≥0∞) - (rateLatency R T s : ℝ≥0∞))) T

private theorem vdev_top_wit (r b R T M u : ℝ≥0) (hle : R ≤ r)
    (hsne : T + u ≠ 0) (hreach : M ≤ (r - R) * u) :
    (M : ℝ≥0∞) ≤ ((tokenBucket r b (T + u) : ℝ≥0∞)
      - (rateLatency R T (T + u) : ℝ≥0∞)) := by
  rw [tokenBucket_ne_zero _ _ _ hsne, rateLatency_eq,
    add_tsub_cancel_left T u, ← ENNReal.coe_sub]
  apply ENNReal.coe_le_coe.mpr
  have hRdecomp : ∀ t : ℝ≥0, r * t = R * t + (r - R) * t := by
    intro t
    have hRR : R + (r - R) = r := add_tsub_cancel_of_le hle
    conv_lhs => rw [← hRR]
    exact add_mul _ _ _
  have hrew : r * (T + u) + b = r * u + (r * T + b) := by
    rw [mul_add]
    ac_rfl
  have hside : R * u ≤ r * (T + u) + b := by
    calc R * u ≤ r * u := mul_le_mul_of_nonneg_right hle zero_le
      _ ≤ r * u + (r * T + b) := le_add_right le_rfl
      _ = r * (T + u) + b := hrew.symm
  apply (le_tsub_iff_left hside).mpr
  calc R * u + M ≤ R * u + (r - R) * u := add_le_add le_rfl hreach
    _ = r * u := (hRdecomp u).symm
    _ ≤ r * u + (r * T + b) := le_add_right le_rfl
    _ = r * (T + u) + b := hrew.symm

/-- For `r > R` the vertical deviation of token bucket against rate latency
is top. -/
theorem vdev_top_of_rate {r b R T : ℝ≥0} (h : R < r) :
    vdev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro M
  have hpos : (0 : ℝ≥0) < r - R := tsub_pos_of_lt h
  have hne : r - R ≠ 0 := ne_of_gt hpos
  have hM1 : (0 : ℝ≥0) < M + 1 := by positivity
  have hu : (0 : ℝ≥0) < (M + 1) / (r - R) := div_pos hM1 hpos
  have hsne : T + (M + 1) / (r - R) ≠ 0 := by
    have hpos2 : (0 : ℝ≥0) < T + (M + 1) / (r - R) := by positivity
    exact ne_of_gt hpos2
  have hreach : M ≤ (r - R) * ((M + 1) / (r - R)) := by
    have heq : (r - R) * ((M + 1) / (r - R)) = M + 1 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
    rw [heq]
    exact le_add_right le_rfl
  have hwit := vdev_top_wit r b R T M _ (le_of_lt h) hsne hreach
  exact le_trans hwit (le_iSup (fun s : ℝ≥0 =>
    ((tokenBucket r b s : ℝ≥0∞) - (rateLatency R T s : ℝ≥0∞)))
    (T + (M + 1) / (r - R)))

private theorem hdev_top_wit (r b R T M u τ : ℝ≥0) (hle : R ≤ r)
    (hsne : T + u ≠ 0) (hlt : R * M < (r - R) * u) (hleτ : τ ≤ M) :
    rateLatency R T (T + u + τ) < tokenBucket r b (T + u) := by
  rw [tokenBucket_ne_zero _ _ _ hsne, rateLatency_eq]
  have h1 : T + u + τ - T = u + τ := by
    calc T + u + τ - T = T + (u + τ) - T := by ac_rfl
      _ = u + τ := add_tsub_cancel_left T (u + τ)
  rw [h1]
  have hRdecomp : ∀ t : ℝ≥0, r * t = R * t + (r - R) * t := by
    intro t
    have hRR : R + (r - R) = r := add_tsub_cancel_of_le hle
    conv_lhs => rw [← hRR]
    exact add_mul _ _ _
  have hrew : r * (T + u) + b = r * u + (r * T + b) := by
    rw [mul_add]
    ac_rfl
  calc R * (u + τ) ≤ R * (u + M) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hleτ) zero_le
    _ = R * u + R * M := mul_add _ _ _
    _ < R * u + (r - R) * u := add_lt_add_of_le_of_lt le_rfl hlt
    _ = r * u := (hRdecomp u).symm
    _ ≤ r * u + (r * T + b) := le_add_right le_rfl
    _ = r * (T + u) + b := hrew.symm

/-- For `r > R` the horizontal deviation of token bucket against rate latency
is top. -/
theorem hdev_top_of_rate {r b R T : ℝ≥0} (h : R < r) :
    hdev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro M
  have hpos : (0 : ℝ≥0) < r - R := tsub_pos_of_lt h
  have hne : r - R ≠ 0 := ne_of_gt hpos
  have hRM1 : (0 : ℝ≥0) < R * M + 1 := by positivity
  have hu : (0 : ℝ≥0) < (R * M + 1) / (r - R) := div_pos hRM1 hpos
  have hsne : T + (R * M + 1) / (r - R) ≠ 0 := by
    have hpos2 : (0 : ℝ≥0) < T + (R * M + 1) / (r - R) := by positivity
    exact ne_of_gt hpos2
  have hlt : R * M < (r - R) * ((R * M + 1) / (r - R)) := by
    have heq : (r - R) * ((R * M + 1) / (r - R)) = R * M + 1 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
    rw [heq]
    exact lt_add_one _
  refine le_trans ?_ (le_iSup (fun s : ℝ≥0 => ⨅ w : { τ : ℝ≥0 //
    tokenBucket r b s ≤ rateLatency R T (s + τ) }, (w.val : ℝ≥0∞))
    (T + (R * M + 1) / (r - R)))
  apply le_iInf
  intro w
  by_cases hMw : M ≤ w.val
  · exact ENNReal.coe_le_coe.mpr hMw
  · push Not at hMw
    have hcon := hdev_top_wit r b R T M _ _ (le_of_lt h) hsne hlt
      (le_of_lt hMw)
    exact absurd w.property (not_le_of_gt hcon)

private theorem hdev_lower_small (r b R T y : ℝ≥0) (hyT : y < T)
    (hpos : 0 < r ∨ 0 < b) :
    (y : ℝ≥0∞) ≤ ⨅ w : { τ : ℝ≥0 //
      tokenBucket r b (T - y) ≤ rateLatency R T (T - y + τ) },
      (w.val : ℝ≥0∞) := by
  have hspos : (0 : ℝ≥0) < T - y := tsub_pos_of_lt hyT
  have hsne : T - y ≠ 0 := ne_of_gt hspos
  apply le_iInf
  intro w
  by_cases hyw : y ≤ w.val
  · exact ENNReal.coe_le_coe.mpr hyw
  · push Not at hyw
    exfalso
    have hsum : T - y + w.val ≤ T := by
      calc T - y + w.val ≤ T - y + y := add_le_add le_rfl (le_of_lt hyw)
        _ = T := tsub_add_cancel_of_le (le_of_lt hyT)
    have hβ0 : rateLatency R T (T - y + w.val) = 0 := by
      rw [rateLatency_eq, tsub_eq_zero_of_le hsum, mul_zero]
    have hγpos : 0 < tokenBucket r b (T - y) := by
      rw [tokenBucket_ne_zero _ _ _ hsne]
      rcases hpos with hr | hb
      · exact lt_of_lt_of_le (mul_pos hr hspos) (le_add_right le_rfl)
      · exact lt_of_lt_of_le hb (le_add_left le_rfl)
    have hprop := w.property
    rw [hβ0] at hprop
    exact absurd hprop (not_le_of_gt hγpos)

private theorem hdev_lower_big (r b R T y s : ℝ≥0) (h : r ≤ R)
    (hyT : T ≤ y) (hRyT : R * (y - T) < b)
    (hspos : 0 < s) (hsmall : (R - r) * s < b - R * (y - T)) :
    (y : ℝ≥0∞) ≤ ⨅ w : { τ : ℝ≥0 //
      tokenBucket r b s ≤ rateLatency R T (s + τ) }, (w.val : ℝ≥0∞) := by
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hRyTle : R * (y - T) ≤ b := le_of_lt hRyT
  have hRdecomp : ∀ t : ℝ≥0, R * t = r * t + (R - r) * t := by
    intro t
    have hRR : r + (R - r) = R := add_tsub_cancel_of_le h
    conv_lhs => rw [← hRR]
    exact add_mul _ _ _
  have hstrict2 : R * s + R * (y - T) < r * s + b := by
    calc R * s + R * (y - T) = r * s + ((R - r) * s + R * (y - T)) := by
          rw [hRdecomp, add_assoc]
      _ < r * s + ((b - R * (y - T)) + R * (y - T)) :=
          add_lt_add_of_le_of_lt le_rfl
            (add_lt_add_of_lt_of_le hsmall le_rfl)
      _ = r * s + b := by rw [tsub_add_cancel_of_le hRyTle]
  apply le_iInf
  intro w
  obtain ⟨τ, hτ⟩ := w
  by_cases hyτ : y ≤ τ
  · exact ENNReal.coe_le_coe.mpr hyτ
  · push Not at hyτ
    exfalso
    have hsub_le : s + τ - T ≤ s + (y - T) := by
      have h1 : s + τ - T ≤ s + y - T :=
        tsub_le_tsub_right (add_le_add le_rfl (le_of_lt hyτ)) T
      have h2 : s + y - T = s + (y - T) := add_tsub_assoc_of_le hyT s
      rw [h2] at h1
      exact h1
    have hle : rateLatency R T (s + τ) ≤ R * s + R * (y - T) := by
      rw [rateLatency_eq]
      calc R * (s + τ - T) ≤ R * (s + (y - T)) :=
            mul_le_mul_of_nonneg_left hsub_le zero_le
        _ = R * s + R * (y - T) := mul_add _ _ _
    have hγ : tokenBucket r b s = r * s + b :=
      tokenBucket_ne_zero _ _ _ hsne
    rw [hγ] at hτ
    have hcon : rateLatency R T (s + τ) < r * s + b :=
      lt_of_le_of_lt hle hstrict2
    exact absurd hτ (not_le_of_gt hcon)

/-- Closed form (Fig. 1.10, corrected): horizontal deviation of token bucket
against rate latency with `r ≤ R` is `T + b / R`, under non-degeneracy. -/
theorem hdev_tokenBucket_rateLatency {r b R T : ℝ≥0} (h : r ≤ R) (hR : 0 < R)
    (hpos : 0 < r ∨ 0 < b) :
    hdev (tokenBucket r b) (rateLatency R T) = ((T + b / R : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    show (⨅ w : { τ : ℝ≥0 //
      tokenBucket r b s ≤ rateLatency R T (s + τ) }, (w.val : ℝ≥0∞))
      ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞)
    by_cases hs : s = 0
    · subst hs
      have h0 : tokenBucket r b 0 ≤ rateLatency R T (0 + 0) := by
        rw [tokenBucket_zero, add_zero, rateLatency_eq, zero_tsub, mul_zero]
      calc (⨅ w : { τ : ℝ≥0 //
            tokenBucket r b 0 ≤ rateLatency R T (0 + τ) }, (w.val : ℝ≥0∞))
            ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
              iInf_le _ (⟨0, h0⟩ : { τ : ℝ≥0 //
                tokenBucket r b 0 ≤ rateLatency R T (0 + τ) })
        _ = 0 := ENNReal.coe_zero
        _ ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞) := zero_le
    · have hwork : tokenBucket r b s ≤ rateLatency R T (s + (T + b / R)) := by
        rw [tokenBucket_ne_zero _ _ _ hs, rateLatency_eq]
        have hsub : s + (T + b / R) - T = s + b / R := by
          calc s + (T + b / R) - T = T + (s + b / R) - T := by ac_rfl
            _ = s + b / R := add_tsub_cancel_left T (s + b / R)
        rw [hsub, mul_add]
        have hbR : R * (b / R) = b := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ hR.ne']
        rw [hbR]
        exact add_le_add (mul_le_mul_of_nonneg_right h zero_le) le_rfl
      exact iInf_le _ (⟨T + b / R, hwork⟩ : { τ : ℝ≥0 //
        tokenBucket r b s ≤ rateLatency R T (s + τ) })
  · by_contra hcon
    push Not at hcon
    obtain ⟨c, hcl, hcr⟩ := exists_between hcon
    have hc_top : c ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hcr le_top)
    obtain ⟨y, hy⟩ : ∃ y : ℝ≥0, (y : ℝ≥0∞) = c :=
      ⟨c.toNNReal, ENNReal.coe_toNNReal hc_top⟩
    subst hy
    have hybR : y < T + b / R := ENNReal.coe_lt_coe.mp hcr
    by_cases hyT : y < T
    · have hle : (y : ℝ≥0∞) ≤ hdev (tokenBucket r b) (rateLatency R T) :=
        le_trans (hdev_lower_small r b R T y hyT hpos)
          (le_iSup (fun s : ℝ≥0 => ⨅ w : { τ : ℝ≥0 //
            tokenBucket r b s ≤ rateLatency R T (s + τ) }, (w.val : ℝ≥0∞))
            (T - y))
      exact (not_le_of_gt hcl) hle
    · push Not at hyT
      have hyTsub : y - T < b / R := by
        rw [tsub_lt_iff_right hyT, add_comm]
        exact hybR
      have hbR : R * (b / R) = b := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hR.ne']
      have hRyT : R * (y - T) < b := by
        calc R * (y - T) < R * (b / R) := mul_lt_mul_of_pos_left hyTsub hR
          _ = b := hbR
      have hδpos : (0 : ℝ≥0) < b - R * (y - T) := tsub_pos_of_lt hRyT
      have hRr1 : (0 : ℝ≥0) < R - r + 1 := by positivity
      have hspos : (0 : ℝ≥0) < (b - R * (y - T)) / (R - r + 1) :=
        div_pos hδpos hRr1
      have hsmall : (R - r) * ((b - R * (y - T)) / (R - r + 1))
          < b - R * (y - T) := by
        rw [← mul_div_assoc, div_lt_iff₀ hRr1]
        have hmul : (b - R * (y - T)) * (R - r + 1)
            = (R - r) * (b - R * (y - T)) + (b - R * (y - T)) := by
          rw [mul_add, mul_one, mul_comm (b - R * (y - T)) (R - r)]
        rw [hmul]
        have hlt : (R - r) * (b - R * (y - T)) + 0
            < (R - r) * (b - R * (y - T)) + (b - R * (y - T)) :=
          add_lt_add_of_le_of_lt le_rfl hδpos
        rw [add_zero] at hlt
        exact hlt
      have hle : (y : ℝ≥0∞) ≤ hdev (tokenBucket r b) (rateLatency R T) :=
        le_trans (hdev_lower_big r b R T y _ h hyT hRyT hspos hsmall)
          (le_iSup (fun s : ℝ≥0 => ⨅ w : { τ : ℝ≥0 //
            tokenBucket r b s ≤ rateLatency R T (s + τ) }, (w.val : ℝ≥0∞))
            ((b - R * (y - T)) / (R - r + 1)))
      exact (not_le_of_gt hcl) hle

end Cslib.Algorithms.Networking.NetworkCalculus
