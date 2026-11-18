/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonnegativity of classical scalar parabolic solutions

For a classical solution of `c_t - D * c_xx + k * c = s` on the closed
cylinder `[0, T] × [0, L]`, with `D > 0`, nonnegative reaction and source
fields, and nonnegative initial and Dirichlet boundary data, the solution
is nonnegative on the whole cylinder, including the initial and boundary
faces. The statement is conditional on the displayed derivative data; it
is a comparison theorem for a given classical solution, not an existence
claim.

## Key results

- `parabolic_solution_nonneg`: the nonnegative-data comparison theorem.
- `parabolic_solution_nonneg_of_oneSided`: the nonlinear comparison theorem
  under a one-sided reaction bound at attained nonpositive values.
- `parabolic_solution_nonneg_of_lipschitzOn`, `oneSided_of_lipschitzOn`: the
  bounded-state-box Lipschitz form of the one-sided bound.
- `massAction_oneSided`, `massAction_lipschitzOn`: the mass-action fixture.
- `sqrtReaction_solution`, `sqrtReaction_negative`,
  `sqrtReaction_not_oneSided`: quasi-positivity alone does not suffice.

The proof is the compact negative-minimum argument: if a negative value
occurred, perturbing by `ε * (t + 1)` would force a strictly negative
minimum at an interior spatial point and a positive time, where the
Fermat conditions and the equation contradict the sign of the source.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.ScalarParabolicComparison

private theorem hasDerivAt_add_const {f : ℝ → ℝ} {f' x C : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => f y + C) f' x :=
  (hasDerivAt_add_const_iff C).mpr hf

private theorem hasDerivAt_affine {a b x : ℝ} :
    HasDerivAt (fun y => a * y + b) a x :=
  (hasDerivAt_add_const_iff b).mpr (hasDerivAt_const_mul a)

private theorem isMinOn_hasDerivAt_le_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhdsWithin x (Set.Iio x)) :
    f' ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hc : 0 < f' / 2 := by linarith
  have hlit : (fun x' : ℝ => f x' - f x - (x' - x) • f') =o[nhdsWithin x (Set.Iio x)]
      fun x' => x' - x :=
    hf.isLittleO.mono nhdsWithin_le_nhds
  have hbound := hlit.bound hc
  have hIio : ∀ᶠ y in nhdsWithin x (Set.Iio x), y ∈ Set.Iio x :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
  have hs : ∀ᶠ y in nhdsWithin x (Set.Iio x), y ∈ s :=
    Filter.eventually_of_mem hmem (fun y hy => hy)
  obtain ⟨y, hby, hylt, hys⟩ := (hbound.and (hIio.and hs)).exists
  have hlt : y < x := hylt
  have hfx : f x ≤ f y := hmin hys
  have hyx : y - x < 0 := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul] at hby
  have habs : |y - x| = -(y - x) := abs_of_neg hyx
  rw [habs] at hby
  have hkey : f y - f x - (y - x) * f' ≤ (f' / 2) * (-(y - x)) := (abs_le.mp hby).2
  have hring : (f' / 2) * (-(y - x)) + (y - x) * f' = (f' / 2) * (y - x) := by ring
  have hle2 : f y - f x ≤ (f' / 2) * (y - x) := by linarith
  have hneg : (f' / 2) * (y - x) < 0 := mul_neg_of_pos_of_neg (by linarith) hyx
  have hlt2 : f y - f x < 0 := lt_of_le_of_lt hle2 hneg
  have hylt2 : f y < f x := by linarith
  exact (not_lt_of_ge hfx) hylt2

private theorem isMinOn_hasDerivAt_nonneg {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhdsWithin x (Set.Ioi x)) :
    0 ≤ f' := by
  by_contra hpos
  push Not at hpos
  have hc : 0 < -f' / 2 := by linarith
  have hlit : (fun x' : ℝ => f x' - f x - (x' - x) • f') =o[nhdsWithin x (Set.Ioi x)]
      fun x' => x' - x :=
    hf.isLittleO.mono nhdsWithin_le_nhds
  have hbound := hlit.bound hc
  have hIoi : ∀ᶠ y in nhdsWithin x (Set.Ioi x), y ∈ Set.Ioi x :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
  have hs : ∀ᶠ y in nhdsWithin x (Set.Ioi x), y ∈ s :=
    Filter.eventually_of_mem hmem (fun y hy => hy)
  obtain ⟨y, hby, hylt, hys⟩ := (hbound.and (hIoi.and hs)).exists
  have hlt : x < y := hylt
  have hfx : f x ≤ f y := hmin hys
  have hyx : 0 < y - x := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul] at hby
  have habs : |y - x| = (y - x) := abs_of_pos hyx
  rw [habs] at hby
  have hkey : f y - f x - (y - x) * f' ≤ (-f' / 2) * (y - x) := (abs_le.mp hby).2
  have hring : (-f' / 2) * (y - x) + (y - x) * f' = (f' / 2) * (y - x) := by ring
  have hle2 : f y - f x ≤ (f' / 2) * (y - x) := by linarith
  have hneg : (f' / 2) * (y - x) < 0 := mul_neg_of_neg_of_pos (by linarith) hyx
  have hlt2 : f y - f x < 0 := lt_of_le_of_lt hle2 hneg
  have hylt2 : f y < f x := by linarith
  exact (not_lt_of_ge hfx) hylt2

private theorem isMinOn_hasDerivAt_eq_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 := by
  apply le_antisymm
  · exact isMinOn_hasDerivAt_le_zero hf hmin (mem_nhdsWithin_of_mem_nhds hmem)
  · exact isMinOn_hasDerivAt_nonneg hf hmin (mem_nhdsWithin_of_mem_nhds hmem)

private theorem isMaxOn_hasDerivAt_eq_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmax : IsMaxOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 := by
  have hmin : IsMinOn (fun y => -f y) s x :=
    Filter.eventually_principal.mpr (fun y hy => by
      have h : f y ≤ f x := hmax hy
      change -f x ≤ -f y
      linarith)
  have h0 : -f' = 0 :=
    isMinOn_hasDerivAt_eq_zero hf.neg hmin hmem
  linarith

private theorem second_deriv_nonneg_of_isMinOn {f g gd : ℝ → ℝ} {x0 a b : ℝ}
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (g y) y)
    (hg : ∀ y ∈ Set.Icc a b, HasDerivAt g (gd y) y)
    (hx0 : x0 ∈ Set.Ioo a b)
    (hmin : IsMinOn f (Set.Icc a b) x0) :
    0 ≤ gd x0 := by
  by_contra hneg
  push Not at hneg
  have hx0' : a < x0 ∧ x0 < b := hx0
  have hx0Icc : x0 ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx0
  have hIcc_mem : Set.Icc a b ∈ nhds x0 :=
    Filter.mem_of_superset (Ioo_mem_nhds hx0'.1 hx0'.2) Set.Ioo_subset_Icc_self
  have hgx0 : g x0 = 0 :=
    isMinOn_hasDerivAt_eq_zero (hf x0 hx0Icc) hmin hIcc_mem
  have hc : 0 < -gd x0 / 2 := by linarith
  have hbound1 : ∀ᶠ y in nhds x0,
      ‖g y - g x0 - (y - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖y - x0‖ :=
    (hg x0 hx0Icc).isLittleO.bound hc
  have hset : {y : ℝ | ‖g y - g x0 - (y - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖y - x0‖} ∈
      nhds x0 :=
    hbound1
  obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hset
  have hxu' : l < x0 ∧ x0 < u := hxu
  set y1 : ℝ := max ((l + x0) / 2) ((a + x0) / 2) with hy1
  have h1 : (l + x0) / 2 < x0 := by linarith
  have h2 : (a + x0) / 2 < x0 := by linarith
  have hy1_lt : y1 < x0 := max_lt_iff.mpr ⟨h1, h2⟩
  have hy1_ge1 : (l + x0) / 2 ≤ y1 := le_max_left _ _
  have hy1_ge2 : (a + x0) / 2 ≤ y1 := le_max_right _ _
  have hy1_gt_a : a < y1 := by
    have hmid_a : a < (a + x0) / 2 := by linarith
    exact lt_of_lt_of_le hmid_a hy1_ge2
  have hsub_Icc : Set.Icc y1 x0 ⊆ Set.Icc a b := by
    intro y hy
    have hy' : y1 ≤ y ∧ y ≤ x0 := hy
    change a ≤ y ∧ y ≤ b
    exact ⟨le_trans hy1_gt_a.le hy'.1, le_trans hy'.2 hx0'.2.le⟩
  have hf_sub : ∀ y ∈ Set.Icc y1 x0, HasDerivAt f (g y) y := by
    intro y hy
    exact hf y (hsub_Icc hy)
  have hf_cont : ContinuousOn f (Set.Icc y1 x0) :=
    fun y hy => (hf_sub y hy).continuousAt.continuousWithinAt
  obtain ⟨c, hcIoo, hslope⟩ := exists_hasDerivAt_eq_slope f g hy1_lt hf_cont
    (fun y hy => hf_sub y (Set.Ioo_subset_Icc_self hy))
  have hslope' : f x0 - f y1 = g c * (x0 - y1) := by
    have hne : x0 - y1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hy1_lt)
    rw [hslope, div_mul_cancel₀ _ hne]
  have hc' : y1 < c ∧ c < x0 := hcIoo
  have hc_gt_l : l < c := by
    have h1' : l < (l + x0) / 2 := by linarith
    linarith
  have hc_lt_u : c < u := lt_trans hc'.2 hxu'.2
  have hc_mem : c ∈ Set.Ioo l u := ⟨hc_gt_l, hc_lt_u⟩
  have hbound_c : ‖g c - g x0 - (c - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖c - x0‖ :=
    hsub hc_mem
  have hcx0 : c - x0 < 0 := by linarith
  have h : |g c - g x0 - (c - x0) * gd x0| ≤ -gd x0 / 2 * |c - x0| := by
    have h := hbound_c
    simp only [Real.norm_eq_abs, smul_eq_mul] at h
    exact h
  have habs : |c - x0| = -(c - x0) := abs_of_neg hcx0
  rw [habs, hgx0] at h
  have hlow : -(-gd x0 / 2 * -(c - x0)) ≤ g c - 0 - (c - x0) * gd x0 :=
    (abs_le.mp h).1
  have hring : -(-gd x0 / 2 * -(c - x0)) + (c - x0) * gd x0 =
      (gd x0 / 2) * (c - x0) := by ring
  have hpos : 0 < (gd x0 / 2) * (c - x0) :=
    mul_pos_of_neg_of_neg (by linarith) hcx0
  have hgc_eq : g c = (g c - 0 - (c - x0) * gd x0) + (c - x0) * gd x0 := by ring
  have hgc_pos : 0 < g c := by linarith
  have hy1c : 0 < x0 - y1 := by linarith
  have hprod : 0 < g c * (x0 - y1) := mul_pos hgc_pos hy1c
  have hfx0 : f x0 ≤ f y1 := by
    have hy1_mem : y1 ∈ Set.Icc a b := by
      change a ≤ y1 ∧ y1 ≤ b
      exact ⟨hy1_gt_a.le, le_trans hy1_lt.le hx0'.2.le⟩
    exact hmin hy1_mem
  linarith

private theorem time_deriv_nonpos {T : ℝ} {f : ℝ → ℝ} {f' tstar : ℝ}
    (hmem : tstar ∈ Set.Ioc 0 T)
    (hmin : ∀ t ∈ Set.Icc 0 T, f tstar ≤ f t)
    (hderiv : HasDerivWithinAt f f' (Set.Icc 0 T) tstar) :
    f' ≤ 0 := by
  by_contra hpos
  have hfpos : 0 < f' := not_le.mp hpos
  have htend : Filter.Tendsto (slope f tstar)
      (nhdsWithin tstar (Set.Icc 0 T \ {tstar})) (nhds f') :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hderiv)
  have hIoi : Set.Ioi 0 ∈ nhds f' := Ioi_mem_nhds hfpos
  have hevIoi : ∀ᶠ y in nhds f', y ∈ Set.Ioi 0 :=
    Filter.eventually_of_mem hIoi (fun y hy => hy)
  have hev : ∀ᶠ x in nhdsWithin tstar (Set.Icc 0 T \ {tstar}), slope f tstar x ∈ Set.Ioi 0 :=
    htend.eventually hevIoi
  have hev' : ∀ᶠ x in nhds tstar, x ∈ (Set.Icc 0 T \ {tstar}) → slope f tstar x ∈ Set.Ioi 0 :=
    (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hev'
  obtain ⟨htpos, htT⟩ := hmem
  set δ : ℝ := min (ε / 2) (tstar / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδle1 : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ tstar / 2 := min_le_right _ _
  have hδε : δ < ε := by linarith
  set t : ℝ := tstar - δ with htdef
  have httstar : t < tstar := by linarith
  have htne : t ≠ tstar := ne_of_lt httstar
  have ht0 : 0 ≤ t := by linarith
  have htT' : t ≤ T := by linarith
  have htIcc : t ∈ Set.Icc 0 T := ⟨ht0, htT'⟩
  have htmem : t ∈ (Set.Icc 0 T \ {tstar}) := ⟨htIcc, by simpa using htne⟩
  have hdist : dist t tstar < ε := by
    rw [Real.dist_eq]
    have : |t - tstar| = δ := by
      rw [htdef]
      have : (tstar - δ - tstar) = -δ := by ring
      rw [this, abs_neg, abs_of_nonneg (le_of_lt hδpos)]
    rw [this]
    exact hδε
  have hballmem : t ∈ Metric.ball tstar ε := hdist
  have hmem2 := hball hballmem
  have hSlopeMem : slope f tstar t ∈ Set.Ioi 0 := hmem2 htmem
  have hSlopePos : 0 < slope f tstar t := hSlopeMem
  have hSlopeEq : slope f tstar t = (f t - f tstar) / (t - tstar) := by
    unfold slope
    simp [div_eq_mul_inv, mul_comm]
  rw [hSlopeEq] at hSlopePos
  have hDenomNeg : t - tstar < 0 := by linarith
  have hNumNeg : f t - f tstar < 0 := by
    have h := (div_pos_iff.mp hSlopePos)
    rcases h with ⟨_, hpos2⟩ | ⟨hneg, _⟩
    · linarith
    · exact hneg
  have hle := hmin t htIcc
  linarith

private theorem second_deriv_nonneg {L : ℝ} {g g' : ℝ → ℝ} {g'' xstar : ℝ}
    (hmem : xstar ∈ Set.Ioo 0 L)
    (hmin : ∀ x ∈ Set.Icc 0 L, g xstar ≤ g x)
    (hderiv1 : ∀ x ∈ Set.Ioo 0 L, HasDerivAt g (g' x) x)
    (hderiv2 : HasDerivAt g' g'' xstar)
    (hcont : ContinuousOn g (Set.Icc 0 L)) :
    0 ≤ g'' := by
  obtain ⟨hx0, hxL⟩ := hmem
  have hmem' : xstar ∈ Set.Ioo 0 L := ⟨hx0, hxL⟩
  have hIccNhds : Set.Icc 0 L ∈ nhds xstar := Icc_mem_nhds hx0 hxL
  have hIsMinOn : IsMinOn g (Set.Icc 0 L) xstar := fun x hx => hmin x hx
  have hLocalMin : IsLocalMin g xstar := hIsMinOn.isLocalMin hIccNhds
  have hderiv_at : HasDerivAt g (g' xstar) xstar := hderiv1 xstar hmem'
  have hg'zero : g' xstar = 0 := hLocalMin.hasDerivAt_eq_zero hderiv_at
  by_contra hneg
  have hgneg : g'' < 0 := not_le.mp hneg
  have htend : Filter.Tendsto (slope g' xstar) (nhdsWithin xstar {xstar}ᶜ) (nhds g'') :=
    HasDerivAt.tendsto_slope hderiv2
  have hIio : Set.Iio 0 ∈ nhds g'' := Iio_mem_nhds hgneg
  have hevIio : ∀ᶠ y in nhds g'', y ∈ Set.Iio 0 :=
    Filter.eventually_of_mem hIio (fun y hy => hy)
  have hev : ∀ᶠ x in nhdsWithin xstar {xstar}ᶜ, slope g' xstar x ∈ Set.Iio 0 :=
    htend.eventually hevIio
  have hev' := (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hev'
  have hIooNhds : Set.Ioo 0 L ∈ nhds xstar := Ioo_mem_nhds hx0 hxL
  obtain ⟨ε2, hε2pos, hball2⟩ := Metric.mem_nhds_iff.mp hIooNhds
  set h : ℝ := min (ε / 2) (ε2 / 2) with hhdef
  have hhpos : 0 < h := lt_min (by linarith) (by linarith)
  have hhε : h < ε := by
    have : h ≤ ε / 2 := min_le_left _ _
    linarith
  have hhε2 : h < ε2 := by
    have : h ≤ ε2 / 2 := min_le_right _ _
    linarith
  have hxstar_h_mem_Ioo : xstar + h ∈ Set.Ioo 0 L := by
    have hdist : dist (xstar + h) xstar < ε2 := by
      rw [Real.dist_eq]
      have : |(xstar + h) - xstar| = h := by
        have : (xstar + h - xstar) = h := by ring
        rw [this, abs_of_nonneg (le_of_lt hhpos)]
      rw [this]
      exact hhε2
    have hballmem : xstar + h ∈ Metric.ball xstar ε2 := hdist
    exact hball2 hballmem
  obtain ⟨hxh0, hxhL⟩ := hxstar_h_mem_Ioo
  have hxlt : xstar < xstar + h := by linarith
  have hsubIcc : Set.Icc xstar (xstar + h) ⊆ Set.Icc 0 L := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · linarith
    · linarith
  have hcontSub : ContinuousOn g (Set.Icc xstar (xstar + h)) := hcont.mono hsubIcc
  have hsubIoo : Set.Ioo xstar (xstar + h) ⊆ Set.Ioo 0 L := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · linarith
    · linarith
  have hderivSub : ∀ x ∈ Set.Ioo xstar (xstar + h), HasDerivAt g (g' x) x := by
    intro x hx
    exact hderiv1 x (hsubIoo hx)
  obtain ⟨c, hcIoo, hcEq⟩ := exists_hasDerivAt_eq_slope g g' hxlt hcontSub hderivSub
  obtain ⟨hc1, hc2⟩ := hcIoo
  have hcne : c ≠ xstar := ne_of_gt hc1
  have hcball : c ∈ Metric.ball xstar ε := by
    have hdist : dist c xstar < ε := by
      rw [Real.dist_eq]
      have habs : |c - xstar| = c - xstar := abs_of_nonneg (by linarith)
      rw [habs]
      have : c - xstar < h := by linarith
      linarith
    exact hdist
  have hmemBall := hball hcball
  have hcCompl : c ∈ ({xstar}ᶜ : Set ℝ) := by simpa using hcne
  have hSlopeMem : slope g' xstar c ∈ Set.Iio 0 := hmemBall hcCompl
  have hSlopeNeg : slope g' xstar c < 0 := hSlopeMem
  have hSlopeEq : slope g' xstar c = (g' c - g' xstar) / (c - xstar) := by
    unfold slope
    simp [div_eq_mul_inv, mul_comm]
  rw [hg'zero] at hSlopeEq
  have hDenomPos : 0 < c - xstar := by linarith
  have hg'c_neg : g' c < 0 := by
    have hEq : (g' c - 0) / (c - xstar) < 0 := by
      rw [← hSlopeEq]
      exact hSlopeNeg
    have hNum : g' c - 0 < 0 := by
      have h := (div_neg_iff.mp hEq)
      rcases h with ⟨_, hneg⟩ | ⟨hneg, _⟩
      · linarith
      · exact hneg
    linarith
  have hMVTpos : 0 < (xstar + h) - xstar := by linarith
  have hEq2 : g' c = (g (xstar + h) - g xstar) / ((xstar + h) - xstar) := hcEq
  have hNum2 : g (xstar + h) - g xstar < 0 := by
    have hDiv : (g (xstar + h) - g xstar) / ((xstar + h) - xstar) < 0 := by
      rw [← hEq2]
      exact hg'c_neg
    have h := (div_neg_iff.mp hDiv)
    rcases h with ⟨_, hneg⟩ | ⟨hneg, _⟩
    · linarith
    · exact hneg
  have hxstar_h_Icc : xstar + h ∈ Set.Icc 0 L := ⟨le_of_lt hxh0, le_of_lt hxhL⟩
  have hle := hmin (xstar + h) hxstar_h_Icc
  linarith

/-- Nonlinear comparison with one-sided control. Let `c` be a classical
solution of `c_t - D * c_xx = r(c, x, t)` on the parabolic interior
`(0, T] × (0, L)`, continuous on the closed cylinder `[0, T] × [0, L]`,
with `D ≥ 0`. Suppose the reaction is bounded below by `K * c` wherever
the solution is nonpositive, with one constant `K` uniform over the
cylinder. Then nonnegative initial data on `[0, L]` and nonnegative
Dirichlet data at `x = 0` and `x = L` on `[0, T]` give `c ≥ 0` on the
whole closed cylinder. The bound is evaluated only at values the solution
attains; quasi-positivity `r(0) ≥ 0` alone is not assumed to suffice.
Intended proof: negative-minimum argument for
`exp (-K * t) * c t x + ε * (1 + t)`, then `ε → 0`. -/
theorem parabolic_solution_nonneg_of_oneSided {D L T K : ℝ} (hD : 0 ≤ D)
    {c ct cx cxx : ℝ → ℝ → ℝ} {r : ℝ → ℝ → ℝ → ℝ}
    (hct : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivWithinAt (fun τ : ℝ => c τ x) (ct t x) (Set.Icc 0 T) t)
    (hcx : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivAt (fun y : ℝ => c t y) (cx t x) x)
    (hcxx : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivAt (fun y : ℝ => cx t y) (cxx t x) x)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 L))
    (hPDE : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      ct t x - D * cxx t x = r (c t x) x t)
    (hbound : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      c t x ≤ 0 → K * c t x ≤ r (c t x) x t)
    (hinit : ∀ x : ℝ, x ∈ Set.Icc 0 L → 0 ≤ c 0 x)
    (hb0 : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t 0)
    (hbL : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t L)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) :
    0 ≤ c t x := by
  by_cases hT : 0 < T
  · by_cases hL : 0 < L
    · have ht0main : 0 ≤ t := ht.1
      have key : ∀ ε : ℝ, 0 < ε → 0 ≤ Real.exp (-K * t) * c t x + ε * (1 + t) := by
        intro ε hε
        have hFst : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
        have hLinC : Continuous (fun p : ℝ × ℝ => -K * p.1) := continuous_const.mul hFst
        have hExpC : Continuous (fun p : ℝ × ℝ => Real.exp (-K * p.1)) :=
          Real.continuous_exp.comp hLinC
        have hExpOn : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-K * p.1))
            (Set.Icc 0 T ×ˢ Set.Icc 0 L) := hExpC.continuousOn
        have hProdC : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-K * p.1) * c p.1 p.2)
            (Set.Icc 0 T ×ˢ Set.Icc 0 L) := hExpOn.mul hcont
        have hOneAdd : Continuous (fun p : ℝ × ℝ => (1 : ℝ) + p.1) :=
          continuous_const.add hFst
        have hEpsC : Continuous (fun p : ℝ × ℝ => ε * (1 + p.1)) :=
          continuous_const.mul hOneAdd
        have hEpsOn : ContinuousOn (fun p : ℝ × ℝ => ε * (1 + p.1))
            (Set.Icc 0 T ×ˢ Set.Icc 0 L) := hEpsC.continuousOn
        have hContV : ContinuousOn
            (fun p : ℝ × ℝ => Real.exp (-K * p.1) * c p.1 p.2 + ε * (1 + p.1))
            (Set.Icc 0 T ×ˢ Set.Icc 0 L) := hProdC.add hEpsOn
        have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, le_of_lt hT⟩
        have h0L : (0 : ℝ) ∈ Set.Icc 0 L := ⟨le_rfl, le_of_lt hL⟩
        have hNonempty : (Set.Icc 0 T ×ˢ Set.Icc 0 L).Nonempty := ⟨(0, 0), h0T, h0L⟩
        have hCompact : IsCompact (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
          IsCompact.prod isCompact_Icc isCompact_Icc
        obtain ⟨⟨tstar, xstar⟩, hmem, hmin⟩ := hCompact.exists_isMinOn hNonempty hContV
        have htstar : tstar ∈ Set.Icc 0 T := hmem.1
        have hxstar : xstar ∈ Set.Icc 0 L := hmem.2
        have htxmem : (t, x) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := ⟨ht, hx⟩
        have hle : Real.exp (-K * tstar) * c tstar xstar + ε * (1 + tstar)
            ≤ Real.exp (-K * t) * c t x + ε * (1 + t) := hmin htxmem
        have hMinNonneg : 0 ≤ Real.exp (-K * tstar) * c tstar xstar + ε * (1 + tstar) := by
          by_contra hneg
          have hlt : Real.exp (-K * tstar) * c tstar xstar + ε * (1 + tstar) < 0 :=
            not_le.mp hneg
          have htstar_ne0 : tstar ≠ 0 := by
            intro h0
            rw [h0] at hlt
            have hExp0 : Real.exp (-K * (0 : ℝ)) = 1 := by
              have h00 : (-K * (0 : ℝ)) = 0 := by ring
              rw [h00, Real.exp_zero]
            rw [hExp0, add_zero, mul_one, one_mul] at hlt
            have hc0 : 0 ≤ c 0 xstar := hinit xstar hxstar
            linarith
          have hxstar_ne0 : xstar ≠ 0 := by
            intro h0
            rw [h0] at hlt
            have hExpPos0 : 0 < Real.exp (-K * tstar) := Real.exp_pos _
            have hc0 : 0 ≤ c tstar 0 := hb0 tstar htstar
            have hProdNonneg : 0 ≤ Real.exp (-K * tstar) * c tstar 0 :=
              mul_nonneg (le_of_lt hExpPos0) hc0
            have htstar0a : 0 ≤ tstar := htstar.1
            have h1ta : 0 < 1 + tstar := by linarith
            have hEpsPosa : 0 < ε * (1 + tstar) := mul_pos hε h1ta
            linarith
          have hxstar_neL : xstar ≠ L := by
            intro h0
            rw [h0] at hlt
            have hExpPos0 : 0 < Real.exp (-K * tstar) := Real.exp_pos _
            have hcL : 0 ≤ c tstar L := hbL tstar htstar
            have hProdNonneg : 0 ≤ Real.exp (-K * tstar) * c tstar L :=
              mul_nonneg (le_of_lt hExpPos0) hcL
            have htstar0b : 0 ≤ tstar := htstar.1
            have h1tb : 0 < 1 + tstar := by linarith
            have hEpsPosb : 0 < ε * (1 + tstar) := mul_pos hε h1tb
            linarith
          have htstar0c : 0 ≤ tstar := htstar.1
          have htstarTc : tstar ≤ T := htstar.2
          have h0ne : (0 : ℝ) ≠ tstar := Ne.symm htstar_ne0
          have htstarPos : 0 < tstar := lt_of_le_of_ne htstar0c h0ne
          have htstarIoc : tstar ∈ Set.Ioc 0 T := ⟨htstarPos, htstarTc⟩
          have hxstar0c : 0 ≤ xstar := hxstar.1
          have hxstarLc : xstar ≤ L := hxstar.2
          have hxstarPos : 0 < xstar := lt_of_le_of_ne hxstar0c (Ne.symm hxstar_ne0)
          have hxstarLt : xstar < L := lt_of_le_of_ne hxstarLc hxstar_neL
          have hxstarIoo : xstar ∈ Set.Ioo 0 L := ⟨hxstarPos, hxstarLt⟩
          have hExpPos : 0 < Real.exp (-K * tstar) := Real.exp_pos _
          have h1tstar : 0 < 1 + tstar := by linarith
          have hEpsPos2 : 0 < ε * (1 + tstar) := mul_pos hε h1tstar
          have hEcneg : Real.exp (-K * tstar) * c tstar xstar < 0 := by linarith
          have hcneg : c tstar xstar < 0 := by
            by_contra hcon
            have hnn : 0 ≤ c tstar xstar := le_of_not_gt hcon
            have hnonneg : 0 ≤ Real.exp (-K * tstar) * c tstar xstar :=
              mul_nonneg (le_of_lt hExpPos) hnn
            linarith
          have hPDE_star : ct tstar xstar - D * cxx tstar xstar
              = r (c tstar xstar) xstar tstar :=
            hPDE tstar xstar htstarIoc hxstarIoo
          have hbound_star : K * c tstar xstar ≤ r (c tstar xstar) xstar tstar :=
            hbound tstar xstar htstarIoc hxstarIoo (le_of_lt hcneg)
          have hct_star : HasDerivWithinAt (fun τ : ℝ => c τ xstar) (ct tstar xstar)
              (Set.Icc 0 T) tstar :=
            hct tstar xstar htstarIoc hxstarIoo
          have hIdT : HasDerivAt (fun τ : ℝ => τ) 1 tstar := hasDerivAt_id' tstar
          have hLinT : HasDerivAt (fun τ : ℝ => -K * τ) (-K) tstar := by
            have h := HasDerivAt.const_mul (-K) hIdT
            simpa using h
          have hExpT : HasDerivAt (fun τ : ℝ => Real.exp (-K * τ))
              (Real.exp (-K * tstar) * (-K)) tstar :=
            HasDerivAt.exp hLinT
          have hExpTW : HasDerivWithinAt (fun τ : ℝ => Real.exp (-K * τ))
              (Real.exp (-K * tstar) * (-K)) (Set.Icc 0 T) tstar :=
            hExpT.hasDerivWithinAt
          have hProdT : HasDerivWithinAt (fun τ : ℝ => Real.exp (-K * τ) * c τ xstar)
              (Real.exp (-K * tstar) * (-K) * c tstar xstar
                + Real.exp (-K * tstar) * ct tstar xstar)
              (Set.Icc 0 T) tstar := hExpTW.mul hct_star
          have hAddT : HasDerivAt (fun τ : ℝ => 1 + τ) 1 tstar :=
            HasDerivAt.const_add 1 hIdT
          have hEpsT : HasDerivAt (fun τ : ℝ => ε * (1 + τ)) ε tstar := by
            have h := HasDerivAt.const_mul ε hAddT
            simpa using h
          have hEpsTW : HasDerivWithinAt (fun τ : ℝ => ε * (1 + τ)) ε (Set.Icc 0 T) tstar :=
            hEpsT.hasDerivWithinAt
          have hDerivF : HasDerivWithinAt
              (fun τ : ℝ => Real.exp (-K * τ) * c τ xstar + ε * (1 + τ))
              (Real.exp (-K * tstar) * (-K) * c tstar xstar
                + Real.exp (-K * tstar) * ct tstar xstar + ε)
              (Set.Icc 0 T) tstar := hProdT.add hEpsTW
          have hminT : ∀ tt ∈ Set.Icc 0 T,
              (fun τ : ℝ => Real.exp (-K * τ) * c τ xstar + ε * (1 + τ)) tstar
                ≤ (fun τ : ℝ => Real.exp (-K * τ) * c τ xstar + ε * (1 + τ)) tt := by
            intro tt htt
            have hmemTT : (tt, xstar) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := ⟨htt, hxstar⟩
            exact hmin hmemTT
          have hvt_le : Real.exp (-K * tstar) * (-K) * c tstar xstar
              + Real.exp (-K * tstar) * ct tstar xstar + ε ≤ 0 :=
            time_deriv_nonpos htstarIoc hminT hDerivF
          have hderiv1 : ∀ y ∈ Set.Ioo 0 L,
              HasDerivAt
                (fun z : ℝ => Real.exp (-K * tstar) * c tstar z + ε * (1 + tstar))
                (Real.exp (-K * tstar) * cx tstar y) y := by
            intro y hy
            have h1 : HasDerivAt (fun z : ℝ => c tstar z) (cx tstar y) y :=
              hcx tstar y htstarIoc hy
            have h2 : HasDerivAt (fun z : ℝ => Real.exp (-K * tstar) * c tstar z)
                (Real.exp (-K * tstar) * cx tstar y) y :=
              HasDerivAt.const_mul _ h1
            exact HasDerivAt.add_const _ h2
          have hderiv2 : HasDerivAt (fun y : ℝ => Real.exp (-K * tstar) * cx tstar y)
              (Real.exp (-K * tstar) * cxx tstar xstar) xstar := by
            have h1 : HasDerivAt (fun y : ℝ => cx tstar y) (cxx tstar xstar) xstar :=
              hcxx tstar xstar htstarIoc hxstarIoo
            exact HasDerivAt.const_mul _ h1
          have hminS : ∀ xx ∈ Set.Icc 0 L,
              (fun y : ℝ => Real.exp (-K * tstar) * c tstar y + ε * (1 + tstar)) xstar
                ≤ (fun y : ℝ => Real.exp (-K * tstar) * c tstar y + ε * (1 + tstar)) xx := by
            intro xx hxx
            have hmemXX : (tstar, xx) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := ⟨htstar, hxx⟩
            exact hmin hmemXX
          have hMapCont : ContinuousOn (fun y : ℝ => (tstar, y)) (Set.Icc 0 L) :=
            (continuous_const.prodMk continuous_id).continuousOn
          have hMapsTo : Set.MapsTo (fun y : ℝ => (tstar, y)) (Set.Icc 0 L)
              (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
            fun y hy => ⟨htstar, hy⟩
          have hContC : ContinuousOn (fun y : ℝ => c tstar y) (Set.Icc 0 L) :=
            hcont.comp hMapCont hMapsTo
          have hcontS : ContinuousOn
              (fun y : ℝ => Real.exp (-K * tstar) * c tstar y + ε * (1 + tstar))
              (Set.Icc 0 L) :=
            (hContC.const_mul _).add_const _
          have hvxx_nonneg : 0 ≤ Real.exp (-K * tstar) * cxx tstar xstar :=
            second_deriv_nonneg hxstarIoo hminS hderiv1 hderiv2 hcontS
          have hDvxx : 0 ≤ D * (Real.exp (-K * tstar) * cxx tstar xstar) :=
            mul_nonneg hD hvxx_nonneg
          have hLe : (Real.exp (-K * tstar) * (-K) * c tstar xstar
              + Real.exp (-K * tstar) * ct tstar xstar + ε)
              - D * (Real.exp (-K * tstar) * cxx tstar xstar) ≤ 0 := by
            linarith
          have hCalc : (Real.exp (-K * tstar) * (-K) * c tstar xstar
              + Real.exp (-K * tstar) * ct tstar xstar + ε)
              - D * (Real.exp (-K * tstar) * cxx tstar xstar)
              = Real.exp (-K * tstar) * (r (c tstar xstar) xstar tstar - K * c tstar xstar)
                + ε := by
            have hEqE : Real.exp (-K * tstar) * (-K) * c tstar xstar
                = -(Real.exp (-K * tstar) * (K * c tstar xstar)) := by ring
            have hEqR : Real.exp (-K * tstar) * (r (c tstar xstar) xstar tstar - K * c tstar xstar)
                = Real.exp (-K * tstar) * r (c tstar xstar) xstar tstar
                  - Real.exp (-K * tstar) * (K * c tstar xstar) := by ring
            have hEqM : Real.exp (-K * tstar) * ct tstar xstar
                - D * (Real.exp (-K * tstar) * cxx tstar xstar)
                = Real.exp (-K * tstar) * (ct tstar xstar - D * cxx tstar xstar) := by ring
            rw [hPDE_star] at hEqM
            linarith
          rw [hCalc] at hLe
          have hRnonneg : 0 ≤ r (c tstar xstar) xstar tstar - K * c tstar xstar := by
            linarith
          have hProdNonneg2 : 0 ≤ Real.exp (-K * tstar)
              * (r (c tstar xstar) xstar tstar - K * c tstar xstar) :=
            mul_nonneg (le_of_lt hExpPos) hRnonneg
          linarith
        exact le_trans hMinNonneg hle
      by_contra hneg2
      have hcneg2 : c t x < 0 := not_le.mp hneg2
      have hExpPos2 : 0 < Real.exp (-K * t) := Real.exp_pos _
      have hEcneg2 : Real.exp (-K * t) * c t x < 0 := mul_neg_of_pos_of_neg hExpPos2 hcneg2
      have h1t2 : 0 < 1 + t := by linarith
      set δ : ℝ := -(Real.exp (-K * t) * c t x) with hδdef
      have hδpos : 0 < δ := by linarith
      have hDenomPos : 0 < 2 * (1 + t) := mul_pos (by linarith) h1t2
      set ε0 : ℝ := δ / (2 * (1 + t)) with hε0def
      have hε0pos : 0 < ε0 := div_pos hδpos hDenomPos
      have hkey := key ε0 hε0pos
      have hEq0 : ε0 * (1 + t) = δ / 2 := by
        rw [hε0def]
        have hne : (1 : ℝ) + t ≠ 0 := ne_of_gt h1t2
        field_simp
      have hContra : Real.exp (-K * t) * c t x + ε0 * (1 + t) < 0 := by
        rw [hEq0]
        have hδeq : Real.exp (-K * t) * c t x = -δ := by
          rw [hδdef]
          ring
        rw [hδeq]
        linarith
      linarith
    · have hLle : L ≤ 0 := not_lt.mp hL
      obtain ⟨hx0, hxL⟩ := hx
      have h0L : (0 : ℝ) ≤ L := le_trans hx0 hxL
      have hLeq : L = 0 := le_antisymm hLle h0L
      rw [hLeq] at hxL
      have hx0' : x = 0 := le_antisymm hxL hx0
      rw [hx0']
      exact hb0 t ht
  · have hTle : T ≤ 0 := not_lt.mp hT
    obtain ⟨ht0, htT⟩ := ht
    have h0T : (0 : ℝ) ≤ T := le_trans ht0 htT
    have hTeq : T = 0 := le_antisymm hTle h0T
    rw [hTeq] at htT
    have ht0' : t = 0 := le_antisymm htT ht0
    rw [ht0']
    exact hinit x hx

/-- Discharging the one-sided bound on a bounded state box: if the reaction
is `K`-Lipschitz in the state on `[-M, 0]` and quasi-positive at `0`, then
`r(u) ≥ K * u` for every `u ∈ [-M, 0]`. -/
theorem oneSided_of_lipschitzOn {M : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hLip : LipschitzOnWith K f (Set.Icc (-M) 0)) (hf0 : 0 ≤ f 0)
    {u : ℝ} (hu : u ∈ Set.Icc (-M) 0) :
    (K : ℝ) * u ≤ f u := by
  obtain ⟨hlo, hhi⟩ := hu
  have hM0 : -M ≤ 0 := le_trans hlo hhi
  have h0mem : (0 : ℝ) ∈ Set.Icc (-M) 0 := ⟨hM0, le_rfl⟩
  have humem : u ∈ Set.Icc (-M) 0 := ⟨hlo, hhi⟩
  have hLip' := hLip humem h0mem
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hEdistU : edist u 0 = ENNReal.ofReal |u - 0| := by
    rw [edist_dist, Real.dist_eq]
  have hRHS : (↑K : ENNReal) * ENNReal.ofReal |u - 0|
      = ENNReal.ofReal ((K : ℝ) * |u - 0|) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hKnn]
  rw [hEdistU, hRHS] at hLip'
  have hNonneg : (0 : ℝ) ≤ (K : ℝ) * |u - 0| := by positivity
  have hDist : dist (f u) (f 0) ≤ (K : ℝ) * |u - 0| :=
    (edist_le_ofReal hNonneg).mp hLip'
  rw [Real.dist_eq] at hDist
  have hu0 : |u - 0| = -u := by
    rw [sub_zero]
    exact abs_of_nonpos hhi
  rw [hu0] at hDist
  have hAbs : -( (K : ℝ) * (-u)) ≤ f u - f 0 := by
    have h := abs_le.mp hDist
    exact h.1
  have hEq : -( (K : ℝ) * (-u)) = (K : ℝ) * u := by ring
  rw [hEq] at hAbs
  linarith

/-- Bounded-state-box corollary: on the parabolic interior the solution stays
in `[-M, ∞)`, and there the reaction is uniformly `K`-Lipschitz in the state
on `[-M, 0]` with `r(0, x, t) ≥ 0`. Then nonnegative initial and Dirichlet
data are preserved. -/
theorem parabolic_solution_nonneg_of_lipschitzOn {D L T M : ℝ} {K : NNReal}
    (hD : 0 ≤ D)
    {c ct cx cxx : ℝ → ℝ → ℝ} {r : ℝ → ℝ → ℝ → ℝ}
    (hct : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivWithinAt (fun τ : ℝ => c τ x) (ct t x) (Set.Icc 0 T) t)
    (hcx : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivAt (fun y : ℝ => c t y) (cx t x) x)
    (hcxx : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      HasDerivAt (fun y : ℝ => cx t y) (cxx t x) x)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 L))
    (hPDE : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      ct t x - D * cxx t x = r (c t x) x t)
    (hbox : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L → -M ≤ c t x)
    (hLip : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      LipschitzOnWith K (fun u : ℝ => r u x t) (Set.Icc (-M) 0))
    (hr0 : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L → 0 ≤ r 0 x t)
    (hinit : ∀ x : ℝ, x ∈ Set.Icc 0 L → 0 ≤ c 0 x)
    (hb0 : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t 0)
    (hbL : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t L)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) :
    0 ≤ c t x := by
  have hbound : ∀ t x : ℝ, t ∈ Set.Ioc 0 T → x ∈ Set.Ioo 0 L →
      c t x ≤ 0 → (K : ℝ) * c t x ≤ r (c t x) x t := by
    intro t x htIoc hxIoo hc0
    have hbox' : -M ≤ c t x := hbox t x htIoc hxIoo
    have hu : c t x ∈ Set.Icc (-M) 0 := ⟨hbox', hc0⟩
    have hLip' : LipschitzOnWith K (fun u : ℝ => r u x t) (Set.Icc (-M) 0) :=
      hLip t x htIoc hxIoo
    have hr0' : 0 ≤ (fun u : ℝ => r u x t) 0 := hr0 t x htIoc hxIoo
    have h := oneSided_of_lipschitzOn hLip' hr0' hu
    simpa using h
  exact parabolic_solution_nonneg_of_oneSided hD hct hcx hcxx hcont hPDE hbound hinit hb0 hbL ht hx

/-! ### Fixtures -/

/-- Nonzero fixture: the mass-action reaction `r(u) = a - b * u ^ 2`
(constant production `a ≥ 0`, dimerization rate `b ≥ 0`) satisfies the
one-sided bound with `K = b * M` on the state range `[-M, 0]`. -/
theorem massAction_oneSided {a b M u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u ∈ Set.Icc (-M) 0) :
    (b * M) * u ≤ a - b * u ^ 2 := by
  obtain ⟨hlo, hhi⟩ := hu
  have hM : 0 ≤ M := by linarith
  have h1 : 0 ≤ -u := by linarith
  have h2 : 0 ≤ M + u := by linarith
  have h3 : 0 ≤ b * (-u) * (M + u) := by positivity
  nlinarith [h3]

/-- The same mass-action reaction is `(2 * b * M)`-Lipschitz on `[-M, 0]`,
so the bounded-box corollary also applies to it. -/
theorem massAction_lipschitzOn {a b M : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) :
    LipschitzOnWith (Real.toNNReal (2 * b * M)) (fun u : ℝ => a - b * u ^ 2)
      (Set.Icc (-M) 0) := by
  have hNN : (0 : ℝ) ≤ 2 * b * M := by positivity
  have hKcoe : ((Real.toNNReal (2 * b * M)) : ℝ) = 2 * b * M :=
    Real.coe_toNNReal _ hNN
  intro x hx y hy
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  have hSumHi : x + y ≤ 0 := by linarith
  have hAbsXY : |x + y| ≤ 2 * M := by
    rw [abs_of_nonpos hSumHi]
    linarith
  have hEq : (a - b * x ^ 2) - (a - b * y ^ 2) = b * (y - x) * (y + x) := by ring
  have hAbsEq : |(a - b * x ^ 2) - (a - b * y ^ 2)| = b * |y - x| * |y + x| := by
    rw [hEq, abs_mul, abs_mul, abs_of_nonneg hb]
  have hComm1 : |y - x| = |x - y| := abs_sub_comm y x
  have hComm2 : |y + x| = |x + y| := by rw [add_comm y x]
  rw [hComm1, hComm2] at hAbsEq
  have hNonneg : (0 : ℝ) ≤ b * |x - y| := by positivity
  have hLe : b * |x - y| * |x + y| ≤ b * |x - y| * (2 * M) :=
    mul_le_mul_of_nonneg_left hAbsXY hNonneg
  have hFinal : |(a - b * x ^ 2) - (a - b * y ^ 2)| ≤ (2 * b * M) * |x - y| := by
    rw [hAbsEq]
    calc b * |x - y| * |x + y| ≤ b * |x - y| * (2 * M) := hLe
      _ = (2 * b * M) * |x - y| := by ring
  have hLHS : edist (a - b * x ^ 2) (a - b * y ^ 2)
      = ENNReal.ofReal |(a - b * x ^ 2) - (a - b * y ^ 2)| := by
    rw [edist_dist, Real.dist_eq]
  have hRHS : edist x y = ENNReal.ofReal |x - y| := by
    rw [edist_dist, Real.dist_eq]
  rw [hLHS, hRHS]
  have hK : ((Real.toNNReal (2 * b * M)) : ENNReal)
      = ENNReal.ofReal (2 * b * M) := by
    rw [← ENNReal.ofReal_coe_nnreal, hKcoe]
  rw [hK, ← ENNReal.ofReal_mul hNN]
  exact ENNReal.ofReal_le_ofReal hFinal

/-- Invalid example, part 1: `c(t) = -t ^ 2 / 4` solves the spatially
constant (Neumann/ODE) problem `c_t = -√|c|` for `t ≥ 0`, with `c(0) = 0`
and quasi-positive reaction `r(0) = 0`, yet `c(t) < 0` for `t > 0`. -/
theorem sqrtReaction_solution {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun τ : ℝ => -τ ^ 2 / 4) (-Real.sqrt |(-t ^ 2 / 4)|) t := by
  have ht2 : (0 : ℝ) ≤ t ^ 2 := by positivity
  have hNonpos : -t ^ 2 / 4 ≤ 0 := by
    have h : (0 : ℝ) ≤ t ^ 2 / 4 := by positivity
    linarith
  have hAbs : |(-t ^ 2 / 4 : ℝ)| = (t / 2) ^ 2 := by
    rw [abs_of_nonpos hNonpos]
    ring
  have hSqrt : Real.sqrt |(-t ^ 2 / 4 : ℝ)| = t / 2 := by
    rw [hAbs, Real.sqrt_sq]
    linarith
  have hDerivEq : (-Real.sqrt |(-t ^ 2 / 4 : ℝ)|) = -(2 * t) / 4 := by
    rw [hSqrt]
    ring
  rw [hDerivEq]
  have h1 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * t) t := by
    have h := hasDerivAt_pow 2 t
    simpa using h
  have h2 : HasDerivAt (fun τ : ℝ => -(τ ^ 2)) (-(2 * t)) t := h1.neg
  have h3 : HasDerivAt (fun τ : ℝ => (-(τ ^ 2)) / 4) ((-(2 * t)) / 4) t :=
    h2.div_const 4
  have hFunEq : (fun τ : ℝ => -τ ^ 2 / 4) = (fun τ : ℝ => (-(τ ^ 2)) / 4) := by
    ext τ
    ring
  rw [hFunEq]
  exact h3

theorem sqrtReaction_negative {t : ℝ} (ht : 0 < t) : -t ^ 2 / 4 < 0 := by
  have ht2 : 0 < t ^ 2 := by positivity
  linarith

/-- Invalid example, part 2: the reaction `r(u) = -√|u|` satisfies no
one-sided bound `r(u) ≥ K * u` on any nontrivial state range `[-M, 0]`,
whatever the constant `K`. -/
theorem sqrtReaction_not_oneSided (K : ℝ) {M : ℝ} (hM : 0 < M) :
    ∃ u ∈ Set.Icc (-M) 0, -Real.sqrt |u| < K * u := by
  have hK2nn : (0 : ℝ) ≤ K ^ 2 := by positivity
  have hDenom : (0 : ℝ) < K ^ 2 + 1 := by linarith
  have hInvPos : (0 : ℝ) < 1 / (K ^ 2 + 1) := by positivity
  set δ : ℝ := min M (1 / (K ^ 2 + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hM hInvPos
  have hδleM : δ ≤ M := min_le_left _ _
  have hδleInv : δ ≤ 1 / (K ^ 2 + 1) := min_le_right _ _
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδpos
  have hMem : (-δ) ∈ Set.Icc (-M) 0 := by
    constructor
    · linarith
    · linarith
  refine ⟨-δ, hMem, ?_⟩
  have hAbs : |(-δ : ℝ)| = δ := by
    rw [abs_neg, abs_of_nonneg hδnn]
  rw [hAbs]
  have hGoal : K * (-δ) = -(K * δ) := by ring
  rw [hGoal, neg_lt_neg_iff]
  by_cases hK : K ≤ 0
  · have hKδ : K * δ ≤ 0 := by
      have : K * δ ≤ 0 * δ := by
        apply mul_le_mul_of_nonneg_right hK hδnn
      simpa using this
    have hSqrtPos : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.mpr hδpos
    linarith
  · have hKpos : 0 < K := not_le.mp hK
    have hKδnn : (0 : ℝ) ≤ K * δ := by positivity
    have hK2δ_lt1 : K ^ 2 * δ < 1 := by
      have h1 : K ^ 2 * δ ≤ K ^ 2 * (1 / (K ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hδleInv hK2nn
      have h2 : K ^ 2 * (1 / (K ^ 2 + 1)) = K ^ 2 / (K ^ 2 + 1) := by ring
      have h3 : K ^ 2 / (K ^ 2 + 1) < 1 := (div_lt_one hDenom).mpr (by linarith)
      rw [h2] at h1
      linarith
    have hSq : (K * δ) ^ 2 < δ := by
      have hMul : (K ^ 2 * δ) * δ < 1 * δ :=
        mul_lt_mul_of_pos_right hK2δ_lt1 hδpos
      have hEq1 : (K * δ) ^ 2 = (K ^ 2 * δ) * δ := by ring
      have hEq2 : (1 : ℝ) * δ = δ := by ring
      rw [← hEq1, hEq2] at hMul
      exact hMul
    have hSqrtLt : Real.sqrt ((K * δ) ^ 2) < Real.sqrt δ :=
      Real.sqrt_lt_sqrt (by positivity) hSq
    rw [Real.sqrt_sq hKδnn] at hSqrtLt
    exact hSqrtLt

/-- Nonnegativity for a classical scalar parabolic solution: let
`c` solve `c_t - D * c_xx + k * c = s` on the closed cylinder
`[0, T] × [0, L]` in the sense that its time derivative `ct`,
first and second spatial derivatives `cx`, `cxx` are given
functions related by the displayed `HasDerivAt` data, with
`D > 0`, `k ≥ 0`, `s ≥ 0` pointwise on the cylinder, nonnegative
initial data `c 0 x ≥ 0` on `[0, L]`, and nonnegative Dirichlet
data `c t 0 ≥ 0`, `c t L ≥ 0` on `[0, T]`. Then `c t x ≥ 0` on the
whole cylinder. This is a comparison theorem for a given
classical solution, not an existence claim. The proof is the
compact negative-minimum argument applied to
`c + ε * (t + 1)`, then `ε → 0`. -/
theorem parabolic_solution_nonneg {D L T : ℝ} (hD : 0 < D)
    (hL : 0 < L) (hT : 0 < T)
    {c ct cx cxx k s : ℝ → ℝ → ℝ}
    (hct : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun τ : ℝ => c τ x) (ct t x) t)
    (hcx : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun y : ℝ => c t y) (cx t x) x)
    (hcxx : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun y : ℝ => cx t y) (cxx t x) x)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 L))
    (hPDE : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      ct t x - D * cxx t x + k t x * c t x = s t x)
    (hk : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L → 0 ≤ k t x)
    (hs : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L → 0 ≤ s t x)
    (hinit : ∀ x : ℝ, x ∈ Set.Icc 0 L → 0 ≤ c 0 x)
    (hb0 : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t 0)
    (hbL : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t L)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) :
    0 ≤ c t x := by
  have key : ∀ eps : ℝ, 0 < eps → ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      0 ≤ c t x + (eps * t + eps) := by
    intro eps heps t x ht hx
    have hcont_eps : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps))
        (Set.Icc 0 T ×ˢ Set.Icc 0 L) := by
      have haff : Continuous (fun r : ℝ => eps * r + eps) := by
        rw [continuous_iff_continuousAt]
        intro r
        exact (hasDerivAt_affine (a := eps) (b := eps) (x := r)).continuousAt
      have h1 : ContinuousOn (fun p : ℝ × ℝ => eps * p.1 + eps)
          (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
        haff.continuousOn.comp continuous_fst.continuousOn (fun p _ => Set.mem_univ _)
      exact hcont.add h1
    have hrect_compact : IsCompact (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
      isCompact_Icc.prod isCompact_Icc
    have hrect_ne : (Set.Icc 0 T ×ˢ Set.Icc 0 L).Nonempty :=
      ⟨(0, 0), Set.mk_mem_prod ⟨le_refl 0, hT.le⟩ ⟨le_refl 0, hL.le⟩⟩
    obtain ⟨p0, hp0mem, hmin0⟩ := hrect_compact.exists_isMinOn hrect_ne hcont_eps
    obtain ⟨t0, x0⟩ := p0
    have hpair : t0 ∈ Set.Icc 0 T ∧ x0 ∈ Set.Icc 0 L := hp0mem
    have ht0 : t0 ∈ Set.Icc 0 T := hpair.1
    have hx0 : x0 ∈ Set.Icc 0 L := hpair.2
    have hmin_time : IsMinOn (fun τ => c τ x0 + (eps * τ + eps)) (Set.Icc 0 T) t0 :=
      Filter.eventually_principal.mpr (fun τ hτ => by
        have hmem : (τ, x0) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := Set.mk_mem_prod hτ hx0
        have h := hmin0 hmem
        change c t0 x0 + (eps * t0 + eps) ≤ c τ x0 + (eps * τ + eps)
        exact h)
    have hmin_space : IsMinOn (fun y => c t0 y + (eps * t0 + eps)) (Set.Icc 0 L) x0 :=
      Filter.eventually_principal.mpr (fun y hy => by
        have hmem : (t0, y) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := Set.mk_mem_prod ht0 hy
        have h := hmin0 hmem
        change c t0 x0 + (eps * t0 + eps) ≤ c t0 y + (eps * t0 + eps)
        exact h)
    have htime_deriv : HasDerivAt (fun τ => c τ x0 + (eps * τ + eps)) (ct t0 x0 + eps) t0 :=
      (hct t0 x0 ht0 hx0).add
        (hasDerivAt_affine (a := eps) (b := eps) (x := t0))
    by_contra hneg2
    push Not at hneg2
    have hle : (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps)) (t0, x0) ≤
        (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps)) (t, x) :=
      hmin0 (Set.mk_mem_prod ht hx)
    have hle' : c t0 x0 + (eps * t0 + eps) ≤ c t x + (eps * t + eps) := hle
    have hmin_neg : c t0 x0 + (eps * t0 + eps) < 0 := by linarith
    have ht0' : 0 ≤ t0 ∧ t0 ≤ T := ht0
    have hx0' : 0 ≤ x0 ∧ x0 ≤ L := hx0
    have ht0_ne : t0 ≠ 0 := by
      intro hcon
      have h1 : 0 ≤ c 0 x0 := hinit x0 hx0
      have h2 : c t0 x0 + (eps * t0 + eps) = c 0 x0 + (eps * 0 + eps) := by rw [hcon]
      have h3 : 0 < eps * 0 + eps := by
        have heq : eps * 0 + eps = eps := by ring
        linarith
      linarith
    have hx0_ne0 : x0 ≠ 0 := by
      intro hcon
      have h1 : 0 ≤ c t0 0 := hb0 t0 ht0
      have h2 : c t0 x0 + (eps * t0 + eps) = c t0 0 + (eps * t0 + eps) := by rw [hcon]
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      have h3 : 0 < eps * t0 + eps := by linarith
      linarith
    have hx0_neL : x0 ≠ L := by
      intro hcon
      have h1 : 0 ≤ c t0 L := hbL t0 ht0
      have h2 : c t0 x0 + (eps * t0 + eps) = c t0 L + (eps * t0 + eps) := by rw [hcon]
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      have h3 : 0 < eps * t0 + eps := by linarith
      linarith
    have hx0Ioo : x0 ∈ Set.Ioo 0 L := by
      change 0 < x0 ∧ x0 < L
      exact ⟨lt_of_le_of_ne hx0'.1 (Ne.symm hx0_ne0), lt_of_le_of_ne hx0'.2 hx0_neL⟩
    have hct_le : ct t0 x0 + eps ≤ 0 := by
      by_cases ht0T : t0 = T
      · have hmem_time : Set.Icc 0 T ∈ nhdsWithin t0 (Set.Iio t0) := by
          rw [ht0T]
          have hIoi : Set.Ioi 0 ∈ nhds T := Ioi_mem_nhds hT
          have h1 : Set.Ioi 0 ∈ nhdsWithin T (Set.Iio T) :=
            mem_nhdsWithin_of_mem_nhds hIoi
          have h2 : Set.Iio T ∈ nhdsWithin T (Set.Iio T) := self_mem_nhdsWithin
          have hinter : Set.Ioi 0 ∩ Set.Iio T ∈ nhdsWithin T (Set.Iio T) :=
            Filter.inter_mem h1 h2
          apply Filter.mem_of_superset hinter
          intro y hy
          have hy' : 0 < y ∧ y < T := hy
          change 0 ≤ y ∧ y ≤ T
          exact ⟨hy'.1.le, hy'.2.le⟩
        exact isMinOn_hasDerivAt_le_zero htime_deriv hmin_time hmem_time
      · have ht0Ioo : t0 ∈ Set.Ioo 0 T := by
          change 0 < t0 ∧ t0 < T
          exact ⟨lt_of_le_of_ne ht0'.1 (Ne.symm ht0_ne), lt_of_le_of_ne ht0'.2 ht0T⟩
        have ht0Ioo' : 0 < t0 ∧ t0 < T := ht0Ioo
        have hmem_time_nhds : Set.Icc 0 T ∈ nhds t0 :=
          Filter.mem_of_superset (Ioo_mem_nhds ht0Ioo'.1 ht0Ioo'.2)
            Set.Ioo_subset_Icc_self
        have hct_eq : ct t0 x0 + eps = 0 :=
          isMinOn_hasDerivAt_eq_zero htime_deriv hmin_time hmem_time_nhds
        exact le_of_eq hct_eq
    have hcxx_nonneg : 0 ≤ cxx t0 x0 :=
      second_deriv_nonneg_of_isMinOn (g := fun y => cx t0 y) (gd := fun y => cxx t0 y)
        (fun y hy => hasDerivAt_add_const (C := eps * t0 + eps) (hcx t0 y ht0 hy))
        (fun y hy => hcxx t0 y ht0 hy)
        hx0Ioo hmin_space
    have hpde := hPDE t0 x0 ht0 hx0
    have hk0 : 0 ≤ k t0 x0 := hk t0 x0 ht0 hx0
    have hs0 : 0 ≤ s t0 x0 := hs t0 x0 ht0 hx0
    have hE_pos : 0 < eps * t0 + eps := by
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      linarith
    have hkE : 0 ≤ k t0 x0 * (eps * t0 + eps) := mul_nonneg hk0 hE_pos.le
    have hdist : k t0 x0 * (c t0 x0 + (eps * t0 + eps)) =
        k t0 x0 * c t0 x0 + k t0 x0 * (eps * t0 + eps) := by ring
    have hLHS_eq : (ct t0 x0 + eps) - D * cxx t0 x0 + k t0 x0 * (c t0 x0 + (eps * t0 + eps)) =
        s t0 x0 + eps + k t0 x0 * (eps * t0 + eps) := by linarith
    have hLHS_pos : 0 < (ct t0 x0 + eps) - D * cxx t0 x0 +
        k t0 x0 * (c t0 x0 + (eps * t0 + eps)) := by
      rw [hLHS_eq]
      linarith
    have hDc : 0 ≤ D * cxx t0 x0 := mul_nonneg hD.le hcxx_nonneg
    have hkV : k t0 x0 * (c t0 x0 + (eps * t0 + eps)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hk0 hmin_neg.le
    have hLHS_nonpos : (ct t0 x0 + eps) - D * cxx t0 x0 +
        k t0 x0 * (c t0 x0 + (eps * t0 + eps)) ≤ 0 := by
      linarith
    linarith
  by_contra hneg
  push Not at hneg
  have ht' : 0 ≤ t ∧ t ≤ T := ht
  have ht1 : 0 < t + 1 := by linarith
  have hcn : 0 < -(c t x) := by linarith
  have hpos2 : 0 < -(c t x) / (t + 1) := div_pos hcn ht1
  obtain ⟨eps, heps0, hepilt⟩ := exists_between hpos2
  have hkey := key eps heps0 t x ht hx
  have hmul : eps * (t + 1) < -(c t x) := by
    have h := mul_lt_mul_of_pos_right hepilt ht1
    rw [div_mul_cancel₀ _ (ne_of_gt ht1)] at h
    exact h
  have hring : eps * t + eps = eps * (t + 1) := by ring
  linarith

end MathlibExt.Analysis.PDE.ScalarParabolicComparison
