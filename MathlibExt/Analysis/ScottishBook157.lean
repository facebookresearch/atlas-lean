/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Order.Basic

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Scottish Book Problem 157

We prove the approximate derivative test for monotonicity by constructing a right approximate
maximum whenever the function decreases. The approximation conditions use Lebesgue outer measure.
-/

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook157Wanted

/-- **Right density zero at the origin.** A set $S \subseteq \mathbb{R}$ has right-hand density
$0$ at $0$ if the Lebesgue outer measure of $S \cap (0, \delta]$, divided by $\delta$, tends to
$0$ as $\delta \to 0^+$. -/
def HasZeroDensityAtRight (S : Set ℝ) : Prop :=
  Filter.Tendsto (fun δ => (MeasureTheory.volume (S ∩ Set.Ioc 0 δ)).toReal / δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- **Approximate continuity.** For every $\varepsilon > 0$, the Lebesgue outer measure of
$\{y : |f(y) - f(x)| \ge \varepsilon\} \cap (x - \delta, x + \delta)$, divided by $2\delta$,
tends to $0$ as $\delta \to 0^+$.

This uses the outer measure of the bad set, rather than requiring the good set to have outer
density one: without measurability, those conditions are not equivalent. -/
def ApproxContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun δ => (MeasureTheory.volume ({y | ε ≤ |f y - f x|} ∩ Set.Ioo (x - δ) (x + δ))).toReal /
        (2 * δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- **Positive upper right approximate derivative.** The upper right-hand approximate derivative
of $f \colon \mathbb{R} \to \mathbb{R}$ at $x$ is positive: there are $a > 0$ and $\varepsilon > 0$
such that for every $\delta > 0$ there is $\delta' \in (0, \delta]$ for which the Lebesgue outer
measure of $\{h \in (0, \delta'] : (f(x + h) - f(x))/h > a\}$ is at least $\varepsilon \delta'$.

Equivalently, the approximate upper limit of the difference quotient $(f(x + h) - f(x))/h$ as
$h \to 0^+$, which neglects sets of $h$ of right density $0$ at $0$, is positive. -/
def HasPositiveUpperRightApproxDeriv (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      ε ≤ (MeasureTheory.volume {h | h ∈ Set.Ioc 0 δ' ∧
        a < (f (x + h) - f x) / h}).toReal / δ'

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Outer measure on a bounded half-open interval, viewed as a real. -/
private noncomputable def mass (s : Set ℝ) (a b : ℝ) : ℝ :=
  (volume.restrict s).real (Ioc a b)

private theorem mass_eq (s : Set ℝ) (a b : ℝ) :
    mass s a b = volume.real (s ∩ Ioc a b) := by
  rw [mass, measureReal_restrict_apply measurableSet_Ioc, inter_comm]

private theorem volume_ne_top_Ioo (a b : ℝ) : volume (Ioo a b) ≠ ∞ := by simp

private theorem volume_ne_top_Ioc (a b : ℝ) : volume (Ioc a b) ≠ ∞ := by simp

private theorem mass_nonneg (s : Set ℝ) (a b : ℝ) : 0 ≤ mass s a b := measureReal_nonneg

private theorem mass_le (s : Set ℝ) {a b : ℝ} (hab : a ≤ b) : mass s a b ≤ b - a := by
  rw [mass_eq, ← Real.volume_real_Ioc_of_le hab]
  exact measureReal_mono inter_subset_right (volume_ne_top_Ioc a b)

private theorem mass_add (s : Set ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    mass s a b + mass s b c = mass s a c := by
  have hfin (u v : ℝ) : (volume.restrict s) (Ioc u v) ≠ ∞ := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    exact measure_ne_top_of_subset inter_subset_left (volume_ne_top_Ioc u v)
  unfold mass
  rw [← measureReal_union (μ := volume.restrict s) (Ioc_disjoint_Ioc_of_le le_rfl)
        measurableSet_Ioc (hfin a b) (hfin b c),
    Ioc_union_Ioc_eq_Ioc hab hbc]

private theorem volume_le_inter_add_compl (s i : Set ℝ) :
    volume.real i ≤ volume.real (s ∩ i) + volume.real (sᶜ ∩ i) := by
  simpa only [← union_inter_distrib_right, union_compl_self, univ_inter] using
    (measureReal_union_le (μ := volume) (s ∩ i) (sᶜ ∩ i))

private theorem length_le_mass_add_compl (s : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    b - a ≤ mass s a b + mass sᶜ a b := by
  simpa only [mass_eq, Real.volume_real_Ioc_of_le hab] using
    volume_le_inter_add_compl s (Ioc a b)

/-- Any set separated from the value at the center has arbitrarily small centered proportions. -/
private theorem small_centered {f : ℝ → ℝ} {t ε : ℝ} (hf : ApproxContinuousAt f t)
    (hε : 0 < ε) {s : Set ℝ} (hs : s ⊆ {y | ε ≤ |f y - f t|}) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ r, 0 < r → r < R → volume.real (s ∩ Ioo (t - r) (t + r)) < η * r := by
  obtain ⟨R, hR, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hf ε hε) (η / 2) (by positivity)
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hdist : dist r 0 < R := by simpa [Real.dist_eq, abs_of_pos hr] using hrR
  have hratio := h (mem_Ioi.mpr hr) hdist
  rw [Real.dist_eq, sub_zero] at hratio
  have hbad := (div_lt_iff₀ (show 0 < 2 * r by positivity)).mp
    (show η / 2 > volume.real ({y | ε ≤ |f y - f t|} ∩ Ioo (t - r) (t + r)) / (2 * r) from
      (le_abs_self _).trans_lt hratio)
  have hmass := measureReal_mono (μ := volume) (inter_subset_inter_left _ hs)
    (measure_ne_top_of_subset inter_subset_right (volume_ne_top_Ioo (t - r) (t + r)))
  linarith

private theorem small_oneSided {f : ℝ → ℝ} {t ε : ℝ} (hf : ApproxContinuousAt f t)
    (hε : 0 < ε) {s : Set ℝ} (hs : s ⊆ {y | ε ≤ |f y - f t|}) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ d, 0 < d → d < R →
      mass s t (t + d) < η * d ∧ mass s (t - d) t < η * d := by
  obtain ⟨R, hR, h⟩ := small_centered hf hε hs (show 0 < η / 2 by positivity)
  refine ⟨R / 2, by positivity, fun d hd hdR ↦ ?_⟩
  have hsmall := h (2 * d) (by positivity) (by linarith)
  have hmono {a b : ℝ} (hab : Ioc a b ⊆ Ioo (t - 2 * d) (t + 2 * d)) :
      mass s a b < η * d := by
    rw [mass_eq]
    have hle := measureReal_mono (μ := volume) (inter_subset_inter_right s hab)
      (measure_ne_top_of_subset inter_subset_right (volume_ne_top_Ioo _ _))
    linarith
  exact ⟨hmono (fun _ hy ↦ ⟨by linarith [hy.1], by linarith [hy.2]⟩),
    hmono (fun _ hy ↦ ⟨by linarith [hy.1], by linarith [hy.2]⟩)⟩

private theorem superlevel_subset_bad {f : ℝ → ℝ} {t c : ℝ} :
    {y | c < f y} ⊆ {y | c - f t ≤ |f y - f t|} := by
  intro y hy
  change c < f y at hy
  exact (sub_le_sub_right hy.le _).trans (le_abs_self _)

private theorem superlevel_compl_subset_bad {f : ℝ → ℝ} {t c : ℝ} :
    {y | c < f y}ᶜ ⊆ {y | f t - c ≤ |f y - f t|} := by
  intro y hy
  have hy' : f y ≤ c := le_of_not_gt hy
  exact (sub_le_sub_left hy' _).trans (neg_sub (f y) (f t) ▸ neg_le_abs (f y - f t))

/-- A decreasing crossing has a point at the crossing level with small right proportions and
large left proportions. The maximum is taken on the cumulative outer mass minus a linear term. -/
private theorem crossing {f : ℝ → ℝ} (hf : ∀ x, ApproxContinuousAt f x)
    {p b c η : ℝ} (hpb : p < b) (hp : c < f p) (hb : f b < c) (hη : 0 < η) (hη' : η < 1) :
    ∃ t ∈ Ioo p b, f t = c ∧
      (∀ u ∈ Icc t b, mass {y | c < f y} t u ≤ η * (u - t)) ∧
      (∀ u ∈ Icc p t, η * (t - u) ≤ mass {y | c < f y} u t) := by
  let s : Set ℝ := {y | c < f y}
  let F (u : ℝ) : ℝ := mass s p u - η * u
  have hcont : ContinuousOn F (Icc p b) := by
    apply (LipschitzOnWith.of_dist_le_mul (K := ⟨1 + η, by positivity⟩) ?_).continuousOn
    have hle (u v : ℝ) (hu : u ∈ Icc p b) (huv : u ≤ v) :
        dist (F u) (F v) ≤ (1 + η) * dist u v := by
      rw [dist_comm (F u), dist_comm u, Real.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr huv)]
      have hadd := mass_add s hu.1 huv
      have h₁ := mass_nonneg s u v
      have h₂ := mass_le s huv
      change |mass s p v - η * v - (mass s p u - η * u)| ≤ (1 + η) * (v - u)
      rw [abs_le]
      constructor <;> nlinarith
    intro u hu v hv
    change dist (F u) (F v) ≤ (1 + η) * dist u v
    rcases le_total u v with huv | hvu
    · simpa using hle u v hu huv
    · simpa [dist_comm] using hle v u hv hvu
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨p, left_mem_Icc.mpr hpb.le⟩ hcont
  have hright (u : ℝ) (hu : u ∈ Icc t b) : mass s t u ≤ η * (u - t) := by
    have h := isMaxOn_iff.mp hmax u ⟨ht.1.trans hu.1, hu.2⟩
    have h' := mass_add s ht.1 hu.1
    change mass s p u - η * u ≤ mass s p t - η * t at h
    linarith
  have hleft (u : ℝ) (hu : u ∈ Icc p t) : η * (t - u) ≤ mass s u t := by
    have h := isMaxOn_iff.mp hmax u ⟨hu.1, hu.2.trans ht.2⟩
    have h' := mass_add s hu.1 hu.2
    change mass s p u - η * u ≤ mass s p t - η * t at h
    linarith
  have not_high (htb : t < b) : ¬ c < f t := by
    intro hct
    obtain ⟨R, hR, h⟩ := small_oneSided (hf t) (sub_pos.mpr hct)
      (s := sᶜ) superlevel_compl_subset_bad (sub_pos.mpr hη')
    let d := min R (b - t) / 2
    have hd : 0 < d := half_pos (lt_min hR (sub_pos.mpr htb))
    have hdR : d < R := (half_lt_self (lt_min hR (sub_pos.mpr htb))).trans_le (min_le_left ..)
    have hdb : d ≤ b - t := (half_le_self (lt_min hR (sub_pos.mpr htb)).le).trans (min_le_right ..)
    have h₁ := (h d hd hdR).1
    have hu : t ∈ Icc t (t + d) := ⟨le_rfl, by linarith⟩
    have h₂ := length_le_mass_add_compl s hu.2
    have h₃ := hright (t + d) ⟨hu.2, by linarith⟩
    linarith
  have not_low (hpt : p < t) : ¬ f t < c := by
    intro htc
    obtain ⟨R, hR, h⟩ := small_oneSided (hf t) (sub_pos.mpr htc)
      (s := s) superlevel_subset_bad hη
    let d := min R (t - p) / 2
    have hd : 0 < d := half_pos (lt_min hR (sub_pos.mpr hpt))
    have hdR : d < R := (half_lt_self (lt_min hR (sub_pos.mpr hpt))).trans_le (min_le_left ..)
    have hdp : d ≤ t - p := (half_le_self (lt_min hR (sub_pos.mpr hpt)).le).trans (min_le_right ..)
    have h₁ := (h d hd hdR).2
    have h₂ := hleft (t - d) ⟨by linarith, by linarith⟩
    linarith
  have hpt : p < t := ht.1.lt_of_ne (fun h ↦ not_high (h ▸ hpb) (h ▸ hp))
  have htb : t < b := ht.2.lt_of_ne (fun h ↦ not_low (h ▸ hpt) (h ▸ hb))
  exact ⟨t, ⟨hpt, htb⟩, le_antisymm (le_of_not_gt (not_high htb)) (le_of_not_gt (not_low hpt)),
    hright, hleft⟩

/-- The endpoints of a decreasing bracket. -/
private structure Bracket (f : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  decrease : f right < f left

/-- Refine a decreasing bracket, retaining the right bound from the crossing lemma and a
centered lower bound for the previous superlevel set that survives at the eventual limit. -/
private theorem nextBracket {f : ℝ → ℝ} (hf : ∀ x, ApproxContinuousAt f x) (P : Bracket f)
    {η β : ℝ} (hη : 0 < η) (hη' : η < 1) (hβ : 0 < β) :
    ∃ Q : Bracket f, P.left ≤ Q.left ∧ Q.right < P.right ∧ f P.right < f Q.right ∧
      (∀ u ∈ Icc Q.right P.right, mass {y | f Q.right < f y} Q.right u ≤ η * (u - Q.right)) ∧
      ∃ r, 0 < r ∧ r < β ∧ Q.right - Q.left < r ∧
        r ≤ volume.real ({y | f P.right < f y} ∩ Ioo (Q.right - r) (Q.right + r)) := by
  obtain ⟨c, hc, hc'⟩ := exists_between P.decrease
  obtain ⟨t, ht, hft, hright, hleft⟩ := crossing hf P.left_lt_right hc' hc hη hη'
  let s : Set ℝ := {y | f P.right < f y}
  have hts : f P.right < f t := hft ▸ hc
  obtain ⟨R, hR, hsmall⟩ := small_centered (hf t) (sub_pos.mpr hts) (s := sᶜ)
    superlevel_compl_subset_bad zero_lt_one
  obtain ⟨r, hr, hr'⟩ := exists_between (lt_min hR hβ)
  have hlarge : r ≤ volume.real (s ∩ Ioo (t - r) (t + r)) := by
    have hcomp := hsmall r hr (hr'.trans_le (min_le_left ..))
    have hsum := volume_le_inter_add_compl s (Ioo (t - r) (t + r))
    rw [Real.volume_real_Ioo_of_le (by linarith : t - r ≤ t + r)] at hsum
    linarith
  obtain ⟨u, hu, hut⟩ := exists_between (max_lt ht.1 (by linarith : t - r < t))
  have hu' : P.left < u := (le_max_left ..).trans_lt hu
  have hm := hleft u ⟨hu'.le, hut.le⟩
  have hpos : 0 < mass {y | c < f y} u t := (mul_pos hη (sub_pos.mpr hut)).trans_le hm
  rw [mass_eq] at hpos
  obtain ⟨p, hfp, hp⟩ := nonempty_of_measureReal_ne_zero hpos.ne'
  have hpt : p < t := hp.2.lt_of_ne (fun h ↦ (show c < f p from hfp).ne (h ▸ hft.symm))
  refine ⟨⟨p, t, hpt, hft ▸ hfp⟩, hu'.le.trans hp.1.le, ht.2, hts, ?_,
    r, hr, hr'.trans_le (min_le_right ..), ?_, hlarge⟩
  · simpa only [hft] using hright
  · have htr : t - r < p := ((le_max_right ..).trans_lt hu).trans hp.1
    linarith

/-- Any decrease of an approximately continuous function produces a right approximate maximum. -/
private theorem exists_right_approxMax {f : ℝ → ℝ} (hf : ∀ x, ApproxContinuousAt f x)
    {a b : ℝ} (hab : a < b) (hdec : f b < f a) :
    ∃ x, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioc 0 δ, mass {y | f x < f y} x (x + h) < ε * h := by
  classical
  let η (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 2
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hη' (n : ℕ) : η n < 1 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [η]
    linarith
  have hηanti : Antitone η := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) (by linarith)) (by norm_num)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  let step (n : ℕ) (P : Bracket f) := nextBracket hf P (hη n) (hη' n) (hη n)
  let P : ℕ → Bracket f := Nat.rec ⟨a, b, hab, hdec⟩ (fun n Q ↦ (step n Q).choose)
  let p (n : ℕ) : ℝ := (P n).left
  let t (n : ℕ) : ℝ := (P n).right
  have hpt (n : ℕ) : p n < t n := (P n).left_lt_right
  have hstep (n : ℕ) : p n ≤ p (n + 1) ∧ t (n + 1) < t n ∧ f (t n) < f (t (n + 1)) ∧
      (∀ u ∈ Icc (t (n + 1)) (t n),
        mass {y | f (t (n + 1)) < f y} (t (n + 1)) u ≤ η n * (u - t (n + 1))) ∧
      ∃ r, 0 < r ∧ r < η n ∧ t (n + 1) - p (n + 1) < r ∧
        r ≤ volume.real ({y | f (t n) < f y} ∩ Ioo (t (n + 1) - r) (t (n + 1) + r)) :=
    (step n (P n)).choose_spec
  have hp : Monotone p := monotone_nat_of_le_succ (fun n ↦ (hstep n).1)
  have ht : Antitone t := antitone_nat_of_succ_le (fun n ↦ (hstep n).2.1.le)
  have hft : Monotone (fun n ↦ f (t n)) := monotone_nat_of_le_succ (fun n ↦ (hstep n).2.2.1.le)
  have hbelow : BddBelow (range t) := by
    refine ⟨p 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hp (Nat.zero_le n)).trans (hpt n).le
  let x := ⨅ n, t n
  have hxt (n : ℕ) : x ≤ t n := ciInf_le hbelow n
  have hpx (n : ℕ) : p n ≤ x := by
    apply le_ciInf
    intro m
    rcases le_total n m with hnm | hmn
    · exact (hp hnm).trans (hpt m).le
    · exact (hpt n).le.trans (ht hmn)
  have htlim : Tendsto t atTop (𝓝 x) := tendsto_atTop_ciInf ht hbelow
  -- The lower bounds persist on balls about the common limit of the nested brackets.
  have hfx (k : ℕ) : f (t k) ≤ f x := by
    by_contra! hk
    obtain ⟨R, hR, hsmall⟩ := small_centered (hf x) (sub_pos.mpr hk)
      (s := {y | f (t k) < f y}) superlevel_subset_bad (show 0 < (1 : ℝ) / 2 by norm_num)
    obtain ⟨n, hnR, hkn⟩ := ((hηlim.eventually_lt_const (half_pos hR)).and
      (eventually_ge_atTop k)).exists
    obtain ⟨r, hr, hrη, hwidth, hlarge⟩ := (hstep n).2.2.2.2
    have hsub :
        {y | f (t n) < f y} ∩ Ioo (t (n + 1) - r) (t (n + 1) + r) ⊆
          {y | f (t k) < f y} ∩ Ioo (x - 2 * r) (x + 2 * r) := by
      intro y hy
      exact ⟨(hft hkn).trans_lt hy.1, by
        have h₁ := hy.2.1
        have h₂ := hy.2.2
        exact ⟨by linarith [hxt (n + 1)], by linarith [hpx (n + 1)]⟩⟩
    have hle := measureReal_mono (μ := volume) hsub
      (measure_ne_top_of_subset inter_subset_right (volume_ne_top_Ioo _ _))
    have hlt := hsmall (2 * r) (by positivity) (by linarith)
    linarith
  let s : Set ℝ := {y | f x < f y}
  have hbound (N : ℕ) {y : ℝ} (hxy : x ≤ y) (hy : y ≤ t N) :
      mass s x y ≤ η N * (y - x) := by
    -- Estimate finite partitions first; the unestimated initial interval has length tending to 0.
    let u (n : ℕ) := min y (t n)
    have hxu (n : ℕ) : x ≤ u n := le_min hxy (hxt n)
    have huy (n : ℕ) : u n ≤ y := min_le_left ..
    have hus (n : ℕ) : u (n + 1) ≤ u n := min_le_min_left y (ht (Nat.le_succ n))
    have hpieces (n : ℕ) (hn : N ≤ n) : mass s (u n) y ≤ η N * (y - u n) := by
      induction n, hn using Nat.le_induction with
      | base => simp [u, min_eq_left hy, mass]
      | succ n hn ih =>
        have hpart : mass s (u (n + 1)) (u n) ≤ η N * (u n - u (n + 1)) := by
          by_cases hy' : y ≤ t (n + 1)
          · have hyt : y ≤ t n := hy'.trans (ht (Nat.le_succ n))
            simp [u, min_eq_left hy', min_eq_left hyt, mass]
          · have htu : t (n + 1) ≤ u n := le_min (le_of_not_ge hy') (ht (Nat.le_succ n))
            have hmin : u (n + 1) = t (n + 1) := min_eq_right (le_of_not_ge hy')
            have h₁ := (hstep n).2.2.2.1 (u n) ⟨htu, min_le_right ..⟩
            have h₂ : mass s (t (n + 1)) (u n) ≤
                mass {z | f (t (n + 1)) < f z} (t (n + 1)) (u n) := by
              simp only [mass_eq]
              exact measureReal_mono (inter_subset_inter_left _ (fun z hz ↦
                (hfx (n + 1)).trans_lt hz))
                (measure_ne_top_of_subset inter_subset_right (volume_ne_top_Ioc _ _))
            rw [hmin]
            exact (h₂.trans h₁).trans (mul_le_mul_of_nonneg_right (hηanti hn) (sub_nonneg.mpr htu))
        have hadd := mass_add s (hus n) (huy n)
        linarith
    have htail (n : ℕ) (hn : N ≤ n) :
        mass s x y ≤ (t n - x) + η N * (y - x) := by
      have hsplit := mass_add s (hxu n) (huy n)
      have hprefix := mass_le s (hxu n)
      have hrest := hpieces n hn
      have hcut : u n ≤ t n := min_le_right ..
      have hprod := mul_nonneg (hη N).le (sub_nonneg.mpr (hxu n))
      linarith
    have hlim : Tendsto (fun n ↦ t n - x + η N * (y - x)) atTop (𝓝 (η N * (y - x))) := by
      simpa only [sub_self, zero_add] using (htlim.sub_const x).add_const (η N * (y - x))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      ((eventually_ge_atTop N).mono (fun n hn ↦ htail n hn))
  refine ⟨x, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := (hηlim.eventually_lt_const hε).exists
  have hxN := (hxt (N + 1)).trans_lt (hstep N).2.1
  refine ⟨t N - x, sub_pos.mpr hxN, fun h hh ↦ ?_⟩
  have hb := hbound N (y := x + h) (by linarith [hh.1]) (by linarith [hh.2])
  rw [show x + h - x = h by ring] at hb
  exact hb.trans_lt (mul_lt_mul_of_pos_right hN hh.1)

/--
**Approximate derivative test for monotonicity (Scottish Book Problem 157).** Let
$f \colon \mathbb{R} \to \mathbb{R}$ be approximately continuous at every point, and suppose that
at every point $x$ the upper right-hand approximate derivative of $f$ is positive. Then $f$ is
monotone nondecreasing.

Source: A. J. (Gus) Ward, Problem 157 of the Scottish Book; solved
affirmatively by D. Ornstein, "A characterization of monotone functions",
Illinois J. Math. 15 (1971), 73-76, and by R. O'Malley (1975), whose theorem
on approximate maxima yields an immediate positive solution; see
K. Beanland, P. Humke, T. Richards, "On Scottish Book Problem 157",
Real Anal. Exchange 41(2) (2016), 331-346.
-/
theorem wardApproximatelyContinuousPositiveDerivMonotone :
    ∀ f : ℝ → ℝ, (∀ x, ApproxContinuousAt f x) →
      (∀ x, HasPositiveUpperRightApproxDeriv f x) → Monotone f := by
  intro f hcont hderiv a b hab
  by_contra! hdec
  have hab' : a < b := hab.lt_of_ne (fun h ↦ hdec.ne (congrArg f h.symm))
  obtain ⟨x, hx⟩ := exists_right_approxMax hcont hab' hdec
  obtain ⟨c, hc, ε, hε, hderiv⟩ := hderiv x
  obtain ⟨δ, hδ, hsmall⟩ := hx ε hε
  obtain ⟨d, hd, hdδ, hbig⟩ := hderiv δ hδ
  let s : Set ℝ := {y | f x < f y} ∩ Ioc x (x + d)
  have hsub : {h | h ∈ Ioc 0 d ∧ c < (f (x + h) - f x) / h} ⊆ (x + ·) ⁻¹' s := by
    intro h hh
    have hh' := hh.1
    have hpos : 0 < (f (x + h) - f x) / h := hc.trans hh.2
    have hfpos := (lt_div_iff₀ hh'.1).mp hpos
    refine ⟨sub_pos.mp (by simpa only [zero_mul] using hfpos), ?_⟩
    change x < x + h ∧ x + h ≤ x + d
    exact ⟨by linarith [hh'.1], by linarith [hh'.2]⟩
  have hfin : volume ((x + ·) ⁻¹' s) ≠ ∞ := by
    rw [measure_preimage_add]
    exact measure_ne_top_of_subset inter_subset_right (volume_ne_top_Ioc _ _)
  have hle := measureReal_mono (μ := volume) hsub hfin
  rw [Measure.real_def _ ((x + ·) ⁻¹' s), measure_preimage_add] at hle
  have hbig' := (le_div_iff₀ hd).mp hbig
  have hsmall' := hsmall d ⟨hd, hdδ⟩
  rw [mass_eq] at hsmall'
  exact (hle.trans_lt hsmall').not_ge hbig'

end MathlibExt.Analysis.ScottishBook157Wanted
