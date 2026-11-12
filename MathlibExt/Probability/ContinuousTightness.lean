/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Equicontinuity

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Tightness in `C([0,1])` from a modulus of continuity

This file proves the modulus-of-continuity tightness criterion for random continuous paths on
`[0,1]`, together with the Arzelà–Ascoli facts it rests on.

## Main results

* `equicontinuous_of_isCompact`: a compact subset of `C([0,1])` is equicontinuous.
* `isCompact_closure_of_bounded_equicontinuous`: Arzelà–Ascoli in `C([0,1])`; a uniformly
  bounded equicontinuous family has compact closure.
* `exists_isCompact_measureReal_notMem_le`: one `C([0,1])`-valued random variable lies in a
  compact set up to an event of arbitrarily small probability.
* `norm_le_of_modulus`: a path pinned at `0` with increments `≤ 1` over gaps `≤ δ` has sup norm
  at most `⌈1/δ⌉`.
* `isTightMeasureSet_of_modulus`: tightness of the laws of paths pinned at `0` from an
  eventual modulus-of-continuity bound (Billingsley 1999, Theorem 7.3).

The results were previously private copies in `MathlibExt.Probability.Donsker` (used for the
tightness step of Donsker's invariance principle) and
`MathlibExt.Probability.Martingale.MartingaleTightness` (used for Aldous's criterion). Both now
call this file.

## What is weakened or deferred

* Billingsley's Theorem 7.3 asks for tightness of the initial values `W n 0`; here the paths are
  pinned, `W n 0 = 0`. Both current callers (Donsker's polygonal process and the polygons of a
  triangular array) start at `0`.
* The time interval is `[0,1]` and the state space is `ℝ`; general compact time sets and Polish
  state spaces are not treated.

Source: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), §7,
Theorems 7.2 and 7.3.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.ContinuousTightness

noncomputable section

variable {Ω : Type*}

/-- A compact set of continuous paths on `[0,1]` is equicontinuous: evaluation is uniformly
continuous on the compact set `C × [0,1]`. This is the easy direction of the Arzelà–Ascoli
theorem (Billingsley 1999, Theorem 7.2). Moved from the private copies
`donsker_isCompact_equicontinuous` in `MathlibExt.Probability.Donsker` and
`isCompact_equicontinuous'` in `MathlibExt.Probability.Martingale.MartingaleTightness`. -/
theorem equicontinuous_of_isCompact
    {C : Set C(Set.Icc (0 : ℝ) 1, ℝ)} (hC : IsCompact C) :
    Equicontinuous ((↑) : C → Set.Icc (0 : ℝ) 1 → ℝ) := by
  have hcompact : IsCompact (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) :=
    hC.prod isCompact_univ
  have heval : Continuous (fun p : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1 =>
      p.1 p.2) := continuous_eval
  have huc := hcompact.uniformContinuousOn_of_continuous heval.continuousOn
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨δ, hδ, fun y hy f => ?_⟩
  have hp : ((f.1, x) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  have hq : ((f.1, y) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  apply hcontrol (f.1, x) hp (f.1, y) hq
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  simpa only [dist_comm] using hy

/-- **Arzelà–Ascoli in `C([0,1])`.** A uniformly bounded equicontinuous family of continuous
paths on `[0,1]` has compact closure (Billingsley 1999, Theorem 7.2). The proof transports
Mathlib's `BoundedContinuousFunction.arzela_ascoli` along the isometry
`C([0,1]) ≃ᵢ [0,1] →ᵇ ℝ`. Moved from the private copies
`donsker_isCompact_closure_of_bounded_equicontinuous` in `MathlibExt.Probability.Donsker` and
`isCompact_closure_of_bounded_equicontinuous'` in
`MathlibExt.Probability.Martingale.MartingaleTightness`. -/
theorem isCompact_closure_of_bounded_equicontinuous
    {A : Set C(Set.Icc (0 : ℝ) 1, ℝ)} {R : ℝ}
    (hbound : ∀ f ∈ A, ‖f‖ ≤ R)
    (hequi : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ) 1 → ℝ)) :
    IsCompact (closure A) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ
  let D : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) := e '' A
  have hin (g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
      (x : Set.Icc (0 : ℝ) 1) (hg : g ∈ D) : g x ∈ Metric.closedBall 0 R := by
    obtain ⟨f, hf, rfl⟩ := hg
    have hfx := (ContinuousMap.norm_coe_le_norm f x).trans (hbound f hf)
    change f x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hfx
  let u : D → A := fun g => ⟨e.symm g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    have : e.symm g.1 = f := by
      calc
        e.symm g.1 = e.symm (e f) := congrArg e.symm hfg.symm
        _ = f := e.symm_apply_apply f
    rwa [this]⟩
  have hequiD : Equicontinuous ((↑) : D → Set.Icc (0 : ℝ) 1 → ℝ) := by
    have h := hequi.comp u
    have hfun :
        (fun g : D => fun x => (u g).1 x) = (fun g : D => fun x => g.1 x) := by
      funext g x
      rfl
    rw [← hfun]
    exact h
  have hD : IsCompact (closure D) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall (0 : ℝ) R) D hin hequiD
  have himage : e '' closure A = closure D := by
    have h := e.toHomeomorph.image_closure A
    change e '' closure A = closure (e '' A) at h
    simpa only [D] using h
  have heq : e.symm '' closure D = closure A := by
    rw [← himage]
    apply Set.Subset.antisymm
    · rintro f ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simpa only [e.symm_apply_apply] using hg
    · intro f hf
      exact ⟨e f, ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  rw [← heq]
  exact hD.image e.symm.continuous

/-- A single `C([0,1])`-valued random variable stays in some compact set except on an event of
probability at most `b > 0`: its law is tight because `C([0,1])` is Polish
(`isTightMeasureSet_singleton`). Moved from the private copies `donsker_compact_capture` in
`MathlibExt.Probability.Donsker` and `compact_capture'` in
`MathlibExt.Probability.Martingale.MartingaleTightness`. -/
theorem exists_isCompact_measureReal_notMem_le [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {W : Ω → C(Set.Icc (0 : ℝ) 1, ℝ)} (hW : Measurable W) {b : ℝ} (hb : 0 < b) :
    ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧ P.real {ω | W ω ∉ C} ≤ b := by
  let _ : IsFiniteMeasure (P.map W) := P.isFiniteMeasure_map W
  have htight : IsTightMeasureSet {P.map W} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨C, hC, hbound⟩ := htight (ENNReal.ofReal b) (ENNReal.ofReal_pos.2 hb)
  refine ⟨C, hC, ?_⟩
  have hmap := hbound (P.map W) (Set.mem_singleton _)
  rw [Measure.map_apply_of_aemeasurable hW.aemeasurable hC.isClosed.measurableSet.compl] at hmap
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 hmap
  change (P (W ⁻¹' Cᶜ)).toReal ≤ b
  simpa only [ENNReal.toReal_ofReal hb.le] using hreal

/-- A continuous path on `[0,1]` vanishing at `0` whose increments over time gaps `≤ δ` are
`≤ 1` is bounded by `⌈1/δ⌉`: chain `m = ⌈1/δ⌉` steps of length `t/m ≤ δ` from `0` to `t`.
Moved from the private lemma of the same name in
`MathlibExt.Probability.Martingale.MartingaleTightness`. -/
theorem norm_le_of_modulus (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (hf0 : f ⟨0, le_rfl, zero_le_one⟩ = 0) {δ : ℝ} (hδ : 0 < δ)
    (hosc : ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ → dist (f s) (f t) ≤ 1) :
    ‖f‖ ≤ ⌈1 / δ⌉₊ := by
  refine (ContinuousMap.norm_le f (Nat.cast_nonneg _)).2 fun t => ?_
  set m := ⌈1 / δ⌉₊ with hm
  have hm0 : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  let p : ℕ → Set.Icc (0 : ℝ) 1 := fun k =>
    ⟨min ((k : ℝ) / m) 1 * t.1, mul_nonneg (le_min (by positivity) zero_le_one) t.2.1,
      by
        have := t.2.2
        have h1 : min ((k : ℝ) / m) 1 ≤ 1 := min_le_right _ _
        nlinarith [t.2.1, le_min (by positivity : (0 : ℝ) ≤ (k : ℝ) / m) zero_le_one]⟩
  have hp0 : p 0 = ⟨0, le_rfl, zero_le_one⟩ := by ext; simp [p]
  have hpm : p m = t := by ext; simp [p, div_self hmR.ne']
  have hstep : ∀ k, dist (p (k + 1)) (p k) ≤ δ := by
    intro k
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [p]
    have hδm : 1 / (m : ℝ) ≤ δ := by
      rw [div_le_iff₀ hmR]
      have := Nat.le_ceil (1 / δ)
      rw [← hm] at this
      calc (1 : ℝ) = (1 / δ) * δ := by field_simp
        _ ≤ m * δ := mul_le_mul_of_nonneg_right this hδ.le
        _ = δ * m := mul_comm _ _
    have hmono : min ((k : ℝ) / m) 1 ≤ min (((k + 1 : ℕ) : ℝ) / m) 1 :=
      min_le_min_right _ (div_le_div_of_nonneg_right (by push_cast; linarith) hmR.le)
    have hgap : min (((k + 1 : ℕ) : ℝ) / m) 1 - min ((k : ℝ) / m) 1 ≤ 1 / m := by
      have h1 : min (((k + 1 : ℕ) : ℝ) / m) 1 ≤ min ((k : ℝ) / m + 1 / m) 1 := by
        refine min_le_min_right _ (le_of_eq ?_); push_cast; ring
      have h2 : min ((k : ℝ) / m + 1 / m) 1 ≤ min ((k : ℝ) / m) 1 + 1 / m := by
        rcases le_total ((k : ℝ) / m) 1 with h | h
        · rw [min_eq_left h]; exact min_le_left _ _
        · rw [min_eq_right h]; exact (min_le_right _ _).trans (by simp)
      linarith
    rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hmono), abs_of_nonneg t.2.1]
    calc _ ≤ 1 / (m : ℝ) * 1 := mul_le_mul hgap t.2.2 t.2.1 (by positivity)
      _ ≤ δ := by rw [mul_one]; exact hδm
  have hchain : ∀ k, |f (p k)| ≤ k := by
    intro k
    induction k with
    | zero => simp [hp0, hf0]
    | succ k ih =>
      have := hosc _ _ (hstep k)
      rw [Real.dist_eq] at this
      push_cast
      calc |f (p (k + 1))| ≤ |f (p (k + 1)) - f (p k)| + |f (p k)| := by
            have := abs_add_le (f (p (k + 1)) - f (p k)) (f (p k))
            rwa [sub_add_cancel] at this
        _ ≤ 1 + k := add_le_add this ih
        _ = k + 1 := add_comm _ _
  have := hchain m
  rw [hpm] at this
  exact this

/- The paths that lie in the `n`-th capture set `C n`, start at `0`, and satisfy the
oscillation bound `1 / (j + 1)` at gap `δ j` for every `j` with `N j ≤ n`. Adapted from
`donskerGoodFamily` in `MathlibExt.Probability.Donsker` (which carried an explicit norm bound
instead of the pinning at `0`), as previously copied into `MartingaleTightness`. -/
private def goodFamily (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (δ : ℕ → ℝ) (N : ℕ → ℕ) :
    Set C(Set.Icc (0 : ℝ) 1, ℝ) :=
  {f | ∃ n, f ∈ C n ∧ f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
    ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j →
      dist (f s) (f t) < 1 / ((j : ℝ) + 1)}

private lemma isCompact_closure_goodFamily (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ))
    (hC : ∀ n, IsCompact (C n)) (δ : ℕ → ℝ) (N : ℕ → ℕ) (hδ : ∀ j, 0 < δ j) :
    IsCompact (closure (goodFamily C δ N)) := by
  let CEarly : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range (N 0), C n
  have hCEarly : IsCompact CEarly := (Finset.range (N 0)).isCompact_biUnion fun n _ => hC n
  obtain ⟨S, hS⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ))).mp hCEarly.isBounded
  have hbound (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (hf : f ∈ goodFamily C δ N) :
      ‖f‖ ≤ max (⌈1 / δ 0⌉₊ : ℝ) S := by
    obtain ⟨n, hfn, hf0, hosc⟩ := hf
    by_cases hn : N 0 ≤ n
    · refine (norm_le_of_modulus f hf0 (hδ 0) fun s t hst => ?_).trans (le_max_left _ _)
      have := hosc 0 hn s t hst
      norm_num at this
      exact this.le
    · have hfearly : f ∈ CEarly :=
        Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (lt_of_not_ge hn), hfn⟩⟩
      have hfball := hS hfearly
      rw [Metric.mem_closedBall, dist_zero_right] at hfball
      exact hfball.trans (le_max_right _ _)
  have hequi : Equicontinuous ((↑) : goodFamily C δ N → Set.Icc (0 : ℝ) 1 → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    let CSmall : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range (N j), C n
    have hCSmall : IsCompact CSmall := (Finset.range (N j)).isCompact_biUnion fun n _ => hC n
    have hearlyAt := equicontinuous_of_isCompact hCSmall x
    rw [Metric.equicontinuousAt_iff] at hearlyAt
    obtain ⟨d, hd, hcontrol⟩ := hearlyAt ε hε
    refine ⟨min d (δ j), lt_min hd (hδ j), fun y hy f => ?_⟩
    obtain ⟨n, hfn, _, hosc⟩ := f.2
    by_cases hjn : N j ≤ n
    · have hxy : dist x y ≤ δ j := by
        rw [dist_comm]
        exact (hy.trans_le (min_le_right _ _)).le
      exact (hosc j hjn x y hxy).trans hj
    · have hfsmall : f.1 ∈ CSmall :=
        Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (lt_of_not_ge hjn), hfn⟩⟩
      exact hcontrol y (hy.trans_le (min_le_left _ _)) ⟨f.1, hfsmall⟩
  exact isCompact_closure_of_bounded_equicontinuous hbound hequi

/-- **Tightness in `C([0,1])` from a modulus-of-continuity bound** (Billingsley 1999,
Theorem 7.3, with the paths pinned at `0`). If every `W n` vanishes at time `0` and, for all
`ε, b > 0`, there is `δ > 0` such that eventually
`P(∃ s t, |s - t| ≤ δ, |W n s - W n t| ≥ ε) ≤ b`, then the laws of `W n` are tight.

The proof is Arzelà–Ascoli: the paths outside a small exceptional set lie in a closed
uniformly bounded equicontinuous family (the bound comes from chaining the modulus from `0`),
and the finitely many early laws are tight individually because `C([0,1])` is Polish. -/
theorem isTightMeasureSet_of_modulus [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℕ → Ω → C(Set.Icc (0 : ℝ) 1, ℝ))
    (hW : ∀ n, Measurable (W n)) (hzero : ∀ n ω, W n ω ⟨0, le_rfl, zero_le_one⟩ = 0)
    (hosc : ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ ∧ ε ≤ dist (W n ω s) (W n ω t)} ≤
        b) :
    IsTightMeasureSet (Set.range fun n => P.map (W n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ζ hζ
  by_cases hζtop : ζ = ∞
  · exact ⟨∅, isCompact_empty, by simp only [hζtop, le_top, implies_true]⟩
  set b := ζ.toReal with hb_def
  have hb : 0 < b := ENNReal.toReal_pos hζ.ne' hζtop
  have hcapture (n : ℕ) : ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧
      P.real {ω | W n ω ∉ C} ≤ b / 2 :=
    exists_isCompact_measureReal_notMem_le (hW n) (div_pos hb (by norm_num))
  choose C hC hCprob using hcapture
  have hdata (j : ℕ) : ∃ δ > 0, ∃ N : ℕ, j ≤ N ∧ ∀ n, N ≤ n →
      P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ ∧
        1 / ((j : ℝ) + 1) ≤ dist (W n ω s) (W n ω t)} ≤ b / 4 * (1 / 2 : ℝ) ^ j := by
    obtain ⟨δ, hδ, hev⟩ := hosc (1 / ((j : ℝ) + 1)) (by positivity)
      (b / 4 * (1 / 2 : ℝ) ^ j) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨δ, hδ, max N j, le_max_right _ _, fun n hn => hN n ((le_max_left _ _).trans hn)⟩
  choose δ hδ N hjN hprob using hdata
  let K := closure (goodFamily C δ N)
  have hK : IsCompact K := isCompact_closure_goodFamily C hC δ N hδ
  refine ⟨K, hK, ?_⟩
  rintro μ ⟨n, rfl⟩
  let oscFail : ℕ → Set Ω := fun j =>
    {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j ∧
      1 / ((j : ℝ) + 1) ≤ dist (W n ω s) (W n ω t)}
  let J := (Finset.range (n + 1)).filter fun j => N j ≤ n
  have hpre : W n ⁻¹' Kᶜ ⊆ {ω | W n ω ∉ C n} ∪ ⋃ j ∈ J, oscFail j := by
    intro ω hω
    by_cases hCω : W n ω ∈ C n
    · by_cases hoscω : ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1,
          dist s t ≤ δ j → dist (W n ω s) (W n ω t) < 1 / ((j : ℝ) + 1)
      · exact absurd (subset_closure (show W n ω ∈ goodFamily C δ N from
          ⟨n, hCω, hzero n ω, hoscω⟩)) hω
      · push Not at hoscω
        obtain ⟨j, hjn, s, t, hst, hbad⟩ := hoscω
        have hjJ : j ∈ J := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le ((hjN j).trans hjn), hjn⟩
        exact Or.inr (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjJ, s, t, hst, hbad⟩⟩)
    · exact Or.inl hCω
  have hoscUnion : P.real (⋃ j ∈ J, oscFail j) ≤ b / 2 := by
    calc P.real (⋃ j ∈ J, oscFail j) ≤ ∑ j ∈ J, P.real (oscFail j) :=
          measureReal_biUnion_finset_le J oscFail
      _ ≤ ∑ j ∈ J, b / 4 * (1 / 2 : ℝ) ^ j :=
          Finset.sum_le_sum fun j hj => hprob j n (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range (n + 1), b / 4 * (1 / 2 : ℝ) ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => by positivity
      _ = b / 4 * ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ b / 4 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = b / 2 := by ring
  have hreal : P.real (W n ⁻¹' Kᶜ) ≤ b :=
    calc P.real (W n ⁻¹' Kᶜ) ≤ P.real ({ω | W n ω ∉ C n} ∪ ⋃ j ∈ J, oscFail j) :=
          measureReal_mono hpre (measure_ne_top P _)
      _ ≤ P.real {ω | W n ω ∉ C n} + P.real (⋃ j ∈ J, oscFail j) := measureReal_union_le _ _
      _ ≤ b / 2 + b / 2 := add_le_add (hCprob n) hoscUnion
      _ = b := by ring
  rw [Measure.map_apply_of_aemeasurable (hW n).aemeasurable hK.isClosed.measurableSet.compl]
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) hζtop).1
  simpa only [measureReal_def, b] using hreal

end

end MathlibExt.Probability.ContinuousTightness
