/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.SimpleFuncDense

import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Bounded measurable functions with the pointwise supremum norm

This file defines the bounded measurable complex-valued functions on a measurable space as the
closed star subalgebra of the raw bounded-function space `lp (fun _ => ℂ) ∞`.  Thus equality is
pointwise equality, not almost-everywhere equality, and all normed algebra and C-star structure is
inherited from the canonical `lp` carrier.

The API includes measurable indicators, conversion of measurable simple functions, and uniform
approximation by finite-range measurable functions.  No measure on the source type is required.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MathlibExt.MeasureTheory.Function

noncomputable section

universe u

variable (X : Type u) [MeasurableSpace X]

/-- The star subalgebra of raw bounded functions consisting of the measurable functions. -/
noncomputable def boundedMeasurableFunctions :
    StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞) where
  carrier := {f | Measurable fun x ↦ f x}
  zero_mem' := by
    change Measurable fun _ : X ↦ (0 : ℂ)
    exact measurable_const
  add_mem' := by
    intro f g hf hg
    change Measurable fun x ↦ f x + g x
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change Measurable fun x ↦ f x * g x
    exact hf.mul hg
  one_mem' := by
    change Measurable fun _ : X ↦ (1 : ℂ)
    exact measurable_const
  algebraMap_mem' := by
    intro c
    change Measurable fun _ : X ↦ c
    exact measurable_const
  star_mem' := by
    intro f hf
    change Measurable fun x ↦ star (f x)
    exact Complex.continuous_conj.measurable.comp hf

/-- Bounded measurable complex-valued functions, with pointwise equality and the supremum norm. -/
abbrev BoundedMeasurableFunction := ↥(boundedMeasurableFunctions X)

namespace BoundedMeasurableFunction

variable {X}

instance : CoeFun (BoundedMeasurableFunction X) (fun _ ↦ X → ℂ) where
  coe f := f.1

/-- The underlying raw bounded function of a bounded measurable function. -/
abbrev toLp (f : BoundedMeasurableFunction X) : lp (fun _ : X ↦ ℂ) ∞ := f

/-- Coercing to the raw bounded function preserves the original pointwise function. -/
theorem coe_toLp (f : BoundedMeasurableFunction X) :
    (f.toLp : X → ℂ) = f :=
  rfl

/-- Build a bounded measurable function from its actual raw function and pointwise norm bound.
No nonempty source or nonnegative bound is required by the DATA constructor. -/
noncomputable def ofBound (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : BoundedMeasurableFunction X := by
  classical
  exact ⟨⟨(show PreLp (fun _ : X => ℂ) from f), by
    change Memℓp f ∞
    rw [memℓp_infty_iff]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hC x⟩, hf⟩

/-- Evaluation of the actual bound-based constructor is the original pointwise function. -/
@[simp]
theorem ofBound_apply (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : X) : ofBound f hf C hC x = f x := rfl

/-- The constructor retains its original pointwise norm bound. -/
theorem norm_ofBound_apply_le (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : X) : ‖ofBound f hf C hC x‖ ≤ C := hC x

/-- A nonnegative pointwise bound controls the supremum norm, including on the empty source. -/
theorem norm_ofBound_le (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hC0 : 0 ≤ C) : ‖ofBound f hf C hC‖ ≤ C := by
  change ‖(ofBound f hf C hC).toLp‖ ≤ C
  exact lp.norm_le_of_forall_le hC0 hC

/-- The supremum norm has a uniform bound without imposing nonemptiness or a bound sign. -/
theorem norm_ofBound_le_max (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : ‖ofBound f hf C hC‖ ≤ max C 0 := by
  change ‖(ofBound f hf C hC).toLp‖ ≤ max C 0
  exact lp.norm_le_of_forall_le (le_max_right C 0)
    (fun x => (hC x).trans (le_max_left C 0))

/-- A bounded measurable function is measurable as an ordinary pointwise function. -/
theorem measurable (f : BoundedMeasurableFunction X) : Measurable fun x ↦ f x :=
  show Measurable (fun x ↦ f.1 x) from f.property

/-- The norm is the pointwise supremum norm, including on the empty source type. -/
theorem norm_eq_iSup_norm (f : BoundedMeasurableFunction X) :
    ‖f‖ = ⨆ x : X, ‖f x‖ :=
  lp.norm_eq_ciSup f.toLp

/-- Evaluation at every point is bounded by the supremum norm. -/
theorem norm_apply_le_norm (f : BoundedMeasurableFunction X) (x : X) :
    ‖f x‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f.toLp x

end BoundedMeasurableFunction

/-- The measurable bounded-function star subalgebra is closed in the raw supremum-norm space. -/
theorem isClosed_boundedMeasurableFunctions :
    IsClosed (boundedMeasurableFunctions X : Set (lp (fun _ : X ↦ ℂ) ∞)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro f g hf hfg
  change Measurable fun x ↦ g x
  apply measurable_of_tendsto_metrizable (fun n ↦ show Measurable (fun x ↦ f n x) from hf n)
  rw [tendsto_pi_nhds]
  intro x
  exact ((lp.evalCLM ℂ (fun _ : X ↦ ℂ) ∞ x).continuous.tendsto _).comp hfg

noncomputable instance boundedMeasurableFunctionsIsClosed :
    IsClosed (boundedMeasurableFunctions X : Set (lp (fun _ : X ↦ ℂ) ∞)) :=
  isClosed_boundedMeasurableFunctions X

namespace BoundedMeasurableFunction

variable {X}

/-! ### Measurable simple functions and indicators -/

/-- A measurable simple function, regarded as a bounded measurable function. -/
noncomputable def ofSimpleFunc (f : SimpleFunc X ℂ) : BoundedMeasurableFunction X :=
  by
    classical
    exact
      ⟨⟨(show PreLp (fun _ : X ↦ ℂ) from fun x ↦ f x), by
          change Memℓp (fun x ↦ f x) ∞
          rw [memℓp_infty_iff]
          refine ⟨∑ y ∈ f.range, ‖y‖, ?_⟩
          rintro _ ⟨x, rfl⟩
          exact Finset.single_le_sum (fun y _ ↦ norm_nonneg y) (f.mem_range_self x)⟩,
        f.measurable⟩

/-- Converting a measurable simple function preserves its pointwise values. -/
@[simp]
theorem ofSimpleFunc_apply (f : SimpleFunc X ℂ) (x : X) : ofSimpleFunc f x = f x :=
  rfl

/-- A measurable-set indicator with the constant value `c` on the set. -/
noncomputable def indicatorConst (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    BoundedMeasurableFunction X :=
  ofSimpleFunc <| SimpleFunc.piecewise s hs (SimpleFunc.const X c) 0

/-- The bounded measurable constant indicator has the usual set-indicator values. -/
@[simp]
theorem indicatorConst_apply (s : Set X) (hs : MeasurableSet s) (c : ℂ) (x : X) :
    indicatorConst s hs c x = s.indicator (fun _ ↦ c) x := by
  by_cases hx : x ∈ s <;> simp [indicatorConst, hx]

/-- The characteristic function of a measurable set as a bounded measurable function. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) :
    BoundedMeasurableFunction X :=
  indicatorConst s hs 1

/-- The bounded measurable indicator evaluates to one on its set and zero elsewhere. -/
@[simp]
theorem indicator_apply (s : Set X) (hs : MeasurableSet s) (x : X) :
    indicator s hs x = s.indicator (fun _ ↦ (1 : ℂ)) x := by
  rw [indicator, indicatorConst_apply]

/-- The constant indicator of the empty set is zero. -/
@[simp]
theorem indicatorConst_empty (c : ℂ) :
    indicatorConst (∅ : Set X) MeasurableSet.empty c = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext x
  simp

/-- The bounded measurable indicator of the empty set is zero. -/
@[simp]
theorem indicator_empty : indicator (∅ : Set X) MeasurableSet.empty = 0 := by
  simp [indicator]

/-- The bounded measurable indicator of the whole space is one. -/
@[simp]
theorem indicator_univ : indicator (Set.univ : Set X) MeasurableSet.univ = 1 := by
  apply Subtype.ext
  apply lp.ext
  funext x
  simp

/-- Multiplying two bounded measurable indicators gives the indicator of their intersection. -/
@[simp]
theorem indicator_inter (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    indicator (s ∩ t) (hs.inter ht) = indicator s hs * indicator t ht := by
  apply Subtype.ext
  apply lp.ext
  funext x
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [indicator_apply, hxs, hxt]

/-- A bounded measurable indicator is self-adjoint. -/
@[simp]
theorem star_indicator (s : Set X) (hs : MeasurableSet s) :
    star (indicator s hs) = indicator s hs := by
  apply Subtype.ext
  apply lp.ext
  funext x
  by_cases hx : x ∈ s <;> simp [indicator_apply, hx]

/-- The norm of a constant-valued indicator is at most the norm of its value. -/
theorem norm_indicatorConst_le (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    ‖indicatorConst s hs c‖ ≤ ‖c‖ := by
  change ‖(indicatorConst s hs c).toLp‖ ≤ ‖c‖
  apply lp.norm_le_of_forall_le (norm_nonneg c)
  intro x
  by_cases hx : x ∈ s <;> simp [indicatorConst_apply, hx]

/-- On a nonempty set, a constant-valued indicator has exactly the norm of its value. -/
theorem norm_indicatorConst (s : Set X) (hs : MeasurableSet s) (hne : s.Nonempty) (c : ℂ) :
    ‖indicatorConst s hs c‖ = ‖c‖ := by
  apply le_antisymm (norm_indicatorConst_le s hs c)
  obtain ⟨x, hx⟩ := hne
  calc
    ‖c‖ = ‖indicatorConst s hs c x‖ := by simp [indicatorConst_apply, hx]
    _ ≤ ‖indicatorConst s hs c‖ := norm_apply_le_norm _ _

/-- A nonempty measurable set has characteristic function of norm one. -/
theorem norm_indicator (s : Set X) (hs : MeasurableSet s) (hne : s.Nonempty) :
    ‖indicator s hs‖ = 1 := by
  simpa [indicator] using norm_indicatorConst s hs hne (1 : ℂ)

/-! ### Uniform finite-range approximation -/

private theorem exists_simpleFunc_uniform_approx
    (f : BoundedMeasurableFunction X) {r : ℝ} (hr : 0 < r) :
    ∃ g : SimpleFunc X ℂ, ∀ x, dist (g x) (f x) < r := by
  classical
  let K : Set ℂ := Metric.closedBall 0 ‖f‖
  have hK : IsCompact K := isCompact_closedBall 0 ‖f‖
  let : Nonempty K := ⟨⟨0, by simp [K]⟩⟩
  let e : ℕ → ℂ := fun n ↦ (denseSeq K n : ℂ)
  have hcover : K ⊆ ⋃ n : ℕ, Metric.ball (e n) r := by
    intro y hy
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq K) ⟨y, hy⟩ r hr
    have hn' : dist y (e n) < r := by
      simpa only [e, Subtype.dist_eq] using hn
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simpa [Metric.mem_ball] using hn'
  obtain ⟨t, _htuniv, htfinite, htcover⟩ :=
    hK.elim_finite_subcover_image (b := Set.univ)
      (c := fun n : ℕ ↦ Metric.ball (e n) r)
      (fun _ _ ↦ Metric.isOpen_ball) (by simpa using hcover)
  have htne : t.Nonempty := by
    have hzero : (0 : ℂ) ∈ K := by simp [K]
    obtain ⟨n, hnt, _hn⟩ := Set.mem_iUnion₂.mp (htcover hzero)
    exact ⟨n, hnt⟩
  let u : Finset ℕ := htfinite.toFinset
  have hune : u.Nonempty := by
    simpa [u] using htne
  let N : ℕ := u.max' hune
  let q : SimpleFunc ℂ ℂ := SimpleFunc.nearestPt e N
  let g : SimpleFunc X ℂ := q.comp (fun x ↦ f x) f.measurable
  refine ⟨g, fun x ↦ ?_⟩
  have hfxK : f x ∈ K := by
    change dist (f x) 0 ≤ ‖f‖
    rw [dist_zero_right]
    exact f.norm_apply_le_norm x
  obtain ⟨n, hnt, hball⟩ := Set.mem_iUnion₂.mp (htcover hfxK)
  have hnu : n ∈ u := by
    simpa [u] using hnt
  have hnN : n ≤ N := by
    dsimp only [N]
    simpa using Finset.le_max' u n hnu
  have hnear := SimpleFunc.edist_nearestPt_le e (f x) hnN
  have hnear' : dist (q (f x)) (f x) ≤ dist (e n) (f x) := by
    simpa [q, edist_dist] using hnear
  have hball' : dist (e n) (f x) < r := by
    simpa [Metric.mem_ball, dist_comm] using hball
  change dist (q (f x)) (f x) < r
  exact hnear'.trans_lt hball'

/-- Every bounded measurable function is uniformly approximable by measurable simple functions. -/
theorem exists_simpleFunc_norm_sub_lt
    (f : BoundedMeasurableFunction X) {r : ℝ} (hr : 0 < r) :
    ∃ g : SimpleFunc X ℂ, ‖f - ofSimpleFunc g‖ < r := by
  obtain ⟨g, hg⟩ := exists_simpleFunc_uniform_approx f (half_pos hr)
  have hle : ‖(f - ofSimpleFunc g).toLp‖ ≤ r / 2 := by
    apply lp.norm_le_of_forall_le (half_pos hr).le
    intro x
    change ‖f x - ofSimpleFunc g x‖ ≤ r / 2
    simpa only [ofSimpleFunc_apply, dist_eq_norm, norm_sub_rev] using (hg x).le
  exact ⟨g, hle.trans_lt (half_lt_self hr)⟩

/-- Every bounded measurable function is uniformly approximable by finite-range bounded measurable
functions. -/
theorem exists_finiteRange_norm_sub_lt
    (f : BoundedMeasurableFunction X) {r : ℝ} (hr : 0 < r) :
    ∃ g : BoundedMeasurableFunction X,
      (Set.range fun x ↦ g x).Finite ∧ ‖f - g‖ < r := by
  obtain ⟨g, hg⟩ := exists_simpleFunc_norm_sub_lt f hr
  refine ⟨ofSimpleFunc g, ?_, hg⟩
  have hfun : (fun x ↦ ofSimpleFunc g x) = fun x ↦ g x := by
    funext x
    exact ofSimpleFunc_apply g x
  rw [hfun]
  exact g.finite_range

end BoundedMeasurableFunction

end

end MathlibExt.MeasureTheory.Function
