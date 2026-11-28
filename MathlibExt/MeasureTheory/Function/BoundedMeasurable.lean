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
# Pointwise bounded measurable functions and uniform approximation

On any measurable space `X`, the bounded measurable complex functions form a closed star
subalgebra of the raw bounded-function space `lp(X,ℂ,∞)`. Equality is pointwise and the norm is
the supremum norm, with value zero on the empty source. No measure is required.

Measurable simple functions and indicators lie in this algebra. Every bounded measurable
function has arbitrarily close measurable simple and finite-range approximants in supremum norm.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MathlibExt.MeasureTheory.Function

noncomputable section

universe u

variable (X : Type u) [MeasurableSpace X]

/-- **Closed star subalgebra of measurable bounded functions.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. `boundedMeasurableFunctions X` is the complex star subalgebra of
`lp(X,ℂ,∞)` with carrier `{f : Measurable f}`. -/
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

/-- **Pointwise bounded measurable complex function.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. `BoundedMeasurableFunction X` is the carrier of that star subalgebra,
with pointwise algebra operations and no almost-everywhere quotient. -/
abbrev BoundedMeasurableFunction := ↥(boundedMeasurableFunctions X)

namespace BoundedMeasurableFunction

variable {X}

instance : CoeFun (BoundedMeasurableFunction X) (fun _ ↦ X → ℂ) where
  coe f := f.1

/-- Bounded measurable functions are equal when their pointwise values are equal,
on any measurable space, including an empty source. -/
@[ext]
theorem ext {f g : BoundedMeasurableFunction X} (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  exact lp.ext (funext h)

/-- **Underlying raw bounded function.** Let `X` be a measurable space. Bounded measurable
complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on an empty
source. for `f : BoundedMeasurableFunction X`, `f.toLp ∈ lp(X,ℂ,∞)` has the same pointwise
values. -/
abbrev toLp (f : BoundedMeasurableFunction X) : lp (fun _ : X ↦ ℂ) ∞ := f

/-- **Pointwise function retained by the bounded-function inclusion.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. for `f : BoundedMeasurableFunction X`, the function
underlying `f.toLp` equals `f : X → ℂ`. -/
theorem coe_toLp (f : BoundedMeasurableFunction X) :
    (f.toLp : X → ℂ) = f :=
  rfl

/-- **Bounded measurable function from a pointwise norm bound.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. if measurable `f : X → ℂ` and `C : ℝ` satisfy `|f(x)|≤C`
for every `x`, `ofBound f C` packages this function. `C≥0` and nonemptiness of `X` are not
required for the constructor. -/
noncomputable def ofBound (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : BoundedMeasurableFunction X := by
  classical
  exact ⟨⟨(show PreLp (fun _ : X => ℂ) from f), by
    change Memℓp f ∞
    rw [memℓp_infty_iff]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hC x⟩, hf⟩

/-- **Pointwise value of a bound-based measurable function.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. for measurable `f` with `|f(x)|≤C`, `ofBound f C x=f(x)`. -/
@[simp]
theorem ofBound_apply (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : X) : ofBound f hf C hC x = f x := rfl

/-- **Pointwise norm bound of the packaged function.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. for measurable `f` with bound `|f(x)|≤C`, the packaged function satisfies
`|ofBound f C x|≤C` at every `x`. -/
theorem norm_ofBound_apply_le (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : X) : ‖ofBound f hf C hC x‖ ≤ C := hC x

/-- **Nonnegative pointwise bound controls the supremum norm.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. if measurable `f` has `|f(x)|≤C` for all `x` and `C≥0`, then
`‖ofBound f C‖∞≤C`. -/
theorem norm_ofBound_le (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hC0 : 0 ≤ C) : ‖ofBound f hf C hC‖ ≤ C := by
  change ‖(ofBound f hf C hC).toLp‖ ≤ C
  exact lp.norm_le_of_forall_le hC0 hC

/-- **Supremum norm bound allowing an empty source and signed constant.** Let `X` be a
measurable space. Bounded measurable complex functions have pointwise equality and norm
`‖f‖∞=sup_x |f(x)|`, zero on an empty source. for measurable `f` with `|f(x)|≤C`
everywhere, `‖ofBound f C‖∞≤max(C,0)`. -/
theorem norm_ofBound_le_max (f : X → ℂ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : ‖ofBound f hf C hC‖ ≤ max C 0 := by
  change ‖(ofBound f hf C hC).toLp‖ ≤ max C 0
  exact lp.norm_le_of_forall_le (le_max_right C 0)
    (fun x => (hC x).trans (le_max_left C 0))

/-- **Measurability of a bounded measurable function.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. the function `x ↦ f(x)` is measurable for every `f :
BoundedMeasurableFunction X`. -/
theorem measurable (f : BoundedMeasurableFunction X) : Measurable fun x ↦ f x :=
  show Measurable (fun x ↦ f.1 x) from f.property

/-- **Supremum formula for a bounded measurable norm.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. for `f : BoundedMeasurableFunction X`, `‖f‖=sup_x |f(x)|`, with the empty
supremum interpreted as zero. -/
theorem norm_eq_iSup_norm (f : BoundedMeasurableFunction X) :
    ‖f‖ = ⨆ x : X, ‖f x‖ :=
  lp.norm_eq_ciSup f.toLp

/-- **Evaluation bounded by the supremum norm.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. for every `f` and `x∈X`, `|f(x)|≤‖f‖∞`. -/
theorem norm_apply_le_norm (f : BoundedMeasurableFunction X) (x : X) :
    ‖f x‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f.toLp x

end BoundedMeasurableFunction

/-- **Uniform closedness of measurable bounded functions.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. the measurable bounded-function subalgebra is closed in
`lp(X,ℂ,∞)` for the supremum-norm topology. -/
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

/-- **Measurable simple function in the bounded-function algebra.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. `ofSimpleFunc f` includes a measurable finite-range
complex function `f : SimpleFunc X ℂ` with its pointwise values. -/
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

/-- **Value of the measurable simple-function inclusion.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. for `f : SimpleFunc X ℂ` and `x∈X`, `ofSimpleFunc f x=f(x)`. -/
@[simp]
theorem ofSimpleFunc_apply (f : SimpleFunc X ℂ) (x : X) : ofSimpleFunc f x = f x :=
  rfl

/-- **Measurable scalar indicator function.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. for measurable `s⊆X` and `c∈ℂ`, `indicatorConst s c` is `c` on `s` and
zero outside `s`. -/
noncomputable def indicatorConst (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    BoundedMeasurableFunction X :=
  ofSimpleFunc <| SimpleFunc.piecewise s hs (SimpleFunc.const X c) 0

/-- **Pointwise scalar indicator values.** Let `X` be a measurable space. Bounded measurable
complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on an empty
source. for measurable `s`, `c∈ℂ`, `indicatorConst s c x=1_s(x)c`. -/
@[simp]
theorem indicatorConst_apply (s : Set X) (hs : MeasurableSet s) (c : ℂ) (x : X) :
    indicatorConst s hs c x = s.indicator (fun _ ↦ c) x := by
  by_cases hx : x ∈ s <;> simp [indicatorConst, hx]

/-- **Measurable characteristic function as a bounded function.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. for measurable `s⊆X`, `indicator s` is the
complex-valued characteristic function `1_s`. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) :
    BoundedMeasurableFunction X :=
  indicatorConst s hs 1

/-- **Pointwise characteristic-function value.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. for measurable `s` and `x∈X`, `indicator s x` is one if `x∈s` and zero
otherwise. -/
@[simp]
theorem indicator_apply (s : Set X) (hs : MeasurableSet s) (x : X) :
    indicator s hs x = s.indicator (fun _ ↦ (1 : ℂ)) x := by
  rw [indicator, indicatorConst_apply]

/-- **Scalar indicator of the empty set.** Let `X` be a measurable space. Bounded measurable
complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on an empty
source. for every `c∈ℂ`, `indicatorConst ∅ c=0`. -/
@[simp]
theorem indicatorConst_empty (c : ℂ) :
    indicatorConst (∅ : Set X) MeasurableSet.empty c = 0 := by
  apply BoundedMeasurableFunction.ext
  intro x
  simp

/-- **Characteristic function of the empty set.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. `indicator ∅=0`. -/
@[simp]
theorem indicator_empty : indicator (∅ : Set X) MeasurableSet.empty = 0 := by
  simp [indicator]

/-- **Characteristic function of the whole source.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. `indicator X=1`, including the empty source where the function algebra is
trivial. -/
@[simp]
theorem indicator_univ : indicator (Set.univ : Set X) MeasurableSet.univ = 1 := by
  apply BoundedMeasurableFunction.ext
  intro x
  simp

/-- **Product of two measurable characteristic functions.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. for measurable `s,t`, `indicator(s∩t)=indicator s * indicator t`
pointwise. -/
@[simp]
theorem indicator_inter (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    indicator (s ∩ t) (hs.inter ht) = indicator s hs * indicator t ht := by
  apply BoundedMeasurableFunction.ext
  intro x
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [indicator_apply, hxs, hxt]

/-- **Self-adjointness of a measurable characteristic function.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. for measurable `s`, pointwise conjugation fixes
`indicator s`. -/
@[simp]
theorem star_indicator (s : Set X) (hs : MeasurableSet s) :
    star (indicator s hs) = indicator s hs := by
  apply BoundedMeasurableFunction.ext
  intro x
  by_cases hx : x ∈ s <;> simp [indicator_apply, hx]

/-- **Supremum norm of a scalar indicator is bounded by its value.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. for measurable `s` and `c∈ℂ`, `‖indicatorConst s
c‖∞≤|c|`. -/
theorem norm_indicatorConst_le (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    ‖indicatorConst s hs c‖ ≤ ‖c‖ := by
  change ‖(indicatorConst s hs c).toLp‖ ≤ ‖c‖
  apply lp.norm_le_of_forall_le (norm_nonneg c)
  intro x
  by_cases hx : x ∈ s <;> simp [indicatorConst_apply, hx]

/-- **Exact norm of a nonempty scalar indicator.** Let `X` be a measurable space. Bounded
measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`, zero on
an empty source. if measurable `s` is nonempty, `‖indicatorConst s c‖∞=|c|` for every
`c∈ℂ`. -/
theorem norm_indicatorConst (s : Set X) (hs : MeasurableSet s) (hne : s.Nonempty) (c : ℂ) :
    ‖indicatorConst s hs c‖ = ‖c‖ := by
  apply le_antisymm (norm_indicatorConst_le s hs c)
  obtain ⟨x, hx⟩ := hne
  calc
    ‖c‖ = ‖indicatorConst s hs c x‖ := by simp [indicatorConst_apply, hx]
    _ ≤ ‖indicatorConst s hs c‖ := norm_apply_le_norm _ _

/-- **Norm one of a nonempty measurable characteristic function.** Let `X` be a measurable
space. Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x
|f(x)|`, zero on an empty source. if measurable `s` is nonempty, `‖indicator s‖∞=1`. -/
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

/-- **Uniform measurable simple-function approximation.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. for every `f : BoundedMeasurableFunction X` and `ε>0`, there
exists measurable simple `g : X → ℂ` with `‖f-ofSimpleFunc g‖∞<ε`. -/
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

/-- **Uniform finite-range bounded measurable approximation.** Let `X` be a measurable space.
Bounded measurable complex functions have pointwise equality and norm `‖f‖∞=sup_x |f(x)|`,
zero on an empty source. for every bounded measurable `f` and `ε>0`, there is bounded
measurable `g` with finite range and `‖f-g‖∞<ε`. -/
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
