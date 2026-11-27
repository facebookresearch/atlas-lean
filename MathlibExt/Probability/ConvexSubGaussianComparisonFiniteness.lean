/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexSubGaussianComparison
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Finiteness of the convex sub-Gaussian comparison constant

This file proves `historicalFinitenessUpperBound`: the convex sub-Gaussian comparison constant
`comparisonConstant` of `MathlibExt.Probability.ConvexSubGaussianComparison` is finite. The proof
shows that the variance factor `256` is admissible: every integrable real random variable `X` with
mean `0` and `P(|X| > t) ≤ 2 exp (-t ^ 2 / 2)` for all `t ≥ 0` is dominated in the convex order by
`16 G`, where `G` is a standard Gaussian. The factor `256` is far from sharp.

## Proof outline

* *Convex order from hinge comparisons.* Let `X` and `Y` be integrable random variables on
  probability spaces with the same mean such that `E (X - t)₊ ≤ E (Y - t)₊` and
  `E (-X - t)₊ ≤ E (-Y - t)₊` for every `t ≥ 0`. Let `f` be convex with right derivative `f'₊`
  and let `δ = 1 / (n + 1)`. On `[0, ∞)` let `gₙ` be the continuous piecewise affine function
  with `gₙ 0 = f 0` whose slope on `[k δ, (k + 1) δ]` is `f'₊ (k δ)` for `k < (n + 1) ^ 2` and is
  `f'₊ (n + 1)` beyond `n + 1`; on `(-∞, 0]` use the same construction for `z ↦ f (-z)`. Each
  `gₙ` is `f 0` plus a linear function plus a nonnegative combination of the hinges
  `x ↦ (x - t)₊` and `x ↦ (-x - t)₊` with `t ≥ 0`, so `E gₙ(X) ≤ E gₙ(Y)`. Tangent-line
  inequalities give `gₙ ≤ f` and `f x - gₙ x ≤ δ (f'₊ x - f'₊ 0)` for `0 ≤ x ≤ n + 1` (and the
  mirror bound for `x ≤ 0`), and dominated convergence gives `E f(X) ≤ E f(Y)` whenever `f(X)`
  and `f(Y)` are integrable.
* *The sub-Gaussian side.* By the layer-cake formula and `(t + s) ^ 2 ≥ t ^ 2 + s ^ 2`,
  `E (|X| - t)₊ ≤ √(2π) exp (-t ^ 2 / 2)` for `t ≥ 0`, and `(X - t)₊` and `(-X - t)₊` are at
  most `(|X| - t)₊`.
* *The Gaussian side.* Since `(16 g - t)₊ ≥ 8 g` for `g ≥ t / 8`, `E (16 G - t)₊ ≥ 8 φ (t / 8)`,
  where `φ` is the standard Gaussian density, and `√(2π) exp (-t ^ 2 / 2) ≤ 8 φ (t / 8)` because
  `π ≤ 4`. By the symmetry of `G` the same bound holds for `E (-16 G - t)₊`.

## Implementation notes

The theorem keeps the full name it had in the `WantedExt` module
`ConvexSubGaussianComparisonWanted`, whose remaining requests concern the sharp constant, so its
namespace is `MathlibExt.Probability.ConvexSubGaussianComparisonWanted`. All auxiliary
declarations are private.

## References

* R. van Handel, *On the subgaussian comparison theorem*, arXiv:2512.18588 (2025). The case
  `n = 1` of its Theorem 1.1 is the statement proved here; the proof in this file is a direct
  one-dimensional argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace MathlibExt.Probability.ConvexSubGaussianComparisonWanted

open MathlibExt.Probability.ConvexSubGaussianComparison

/-- The right derivative `x ↦ f'₊(x)`. -/
private noncomputable def rd (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (Ioi x) x

/-- Tangent-line inequality for a convex function and its right derivative. -/
private lemma convex_tangent_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x y : ℝ) :
    f x + rd f x * (y - x) ≤ f y := by
  rw [rd]
  have hx : x ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.rightDeriv_le_slope_of_mem_interior hx (mem_univ y) hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h1 := hf.slope_le_leftDeriv_of_mem_interior (mem_univ y) hx hyx
    have h2 := hf.leftDeriv_le_rightDeriv_of_mem_interior hx
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at h1
    have h3 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hyx.le)
    linarith

/-- The right derivative of a convex function on `ℝ` is monotone. -/
private lemma convex_rightDeriv_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    Monotone (rd f) := by
  have h := hf.monotoneOn_rightDeriv
  rw [interior_univ] at h
  exact fun x y hxy => h (mem_univ x) (mem_univ y) hxy

/-- A hinge as a difference with a minimum: `(x - a)₊ = x - min x a`. -/
private lemma max_sub_zero_eq_sub_min (x a : ℝ) : max (x - a) 0 = x - min x a := by
  rcases le_total x a with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_self]
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]

/-- The right half of the grid approximant, in hinge form: slope `D 0` from `0`, increased by
`D ((k + 1) δ) - D (k δ)` at each grid point `(k + 1) δ` with `k < N`. -/
private noncomputable def approxRight (D : ℝ → ℝ) (δ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  D 0 * max x 0 + ∑ k ∈ Finset.range N,
    (D (((k + 1 : ℕ) : ℝ) * δ) - D ((k : ℝ) * δ)) * max (x - ((k + 1 : ℕ) : ℝ) * δ) 0

/-- One more grid point adds one hinge. -/
private lemma approxRight_succ (D : ℝ → ℝ) (δ : ℝ) (n : ℕ) (x : ℝ) :
    approxRight D δ (n + 1) x = approxRight D δ n x +
      (D (((n + 1 : ℕ) : ℝ) * δ) - D ((n : ℝ) * δ)) * max (x - ((n + 1 : ℕ) : ℝ) * δ) 0 := by
  simp only [approxRight, Finset.sum_range_succ, add_assoc]

/-- Summation by parts: on the grid interval `[k δ, (k + 1) δ]` the approximant has slope
`D (k δ)`, and beyond `N δ` it has slope `D (N δ)`. -/
private lemma approxRight_eq_clamp (D : ℝ → ℝ) (δ : ℝ) (N : ℕ) (x : ℝ) :
    approxRight D δ N x = ∑ k ∈ Finset.range N, D ((k : ℝ) * δ) *
        (min x (((k + 1 : ℕ) : ℝ) * δ) - min x ((k : ℝ) * δ)) +
      D ((N : ℝ) * δ) * (x - min x ((N : ℝ) * δ)) := by
  induction N with
  | zero =>
    simp only [approxRight, Finset.range_zero, Finset.sum_empty, add_zero, CharP.cast_eq_zero,
      zero_mul, zero_add]
    rw [← max_sub_zero_eq_sub_min, sub_zero]
  | succ n ih =>
    rw [approxRight_succ, ih, Finset.sum_range_succ, max_sub_zero_eq_sub_min]
    ring

/-- The right approximant vanishes on `(-∞, 0]`. -/
private lemma approxRight_of_nonpos (D : ℝ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) {x : ℝ}
    (hx : x ≤ 0) : approxRight D δ N x = 0 := by
  rw [approxRight, max_eq_right hx, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : x - ((k + 1 : ℕ) : ℝ) * δ ≤ 0 := by
    have : 0 ≤ ((k + 1 : ℕ) : ℝ) * δ := by positivity
    linarith
  rw [max_eq_right this, mul_zero]

/-- For monotone `D` the extra hinges have nonnegative coefficients. -/
private lemma le_approxRight {D : ℝ → ℝ} (hD : Monotone D) {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ)
    (x : ℝ) : D 0 * max x 0 ≤ approxRight D δ N x := by
  rw [approxRight]
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => mul_nonneg ?_ (le_max_right _ _))
  refine sub_nonneg.mpr (hD ?_)
  have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
  exact mul_le_mul_of_nonneg_right this hδ

/-- On `[0, ∞)`, `f 0` plus the right approximant built from the right derivative `f'₊` of
`f` lies below `f`, and within `δ (f'₊ x - f'₊ 0)` of `f x` when `x ≤ N δ`. -/
private lemma approxRight_bounds {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    f 0 + approxRight (rd f) δ N x ≤ f x ∧
      (x ≤ (N : ℝ) * δ → f x ≤ f 0 + approxRight (rd f) δ N x + δ * (rd f x - rd f 0)) := by
  set D : ℝ → ℝ := rd f
  have hD : Monotone D := convex_rightDeriv_mono hf
  have htan : ∀ a b, f a + D a * (b - a) ≤ f b := convex_tangent_le hf
  set c : ℕ → ℝ := fun k => min x ((k : ℝ) * δ) with hc_def
  have hc0 : c 0 = 0 := by simp [hc_def, hx]
  have hterm : ∀ k : ℕ, 0 ≤ f (c (k + 1)) - f (c k) - D ((k : ℝ) * δ) * (c (k + 1) - c k) ∧
      f (c (k + 1)) - f (c k) - D ((k : ℝ) * δ) * (c (k + 1) - c k) ≤
        δ * (D (c (k + 1)) - D (c k)) := by
    intro k
    set a : ℝ := (k : ℝ) * δ with ha
    set b : ℝ := ((k + 1 : ℕ) : ℝ) * δ with hb
    have hab : b - a = δ := by
      rw [ha, hb]
      push_cast
      ring
    have hck : c k = min x a := rfl
    have hck1 : c (k + 1) = min x b := rfl
    rw [hck, hck1]
    rcases le_or_gt x a with hxa | hax
    · have hxb : x ≤ b := hxa.trans (by linarith)
      rw [min_eq_left hxa, min_eq_left hxb]
      simp
    · rw [min_eq_right hax.le]
      have hm1 : a ≤ min x b := le_min hax.le (by linarith)
      have hm2 : min x b - a ≤ δ := by
        have := min_le_right x b
        linarith
      refine ⟨by linarith [htan a (min x b)], ?_⟩
      have h1 := htan (min x b) a
      have h2 : 0 ≤ D (min x b) - D a := sub_nonneg.mpr (hD hm1)
      have h3 := mul_le_mul_of_nonneg_left hm2 h2
      nlinarith
  have hlast : 0 ≤ f x - f (c N) - D ((N : ℝ) * δ) * (x - c N) ∧
      (x ≤ (N : ℝ) * δ → f x - f (c N) - D ((N : ℝ) * δ) * (x - c N) = 0) := by
    have hcN : c N = min x ((N : ℝ) * δ) := rfl
    rw [hcN]
    refine ⟨?_, fun h => by simp [min_eq_left h]⟩
    rcases le_or_gt x ((N : ℝ) * δ) with h | h
    · rw [min_eq_left h]
      simp
    · rw [min_eq_right h.le]
      linarith [htan ((N : ℝ) * δ) x]
  have htel : f x - f 0 = ∑ k ∈ Finset.range N, (f (c (k + 1)) - f (c k)) + (f x - f (c N)) := by
    rw [Finset.sum_range_sub (fun k => f (c k)), hc0]
    ring
  have hDtel : ∑ k ∈ Finset.range N, (D (c (k + 1)) - D (c k)) = D (c N) - D (c 0) :=
    Finset.sum_range_sub (fun k => D (c k)) N
  have hdecomp : f x - f 0 - approxRight D δ N x =
      ∑ k ∈ Finset.range N, (f (c (k + 1)) - f (c k) - D ((k : ℝ) * δ) * (c (k + 1) - c k)) +
        (f x - f (c N) - D ((N : ℝ) * δ) * (x - c N)) := by
    have hclamp : approxRight D δ N x =
        ∑ k ∈ Finset.range N, D ((k : ℝ) * δ) * (c (k + 1) - c k) +
          D ((N : ℝ) * δ) * (x - c N) :=
      approxRight_eq_clamp D δ N x
    have hsplit : ∑ k ∈ Finset.range N,
        (f (c (k + 1)) - f (c k) - D ((k : ℝ) * δ) * (c (k + 1) - c k)) =
          ∑ k ∈ Finset.range N, (f (c (k + 1)) - f (c k)) -
            ∑ k ∈ Finset.range N, D ((k : ℝ) * δ) * (c (k + 1) - c k) :=
      Finset.sum_sub_distrib _ _
    rw [hclamp, htel, hsplit]
    ring
  constructor
  · have : 0 ≤ f x - f 0 - approxRight D δ N x := by
      rw [hdecomp]
      exact add_nonneg (Finset.sum_nonneg fun k _ => (hterm k).1) hlast.1
    linarith
  · intro hxN
    have hsum : ∑ k ∈ Finset.range N,
        (f (c (k + 1)) - f (c k) - D ((k : ℝ) * δ) * (c (k + 1) - c k)) ≤
          δ * (D (c N) - D (c 0)) := by
      rw [← hDtel, Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => (hterm k).2
    have hcN : c N = x := min_eq_left hxN
    rw [hcN, hc0] at hsum
    have := hlast.2 hxN
    have hfin : f x - f 0 - approxRight D δ N x ≤ δ * (D x - D 0) := by
      rw [hdecomp]
      linarith
    linarith

/-- Reflecting a convex function keeps it convex. -/
private lemma convexOn_comp_neg {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (fun z => f (-z)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have e : -(a • x + b • y) = a • (-x) + b • (-y) := by
    simp only [smul_eq_mul]
    ring
  change f (-(a • x + b • y)) ≤ a • f (-x) + b • f (-y)
  rw [e]
  exact hf.2 (mem_univ _) (mem_univ _) ha hb hab

/-- The `n`-th approximant of `f`, with grid step `1 / (n + 1)` on `[-(n + 1), n + 1]`: the
right half comes from `f`, the left half from `z ↦ f (-z)`. -/
private noncomputable def approx (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f 0 + approxRight (rd f) (1 / ((n : ℝ) + 1)) ((n + 1) * (n + 1)) x +
    approxRight (rd fun z => f (-z)) (1 / ((n : ℝ) + 1)) ((n + 1) * (n + 1)) (-x)

/-- The approximants lie below `f`. -/
private lemma approx_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (n : ℕ) (x : ℝ) :
    approx f n x ≤ f x := by
  have hδ : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  rcases le_total 0 x with hx | hx
  · rw [approx, approxRight_of_nonpos _ hδ _ (by linarith : -x ≤ 0), add_zero]
    exact (approxRight_bounds hf hδ _ hx).1
  · rw [approx, approxRight_of_nonpos _ hδ _ hx, add_zero]
    have := (approxRight_bounds (convexOn_comp_neg hf) hδ ((n + 1) * (n + 1))
      (by linarith : (0 : ℝ) ≤ -x)).1
    simpa using this

/-- The approximants lie above a function of linear growth. -/
private lemma approx_ge {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (n : ℕ) (x : ℝ) :
    f 0 + rd f 0 * max x 0 + rd (fun z => f (-z)) 0 * max (-x) 0 ≤ approx f n x := by
  have hδ : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h1 := le_approxRight (convex_rightDeriv_mono hf) hδ ((n + 1) * (n + 1)) x
  have h2 := le_approxRight (convex_rightDeriv_mono (convexOn_comp_neg hf)) hδ
    ((n + 1) * (n + 1)) (-x)
  rw [approx]
  linarith

/-- The approximants converge pointwise to `f`. -/
private lemma approx_tendsto {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    Tendsto (fun n => approx f n x) atTop (𝓝 (f x)) := by
  set M : ℝ := |rd f x - rd f 0| + |rd (fun z => f (-z)) (-x) - rd (fun z => f (-z)) 0|
  have hlow : Tendsto (fun n : ℕ => f x - 1 / ((n : ℝ) + 1) * M) atTop (𝓝 (f x)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const M
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => approx_le hf n x)
  rw [eventually_atTop]
  refine ⟨⌈|x|⌉₊, fun n hn => ?_⟩
  have hδ : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hN : (((n + 1) * (n + 1) : ℕ) : ℝ) * (1 / ((n : ℝ) + 1)) = (n : ℝ) + 1 := by
    push_cast
    field_simp
  have hxn : |x| ≤ (n : ℝ) + 1 := by
    have h1 : |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈|x|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rcases le_total 0 x with hx | hx
  · have hb := (approxRight_bounds hf hδ ((n + 1) * (n + 1)) hx).2
      (by rw [hN]; linarith [le_abs_self x])
    rw [approx, approxRight_of_nonpos _ hδ _ (by linarith : -x ≤ 0), add_zero]
    have : 1 / ((n : ℝ) + 1) * (rd f x - rd f 0) ≤ 1 / ((n : ℝ) + 1) * M := by
      refine mul_le_mul_of_nonneg_left ?_ hδ
      exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    linarith
  · have hb := (approxRight_bounds (convexOn_comp_neg hf) hδ ((n + 1) * (n + 1))
      (by linarith : (0 : ℝ) ≤ -x)).2 (by rw [hN]; linarith [neg_abs_le x])
    rw [approx, approxRight_of_nonpos _ hδ _ hx, add_zero]
    simp only [neg_neg, neg_zero] at hb
    have : 1 / ((n : ℝ) + 1) * (rd (fun z => f (-z)) (-x) - rd (fun z => f (-z)) 0) ≤
        1 / ((n : ℝ) + 1) * M := by
      refine mul_le_mul_of_nonneg_left ?_ hδ
      exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    linarith

section HingeGood

variable {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]

/-- A good test function `φ`: `φ ∘ X` and `φ ∘ Y` are integrable and
`∫ φ ∘ X ≤ ∫ φ ∘ Y`. -/
private def HingeGood (μX : Measure ΩX) (X : ΩX → ℝ) (μY : Measure ΩY) (Y : ΩY → ℝ)
    (φ : ℝ → ℝ) : Prop :=
  Integrable (fun ω => φ (X ω)) μX ∧ Integrable (fun ω => φ (Y ω)) μY ∧
    ∫ ω, φ (X ω) ∂μX ≤ ∫ ω, φ (Y ω) ∂μY

variable {μX : Measure ΩX} {X : ΩX → ℝ} {μY : Measure ΩY} {Y : ΩY → ℝ}

/-- Sums of good test functions are good. -/
private lemma HingeGood.add {φ ψ : ℝ → ℝ} (hφ : HingeGood μX X μY Y φ)
    (hψ : HingeGood μX X μY Y ψ) : HingeGood μX X μY Y (fun x => φ x + ψ x) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, by
    rw [integral_add hφ.1 hψ.1, integral_add hφ.2.1 hψ.2.1]
    exact add_le_add hφ.2.2 hψ.2.2⟩

/-- Nonnegative multiples of good test functions are good. -/
private lemma HingeGood.const_mul {φ : ℝ → ℝ} (hφ : HingeGood μX X μY Y φ) {c : ℝ}
    (hc : 0 ≤ c) : HingeGood μX X μY Y (fun x => c * φ x) :=
  ⟨hφ.1.const_mul c, hφ.2.1.const_mul c, by
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hφ.2.2 hc⟩

/-- Goodness depends only on the values of the test function. -/
private lemma HingeGood.congr {φ ψ : ℝ → ℝ} (h : ∀ x, φ x = ψ x)
    (hφ : HingeGood μX X μY Y φ) : HingeGood μX X μY Y ψ := by
  have : φ = ψ := funext h
  subst this
  exact hφ

/-- Finite sums of good test functions are good. -/
private lemma HingeGood.sum {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i ∈ s, HingeGood μX X μY Y (φ i)) :
    HingeGood μX X μY Y (fun x => ∑ i ∈ s, φ i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine HingeGood.congr (φ := fun _ => 0) (fun x => by simp) ?_
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, by simp⟩
  | insert i s hi ih =>
    have h := (hφ i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hφ j (Finset.mem_insert_of_mem hj))
    exact HingeGood.congr (fun x => (Finset.sum_insert hi).symm) h

/-- Constants are good test functions for probability measures. -/
private lemma HingeGood.const [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (c : ℝ) :
    HingeGood μX X μY Y (fun _ => c) :=
  ⟨integrable_const c, integrable_const c, by simp⟩

/-- Linear functions are good test functions when the means agree. -/
private lemma HingeGood.linear (hX : Integrable X μX) (hY : Integrable Y μY)
    (hmean : ∫ ω, X ω ∂μX = ∫ ω, Y ω ∂μY) (β : ℝ) :
    HingeGood μX X μY Y (fun x => β * x) :=
  ⟨hX.const_mul β, hY.const_mul β, by rw [integral_const_mul, integral_const_mul, hmean]⟩

end HingeGood

/-- The right derivative of `z ↦ f (-z)` at `0` is at least `-f'₊ 0`. -/
private lemma neg_rd_comp_neg_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    -rd (fun z => f (-z)) 0 ≤ rd f 0 := by
  have h := hf.rightDeriv_eq_sInf_slope_of_mem_interior (x := 0) (by simp)
  rw [show rd f 0 = derivWithin f (Ioi 0) 0 from rfl, h]
  refine le_csInf ⟨slope f 0 1, 1, ⟨mem_univ _, one_pos⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
  have ht := convex_tangent_le (convexOn_comp_neg hf) 0 (-y)
  simp only [neg_zero, neg_neg] at ht
  rw [slope_def_field, sub_zero, le_div_iff₀ hy]
  linarith

/-- Convex domination from hinge comparisons: equal means and `E (X - t)₊ ≤ E (Y - t)₊`,
`E (-X - t)₊ ≤ E (-Y - t)₊` for all `t ≥ 0` give `X ≤ Y` in the convex order. -/
private theorem convexDominated_of_hinge {ΩX ΩY : Type*} [MeasurableSpace ΩX]
    [MeasurableSpace ΩY] {μX : Measure ΩX} {μY : Measure ΩY} [IsProbabilityMeasure μX]
    [IsProbabilityMeasure μY] {X : ΩX → ℝ} {Y : ΩY → ℝ} (hX : Integrable X μX)
    (hY : Integrable Y μY) (hmean : ∫ ω, X ω ∂μX = ∫ ω, Y ω ∂μY)
    (hright : ∀ t : ℝ, 0 ≤ t → ∫ ω, max (X ω - t) 0 ∂μX ≤ ∫ ω, max (Y ω - t) 0 ∂μY)
    (hleft : ∀ t : ℝ, 0 ≤ t → ∫ ω, max (-X ω - t) 0 ∂μX ≤ ∫ ω, max (-Y ω - t) 0 ∂μY) :
    ConvexDominated μX X μY Y := by
  intro f hf hfX hfY
  have hg := convexOn_comp_neg hf
  have hDf := convex_rightDeriv_mono hf
  have hDg := convex_rightDeriv_mono hg
  have hR : ∀ t : ℝ, 0 ≤ t → HingeGood μX X μY Y (fun x => max (x - t) 0) := fun t ht =>
    ⟨(hX.sub (integrable_const t)).pos_part, (hY.sub (integrable_const t)).pos_part,
      hright t ht⟩
  have hL : ∀ t : ℝ, 0 ≤ t → HingeGood μX X μY Y (fun x => max (-x - t) 0) := fun t ht =>
    ⟨(hX.neg.sub (integrable_const t)).pos_part, (hY.neg.sub (integrable_const t)).pos_part,
      hleft t ht⟩
  have hc0 : 0 ≤ rd f 0 + rd (fun z => f (-z)) 0 := by
    linarith [neg_rd_comp_neg_le hf]
  have hgood : ∀ n : ℕ, HingeGood μX X μY Y (approx f n) := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 ≤ δ := by positivity
    have hknot : ∀ k : ℕ, (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := fun k =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hδ
    have hsum : ∀ D : ℝ → ℝ, Monotone D →
        HingeGood μX X μY Y (fun x => approxRight D δ ((n + 1) * (n + 1)) x - D 0 * max x 0) ∧
        HingeGood μX X μY Y
          (fun x => approxRight D δ ((n + 1) * (n + 1)) (-x) - D 0 * max (-x) 0) := by
      intro D hD
      constructor
      · refine HingeGood.congr (fun x => ?_) (HingeGood.sum (Finset.range ((n + 1) * (n + 1)))
          (φ := fun k x => (D (((k + 1 : ℕ) : ℝ) * δ) - D ((k : ℝ) * δ)) *
            max (x - ((k + 1 : ℕ) : ℝ) * δ) 0)
          fun k _ => (hR _ (by positivity)).const_mul (sub_nonneg.mpr (hD (hknot k))))
        simp only [approxRight]
        ring
      · refine HingeGood.congr (fun x => ?_) (HingeGood.sum (Finset.range ((n + 1) * (n + 1)))
          (φ := fun k x => (D (((k + 1 : ℕ) : ℝ) * δ) - D ((k : ℝ) * δ)) *
            max (-x - ((k + 1 : ℕ) : ℝ) * δ) 0)
          fun k _ => (hL _ (by positivity)).const_mul (sub_nonneg.mpr (hD (hknot k))))
        simp only [approxRight]
        ring
    have hbase : HingeGood μX X μY Y (fun x => f 0 + rd f 0 * x +
        (rd f 0 + rd (fun z => f (-z)) 0) * max (-x) 0) := by
      refine ((HingeGood.const (f 0)).add (HingeGood.linear hX hY hmean (rd f 0))).add ?_
      exact ((hL 0 le_rfl).const_mul hc0).congr fun x => by rw [sub_zero]
    refine HingeGood.congr (fun x => ?_) ((hbase.add (hsum _ hDf).1).add (hsum _ hDg).2)
    have hmax := max_zero_sub_max_neg_zero_eq_self x
    simp only [approx]
    linear_combination (-(rd f 0)) * hmax
  have hbound : ∀ n : ℕ, ∀ x : ℝ, ‖approx f n x‖ ≤
      |f 0| + (|rd f 0| + |rd (fun z => f (-z)) 0|) * |x| + |f x| := by
    intro n x
    have hle := approx_le hf n x
    have hge := approx_ge hf n x
    have h1 : |rd f 0 * max x 0| ≤ |rd f 0| * |x| := by
      rw [abs_mul, abs_of_nonneg (le_max_right x 0)]
      exact mul_le_mul_of_nonneg_left (max_le (le_abs_self x) (abs_nonneg x)) (abs_nonneg _)
    have h2 : |rd (fun z => f (-z)) 0 * max (-x) 0| ≤ |rd (fun z => f (-z)) 0| * |x| := by
      rw [abs_mul, abs_of_nonneg (le_max_right (-x) 0)]
      exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs x) (abs_nonneg x)) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (rd f 0 * max x 0), neg_abs_le (rd (fun z => f (-z)) 0 * max (-x) 0),
        neg_abs_le (f 0), abs_nonneg (f x)]
    · linarith [le_abs_self (f x), abs_nonneg (f 0), abs_nonneg x, abs_nonneg (rd f 0),
        abs_nonneg (rd (fun z => f (-z)) 0),
        mul_nonneg (add_nonneg (abs_nonneg (rd f 0)) (abs_nonneg (rd (fun z => f (-z)) 0)))
          (abs_nonneg x)]
  have hlimX : Tendsto (fun n => ∫ ω, approx f n (X ω) ∂μX) atTop
      (𝓝 (∫ ω, f (X ω) ∂μX)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => |f 0| + (|rd f 0| + |rd (fun z => f (-z)) 0|) * |X ω| + |f (X ω)|)
      (fun n => (hgood n).1.aestronglyMeasurable) ?_
      (fun n => Eventually.of_forall fun ω => hbound n (X ω))
      (Eventually.of_forall fun ω => approx_tendsto hf (X ω))
    exact ((integrable_const _).add (hX.abs.const_mul _)).add hfX.abs
  have hlimY : Tendsto (fun n => ∫ ω, approx f n (Y ω) ∂μY) atTop
      (𝓝 (∫ ω, f (Y ω) ∂μY)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => |f 0| + (|rd f 0| + |rd (fun z => f (-z)) 0|) * |Y ω| + |f (Y ω)|)
      (fun n => (hgood n).2.1.aestronglyMeasurable) ?_
      (fun n => Eventually.of_forall fun ω => hbound n (Y ω))
      (Eventually.of_forall fun ω => approx_tendsto hf (Y ω))
    exact ((integrable_const _).add (hY.abs.const_mul _)).add hfY.abs
  exact le_of_tendsto_of_tendsto' hlimX hlimY fun n => (hgood n).2.2

/-- Layer-cake bound on the excess of `|X|` over `t`. -/
private lemma integral_max_abs_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : IsOneSubGaussianTail μ X) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, max (|X ω| - t) 0 ∂μ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) := by
  have hint : Integrable (fun ω => max (|X ω| - t) 0) μ :=
    (hX.integrable.abs.sub (integrable_const t)).pos_part
  have hnn : 0 ≤ᵐ[μ] fun ω => max (|X ω| - t) 0 :=
    Eventually.of_forall fun ω => le_max_right _ _
  rw [integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [lintegral_eq_lintegral_meas_lt μ hnn hint.aemeasurable]
  have hgi : Integrable
      (fun s : ℝ => 2 * Real.exp (-t ^ 2 / 2) * Real.exp (-(1 / 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  calc ∫⁻ s in Ioi 0, μ {ω | s < max (|X ω| - t) 0}
      ≤ ∫⁻ s in Ioi 0,
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2) * Real.exp (-(1 / 2) * s ^ 2)) := by
        refine setLIntegral_mono (by fun_prop) fun s hs => ?_
        have hs : 0 < s := hs
        have hset : {ω | s < max (|X ω| - t) 0} = {ω | |X ω| > t + s} := by
          ext ω
          simp only [mem_ofPred_eq, lt_max_iff, gt_iff_lt]
          constructor
          · rintro (h | h)
            · linarith
            · exact absurd h (not_lt.mpr hs.le)
          · intro h
            left
            linarith
        rw [hset]
        refine (hX.tail_le (t + s) (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [mul_assoc, ← Real.exp_add]
        gcongr
        nlinarith [mul_nonneg ht hs.le]
    _ = ENNReal.ofReal
          (∫ s in Ioi 0, 2 * Real.exp (-t ^ 2 / 2) * Real.exp (-(1 / 2) * s ^ 2)) :=
        (ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
          (Eventually.of_forall fun s => by positivity)).symm
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2)) := by
        rw [integral_const_mul, integral_gaussian_Ioi,
          show Real.pi / (1 / 2) = 2 * Real.pi by ring]
        congr 1
        ring

/-- `∫_c^∞ x exp (-x ^ 2 / 2) dx = exp (-c ^ 2 / 2)`. -/
private lemma integral_Ioi_mul_exp_neg_sq_div_two (c : ℝ) :
    ∫ x in Ioi c, x * Real.exp (-x ^ 2 / 2) = Real.exp (-c ^ 2 / 2) := by
  have hderiv : ∀ x ∈ Ioi c, HasDerivAt (fun x => -Real.exp (-x ^ 2 / 2))
      (x * Real.exp (-x ^ 2 / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (-1 / 2 : ℝ)
      convert h using 1
      · ext y
        ring
      · norm_num
        ring
    convert h1.exp.fun_neg using 1
    ring
  have hint : IntegrableOn (fun x => x * Real.exp (-x ^ 2 / 2)) (Ioi c) := by
    have h := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    have e : (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2)) =
        fun x => x * Real.exp (-x ^ 2 / 2) := by
      ext x
      congr 2
      ring
    rw [e] at h
    exact h.integrableOn
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot := by
      refine Tendsto.atBot_div_const two_pos ?_
      exact tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
    simpa using (Real.tendsto_exp_atBot.comp h1).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop : Continuous fun x : ℝ =>
    -Real.exp (-x ^ 2 / 2)).continuousWithinAt hderiv hint hlim]
  ring

/-- A standard Gaussian variable is integrable. -/
private lemma integrable_id_gaussianReal_zero_one :
    Integrable (fun g : ℝ => g) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)

/-- `E [G; G ≥ c] = φ c` for a standard Gaussian `G` with density `φ`. -/
private lemma integral_indicator_Ici_gaussianReal (c : ℝ) :
    ∫ g, (Ici c).indicator (fun g => g) g ∂gaussianReal 0 1 =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c ^ 2 / 2) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ g : ℝ, gaussianPDFReal 0 1 g • (Ici c).indicator (fun g => g) g =
      (Ici c).indicator
        (fun g => (Real.sqrt (2 * Real.pi))⁻¹ * (g * Real.exp (-g ^ 2 / 2))) g := by
    intro g
    by_cases hg : g ∈ Ici c
    · simp only [indicator_of_mem hg, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
        smul_eq_mul]
      ring
    · simp [indicator_of_notMem hg]
  simp_rw [h]
  rw [integral_indicator measurableSet_Ici, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_Ioi_mul_exp_neg_sq_div_two]

/-- Lower bound for the hinge expectations of `16 G`. -/
private lemma gaussian_hinge_lower (t : ℝ) :
    8 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / 8) ^ 2 / 2)) ≤
      ∫ g, max (16 * g - t) 0 ∂gaussianReal 0 1 := by
  have hid := integrable_id_gaussianReal_zero_one
  rw [← integral_indicator_Ici_gaussianReal (t / 8), ← integral_const_mul]
  refine integral_mono ((hid.indicator measurableSet_Ici).const_mul 8)
    ((hid.const_mul 16).sub (integrable_const t)).pos_part fun g => ?_
  by_cases hg : g ∈ Ici (t / 8)
  · rw [indicator_of_mem hg]
    have : t / 8 ≤ g := hg
    exact le_max_of_le_left (by linarith)
  · rw [indicator_of_notMem hg, mul_zero]
    exact le_max_right _ _

/-- The hinge expectations of `-16 G` and `16 G` agree. -/
private lemma gaussian_hinge_neg (t : ℝ) :
    ∫ g, max (-(16 * g) - t) 0 ∂gaussianReal 0 1 =
      ∫ g, max (16 * g - t) 0 ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  calc ∫ g, max (-(16 * g) - t) 0 ∂gaussianReal 0 1
      = ∫ g, (fun y => max (16 * y - t) 0) (-g) ∂gaussianReal 0 1 := by
        simp only [mul_neg]
    _ = ∫ y, max (16 * y - t) 0 ∂(gaussianReal 0 1).map (fun x => -x) :=
        (integral_map measurable_neg.aemeasurable
          (by fun_prop : Continuous fun y : ℝ => max (16 * y - t) 0).aestronglyMeasurable).symm
    _ = ∫ g, max (16 * g - t) 0 ∂gaussianReal 0 1 := by rw [hmap]

/-- The sub-Gaussian bound is below the Gaussian bound, since `π ≤ 4`. -/
private lemma sqrt_two_pi_mul_exp_le (t : ℝ) :
    Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) ≤
      8 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / 8) ^ 2 / 2)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hpi
  have hss : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt hpi.le
  have h1 : Real.exp (-t ^ 2 / 2) ≤ Real.exp (-(t / 8) ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have h2 : 2 * Real.pi ≤ 8 := by linarith [Real.pi_le_four]
  have key : 2 * Real.pi * Real.exp (-t ^ 2 / 2) ≤ 8 * Real.exp (-(t / 8) ^ 2 / 2) :=
    calc 2 * Real.pi * Real.exp (-t ^ 2 / 2) ≤ 8 * Real.exp (-t ^ 2 / 2) := by gcongr
      _ ≤ 8 * Real.exp (-(t / 8) ^ 2 / 2) := by gcongr
  have e : Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * (2 * Real.pi * Real.exp (-t ^ 2 / 2)) := by
    rw [eq_inv_mul_iff_mul_eq₀ hs.ne', ← mul_assoc, hss]
  rw [e]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * (2 * Real.pi * Real.exp (-t ^ 2 / 2))
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (8 * Real.exp (-(t / 8) ^ 2 / 2)) := by gcongr
    _ = 8 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / 8) ^ 2 / 2)) := by ring

/-- The variance factor `256` is admissible. -/
private theorem isAdmissibleConstant_256 : IsAdmissibleConstant 256 := by
  refine ⟨by simp, by simp, fun Ω _ μ _ X hX => ?_⟩
  have h16 : Real.sqrt (256 : ENNReal).toReal = 16 := by
    rw [ENNReal.toReal_ofNat, show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [h16]
  have hY : Integrable (fun g : ℝ => 16 * g) (gaussianReal 0 1) :=
    integrable_id_gaussianReal_zero_one.const_mul 16
  refine convexDominated_of_hinge hX.integrable hY ?_ ?_ ?_
  · rw [hX.mean_zero, integral_const_mul, integral_id_gaussianReal, mul_zero]
  · intro t ht
    calc ∫ ω, max (X ω - t) 0 ∂μ ≤ ∫ ω, max (|X ω| - t) 0 ∂μ :=
          integral_mono (hX.integrable.sub (integrable_const t)).pos_part
            (hX.integrable.abs.sub (integrable_const t)).pos_part
            fun ω => max_le_max (by linarith [le_abs_self (X ω)]) le_rfl
      _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) := integral_max_abs_sub_le hX ht
      _ ≤ 8 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / 8) ^ 2 / 2)) :=
          sqrt_two_pi_mul_exp_le t
      _ ≤ ∫ g, max (16 * g - t) 0 ∂gaussianReal 0 1 := gaussian_hinge_lower t
  · intro t ht
    calc ∫ ω, max (-X ω - t) 0 ∂μ ≤ ∫ ω, max (|X ω| - t) 0 ∂μ :=
          integral_mono (hX.integrable.neg.sub (integrable_const t)).pos_part
            (hX.integrable.abs.sub (integrable_const t)).pos_part
            fun ω => max_le_max (by linarith [neg_le_abs (X ω)]) le_rfl
      _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) := integral_max_abs_sub_le hX ht
      _ ≤ 8 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / 8) ^ 2 / 2)) :=
          sqrt_two_pi_mul_exp_le t
      _ ≤ ∫ g, max (16 * g - t) 0 ∂gaussianReal 0 1 := gaussian_hinge_lower t
      _ = ∫ g, max (-(16 * g) - t) 0 ∂gaussianReal 0 1 := (gaussian_hinge_neg t).symm

/-- **Finiteness of the convex sub-Gaussian comparison constant.** The comparison constant is
finite. Here the comparison constant is the infimum, in $[0, \infty]$, of the variance factors
$C \in (0, \infty)$ such that every real random variable $X$ on a probability space that is
integrable, has mean zero and satisfies $P(|X| > t) \le 2e^{-t^2/2}$ for all $t \ge 0$ satisfies
$E f(X) \le E f(\sqrt{C}\,G)$ for every convex $f : \mathbb{R} \to \mathbb{R}$ for which both
expectations are finite, where $G$ is a standard Gaussian. Equivalently, such a factor $C$ exists.

Source: van Handel (2025), historical one-dimensional finiteness consequence. -/
theorem historicalFinitenessUpperBound :
    comparisonConstant ≠ ⊤ := fun h =>
  comparisonConstant_eq_top_iff.mp h 256 isAdmissibleConstant_256

end MathlibExt.Probability.ConvexSubGaussianComparisonWanted
