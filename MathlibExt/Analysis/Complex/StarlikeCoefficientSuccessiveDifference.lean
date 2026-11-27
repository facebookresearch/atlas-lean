/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Analysis.Complex.Wiman
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Research Problems in Function Theory — Problem 6.46

This file proves Leung's theorem `conjecture_holds`: if $f(z) = z + a_2 z^2 + \cdots$ is
analytic on the open unit disc, normalized by $f(0) = 0$ and $f'(0) = 1$, univalent and
starlike, then its Taylor coefficients satisfy $\bigl| |a_{n+1}| - |a_n| \bigr| \le 1$ for every
$n \ge 1$. This answers Problem 6.46 of Hayman and Lingham affirmatively.

Source clause list (every item appears in the formal text below):
1. `f` is in the class `S`: analytic in the unit disc, normalized by
  `f 0 = 0` and `f'(0) = 1`, and univalent (injective) on the unit disc.
2. `f` is star-like: `Re (z * f'(z) / f z) > 0` for `z ≠ 0` in the unit disc.
3. `a n` denotes the Taylor coefficient of `f` at `0`
  (`iteratedDeriv n f 0 / n!`).
4. Quantifier domain: all such `f`, all `n : ℕ` with `1 ≤ n`.
5. Questioned bound: `‖ |a (n+1)| - |a n| ‖ ≤ 1`, stated as the
  source's question (the `Prop` `conjecture`), proved as `conjecture_holds`.

## Main results

* `conjecture`: the statement of the successive coefficient bound for starlike functions.
* `conjecture_holds`: the statement holds (Leung, 1978).

## Proof outline

We follow Leung's argument as presented by Arora, Ponnusamy and Sahoo (Lemma 3.1 and the proof
of Theorem 1.1 of the reference below, with `α = γ = 0`).

* Let `p z = z f'(z) / f(z)` for `z ≠ 0` and `p 0 = 1`, that is `p = f' / dslope f 0`. It is
  analytic on the disc with `Re p > 0`; the starlikeness condition already forces `f z ≠ 0` for
  `z ≠ 0`, so injectivity is not used. Writing `c k` for the Taylor coefficients of `p` and `a k`
  for those of `f`, the Leibniz rule applied to `z f'(z) = p(z) f(z)` gives
  `m a m = ∑_{i ≤ m} c i a (m - i)`.
* Fix `0 < r < 1` and `n`. Integrating `Re p(r e^{iθ})` against the trigonometric polynomial
  `S θ = ∑_{k=1}^n Re (c k r^k e^{ikθ}) / k` and using the Cauchy integral formula gives
  `π ∑_{k=1}^n |c k|² r^{2k} / k`, while `∫ Re p(r e^{iθ}) dθ = 2π`. As `Re p > 0`, some `θ`
  satisfies `∑_{k=1}^n |c k|² r^{2k} / (2k) ≤ S θ`.
* With `x = e^{-iθ}`, the numbers `b m = a (m + 1) r^m - x a m r^(m-1)`, the Taylor
  coefficients of `(1 - x z) f(r z) / (r z)`, satisfy `b 0 = 1` and
  `m b m = ∑_{k=1}^m (c k r^k - x^k) b (m - k)`. The third Lebedev–Milin inequality gives
  `|b n|² ≤ exp (∑_{k=1}^n (|c k r^k - x^k|² - 1) / k)`, and the exponent equals
  `2 ∑_{k=1}^n (|c k|² r^{2k} / (2k) - Re (c k r^k e^{ikθ}) / k) ≤ 0`. Hence
  `| |a (n+1)| r^n - |a n| r^(n-1) | ≤ |b n| ≤ 1`, and we let `r → 1`.
* The Lebedev–Milin inequalities are proved from the recursion: the Cauchy–Schwarz inequality
  gives `m² |β m|² ≤ (∑_{k=1}^m |w k|²) (∑_{j<m} |β j|²)`, induction on `n` gives the second
  inequality `∑_{j ≤ n} |β j|² ≤ (n + 1) exp (∑_{k=1}^n (1 - k / (n + 1)) (|w k|² - 1) / k)`,
  and the third follows from it and `1 + y ≤ exp y`.

## Implementation notes

The definitions `IsInClassS`, `IsStarlike` and `conjecture` and the theorem `conjecture_holds`
keep the full names they had in the former wanted module, so the namespace still reads
`StarlikeCoefficientSuccessiveDifferenceWanted`.

## References

* V. Arora, S. Ponnusamy and S. K. Sahoo, *Successive coefficients for spirallike and related
  functions*, https://arxiv.org/abs/1903.10232. Its Theorem A is Leung's theorem (Y. Leung,
  Bull. London Math. Soc. 10 (1978), 193–196); its Lemma 3.1 and the proof of its Theorem 1.1
  give the argument followed here.
-/

@[expose] public section

namespace MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted

open Complex (wimanTaylorCoefficient)

/-- **Normalized univalent functions (the class $S$).** A function $f : \mathbb{C} \to \mathbb{C}$
is in the class $S$ when it is analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$,
satisfies $f(0) = 0$ and $f'(0) = 1$, and is injective on $\mathbb{D}$.

Source: Hayman and Lingham, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def IsInClassS (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    f 0 = 0 ∧ HasDerivAt f 1 0 ∧ Set.InjOn f (Metric.ball (0 : ℂ) 1)

/-- **Starlike functions on the unit disc.** A function $f : \mathbb{C} \to \mathbb{C}$ is
starlike when it is analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$ and, for every
$z \ne 0$ in $\mathbb{D}$, $f(z) \ne 0$ and $\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$.

Source: Hayman, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def IsStarlike (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → 0 < (z * deriv f z / f z).re

/-- **Hayman's successive coefficient problem for starlike functions.** The statement that for
every function $f : \mathbb{C} \to \mathbb{C}$ in the class $S$ (analytic on the open unit disc
$\mathbb{D} = \{z : |z| < 1\}$, with $f(0) = 0$ and $f'(0) = 1$, and injective on $\mathbb{D}$)
that is moreover starlike ($\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$ for every $z \ne 0$
in $\mathbb{D}$), the Taylor coefficients $a_n = f^{(n)}(0) / n!$ of $f$ at $0$ satisfy
$\bigl| |a_{n+1}| - |a_n| \bigr| \le 1$ for every natural number $n \ge 1$.

Source: Hayman and Lingham, Research Problems in Function Theory (2018), Problem 6.46,
https://arxiv.org/abs/1809.07200. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, IsInClassS f → IsStarlike f →
    ∀ n : ℕ, 1 ≤ n → |‖wimanTaylorCoefficient f (n + 1)‖ - ‖wimanTaylorCoefficient f n‖| ≤ 1

open Finset Complex Metric Real
open scoped Topology

/-! ### The Lebedev–Milin inequalities

Throughout, `β : ℕ → ℂ` satisfies `β 0 = 1` and `m β m = ∑_{k=1}^m w k β (m - k)` for every `m`,
that is, `∑ β m z^m = exp (∑_{k ≥ 1} (w k / k) z^k)` as formal power series. -/

/-- The exponent `∑_{k=1}^{n+1} (1 - k / (n + 1)) (|w k|² - 1) / k` of the second Lebedev–Milin
inequality; its last term vanishes. -/
private noncomputable def lmExp (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1) / (k + 1) * (1 - (k + 1) / (n + 1))

/-- The Cauchy–Schwarz step `m² |β m|² ≤ (∑_{k=1}^m |w k|²) (∑_{j<m} |β j|²)`. -/
private theorem sq_mul_norm_le (w β : ℕ → ℂ)
    (hrec : ∀ m : ℕ, (m : ℂ) * β m = ∑ k ∈ range m, w (k + 1) * β (m - 1 - k)) (m : ℕ) :
    ((m : ℝ) * ‖β m‖) ^ 2 ≤ (∑ k ∈ range m, ‖w (k + 1)‖ ^ 2) * ∑ j ∈ range m, ‖β j‖ ^ 2 := by
  have h1 : (m : ℝ) * ‖β m‖ ≤ ∑ k ∈ range m, ‖w (k + 1)‖ * ‖β (m - 1 - k)‖ := by
    calc (m : ℝ) * ‖β m‖ = ‖(m : ℂ) * β m‖ := by simp
      _ = ‖∑ k ∈ range m, w (k + 1) * β (m - 1 - k)‖ := by rw [hrec]
      _ ≤ ∑ k ∈ range m, ‖w (k + 1) * β (m - 1 - k)‖ := norm_sum_le _ _
      _ = _ := by simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (range m) (fun k ↦ ‖w (k + 1)‖)
    (fun k ↦ ‖β (m - 1 - k)‖)
  rw [Finset.sum_range_reflect (fun j ↦ ‖β j‖ ^ 2) m] at h2
  calc ((m : ℝ) * ‖β m‖) ^ 2 ≤ (∑ k ∈ range m, ‖w (k + 1)‖ * ‖β (m - 1 - k)‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

private theorem lmExp_succ (w : ℕ → ℂ) (n : ℕ) :
    lmExp w (n + 1) = lmExp w n +
      (∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1)) / ((n + 1) * (n + 2)) := by
  simp only [lmExp]
  rw [Finset.sum_range_succ (n := n + 1), Finset.sum_div, ← Finset.sum_add_distrib]
  have hlast : (‖w (n + 1 + 1)‖ ^ 2 - 1) / (((n + 1 : ℕ) : ℝ) + 1) *
      (1 - (((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) + 1)) = 0 := by
    rw [div_self (by positivity)]; ring
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  push_cast
  field_simp
  ring

private theorem lmExp_add (w : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ range (n + 1), ‖w (k + 1)‖ ^ 2 - (n + 1)) / (n + 1) + lmExp w n =
      ∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1) / (k + 1) := by
  simp only [lmExp]
  have : (∑ k ∈ range (n + 1), ‖w (k + 1)‖ ^ 2 - (n + 1)) =
      ∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [this, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  field_simp
  ring

/-- **Second Lebedev–Milin inequality.** If `β 0 = 1` and `m β m = ∑_{k=1}^m w k β (m - k)`,
then `∑_{j ≤ n} |β j|² ≤ (n + 1) exp (∑_{k=1}^n (1 - k / (n + 1)) (|w k|² - 1) / k)`. -/
private theorem lebedev_milin_second (w β : ℕ → ℂ) (h0 : β 0 = 1)
    (hrec : ∀ m : ℕ, (m : ℂ) * β m = ∑ k ∈ range m, w (k + 1) * β (m - 1 - k)) (n : ℕ) :
    ∑ j ∈ range (n + 1), ‖β j‖ ^ 2 ≤ (n + 1) * Real.exp (lmExp w n) := by
  induction n with
  | zero => simp [lmExp, h0]
  | succ n ih =>
    have hcs := sq_mul_norm_le w β hrec (n + 1)
    set B := ∑ k ∈ range (n + 1), ‖w (k + 1)‖ ^ 2 with hB
    set D := ∑ j ∈ range (n + 1), ‖β j‖ ^ 2
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ by positivity
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ by positivity
    push_cast at hcs ih ⊢
    have hm : (0 : ℝ) < n + 1 := by positivity
    have hβ : ‖β (n + 1)‖ ^ 2 ≤ B * D / (n + 1) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hcs]
    have hsum : ∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1) = B - (n + 1) := by
      rw [Finset.sum_sub_distrib, hB]; simp
    have key := lmExp_succ w n
    rw [hsum] at key
    set Y := (B - (n + 1)) / ((n + 1) * (n + 2)) with hY
    have hY1 : 0 ≤ 1 + Y := by
      have : 1 + Y = ((n + 1) ^ 2 + B) / ((n + 1) * (n + 2)) := by rw [hY]; field_simp; ring
      rw [this]; positivity
    have hexp : 1 + Y ≤ Real.exp Y := by linarith [Real.add_one_le_exp Y]
    rw [Finset.sum_range_succ]
    calc D + ‖β (n + 1)‖ ^ 2 ≤ D + B * D / (n + 1) ^ 2 := by linarith
      _ = D * ((n + 2) / (n + 1)) * (1 + Y) := by rw [hY]; field_simp; ring
      _ ≤ ((n + 1) * Real.exp (lmExp w n)) * ((n + 2) / (n + 1)) * Real.exp Y := by
          apply mul_le_mul _ hexp hY1 (by positivity)
          exact mul_le_mul_of_nonneg_right ih (by positivity)
      _ = (n + 1 + 1) * Real.exp (lmExp w (n + 1)) := by
          rw [key, Real.exp_add]; field_simp; ring

/-- **Third Lebedev–Milin inequality.** If `β 0 = 1` and `m β m = ∑_{k=1}^m w k β (m - k)`,
then `|β (n + 1)|² ≤ exp (∑_{k=1}^{n+1} (|w k|² - 1) / k)`. -/
private theorem lebedev_milin_third (w β : ℕ → ℂ) (h0 : β 0 = 1)
    (hrec : ∀ m : ℕ, (m : ℂ) * β m = ∑ k ∈ range m, w (k + 1) * β (m - 1 - k)) (n : ℕ) :
    ‖β (n + 1)‖ ^ 2 ≤ Real.exp (∑ k ∈ range (n + 1), (‖w (k + 1)‖ ^ 2 - 1) / (k + 1)) := by
  have hcs := sq_mul_norm_le w β hrec (n + 1)
  have hD := lebedev_milin_second w β h0 hrec n
  rw [← lmExp_add w n]
  set B := ∑ k ∈ range (n + 1), ‖w (k + 1)‖ ^ 2
  set D := ∑ j ∈ range (n + 1), ‖β j‖ ^ 2
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ by positivity
  push_cast at hcs
  have hm : (0 : ℝ) < n + 1 := by positivity
  set Y := (B - (n + 1)) / (n + 1) with hY
  have hexp : 1 + Y ≤ Real.exp Y := by linarith [Real.add_one_le_exp Y]
  have h1Y : 1 + Y = B / (n + 1) := by rw [hY]; field_simp; ring
  calc ‖β (n + 1)‖ ^ 2 ≤ B * D / (n + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [hcs]
    _ ≤ B * ((n + 1) * Real.exp (lmExp w n)) / (n + 1) ^ 2 := by gcongr
    _ = (1 + Y) * Real.exp (lmExp w n) := by rw [h1Y]; field_simp
    _ ≤ Real.exp Y * Real.exp (lmExp w n) := by gcongr
    _ = Real.exp (Y + lmExp w n) := (Real.exp_add _ _).symm

/-- The sequence `E` shifted by one place: `0, E 0, E 1, …`. -/
private def shiftSeq (E : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | j + 1 => E j

/-- If `m E m = ∑_{k=1}^m C k E (m - k)`, then `b m = E m - x E (m - 1)` (the coefficients of
`(1 - x z) ∑ E m z^m`) satisfies `m b m = ∑_{k=1}^m (C k - x^k) b (m - k)`. -/
private theorem shift_rec (C E : ℕ → ℂ) (x : ℂ)
    (hrec : ∀ m : ℕ, (m : ℂ) * E m = ∑ k ∈ range m, C (k + 1) * E (m - 1 - k)) (m : ℕ) :
    (m : ℂ) * (E m - x * shiftSeq E m) =
      ∑ k ∈ range m,
        (C (k + 1) - x ^ (k + 1)) * (E (m - 1 - k) - x * shiftSeq E (m - 1 - k)) := by
  cases m with
  | zero => simp
  | succ j =>
    have h1 := hrec (j + 1)
    have h2 := hrec j
    simp only [Nat.add_sub_cancel] at h1
    have hsh0 : shiftSeq E 0 = 0 := rfl
    have hshift : ∀ k ∈ range j, shiftSeq E (j - k) = E (j - 1 - k) := by
      intro k hk
      have hk' : j - k = (j - 1 - k) + 1 := by have := Finset.mem_range.1 hk; omega
      rw [hk']
      rfl
    have hS2 : ∑ k ∈ range (j + 1), C (k + 1) * shiftSeq E (j - k) =
        ∑ k ∈ range j, C (k + 1) * E (j - 1 - k) := by
      rw [Finset.sum_range_succ, Nat.sub_self, hsh0, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hshift k hk]
    have hS3 : ∑ k ∈ range (j + 1), x ^ (k + 1) * E (j - k) =
        ∑ k ∈ range j, x ^ (k + 2) * E (j - 1 - k) + x * E j := by
      rw [Finset.sum_range_succ']
      simp only [zero_add, pow_one, Nat.sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [show j - (k + 1) = j - 1 - k by omega]
    have hS4 : ∑ k ∈ range (j + 1), x ^ (k + 1) * shiftSeq E (j - k) =
        ∑ k ∈ range j, x ^ (k + 1) * E (j - 1 - k) := by
      rw [Finset.sum_range_succ, Nat.sub_self, hsh0, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [hshift k hk]
    have hS4' : ∑ k ∈ range j, x ^ (k + 2) * E (j - 1 - k) =
        x * ∑ k ∈ range j, x ^ (k + 1) * E (j - 1 - k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hexp : ∑ k ∈ range (j + 1),
        (C (k + 1) - x ^ (k + 1)) * (E (j + 1 - 1 - k) - x * shiftSeq E (j + 1 - 1 - k)) =
        ∑ k ∈ range (j + 1), C (k + 1) * E (j - k)
          - x * ∑ k ∈ range (j + 1), C (k + 1) * shiftSeq E (j - k)
          - ∑ k ∈ range (j + 1), x ^ (k + 1) * E (j - k)
          + x * ∑ k ∈ range (j + 1), x ^ (k + 1) * shiftSeq E (j - k) := by
      simp only [Nat.add_sub_cancel, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hexp, hS2, hS3, hS4, ← h1, ← h2, hS4']
    simp only [shiftSeq]
    push_cast
    ring

/-! ### Circle averages of a function with positive real part -/

/-- `∫_0^{2π} z^{j+1} p(z) dθ = 0` on the circle `z = r e^{iθ}` (Cauchy's theorem). -/
private theorem integral_circleMap_pow_mul_eq_zero (p : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (hp : DifferentiableOn ℂ p (closedBall 0 r)) (j : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, circleMap 0 r θ ^ (j + 1) * p (circleMap 0 r θ) = 0 := by
  have h := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (f := fun z ↦ z ^ j * p z) (c := 0) hr.le Set.countable_empty
    ((continuousOn_pow j).mul hp.continuousOn)
    (fun z hz ↦ (differentiableAt_pow j).mul
      (hp.differentiableAt (closedBall_mem_nhds_of_mem (mem_ball.1 hz.1))))
  simp only [circleIntegral, deriv_circleMap] at h
  have : ∀ θ : ℝ, (circleMap 0 r θ * I) • (circleMap 0 r θ ^ j * p (circleMap 0 r θ)) =
      I * (circleMap 0 r θ ^ (j + 1) * p (circleMap 0 r θ)) := by
    intro θ; rw [smul_eq_mul]; ring
  simp_rw [this, intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left I_ne_zero

/-- `∫_0^{2π} p(z) / z^k dθ = 2π p^{(k)}(0) / k!` on the circle `z = r e^{iθ}` (Cauchy's integral
formula). -/
private theorem integral_circleMap_div_pow (p : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (hp : DifferentiableOn ℂ p (closedBall 0 r)) (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, p (circleMap 0 r θ) / circleMap 0 r θ ^ k =
      2 * π * (iteratedDeriv k p 0 / k.factorial) := by
  have h := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (c := 0) hr k Set.countable_empty hp.continuousOn
    (fun z hz ↦ hp.differentiableAt (closedBall_mem_nhds_of_mem (mem_ball.1 hz.1)))
  simp only [circleIntegral, deriv_circleMap, sub_zero] at h
  have : ∀ θ : ℝ, (circleMap 0 r θ * I) • ((1 / circleMap 0 r θ ^ (k + 1)) •
      p (circleMap 0 r θ)) = I * (p (circleMap 0 r θ) / circleMap 0 r θ ^ k) := by
    intro θ
    have : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
    rw [smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  simp_rw [this, intervalIntegral.integral_const_mul] at h
  rw [smul_eq_mul] at h
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  apply mul_left_cancel₀ I_ne_zero
  rw [h]
  field_simp

/-- **Averaging inequality.** Let `p` be analytic on the unit disc with `Re p > 0` and
`p 0 = 1`, with Taylor coefficients `c k`, and let `0 < r < 1`. Then some unimodular `e`
satisfies `∑_{k=1}^n |c k|² r^{2k} / (2k) ≤ ∑_{k=1}^n Re (c k r^k e^k) / k`.

Source: Arora, Ponnusamy and Sahoo, https://arxiv.org/abs/1903.10232, Lemma 3.1 (with
`α = γ = 0`). -/
private theorem exists_sum_sq_le_sum_re (p : ℂ → ℂ) (hp : DifferentiableOn ℂ p (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (p z).re) (hp0 : p 0 = 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (n : ℕ) :
    ∃ e : ℂ, ‖e‖ = 1 ∧
      ∑ k ∈ range n, ‖iteratedDeriv (k + 1) p 0 / (k + 1).factorial‖ ^ 2 * r ^ (2 * (k + 1)) /
          (2 * (k + 1)) ≤
        ∑ k ∈ range n,
          (iteratedDeriv (k + 1) p 0 / (k + 1).factorial * r ^ (k + 1) * e ^ (k + 1)).re /
            (k + 1) := by
  set c : ℕ → ℂ := fun k ↦ iteratedDeriv k p 0 / k.factorial
  have hpc : DifferentiableOn ℂ p (closedBall 0 r) := hp.mono (closedBall_subset_ball hr1)
  set z : ℝ → ℂ := fun θ ↦ circleMap 0 r θ with hz
  have hzball : ∀ θ, z θ ∈ ball (0 : ℂ) 1 := by
    intro θ
    rw [mem_ball, dist_zero_right, hz]
    simp only
    rw [norm_circleMap_zero, abs_of_pos hr0]
    exact hr1
  have hzne : ∀ θ, z θ ≠ 0 := fun _ ↦ circleMap_ne_center hr0.ne'
  have hzcont : Continuous z := continuous_circleMap 0 r
  have hPcont : Continuous fun θ ↦ p (z θ) := hp.continuousOn.comp_continuous hzcont hzball
  set S : ℝ → ℝ := fun θ ↦ ∑ k ∈ range n, (c (k + 1) * z θ ^ (k + 1)).re / (k + 1) with hS
  have hScont : Continuous S := by
    rw [hS]
    refine continuous_finsetSum _ fun k _ ↦ ?_
    exact (continuous_re.comp (continuous_const.mul (hzcont.pow _))).div_const _
  obtain ⟨θ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by positivity : (0 : ℝ) ≤ 2 * π)) hScont.continuousOn
  refine ⟨Complex.exp (θ₀ * I), Complex.norm_exp_ofReal_mul_I θ₀, ?_⟩
  -- The mean value of `Re p` over the circle is `Re (p 0) = 1`.
  have hI1 : ∫ θ in (0 : ℝ)..2 * π, (p (z θ)).re = 2 * π := by
    have h0 := integral_circleMap_div_pow p hr0 hpc 0
    simp only [pow_zero, div_one, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
      hp0] at h0
    have := intervalIntegral.intervalIntegral_re (μ := MeasureTheory.volume) (a := 0)
      (b := 2 * π) (hPcont.intervalIntegrable _ _)
    simp only [RCLike.re_to_complex] at this
    rw [this, hz]
    simp only
    rw [h0]
    simp
  -- On the circle `conj z = r² / z`, so `Re p · Re (c z^k)` integrates to `π r^{2k} |c|²`.
  have hI2 : ∀ k : ℕ, ∫ θ in (0 : ℝ)..2 * π, (p (z θ)).re * (c (k + 1) * z θ ^ (k + 1)).re =
      π * r ^ (2 * (k + 1)) * ‖c (k + 1)‖ ^ 2 := by
    intro k
    have hpt : ∀ θ, (p (z θ)).re * (c (k + 1) * z θ ^ (k + 1)).re =
        ((c (k + 1) * (z θ ^ (k + 1) * p (z θ)) +
          (starRingEnd ℂ) (c (k + 1)) * (r : ℂ) ^ (2 * (k + 1)) *
            (p (z θ) / z θ ^ (k + 1))) / 2).re := by
      intro θ
      have hzc : (starRingEnd ℂ) (z θ) = (r : ℂ) ^ 2 / z θ := by
        have h1 := Complex.mul_conj (z θ)
        rw [Complex.normSq_eq_norm_sq, hz] at h1
        simp only at h1
        rw [norm_circleMap_zero, abs_of_pos hr0] at h1
        rw [eq_div_iff (hzne θ), mul_comm, h1]
        push_cast
        ring
      have hconj : (starRingEnd ℂ) (c (k + 1)) * (r : ℂ) ^ (2 * (k + 1)) *
          (p (z θ) / z θ ^ (k + 1)) =
          p (z θ) * (starRingEnd ℂ) (c (k + 1) * z θ ^ (k + 1)) := by
        rw [map_mul, map_pow, hzc, div_pow, ← pow_mul]
        ring
      have hgen : ∀ P w : ℂ, ((P * w + P * (starRingEnd ℂ) w) / 2).re = P.re * w.re := by
        intro P w
        simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re, Complex.conj_re,
          Complex.conj_im]
        ring
      rw [hconj, ← hgen]
      congr 2
      ring
    simp_rw [hpt]
    have hint1 : IntervalIntegrable (fun θ ↦ c (k + 1) * (z θ ^ (k + 1) * p (z θ)))
        MeasureTheory.volume 0 (2 * π) :=
      (continuous_const.mul ((hzcont.pow _).mul hPcont)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun θ ↦ (starRingEnd ℂ) (c (k + 1)) *
        (r : ℂ) ^ (2 * (k + 1)) * (p (z θ) / z θ ^ (k + 1))) MeasureTheory.volume 0 (2 * π) :=
      (continuous_const.mul (hPcont.div (hzcont.pow _) fun θ ↦ pow_ne_zero _ (hzne θ))
        ).intervalIntegrable _ _
    have := intervalIntegral.intervalIntegral_re (μ := MeasureTheory.volume) (a := 0)
      (b := 2 * π) ((hint1.add hint2).div_const 2)
    simp only [RCLike.re_to_complex] at this
    rw [this, intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have e1 : ∫ θ in (0 : ℝ)..2 * π, z θ ^ (k + 1) * p (z θ) = 0 :=
      integral_circleMap_pow_mul_eq_zero p hr0 hpc k
    have e2 : ∫ θ in (0 : ℝ)..2 * π, p (z θ) / z θ ^ (k + 1) = 2 * π * c (k + 1) :=
      integral_circleMap_div_pow p hr0 hpc (k + 1)
    rw [e1, e2]
    simp only [mul_zero, zero_add]
    have : (starRingEnd ℂ) (c (k + 1)) * (r : ℂ) ^ (2 * (k + 1)) * (2 * π * c (k + 1)) / 2 =
        ((π * r ^ (2 * (k + 1)) * ‖c (k + 1)‖ ^ 2 : ℝ) : ℂ) := by
      have h1 := Complex.mul_conj (c (k + 1))
      rw [Complex.normSq_eq_norm_sq] at h1
      push_cast at h1 ⊢
      rw [mul_comm ((starRingEnd ℂ) (c (k + 1))) _]
      linear_combination (π * (r : ℂ) ^ (2 * (k + 1))) * h1
    rw [this, Complex.ofReal_re]
  have hint : ∀ k ∈ range n, IntervalIntegrable
      (fun θ ↦ (p (z θ)).re * (c (k + 1) * z θ ^ (k + 1)).re / (k + 1))
      MeasureTheory.volume 0 (2 * π) := by
    intro k _
    exact (((continuous_re.comp hPcont).mul
      (continuous_re.comp (continuous_const.mul (hzcont.pow _)))).div_const _).intervalIntegrable
        _ _
  have hI3 : ∫ θ in (0 : ℝ)..2 * π, (p (z θ)).re * S θ =
      ∑ k ∈ range n, π * r ^ (2 * (k + 1)) * ‖c (k + 1)‖ ^ 2 / (k + 1) := by
    simp only [hS, Finset.mul_sum, mul_div_assoc']
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [intervalIntegral.integral_div, hI2 k]
  -- Since `Re p > 0`, the integral of `Re p · S` is at most `2π max S`.
  have hI4 : ∫ θ in (0 : ℝ)..2 * π, (p (z θ)).re * S θ ≤ 2 * π * S θ₀ := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (f := fun θ ↦ (p (z θ)).re * S θ) (g := fun θ ↦ (p (z θ)).re * S θ₀)
      (by positivity : (0 : ℝ) ≤ 2 * π)
      (((continuous_re.comp hPcont).mul hScont).intervalIntegrable _ _)
      (((continuous_re.comp hPcont).mul continuous_const).intervalIntegrable _ _)
      (fun θ hθ ↦ mul_le_mul_of_nonneg_left (hmax hθ) (hpos _ (hzball θ)).le)
    rw [intervalIntegral.integral_mul_const, hI1] at hmono
    exact hmono
  rw [hI3] at hI4
  have hS0 : S θ₀ = ∑ k ∈ range n,
      (c (k + 1) * r ^ (k + 1) * Complex.exp (θ₀ * I) ^ (k + 1)).re / (k + 1) := by
    rw [hS]
    simp only
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hz]
    simp only [circleMap, zero_add]
    ring_nf
  rw [← hS0]
  have hsum : ∑ k ∈ range n, π * r ^ (2 * (k + 1)) * ‖c (k + 1)‖ ^ 2 / (k + 1) =
      2 * π * ∑ k ∈ range n, ‖c (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) / (2 * (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    field_simp
  rw [hsum] at hI4
  exact le_of_mul_le_mul_left hI4 (by positivity)

/-! ### Proof of Leung's theorem -/

/-- If `z f'(z) = p(z) f(z)` near `0`, the Taylor coefficients satisfy
`m a m = ∑_{i ≤ m} c i a (m - i)` (Leibniz rule). -/
private theorem mul_taylorCoeff_eq_sum (f p : ℂ → ℂ) (hfa : AnalyticAt ℂ f 0)
    (hpa : AnalyticAt ℂ p 0) (hid : (fun z ↦ z * deriv f z) =ᶠ[𝓝 0] (fun z ↦ p z * f z))
    (m : ℕ) :
    (m : ℂ) * (iteratedDeriv m f 0 / m.factorial) =
      ∑ i ∈ range (m + 1), (iteratedDeriv i p 0 / i.factorial) *
        (iteratedDeriv (m - i) f 0 / (m - i).factorial) := by
  have hL := iteratedDeriv_fun_mul (n := m) (x := (0 : ℂ)) (f := fun z ↦ z) (g := deriv f)
    contDiffAt_fun_id hfa.deriv.contDiffAt
  have hR := iteratedDeriv_fun_mul (n := m) (x := (0 : ℂ)) (f := p) (g := f)
    hpa.contDiffAt hfa.contDiffAt
  rw [hid.iteratedDeriv_eq m, hR] at hL
  simp only [iteratedDeriv_fun_id_zero] at hL
  have hlhs : ∑ i ∈ range (m + 1), (m.choose i : ℂ) * (if i = 1 then 1 else 0) *
      iteratedDeriv (m - i) (deriv f) 0 = m * iteratedDeriv m f 0 := by
    cases m with
    | zero => simp
    | succ j =>
      rw [Finset.sum_eq_single 1]
      · simp [iteratedDeriv_succ']
      · intro b _ hb; simp [hb]
      · intro h; simp at h
  rw [hlhs] at hL
  rw [mul_div_assoc', ← hL, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((m - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (m - i).factorial_ne_zero
  have h3 : (m.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← Nat.choose_mul_factorial_mul_factorial hi']
  push_cast
  field_simp

/-- **Leung's bound on a circle of radius `r < 1`.** Let `p` be analytic on the unit disc with
`Re p > 0` and `p 0 = 1`, with Taylor coefficients `c i`, and let `a` satisfy `a 0 = 0`,
`a 1 = 1` and `m a m = ∑_{i ≤ m} c i a (m - i)`. Then
`| |a (n + 1)| r^n - |a n| r^(n-1) | ≤ 1` for `n ≥ 1` and `0 < r < 1`.

Source: Arora, Ponnusamy and Sahoo, https://arxiv.org/abs/1903.10232, proof of Theorem 1.1
(with `α = γ = 0`). -/
private theorem abs_norm_mul_pow_sub_le_one (a : ℕ → ℂ) (p : ℂ → ℂ)
    (hpd : DifferentiableOn ℂ p (ball 0 1)) (hppos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (p z).re)
    (hp0 : p 0 = 1)
    (hrec : ∀ m : ℕ, (m : ℂ) * a m =
      ∑ i ∈ range (m + 1), iteratedDeriv i p 0 / i.factorial * a (m - i))
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    |‖a (n + 1)‖ * r ^ n - ‖a n‖ * r ^ (n - 1)| ≤ 1 := by
  set c : ℕ → ℂ := fun k ↦ iteratedDeriv k p 0 / k.factorial
  have hc0 : c 0 = 1 := by simp [c, hp0]
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  obtain ⟨e, he, hherg⟩ := exists_sum_sq_le_sum_re p hpd hppos hp0 hr0 hr1 n
  have hherg' : ∑ k ∈ range n, ‖c (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) / (2 * (k + 1)) ≤
      ∑ k ∈ range n, (c (k + 1) * r ^ (k + 1) * e ^ (k + 1)).re / (k + 1) := hherg
  set E : ℕ → ℂ := fun j ↦ a (j + 1) * (r : ℂ) ^ j with hE
  set C : ℕ → ℂ := fun k ↦ c k * (r : ℂ) ^ k with hC
  -- The coefficients of `f(r z) / (r z)` satisfy the exponential recursion.
  have hErec : ∀ m : ℕ, (m : ℂ) * E m = ∑ k ∈ range m, C (k + 1) * E (m - 1 - k) := by
    intro j
    have h := hrec (j + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
    simp only [Nat.sub_self, ha0, mul_zero, add_zero, Nat.sub_zero] at h
    have hs : ∑ i ∈ range j, c (i + 1) * a (j + 1 - (i + 1)) =
        ∑ i ∈ range j, c (i + 1) * a (j - i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Nat.add_sub_add_right]
    have h0 : iteratedDeriv 0 p 0 / (Nat.factorial 0 : ℂ) = 1 := hc0
    rw [h0, one_mul] at h
    change (((j + 1 : ℕ) : ℂ)) * a (j + 1) =
      ∑ i ∈ range j, c (i + 1) * a (j + 1 - (i + 1)) + a (j + 1) at h
    rw [hs] at h
    push_cast at h
    have h' : (j : ℂ) * a (j + 1) = ∑ i ∈ range j, c (i + 1) * a (j - i) := by
      linear_combination h
    simp only [hE, hC]
    calc (j : ℂ) * (a (j + 1) * (r : ℂ) ^ j) =
          (∑ i ∈ range j, c (i + 1) * a (j - i)) * (r : ℂ) ^ j := by rw [← h']; ring
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hi' : i < j := Finset.mem_range.1 hi
        have h2 : (r : ℂ) ^ j = (r : ℂ) ^ (i + 1) * (r : ℂ) ^ (j - 1 - i) := by
          rw [← pow_add]; congr 1; omega
        rw [show j - 1 - i + 1 = j - i by omega, h2]
        ring
  set x := (starRingEnd ℂ) e with hx
  have hb0 : E 0 - x * shiftSeq E 0 = 1 := by simp [shiftSeq, hE, ha1]
  have hLM := lebedev_milin_third (fun k ↦ C k - x ^ k) (fun m ↦ E m - x * shiftSeq E m) hb0
    (shift_rec C E x hErec) (n - 1)
  rw [hn'] at hLM
  -- The exponent of the Lebedev–Milin bound is nonpositive.
  have hexp : ∑ k ∈ range n, (‖C (k + 1) - x ^ (k + 1)‖ ^ 2 - 1) / (k + 1) ≤ 0 := by
    have hterm : ∀ k : ℕ, (‖C (k + 1) - x ^ (k + 1)‖ ^ 2 - 1) / (k + 1) =
        2 * (‖c (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) / (2 * (k + 1)) -
          (c (k + 1) * r ^ (k + 1) * e ^ (k + 1)).re / (k + 1)) := by
      intro k
      have hxk : ‖x ^ (k + 1)‖ = 1 := by simp [hx, he]
      have hconj : (starRingEnd ℂ) (x ^ (k + 1)) = e ^ (k + 1) := by simp [hx]
      rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm, hxk,
        hconj]
      simp only [hC]
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun k _ ↦ hterm k, ← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  have hb1 : ‖E n - x * shiftSeq E n‖ ≤ 1 := by
    have h1 : ‖E n - x * shiftSeq E n‖ ^ 2 ≤ 1 :=
      hLM.trans (by simpa using Real.exp_le_exp.2 hexp)
    nlinarith [norm_nonneg (E n - x * shiftSeq E n)]
  have hsh : shiftSeq E n = a n * (r : ℂ) ^ (n - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, hn'.symm⟩
    simp [shiftSeq, hE]
  rw [hsh] at hb1
  have hxn : ‖x‖ = 1 := by simp [hx, he]
  calc |‖a (n + 1)‖ * r ^ n - ‖a n‖ * r ^ (n - 1)| =
        |‖E n‖ - ‖x * (a n * (r : ℂ) ^ (n - 1))‖| := by
        simp only [hE, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr0, hxn, one_mul]
    _ ≤ ‖E n - x * (a n * (r : ℂ) ^ (n - 1))‖ := abs_norm_sub_norm_le _ _
    _ ≤ 1 := hb1

/--
**Leung's theorem on successive coefficients of starlike functions.** Let
$f : \mathbb{C} \to \mathbb{C}$ be analytic on the open unit disc $\mathbb{D} = \{z : |z| < 1\}$,
with $f(0) = 0$ and $f'(0) = 1$, injective on $\mathbb{D}$, and starlike, meaning that
$\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$ for every $z \ne 0$ in $\mathbb{D}$. Let
$a_n = f^{(n)}(0) / n!$ be the Taylor coefficients of $f$ at $0$. Then
$\bigl| |a_{n+1}| - |a_n| \bigr| \le 1$ for every natural number $n \ge 1$.

This answers Problem 6.46 of Hayman and Lingham, Research Problems in Function Theory (2018),
affirmatively. It was proved by Y. Leung (Bull. London Math. Soc. 10 (1978), 193-196) and
independently by D. H. Hamilton.

Source: Moduli difference of initial inverse logarithmic
coefficients for starlike and convex functions (2026), arXiv:2603.17600,
https://arxiv.org/abs/2603.17600. Moved from
`OpenConjectures/Analysis/StarlikeCoefficientSuccessiveDifference`.
-/
theorem conjecture_holds : conjecture := by
  intro f hS hstar n hn
  obtain ⟨hf, hf0, hf1, -⟩ := hS
  obtain ⟨-, hpos⟩ := hstar
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 0 := ball_mem_nhds 0 one_pos
  have hfa : AnalyticOnNhd ℂ f (ball 0 1) := (isOpen_ball.analyticOn_iff_analyticOnNhd).1 hf
  have hd0 : deriv f 0 = 1 := hf1.deriv
  -- `g z = f z / z`, extended by `g 0 = 1`, does not vanish on the disc.
  set g : ℂ → ℂ := dslope f 0 with hg
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (Complex.differentiableOn_dslope hball).2 hfa.differentiableOn
  have hg_eq : ∀ z, z ≠ 0 → g z = f z / z := by
    intro z hz
    rw [hg, dslope_of_ne _ hz, slope_def_field, hf0, sub_zero, sub_zero]
  have hg0 : g 0 = 1 := by rw [hg, dslope_same, hd0]
  have hfz : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → f z ≠ 0 := by
    intro z hz hz0 h
    have := hpos z hz hz0
    rw [h, div_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hg0]
      exact one_ne_zero
    · rw [hg_eq z hz0]
      exact div_ne_zero (hfz z hz hz0) hz0
  -- `p z = z f'(z) / f(z)`, extended by `p 0 = 1`, has positive real part on the disc.
  set p : ℂ → ℂ := fun z ↦ deriv f z / g z with hp
  have hpd : DifferentiableOn ℂ p (ball 0 1) := hfa.deriv.differentiableOn.div hgd hgne
  have hp0 : p 0 = 1 := by simp [hp, hd0, hg0]
  have hp_eq : ∀ z, z ≠ 0 → p z = z * deriv f z / f z := by
    intro z hz
    simp only [hp]
    rw [hg_eq z hz, div_div_eq_mul_div]
    ring
  have hppos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (p z).re := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hp0]
      simp
    · rw [hp_eq z hz0]
      exact hpos z hz hz0
  have hid : (fun z ↦ z * deriv f z) =ᶠ[𝓝 0] (fun z ↦ p z * f z) := by
    filter_upwards [hball] with z hz
    by_cases hz0 : z = 0
    · simp [hz0, hf0]
    · rw [hp_eq z hz0, div_mul_cancel₀ _ (hfz z hz hz0)]
  have hrec : ∀ m : ℕ, (m : ℂ) * wimanTaylorCoefficient f m =
      ∑ i ∈ range (m + 1), iteratedDeriv i p 0 / i.factorial *
        wimanTaylorCoefficient f (m - i) :=
    mul_taylorCoeff_eq_sum f p (hfa 0 (mem_ball_self one_pos)) (hpd.analyticAt hball) hid
  have ha0 : wimanTaylorCoefficient f 0 = 0 := by simp [wimanTaylorCoefficient, hf0]
  have ha1 : wimanTaylorCoefficient f 1 = 1 := by simp [wimanTaylorCoefficient, hd0]
  have hr_bound : ∀ r ∈ Set.Ioo (0 : ℝ) 1, |‖wimanTaylorCoefficient f (n + 1)‖ * r ^ n -
      ‖wimanTaylorCoefficient f n‖ * r ^ (n - 1)| ≤ 1 := fun r hr ↦
    abs_norm_mul_pow_sub_le_one _ p hpd hppos hp0 hrec ha0 ha1 hn hr.1 hr.2
  -- Let `r → 1`.
  have hcont : Continuous fun r : ℝ ↦ |‖wimanTaylorCoefficient f (n + 1)‖ * r ^ n -
      ‖wimanTaylorCoefficient f n‖ * r ^ (n - 1)| := by
    fun_prop
  have htend := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  have hle := le_of_tendsto htend (Filter.eventually_of_mem (Ioo_mem_nhdsLT one_pos) hr_bound)
  simpa using hle

end MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted
