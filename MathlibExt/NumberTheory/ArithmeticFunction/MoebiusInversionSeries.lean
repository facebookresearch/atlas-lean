/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.ArithmeticFunction.KFoldDivisor
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Möbius inversion for series

For functions `f g : ℝ → ℝ`, the relation `g(x) = ∑_{m ≥ 1} f(m x)` inverts to
`f(x) = ∑_{n ≥ 1} μ(n) g(n x)`, under absolute convergence hypotheses weighted by the Piltz
divisor functions `d_3` and `d = σ 0`.

## Main statements

* `ArithmeticFunction.summable_sigma_zero_mul_abs_of_summable_piltz_three_mul_abs`
* `ArithmeticFunction.tsum_moebius_inversion`
* `ArithmeticFunction.eq_tsum_moebius_mul_of_eq_tsum`
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius

namespace ArithmeticFunction


/-- Shifting a weighted series whose weight vanishes at zero. -/
private theorem summable_shift_iff (w : ℕ → ℝ) (h : ℝ → ℝ) (x : ℝ) :
    (Summable fun k : ℕ => w k * |h (k * x)|) ↔
      Summable fun k : ℕ => w (k + 1) * |h (((k : ℝ) + 1) * x)| := by
  rw [← summable_nat_add_iff 1]
  push_cast
  rfl

/-- If `∑_k d_3(k) |f(k x)| < ∞` for every `x` and `g(x) = ∑_{m ≥ 1} f(m x)`, then
`∑_k d(k) |g(k x)| < ∞`, where `d = σ 0` is the number-of-divisors function. -/
theorem summable_sigma_zero_mul_abs_of_summable_piltz_three_mul_abs (f g : ℝ → ℝ)
    (hf : ∀ x, Summable fun k : ℕ => (piltz 3 k : ℝ) * |f (k * x)|)
    (hgf : ∀ x, g x = ∑' m : ℕ, f ((m + 1) * x)) (x : ℝ) :
    Summable fun k : ℕ => (σ 0 k : ℝ) * |g (k * x)| := by
  classical
  have hd3sum : ∀ A : ℕ, piltz 3 A = ∑ B ∈ A.divisors, σ 0 B := by
    intro A; rw [piltz_succ_apply, piltz_two]
  -- Along any ray, `∑_m |f (m y)| < ∞`, since `1 ≤ d₃`.
  have hfabs : ∀ y : ℝ, Summable fun m : ℕ => |f (((m : ℝ) + 1) * y)| := by
    intro y
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
      ((summable_shift_iff _ f y).mp (hf y))
    have h1 : (1 : ℝ) ≤ (piltz 3 (m + 1) : ℝ) := by
      exact_mod_cast piltz_pos (by norm_num) (Nat.succ_ne_zero m)
    exact le_mul_of_one_le_left (abs_nonneg _) h1
  -- The array `U (A, B) = d B * |f (A x)|`, supported on the pairs with `B ∣ A`. Its rows sum
  -- to `d₃ A * |f (A x)|`, so it is summable by hypothesis.
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ × ℕ → ℝ,
      U = fun q : ℕ × ℕ => if q.2 ∈ q.1.divisors then
        (σ 0 q.2 : ℝ) * |f ((q.1 : ℝ) * x)| else 0 := ⟨_, rfl⟩
  have hUnonneg : ∀ q, 0 ≤ U q := by
    intro q; rw [hUdef]; dsimp only; split_ifs <;> positivity
  have hUrow : ∀ A : ℕ, Summable fun B : ℕ => U (A, B) := by
    intro A
    refine summable_of_ne_finset_zero (s := A.divisors) fun B hB => ?_
    rw [hUdef]; simp [hB]
  have hUrowsum : ∀ A : ℕ,
      (∑' B : ℕ, U (A, B)) = (piltz 3 A : ℝ) * |f ((A : ℝ) * x)| := by
    intro A
    rw [tsum_eq_sum (s := A.divisors) fun B hB => by rw [hUdef]; simp [hB],
      Finset.sum_congr rfl fun B hB => (by rw [hUdef]; simp [hB] :
        U (A, B) = (σ 0 B : ℝ) * |f ((A : ℝ) * x)|), ← Finset.sum_mul,
      hd3sum A, Nat.cast_sum]
  have hUsum : Summable U := by
    rw [summable_prod_of_nonneg hUnonneg]
    exact ⟨hUrow, by simpa only [hUrowsum] using hf x⟩
  -- Pull `U` back along the injection `(k, m) ↦ ((k+1)(m+1), k+1)`.
  have hρinj : Function.Injective
      (fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1), p.1 + 1)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hcd
    simp only [Prod.mk.injEq] at hcd
    obtain ⟨h1, h2⟩ := hcd
    have hac : a = c := by omega
    subst hac
    have hbd : b + 1 = d + 1 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos a) h1
    simp only [Prod.mk.injEq]
    exact ⟨trivial, by omega⟩
  have hWρ : ∀ p : ℕ × ℕ, U ((p.1 + 1) * (p.2 + 1), p.1 + 1)
      = (σ 0 (p.1 + 1) : ℝ) * |f (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x)| := by
    intro p
    rw [hUdef]
    dsimp only
    rw [ite_eq_left (Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,
      Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)⟩)]
    push_cast
    ring_nf
  have hWsum : Summable fun p : ℕ × ℕ =>
      (σ 0 (p.1 + 1) : ℝ) * |f (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x)| :=
    (hUsum.comp_injective hρinj).congr hWρ
  have hWnonneg : ∀ p : ℕ × ℕ,
      0 ≤ (σ 0 (p.1 + 1) : ℝ) * |f (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x)| :=
    fun p => by positivity
  obtain ⟨-, hWcol⟩ := (summable_prod_of_nonneg hWnonneg).mp hWsum
  -- Finally `d (k+1) |g ((k+1) x)| ≤ ∑_m d (k+1) |f ((k+1)(m+1) x)|`.
  rw [summable_shift_iff _ g x]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hWcol
  dsimp only
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hgf (((k : ℝ) + 1) * x)]
  have h1 : |∑' m : ℕ, f (((m : ℝ) + 1) * (((k : ℝ) + 1) * x))|
      ≤ ∑' m : ℕ, |f (((m : ℝ) + 1) * (((k : ℝ) + 1) * x))| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun m : ℕ => f (((m : ℝ) + 1) * (((k : ℝ) + 1) * x)))
        (by simpa only [Real.norm_eq_abs] using hfabs (((k : ℝ) + 1) * x))
  refine h1.trans_eq (tsum_congr fun m => ?_)
  rw [show ((m : ℝ) + 1) * (((k : ℝ) + 1) * x) = ((k : ℝ) + 1) * ((m : ℝ) + 1) * x by ring]

/-- **Möbius inversion for series.** Suppose `∑_k d_3(k) |f(k x)|` and `∑_k d(k) |g(k x)|`
converge for every `x`, where `d_3` is the Piltz divisor function and `d = σ 0`. Then
`g(x) = ∑_{m ≥ 1} f(m x)` for all `x` if and only if `f(x) = ∑_{n ≥ 1} μ(n) g(n x)` for all `x`.

The hypothesis on `g` follows from the one on `f` in the forward direction
(`ArithmeticFunction.summable_sigma_zero_mul_abs_of_summable_piltz_three_mul_abs`); see
`ArithmeticFunction.eq_tsum_moebius_mul_of_eq_tsum`. -/
theorem tsum_moebius_inversion (f g : ℝ → ℝ)
    (hf : ∀ x, Summable fun k : ℕ => (piltz 3 k : ℝ) * |f (k * x)|)
    (hg : ∀ x, Summable fun k : ℕ => (σ 0 k : ℝ) * |g (k * x)|) :
    (∀ x, g x = ∑' m : ℕ, f ((m + 1) * x)) ↔ ∀ x, f x = ∑' n : ℕ, (μ n : ℝ) * g (n * x) := by
  classical
  -- shift the Möbius series to start at `n = 1`
  have hshift : ∀ x, (∑' n : ℕ, (μ n : ℝ) * g (n * x)) =
      ∑' n : ℕ, (μ (n + 1) : ℝ) * g (((n : ℝ) + 1) * x) := by
    intro x
    rw [← Nat.succ_injective.tsum_eq (f := fun n : ℕ => (μ n : ℝ) * g (n * x))]
    · simp
    · rintro n hn
      rcases n with _ | n
      · simp at hn
      · exact ⟨n, rfl⟩
  simp_rw [hshift]
  have hd23 : ∀ n : ℕ, σ 0 n ≤ piltz 3 n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simpa using piltz_le_piltz_succ 2 hn
  -- The Dirichlet rearrangement `∑_{n,m} μ n h (n m x) = ∑_N (∑_{δ ∣ N} μ δ) h (N x) = h x`,
  -- valid whenever `∑_N d N |h (N x)| < ∞`.
  have core : ∀ (h : ℝ → ℝ) (x : ℝ),
      (Summable fun k : ℕ => (σ 0 k : ℝ) * |h (k * x)|) →
      (Summable fun p : ℕ × ℕ =>
          (μ (p.1 + 1) : ℝ) * h (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x)) ∧
        (∑' p : ℕ × ℕ, (μ (p.1 + 1) : ℝ) * h (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x)) = h x := by
    intro h x hsum
    obtain ⟨W, hWdef⟩ : ∃ W : ℕ × ℕ → ℝ,
        W = fun q : ℕ × ℕ => if q.2 ∈ q.1.divisors then |h ((q.1 : ℝ) * x)| else 0 := ⟨_, rfl⟩
    obtain ⟨V, hVdef⟩ : ∃ V : ℕ × ℕ → ℝ,
        V = fun q : ℕ × ℕ => if q.2 ∈ q.1.divisors then (μ q.2 : ℝ) * h ((q.1 : ℝ) * x) else 0 :=
      ⟨_, rfl⟩
    have hWnonneg : ∀ q, 0 ≤ W q := by
      intro q; rw [hWdef]; dsimp only; split_ifs <;> positivity
    have hWrow : ∀ A : ℕ, Summable fun B : ℕ => W (A, B) := by
      intro A
      refine summable_of_ne_finset_zero (s := A.divisors) fun B hB => ?_
      rw [hWdef]; simp [hB]
    have hWrowsum : ∀ A : ℕ,
        (∑' B : ℕ, W (A, B)) = (σ 0 A : ℝ) * |h ((A : ℝ) * x)| := by
      intro A
      rw [tsum_eq_sum (s := A.divisors) fun B hB => by rw [hWdef]; simp [hB],
        Finset.sum_congr rfl fun B hB => (by rw [hWdef]; simp [hB] :
          W (A, B) = |h ((A : ℝ) * x)|), Finset.sum_const, nsmul_eq_mul, sigma_zero_apply]
    have hWsum : Summable W := by
      rw [summable_prod_of_nonneg hWnonneg]
      exact ⟨hWrow, by simpa only [hWrowsum] using hsum⟩
    have hVle : ∀ q, ‖V q‖ ≤ W q := by
      intro q
      rw [hVdef, hWdef]
      dsimp only
      split_ifs with hq
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q.2))
      · simp
    have hVsum : Summable V := Summable.of_norm_bounded hWsum hVle
    have hρinj : Function.Injective
        (fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1), p.1 + 1)) := by
      rintro ⟨a, b⟩ ⟨c, d⟩ hcd
      simp only [Prod.mk.injEq] at hcd
      obtain ⟨h1, h2⟩ := hcd
      have hac : a = c := by omega
      subst hac
      have hbd : b + 1 = d + 1 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos a) h1
      simp only [Prod.mk.injEq]
      exact ⟨trivial, by omega⟩
    have hVsupp : Function.support V ⊆
        Set.range (fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1), p.1 + 1)) := by
      rintro ⟨A, B⟩ hq
      rw [Function.mem_support, hVdef] at hq
      dsimp only at hq
      by_cases hmem : B ∈ A.divisors
      · obtain ⟨hBA, hA0⟩ := Nat.mem_divisors.mp hmem
        have hB0 : B ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hBA)
        refine ⟨(B - 1, A / B - 1), ?_⟩
        have hB1 : B - 1 + 1 = B := by omega
        have hABpos : 0 < A / B :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hBA) (Nat.pos_of_ne_zero hB0)
        have hAB1 : A / B - 1 + 1 = A / B := by omega
        simp only [hB1, hAB1, Prod.mk.injEq]
        exact ⟨Nat.mul_div_cancel' hBA, trivial⟩
      · simp [hmem] at hq
    have hVρ : ∀ p : ℕ × ℕ, V ((p.1 + 1) * (p.2 + 1), p.1 + 1)
        = (μ (p.1 + 1) : ℝ) * h (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x) := by
      intro p
      rw [hVdef]
      dsimp only
      rw [ite_eq_left (Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,
        Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)⟩)]
      push_cast
      ring_nf
    have hΦsum : Summable fun p : ℕ × ℕ =>
        (μ (p.1 + 1) : ℝ) * h (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x) :=
      (hVsum.comp_injective hρinj).congr hVρ
    refine ⟨hΦsum, ?_⟩
    have e1 : (∑' p : ℕ × ℕ, (μ (p.1 + 1) : ℝ) * h (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x))
        = ∑' q : ℕ × ℕ, V q := by
      rw [← hρinj.tsum_eq hVsupp]
      exact tsum_congr fun p => (hVρ p).symm
    rw [e1, hVsum.tsum_prod]
    have e2 : ∀ A : ℕ,
        (∑' B : ℕ, V (A, B)) = (if A = 1 then (1 : ℝ) else 0) * h ((A : ℝ) * x) := by
      intro A
      rw [tsum_eq_sum (s := A.divisors) fun B hB => by rw [hVdef]; simp [hB],
        Finset.sum_congr rfl fun B hB => (by rw [hVdef]; simp [hB] :
          V (A, B) = (μ B : ℝ) * h ((A : ℝ) * x)), ← Finset.sum_mul]
      congr 1
      have := congrArg (fun F : ArithmeticFunction ℤ => F A) moebius_mul_coe_zeta
      rw [coe_mul_zeta_apply, one_apply] at this
      rw [← Int.cast_sum, this]
      split_ifs <;> simp
    rw [tsum_congr e2, tsum_eq_single 1 (fun b hb => by simp [hb])]
    norm_num
  constructor
  · intro hgf x
    have hfsum : Summable fun k : ℕ => (σ 0 k : ℝ) * |f (k * x)| := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hf x)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd23 k) (abs_nonneg _)
    obtain ⟨hps, hpe⟩ := core f x hfsum
    rw [← hpe, hps.tsum_prod]
    refine tsum_congr fun n => ?_
    dsimp only
    rw [tsum_mul_left]
    congr 1
    rw [hgf (((n : ℝ) + 1) * x)]
    refine tsum_congr fun m => ?_
    congr 1
    ring
  · intro hfg x
    obtain ⟨hps, hpe⟩ := core g x (hg x)
    rw [← hpe]
    have e0 : (∑' p : ℕ × ℕ, (μ (p.1 + 1) : ℝ) * g (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x))
        = ∑' p : ℕ × ℕ, (μ (p.2 + 1) : ℝ) * g (((p.2 : ℝ) + 1) * ((p.1 : ℝ) + 1) * x) :=
      ((Equiv.prodComm ℕ ℕ).tsum_eq
        (fun p : ℕ × ℕ => (μ (p.1 + 1) : ℝ) * g (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * x))).symm
    have hsw : Summable fun p : ℕ × ℕ =>
        (μ (p.2 + 1) : ℝ) * g (((p.2 : ℝ) + 1) * ((p.1 : ℝ) + 1) * x) := hps.prod_symm
    rw [e0, hsw.tsum_prod]
    refine tsum_congr fun m => ?_
    dsimp only
    rw [hfg (((m : ℝ) + 1) * x)]
    refine tsum_congr fun n => ?_
    congr 2
    ring

/-- **Möbius inversion for series**, forward direction: if `∑_k d_3(k) |f(k x)| < ∞` for every
`x` and `g(x) = ∑_{m ≥ 1} f(m x)`, then `f(x) = ∑_{n ≥ 1} μ(n) g(n x)`. -/
theorem eq_tsum_moebius_mul_of_eq_tsum (f g : ℝ → ℝ)
    (hf : ∀ x, Summable fun k : ℕ => (piltz 3 k : ℝ) * |f (k * x)|)
    (hgf : ∀ x, g x = ∑' m : ℕ, f ((m + 1) * x)) (x : ℝ) :
    f x = ∑' n : ℕ, (μ n : ℝ) * g (n * x) :=
  (tsum_moebius_inversion f g hf
    (summable_sigma_zero_mul_abs_of_summable_piltz_three_mul_abs f g hf hgf)).mp hgf x

end ArithmeticFunction
