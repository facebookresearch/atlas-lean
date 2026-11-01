/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Dirichlet's hyperbola method

For arithmetic functions `f` and `g` and reals `x` and `y > 0`, the summatory function of the
Dirichlet convolution `f * g` up to `x` splits along the hyperbola `de = x`:

`∑_{n ≤ x} (f * g) n = ∑_{d ≤ y} f d G(x / d) + ∑_{e ≤ x / y} F(x / e) g e - F(y) G(x / y)`,

where `F` and `G` are the summatory functions of `f` and `g`. Mathlib's
`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` is the one-sided case `y = x`.

We also record the elementary estimate used together with the hyperbola method when one factor
is `ζ`: replacing `⌊x / d⌋` by `x / d` in `∑_{d ∈ s} a d ⌊x / d⌋` costs at most `∑_{d ∈ s} ‖a d‖`.

## Main statements

* `ArithmeticFunction.sum_Ioc_mul_eq_hyperbola`: Dirichlet's hyperbola method.
* `norm_sum_mul_floor_div_sub_mul_sum_div_le`: removing the floor in `∑ a d ⌊x / d⌋`.
* `norm_sum_mul_natFloor_div_sub_mul_sum_div_le`: the same with `Nat.floor`, for `0 ≤ x`.
-/

@[expose] public section

open Finset

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

/-- **Dirichlet's hyperbola method.** For arithmetic functions `f` and `g` with values in a
commutative ring and reals `x` and `y > 0`,

`∑_{n ≤ x} (f * g) n = ∑_{d ≤ y} f d G(x / d) + ∑_{e ≤ x / y} F(x / e) g e - F(y) G(x / y)`,

where `F(t) = ∑_{d ≤ t} f d` and `G(t) = ∑_{e ≤ t} g e`. -/
theorem sum_Ioc_mul_eq_hyperbola (f g : ArithmeticFunction R) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n =
      ∑ d ∈ Ioc 0 ⌊y⌋₊, f d * ∑ e ∈ Ioc 0 ⌊x / d⌋₊, g e
        + ∑ e ∈ Ioc 0 ⌊x / y⌋₊, (∑ d ∈ Ioc 0 ⌊x / e⌋₊, f d) * g e
        - (∑ d ∈ Ioc 0 ⌊y⌋₊, f d) * ∑ e ∈ Ioc 0 ⌊x / y⌋₊, g e := by
  set N := ⌊x⌋₊ with hN
  set M := ⌊y⌋₊ with hM
  set K := ⌊x / y⌋₊ with hK
  have hy' : (0 : ℝ) ≤ y := hy.le
  -- The summatory functions evaluated at `x / d` are sums over `Ioc 0 (N / d)`.
  have hfl : ∀ d : ℕ, ⌊x / (d : ℝ)⌋₊ = N / d := fun d ↦ by rw [hN, Nat.floor_div_natCast]
  simp only [hfl]
  -- `d ≤ y` together with `e ≤ x / y` forces `de ≤ x`.
  have hab : ∀ d e : ℕ, 1 ≤ e → d ≤ M → e ≤ K → d * e ≤ N := by
    intro d e he hdM heK
    have hxy1 : (1 : ℝ) ≤ x / y := Nat.floor_pos.1 (lt_of_lt_of_le he heK)
    have hd' : (d : ℝ) ≤ y := (Nat.le_floor_iff hy').1 hdM
    have he' : (e : ℝ) ≤ x / y := (Nat.le_floor_iff (by linarith)).1 heK
    refine Nat.le_floor ?_
    push_cast
    calc (d : ℝ) * e ≤ y * (x / y) := mul_le_mul hd' he' (by positivity) hy'
      _ = x := by field_simp
  -- Conversely `de ≤ x` with `d > y` forces `e ≤ x / y`.
  have hba : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e → M < d → d * e ≤ N → e ≤ K := by
    intro d e hd he hdM hde
    have hx1 : (1 : ℝ) ≤ x := Nat.floor_pos.1 (by nlinarith)
    have hcast : ((d * e : ℕ) : ℝ) ≤ x :=
      le_trans (Nat.cast_le.2 hde) (Nat.floor_le (by linarith))
    have hyd : y < (d : ℝ) := (Nat.floor_lt hy').1 hdM
    have h2 : (e : ℝ) * y ≤ (e : ℝ) * d := mul_le_mul_of_nonneg_left hyd.le (by positivity)
    push_cast at hcast
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hy]
    linarith
  -- The left-hand side, reindexed over the pairs `(d, e)` with `de ≤ x`.
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_filter_add_sum_filter_not (Ioc 0 N) (fun d ↦ d ≤ M)]
  -- The terms with `d ≤ y` make up the first sum on the right.
  have hT1 : ∑ d ∈ (Ioc 0 N).filter (fun d ↦ d ≤ M), f d * ∑ e ∈ Ioc 0 (N / d), g e
      = ∑ d ∈ Ioc 0 M, f d * ∑ e ∈ Ioc 0 (N / d), g e := by
    refine sum_subset (fun d hd ↦ ?_) (fun d hd hdn ↦ ?_)
    · simp only [mem_filter, mem_Ioc] at hd ⊢
      exact ⟨hd.1.1, hd.2⟩
    · simp only [mem_Ioc] at hd
      have hNd : N < d := by
        by_contra hc
        exact hdn (mem_filter.2 ⟨mem_Ioc.2 ⟨hd.1, by omega⟩, hd.2⟩)
      simp [Nat.div_eq_of_lt hNd]
  -- For `e ≤ x / y` the whole range `d ≤ y` sits inside the range `d ≤ x / e`.
  have hMle : ∀ e ∈ Ioc 0 K, (Ioc 0 (N / e)).filter (fun d ↦ d ≤ M) = Ioc 0 M := by
    intro e he
    simp only [mem_Ioc] at he
    have hMN : M ≤ N / e := by
      rcases Nat.eq_zero_or_pos M with hM0 | hM0
      · rw [hM0]; exact Nat.zero_le _
      · exact (Nat.le_div_iff_mul_le (by omega)).2 (hab M e he.1 le_rfl he.2)
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hMN⟩, h2⟩
  -- The second sum minus the correction term keeps exactly the terms with `d > y`.
  have hT2T3 : ∑ e ∈ Ioc 0 K, (∑ d ∈ Ioc 0 (N / e), f d) * g e
        - (∑ d ∈ Ioc 0 M, f d) * ∑ e ∈ Ioc 0 K, g e
      = ∑ e ∈ Ioc 0 K, (∑ d ∈ (Ioc 0 (N / e)).filter (fun d ↦ ¬ d ≤ M), f d) * g e := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e he ↦ ?_
    rw [← sum_filter_add_sum_filter_not (Ioc 0 (N / e)) (fun d ↦ d ≤ M) f, hMle e he]
    ring
  -- Swapping the order of summation in the terms with `d > y`.
  have hswap : ∑ d ∈ (Ioc 0 N).filter (fun d ↦ ¬ d ≤ M), f d * ∑ e ∈ Ioc 0 (N / d), g e
      = ∑ e ∈ Ioc 0 K, (∑ d ∈ (Ioc 0 (N / e)).filter (fun d ↦ ¬ d ≤ M), f d) * g e := by
    have hcond : ∀ d e : ℕ,
        d ∈ (Ioc 0 N).filter (fun d ↦ ¬ d ≤ M) ∧ e ∈ Ioc 0 (N / d) ↔
          d ∈ (Ioc 0 (N / e)).filter (fun d ↦ ¬ d ≤ M) ∧ e ∈ Ioc 0 K := by
      intro d e
      simp only [mem_filter, mem_Ioc, not_le]
      constructor
      · rintro ⟨⟨⟨hd1, hdN⟩, hdM⟩, he1, heN⟩
        have hde : d * e ≤ N := by
          rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).1 heN
        exact ⟨⟨⟨hd1, (Nat.le_div_iff_mul_le (by omega)).2 hde⟩, hdM⟩, he1,
          hba d e hd1 he1 hdM hde⟩
      · rintro ⟨⟨⟨hd1, hdNe⟩, hdM⟩, he1, heK⟩
        have hde : d * e ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdNe
        refine ⟨⟨⟨hd1, le_trans (Nat.le_mul_of_pos_right d he1) hde⟩, hdM⟩, he1, ?_⟩
        rw [mul_comm] at hde
        exact (Nat.le_div_iff_mul_le (by omega)).2 hde
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm' hcond]
  rw [hT1, hswap, add_sub_assoc, hT2T3]

end ArithmeticFunction

section FloorSum

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Removing the floor in a weighted sum.** For coefficients `a : ℕ → 𝕜`, a real `x` and a
finite set `s` of natural numbers,

`‖∑_{d ∈ s} a d ⌊x / d⌋ - x ∑_{d ∈ s} a d / d‖ ≤ ∑_{d ∈ s} ‖a d‖`. -/
theorem norm_sum_mul_floor_div_sub_mul_sum_div_le (a : ℕ → 𝕜) (x : ℝ) (s : Finset ℕ) :
    ‖∑ d ∈ s, a d * (⌊x / d⌋ : 𝕜) - (x : 𝕜) * ∑ d ∈ s, a d / d‖ ≤ ∑ d ∈ s, ‖a d‖ := by
  rw [mul_sum, ← sum_sub_distrib]
  refine norm_sum_le_of_le _ fun d _ ↦ ?_
  have key : a d * (⌊x / d⌋ : 𝕜) - (x : 𝕜) * (a d / d) =
      a d * (((⌊x / d⌋ : ℝ) - x / d : ℝ) : 𝕜) := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · have hd' : (d : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hd
      push_cast
      field_simp
  rw [key, norm_mul, RCLike.norm_ofReal]
  have h1 : |(⌊x / d⌋ : ℝ) - x / d| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Int.lt_floor_add_one (x / d), Int.floor_le (x / d)]
  simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg (a d))

/-- **Removing the floor in a weighted sum**, `Nat.floor` version: for `0 ≤ x`,

`‖∑_{d ∈ s} a d ⌊x / d⌋₊ - x ∑_{d ∈ s} a d / d‖ ≤ ∑_{d ∈ s} ‖a d‖`. -/
theorem norm_sum_mul_natFloor_div_sub_mul_sum_div_le (a : ℕ → 𝕜) {x : ℝ} (hx : 0 ≤ x)
    (s : Finset ℕ) :
    ‖∑ d ∈ s, a d * (⌊x / d⌋₊ : 𝕜) - (x : 𝕜) * ∑ d ∈ s, a d / d‖ ≤ ∑ d ∈ s, ‖a d‖ := by
  convert norm_sum_mul_floor_div_sub_mul_sum_div_le a x s using 5 with d
  rw [← Int.natCast_floor_eq_floor (by positivity), Int.cast_natCast]

end FloorSum
