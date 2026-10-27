/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# The Mertens function and Möbius inversion for summatory functions

This file defines the Mertens function `M(x) = ∑_{n ≤ x} μ(n)` of a real variable, and proves
Möbius inversion for summatory functions of a real variable:
`G(x) = ∑_{n ≤ x} F(x / n)` for all `x ≥ 1` if and only if
`F(x) = ∑_{n ≤ x} μ(n) G(x / n)` for all `x ≥ 1`.

Sums over `n ≤ x` for real `x` are written `∑ n ∈ Finset.Icc 1 ⌊x⌋₊, _`.

## Main definitions

* `ArithmeticFunction.mertens`: the Mertens function.

## Main statements

* `Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors`: the hyperbola reindexing
  `∑_{n ≤ N} ∑_{m ≤ N / n} f n m = ∑_{r ≤ N} ∑_{d ∣ r} f d (r / d)`.
* `ArithmeticFunction.sum_floor_div_eq_iff_sum_moebius_smul_floor_div_eq`: Möbius inversion for
  summatory functions.
-/

@[expose] public section

open Finset

namespace Nat

variable {M : Type*} [AddCommMonoid M]

/-- **Hyperbola reindexing.** The pairs `(n, m)` with `n ≤ N` and `m ≤ N / n` are exactly the
pairs `(d, r / d)` with `r ≤ N` and `d ∣ r`, via `(n, m) ↦ n * m`. -/
theorem sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / n), f n m = ∑ r ∈ Icc 1 N, ∑ d ∈ r.divisors, f d (r / d) := by
  rw [sum_sigma' (Icc 1 N) (fun n => Icc 1 (N / n)) f,
    sum_sigma' (Icc 1 N) (fun r => r.divisors) (fun r d => f d (r / d))]
  refine sum_nbij' (fun p => ⟨p.1 * p.2, p.1⟩) (fun p => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hn1, -⟩, hm1, hmN⟩ := h
    have hnm : n * m ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hn1).1 hmN
    exact ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hnm⟩,
      dvd_mul_right n m, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨r, d⟩ h
    simp only [mem_sigma, mem_Icc] at h ⊢
    obtain ⟨⟨hr1, hrN⟩, hd⟩ := h
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdr : d ≤ r := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
    exact ⟨⟨hd0, by omega⟩, (Nat.one_le_div_iff hd0).2 hdr, Nat.div_le_div_right hrN⟩
  · rintro ⟨n, m⟩ h
    simp only [mem_sigma, mem_Icc] at h
    simp [Nat.mul_div_cancel_left _ (show 0 < n from h.1.1)]
  · rintro ⟨r, d⟩ h
    simp only [mem_sigma] at h
    simp [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors h.2)]
  · rintro ⟨n, m⟩ h
    simp only [mem_sigma, mem_Icc] at h
    simp [Nat.mul_div_cancel_left _ (show 0 < n from h.1.1)]

end Nat

namespace ArithmeticFunction

open scoped Moebius

/-- **The Mertens function** `M(x) = ∑_{n ≤ x} μ(n)`, the summatory function of the Möbius
function, as a function of a real variable. It vanishes for `x < 1`. -/
noncomputable def mertens (x : ℝ) : ℤ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, μ n

theorem mertens_apply (x : ℝ) : mertens x = ∑ n ∈ Icc 1 ⌊x⌋₊, μ n := rfl

/-- The Mertens function vanishes to the left of `1`. -/
theorem mertens_of_lt_one {x : ℝ} (hx : x < 1) : mertens x = 0 := by
  simp [mertens, Nat.floor_eq_zero.2 hx]

/-- At a natural number, the Mertens function is the partial sum of `μ`. -/
@[simp]
theorem mertens_natCast (N : ℕ) : mertens N = ∑ n ∈ Icc 1 N, μ n := by
  simp [mertens]

/-- The trivial bound `|M(x)| ≤ ⌊x⌋`. -/
theorem abs_mertens_le (x : ℝ) : |mertens x| ≤ ⌊x⌋₊ := by
  calc |mertens x| ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, |μ n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, (1 : ℤ) := sum_le_sum fun n _ => abs_moebius_le_one
    _ = ⌊x⌋₊ := by simp

/-- **Möbius inversion for summatory functions.** For functions `F G` of a real variable,
`G(x) = ∑_{n ≤ x} F(x / n)` for all `x ≥ 1` if and only if
`F(x) = ∑_{n ≤ x} μ(n) G(x / n)` for all `x ≥ 1`.

The restriction to `x ≥ 1` cannot be dropped: on `(0, 1)` both sums are empty. -/
theorem sum_floor_div_eq_iff_sum_moebius_smul_floor_div_eq {A : Type*} [AddCommGroup A]
    (F G : ℝ → A) :
    (∀ x : ℝ, 1 ≤ x → G x = ∑ n ∈ Icc 1 ⌊x⌋₊, F (x / n)) ↔
      ∀ x : ℝ, 1 ≤ x → F x = ∑ n ∈ Icc 1 ⌊x⌋₊, μ n • G (x / n) := by
  have hmob : ∀ (r : ℕ) (a : A), (∑ d ∈ r.divisors, μ d • a) = if r = 1 then a else 0 := by
    intro r a
    rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
    split_ifs <;> simp
  -- Collapsing a sum over `r ≤ x` of `δ_{r,1} • H (x / r)`.
  have hcollapse : ∀ (H : ℝ → A) (x : ℝ), 1 ≤ x →
      ∑ r ∈ Icc 1 ⌊x⌋₊, (if r = 1 then H (x / r) else 0) = H x := by
    intro H x hx
    have h1 : 1 ∈ Icc 1 ⌊x⌋₊ := mem_Icc.2 ⟨le_rfl, Nat.one_le_floor_iff _ |>.2 hx⟩
    simp [sum_ite_eq', h1]
  have hdiv : ∀ x : ℝ, 1 ≤ x → ∀ n ∈ Icc 1 ⌊x⌋₊, 1 ≤ x / n ∧ ⌊x / n⌋₊ = ⌊x⌋₊ / n := by
    intro x hx n hn
    obtain ⟨hn1, hnx⟩ := mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    refine ⟨(one_le_div hn0).2 ((Nat.le_floor_iff (by linarith)).1 hnx), Nat.floor_div_natCast _ _⟩
  have hcast : ∀ (x : ℝ) (n m : ℕ), x / n / m = x / ((n * m : ℕ) : ℝ) := by
    intro x n m; rw [div_div, Nat.cast_mul]
  constructor
  · intro hG x hx
    symm
    calc ∑ n ∈ Icc 1 ⌊x⌋₊, μ n • G (x / n)
        = ∑ n ∈ Icc 1 ⌊x⌋₊, ∑ m ∈ Icc 1 (⌊x⌋₊ / n), μ n • F (x / ((n * m : ℕ) : ℝ)) := by
          refine sum_congr rfl fun n hn => ?_
          obtain ⟨h1, hfl⟩ := hdiv x hx n hn
          rw [hG _ h1, hfl, smul_sum]
          simp_rw [hcast]
      _ = ∑ r ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, μ d • F (x / ((d * (r / d) : ℕ) : ℝ)) :=
          Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors _ _
      _ = ∑ r ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, μ d • F (x / r) := by
          refine sum_congr rfl fun r _ => sum_congr rfl fun d hd => ?_
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      _ = F x := by simp_rw [hmob]; exact hcollapse F x hx
  · intro hF x hx
    symm
    calc ∑ n ∈ Icc 1 ⌊x⌋₊, F (x / n)
        = ∑ n ∈ Icc 1 ⌊x⌋₊, ∑ m ∈ Icc 1 (⌊x⌋₊ / n), μ m • G (x / ((n * m : ℕ) : ℝ)) := by
          refine sum_congr rfl fun n hn => ?_
          obtain ⟨h1, hfl⟩ := hdiv x hx n hn
          rw [hF _ h1, hfl]
          simp_rw [hcast]
      _ = ∑ r ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, μ (r / d) • G (x / ((d * (r / d) : ℕ) : ℝ)) :=
          Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors _ _
      _ = ∑ r ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, μ (r / d) • G (x / r) := by
          refine sum_congr rfl fun r _ => sum_congr rfl fun d hd => ?_
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      _ = ∑ r ∈ Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, μ d • G (x / r) :=
          sum_congr rfl fun r _ => Nat.sum_div_divisors r fun d => μ d • G (x / r)
      _ = G x := by simp_rw [hmob]; exact hcollapse G x hx

end ArithmeticFunction
