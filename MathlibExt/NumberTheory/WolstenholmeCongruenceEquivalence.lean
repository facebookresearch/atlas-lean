/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.WolstenholmeBinomialCongruence
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-!
# Equivalent forms of Wolstenholme's congruence

In Kehila's general congruence the first correction vanishes, and the second is a multiple of
`(2 * p).choose p - 2`. Following the proof of Theorem 5, the case `n = -1`, `k = 1` shows that
this common factor is divisible by `p ^ 3`.
-/

namespace MetaMathlibExt

private theorem pow_three_dvd_of_rat_valuation (p : ℕ) (hp : p.Prime) (z : ℤ)
    (h : (z : ℚ) = 0 ∨ 3 ≤ padicValRat p (z : ℚ)) : (p : ℤ) ^ 3 ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  have : Fact p.Prime := ⟨hp⟩
  have hv := h.resolve_left (by exact_mod_cast hz)
  rw [padicValRat.of_int] at hv
  rw [← Int.natCast_pow, Int.natCast_dvd, multiplicity_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)]
  exact_mod_cast hv

-- The order-two correction, for a positive lower index, also works at negative upper indices.
private theorem choose_sub_correction_dvd (p k : ℕ) (n : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ Ring.choose (n * p) ((k + 1) * p) - Ring.choose n (k + 1) -
      Ring.choose n 2 * (((2 * p).choose p : ℤ) - 2) * Ring.choose (n - 2) k := by
  let C (x : ℤ) (i : ℕ) : ℚ := (Ring.choose x i : ℤ)
  let B : ℚ := (2 * p).choose p
  let c (j : ℕ) : ℚ := ∑ s ∈ Finset.range (j + 1),
    if s ≤ k + 1 then C ((j * p : ℕ) : ℤ) (s * p) * C (n - j) (k + 1 - s) else 0
  have pascal (x : ℤ) (i : ℕ) :
      C (x + 1) i = C x i + (if 1 ≤ i then C x (i - 1) else 0) := by
    cases i with
    | zero => simp [C]
    | succ i => simp [C, Ring.choose_succ_succ, add_comm]
  have c₀ : c 0 = C n (k + 1) := by
    simp [c, C]
  have c₁ : c 1 = C n (k + 1) := by
    have h := pascal (n - 1) (k + 1)
    simp only [sub_add_cancel, Nat.le_add_left, ite_true, Nat.add_sub_cancel] at h
    simpa [c, C, Finset.sum_range_succ, Ring.choose_natCast, Ring.choose_zero_right, add_comm]
      using h.symm
  have c₂ : c 2 = C n (k + 1) + (B - 2) * C (n - 2) k := by
    have h₁ := pascal (n - 1) (k + 1)
    have h₂ := pascal (n - 2) (k + 1)
    have h₃ := pascal (n - 2) k
    rw [show n - 2 + 1 = n - 1 by omega] at h₂ h₃
    simp only [sub_add_cancel, Nat.le_add_left, ite_true, Nat.add_sub_cancel] at h₁ h₂
    have hi : (2 ≤ k + 1) ↔ (1 ≤ k) := by omega
    have hj : k + 1 - 2 = k - 1 := by omega
    calc
      c 2 = C (n - 2) (k + 1) + B * C (n - 2) k +
          (if 1 ≤ k then C (n - 2) (k - 1) else 0) := by
        simp only [c, C, B, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ite_true,
          Nat.sub_zero, zero_mul, one_mul, Nat.cast_one, Nat.le_add_left, Nat.add_sub_cancel,
          Nat.cast_ofNat, Ring.choose_natCast, Nat.choose_self, Nat.choose_zero_right,
          Int.cast_natCast, hi, hj]
      _ = _ := by rw [h₁, h₂, h₃]; ring
  let d (l : ℕ) : ℚ :=
    C n l * ∑ j ∈ Finset.range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j
  have d₁ : d 1 = 0 := by
    norm_num [d, Finset.sum_range_succ, c₀, c₁]
  have d₂ : d 2 = C n 2 * (B - 2) * C (n - 2) k := by
    norm_num [d, Finset.sum_range_succ, c₀, c₁, c₂]
    ring
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h := ringChoose_mul_prime_sub_congr_sum_d p 2 (k + 1) n hp (by omega)
  let z : ℤ := Ring.choose (n * p) ((k + 1) * p) - Ring.choose n (k + 1) -
    Ring.choose n 2 * (((2 * p).choose p : ℤ) - 2) * Ring.choose (n - 2) k
  have he : C (n * p) ((k + 1) * p) - C n (k + 1) - ∑ l ∈ Finset.Icc 1 2, d l =
      (z : ℚ) := by
    rw [hI, Finset.sum_pair (by decide), d₁, d₂, zero_add]
    push_cast [z, C, B]
    rfl
  change let X := C (n * p) ((k + 1) * p) - C n (k + 1) - ∑ l ∈ Finset.Icc 1 2, d l
    X = 0 ∨ (C n 3 ≠ 0 ∧ 3 + padicValRat p (C n 3) ≤ padicValRat p X) at h
  dsimp only at h
  rw [he] at h
  apply pow_three_dvd_of_rat_valuation p hp z
  refine h.imp_right fun ⟨_, hv⟩ => ?_
  rw [show padicValRat p (C n 3) = (padicValInt p (Ring.choose n 3) : ℤ) from
    padicValRat.of_int] at hv
  exact (le_add_of_nonneg_right (Int.natCast_nonneg _)).trans hv

-- Apply the correction at n = -1, k = 1, where the negative-index identity
-- turns its remainder into -3/2 times the central binomial difference.
private theorem central_choose_sub_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2 := by
  have h := choose_sub_correction_dvd p 0 (-1) hp hp5
  norm_num [Ring.choose_one_right, Ring.choose_zero_right,
    show Ring.choose (-1 : ℤ) 2 = 1 by decide] at h
  have hneg : 2 * Ring.choose (-(p : ℤ)) p = -((2 * p).choose p : ℤ) := by
    have h' := (ringChoose_neg_mul_mul_eq p 1 1 hp.pos (by decide)).2
    have hodd : (-1 : ℚ) ^ p = -1 := (hp.odd_of_ne_two (by omega)).neg_one_pow
    norm_num [hodd] at h'
    exact_mod_cast (show (2 : ℚ) * (Ring.choose (-(p : ℤ)) p : ℤ) = -((2 * p).choose p : ℚ) by
      linarith only [h'])
  have hmul : (p : ℤ) ^ 3 ∣ 3 * (((2 * p).choose p : ℤ) - 2) := by
    convert dvd_mul_of_dvd_right h (-2 : ℤ) using 1
    linear_combination hneg
  have hcop : (p ^ 3).Coprime 3 :=
    (hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)).pow_left 3
  rw [← Int.natCast_pow, Int.natCast_dvd, Int.natAbs_mul] at hmul
  rw [← Int.natCast_pow, Int.natCast_dvd]
  exact hcop.dvd_of_dvd_mul_left hmul

private theorem choose_mul_prime_sub_dvd (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcentral : (p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2) :
    (p : ℤ) ^ 3 ∣ ((n * p).choose (k * p) : ℤ) - n.choose k := by
  cases k with
  | zero => simp
  | succ k =>
      have h := choose_sub_correction_dvd p k n hp hp5
      have hcorr := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hcentral (Ring.choose (n : ℤ) 2))
        (Ring.choose ((n : ℤ) - 2) k)
      simpa only [sub_add_cancel, ← Nat.cast_mul, Ring.choose_natCast] using dvd_add h hcorr

/-- **Equivalent forms of Wolstenholme's congruence.** Let $p \ge 5$ be a prime and let $n$ and
$k$ be natural numbers. Then the congruences $\binom{2p}{p} \equiv 2$, $\binom{np}{p} \equiv n$ and
$\binom{np}{kp} \equiv \binom{n}{k}$ modulo $p^3$ are equivalent.

By Wolstenholme's theorem all three hold for every such $p$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Corollary 2
(`integers-2026-A32-cor-2`). -/
public theorem choose_two_mul_prime_congr_iff_pow_three (p n k : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2 ↔ (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n) ∧
      ((p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n ↔
        (p : ℤ) ^ 3 ∣ ((n * p).choose (k * p) : ℤ) - n.choose k) := by
  have h₂ := central_choose_sub_dvd p hp hp5
  have h₁ : (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n := by
    simpa using choose_mul_prime_sub_dvd p n 1 hp hp5 h₂
  have hₖ := choose_mul_prime_sub_dvd p n k hp hp5 h₂
  exact ⟨⟨fun _ => h₁, fun _ => h₂⟩, ⟨fun _ => hₖ, fun _ => h₁⟩⟩

end MetaMathlibExt
