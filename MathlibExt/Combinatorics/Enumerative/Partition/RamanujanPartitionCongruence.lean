/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.PentagonalNumber
import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

@[expose] public section

section
/-!
# Ramanujan's partition congruences

Source: Hartosh Singh Bal and Gaurav Bhatnagar, "Glaisher's Divisors and
Infinite Products", Journal of Integer Sequences 27 (2024), Article 24.1.6,
proposition at lines 801–804.
Live TeX: https://cs.uwaterloo.ca/journals/JIS/VOL27/Bhatnagar/bhat4.tex

The source proposition is Ramanujan's partition congruence `p(5m + 4) ≡ 0`
(mod 5), where `p(n)` is the number of unordered integer partitions of `n`.
It holds also at `m = 0`, so quantifying over all `m : ℕ` is faithful.
It also proves the mod-7 congruence `p(7m + 5) ≡ 0` (mod 7), following
S. Ramanujan, "Some properties of p(n), the number of partitions of n",
Proceedings of the Cambridge Philosophical Society 19 (1919), 207–210.
-/

namespace MetaMathlibExt
open MathlibExt

private theorem map_gaussBinom {R S : Type*} [CommRing R] [CommRing S]
    (Q : R) (f : R →+* S) (M k : ℕ) :
    f (gaussBinom Q M k) = gaussBinom (f Q) M k := by
  induction M generalizing k with
  | zero =>
      cases k with
      | zero => simp [map_one]
      | succ k => simp [map_zero]
  | succ M ih =>
      cases k with
      | zero => simp [map_one]
      | succ k =>
          rw [gaussBinom_succ_succ, gaussBinom_succ_succ, map_add, map_mul,
            map_pow, ih, ih]

/-- Rothe's finite q-binomial theorem. -/
private theorem prod_one_add_mul_pow_eq_sum_gaussBinom {R : Type*}
    [CommRing R] (Q x : R) (M : ℕ) :
    ∏ j ∈ Finset.range M, (1 + x * Q ^ j)
      = ∑ k ∈ Finset.range (M + 1),
        gaussBinom Q M k * Q ^ (k.choose 2) * x ^ k := by
  induction M generalizing x with
  | zero =>
      have hc0 : (0 : ℕ).choose 2 = 0 := by decide
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_zero,
        Finset.sum_range_one, gaussBinom_zero_right, hc0]
      simp
  | succ M ih =>
      have hchoose : ∀ k : ℕ, k.choose 2 + k = (k + 1).choose 2 := by
        intro k
        have h := Nat.choose_succ_succ' k 1
        rw [Nat.choose_one_right] at h
        have h2 : (1 : ℕ) + 1 = 2 := rfl
        rw [h2] at h
        omega
      have hterm : ∀ k : ℕ, gaussBinom Q M k * Q ^ (k.choose 2)
            * (x * Q) ^ k
          = gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k := by
        intro k
        have hQQ : Q ^ (k.choose 2) * Q ^ k = Q ^ ((k + 1).choose 2) := by
          rw [← pow_add, hchoose k]
        calc gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k
            = (Q ^ (k.choose 2) * Q ^ k)
              * (gaussBinom Q M k * x ^ k) := by
                rw [mul_pow]
                ring
          _ = gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k := by
                rw [hQQ]
                ring
      have hterm2 : ∀ k : ℕ, gaussBinom Q (M + 1) (k + 1)
            * Q ^ ((k + 1).choose 2) * x ^ (k + 1)
          = x * (gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k)
            + gaussBinom Q M (k + 1) * Q ^ ((k + 1 + 1).choose 2)
              * x ^ (k + 1) := by
        intro k
        rw [gaussBinom_succ_succ]
        have hQQ2 : Q ^ (k + 1) * Q ^ ((k + 1).choose 2)
            = Q ^ ((k + 1 + 1).choose 2) := by
          rw [← pow_add]
          congr 1
          have h := hchoose (k + 1)
          omega
        rw [pow_succ' x k, ← hQQ2]
        ring
      set S : R := ∑ k ∈ Finset.range (M + 1),
        gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k with hS
      set T : R := ∑ k ∈ Finset.range (M + 1),
        gaussBinom Q M (k + 1) * Q ^ ((k + 1 + 1).choose 2) * x ^ (k + 1)
        with hT
      have hLHS : ∏ j ∈ Finset.range (M + 1), (1 + x * Q ^ j)
          = S * (1 + x) := by
        rw [Finset.prod_range_succ']
        have hprod : (∏ k ∈ Finset.range M, (1 + x * Q ^ (k + 1)))
            = ∑ k ∈ Finset.range (M + 1),
              gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k := by
          rw [← ih (x * Q)]
          apply Finset.prod_congr rfl
          intro j _
          rw [pow_succ']
          ring
        rw [hprod]
        have hsum : (∑ k ∈ Finset.range (M + 1),
            gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k) = S :=
          Finset.sum_congr rfl (fun k _ => hterm k)
        rw [hsum]
        simp
      have hRHS : ∑ k ∈ Finset.range (M + 1 + 1),
            gaussBinom Q (M + 1) k * Q ^ (k.choose 2) * x ^ k
          = (x * S + T) + 1 := by
        rw [Finset.sum_range_succ']
        have h0 : gaussBinom Q (M + 1) 0 * Q ^ ((0 : ℕ).choose 2)
            * x ^ (0 : ℕ) = 1 := by
          have hc0 : (0 : ℕ).choose 2 = 0 := by decide
          rw [gaussBinom_zero_right, hc0]
          simp
        have hrest : (∑ k ∈ Finset.range (M + 1),
            gaussBinom Q (M + 1) (k + 1) * Q ^ ((k + 1).choose 2)
              * x ^ (k + 1)) = x * S + T := by
          have hcongr : (∑ k ∈ Finset.range (M + 1),
              gaussBinom Q (M + 1) (k + 1) * Q ^ ((k + 1).choose 2)
                * x ^ (k + 1))
              = ∑ k ∈ Finset.range (M + 1),
                (x * (gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k)
                  + gaussBinom Q M (k + 1)
                    * Q ^ ((k + 1 + 1).choose 2) * x ^ (k + 1)) :=
            Finset.sum_congr rfl (fun k _ => hterm2 k)
          rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS,
            ← hT]
        rw [hrest, h0]
      have hTS : T + 1 = S := by
        have hU1 : (∑ k ∈ Finset.range (M + 1 + 1),
            gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k)
            = S + gaussBinom Q M (M + 1)
              * Q ^ ((M + 1 + 1).choose 2) * x ^ (M + 1) :=
          Finset.sum_range_succ _ _
        have hU2 : (∑ k ∈ Finset.range (M + 1 + 1),
            gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ k)
            = T + gaussBinom Q M 0 * Q ^ ((0 + 1).choose 2)
              * x ^ (0 : ℕ) :=
          Finset.sum_range_succ' _ _
        have hM1 : gaussBinom Q M (M + 1) * Q ^ ((M + 1 + 1).choose 2)
            * x ^ (M + 1) = 0 := by
          rw [gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M)]
          simp
        have h00 : gaussBinom Q M 0 * Q ^ ((0 + 1).choose 2)
            * x ^ (0 : ℕ) = 1 := by
          have hc1 : (0 + 1 : ℕ).choose 2 = 0 := by decide
          rw [gaussBinom_zero_right, hc1]
          simp
        rw [hM1] at hU1
        rw [h00] at hU2
        linear_combination hU1 - hU2
      calc ∏ j ∈ Finset.range (M + 1), (1 + x * Q ^ j)
          = S * (1 + x) := hLHS
        _ = (x * S + T) + 1 := by linear_combination -hTS
        _ = ∑ k ∈ Finset.range (M + 1 + 1),
              gaussBinom Q (M + 1) k * Q ^ (k.choose 2) * x ^ k :=
            hRHS.symm

/-- **Twice a triangular number.** For every natural number $a$, $2\binom{a+1}{2} = a(a+1)$. -/
theorem two_mul_choose_two_succ (a : ℕ) : 2 * (a + 1).choose 2 = a * (a + 1) := by
  have h := Nat.choose_two_right (a + 1)
  have hpred : (a + 1) - 1 = a := Nat.add_sub_cancel a 1
  rw [hpred] at h
  have hev : Even ((a + 1) * ((a + 1) - 1)) := Nat.even_mul_pred_self (a + 1)
  rw [hpred] at hev
  have heven : 2 ∣ (a + 1) * a := Even.two_dvd hev
  have hcancel : (a + 1) * a / 2 * 2 = (a + 1) * a := Nat.div_mul_cancel heven
  calc 2 * (a + 1).choose 2
      = 2 * ((a + 1) * a / 2) := by rw [h]
    _ = (a + 1) * a / 2 * 2 := Nat.mul_comm _ _
    _ = (a + 1) * a := hcancel
    _ = a * (a + 1) := Nat.mul_comm _ _

private theorem five_dvd_two_mul_add_one_of_pentagonal_add_triangle
    (k : ℤ) (t : ℕ)
    (h : 5 ∣ pentagonal k + (t + 1).choose 2 + 1) :
    5 ∣ 2 * t + 1 := by
  have hcast : (((pentagonal k + (t + 1).choose 2 + 1 : ℕ)) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  have h2 : (2 : ZMod 5) * (((pentagonal k + (t + 1).choose 2 + 1 : ℕ)) : ZMod 5) = 0 := by
    rw [hcast, mul_zero]
  push_cast at h2
  have hpent : (2 : ZMod 5) * (((pentagonal k : ℕ)) : ZMod 5)
      = ((k * (3 * k - 1) : ℤ) : ZMod 5) := by
    have hpk := two_mul_natCast_pentagonal k
    have hcc : (((2 * (pentagonal k : ℤ) : ℤ)) : ZMod 5) = (((k * (3 * k - 1) : ℤ)) : ZMod 5) := by
      rw [hpk]
    push_cast at hcc
    simpa using hcc
  have htri : (2 : ZMod 5) * ((((t + 1).choose 2 : ℕ)) : ZMod 5)
      = (t : ZMod 5) * ((t : ZMod 5) + 1) := by
    have h2T := two_mul_choose_two_succ t
    have hcc : ((((2 * (t + 1).choose 2 : ℕ))) : ZMod 5) = ((((t * (t + 1) : ℕ))) : ZMod 5) := by
      rw [h2T]
    push_cast at hcc ⊢
    simpa [Nat.cast_mul, Nat.cast_add] using hcc
  have h2dist : (2 : ZMod 5) * ((pentagonal k : ℕ) : ZMod 5)
      + (2 : ZMod 5) * ((((t + 1).choose 2 : ℕ)) : ZMod 5) + 2 = 0 := by
    have h2copy := h2
    rw [mul_add, mul_add, mul_one] at h2copy
    exact h2copy
  rw [hpent, htri] at h2dist
  have key : ∀ x y : ZMod 5, x * (3 * x - 1) + y * (y + 1) + 2 = 0 → 2 * y + 1 = 0 := by
    decide
  have hcast2 : (((k * (3 * k - 1) : ℤ)) : ZMod 5)
      = (k : ZMod 5) * (3 * (k : ZMod 5) - 1) := by push_cast; ring
  rw [hcast2] at h2dist
  have hfin : (2 * (t : ZMod 5) + 1) = 0 := key _ _ h2dist
  have hzero : ((((2 * t + 1 : ℕ))) : ZMod 5) = 0 := by
    push_cast
    simpa using hfin
  rwa [ZMod.natCast_eq_zero_iff] at hzero

/-- **Jacobi's cube series.** Jacobi's cube series is the formal power series
$J(X) = \sum_{t \ge 0} (-1)^t (2t+1) X^{t(t+1)/2}$ in $\mathbb{Z}[[X]]$: for each natural
number $t$ its coefficient at the triangular number $t(t+1)/2$ is $(-1)^t (2t+1)$, and all its
other coefficients are $0$. -/
noncomputable def jacobiCubeSeries : PowerSeries ℤ :=
  PowerSeries.mk fun b =>
    ∑ t ∈ Finset.range (b + 1),
      (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * t + 1) else 0)

/-- **Coefficients of Jacobi's cube series at triangular numbers.** Let $J(X)$ be Jacobi's cube
series. For every natural number $t$, the coefficient of $X^{t(t+1)/2}$ in $J(X)$ is
$(-1)^t (2t+1)$. -/
theorem coeff_jacobiCubeSeries_triangle (t : ℕ) :
    PowerSeries.coeff ((t + 1).choose 2) jacobiCubeSeries = (-1 : ℤ) ^ t * (2 * t + 1) := by
  unfold jacobiCubeSeries
  rw [PowerSeries.coeff_mk]
  have hmono : StrictMono (fun t : ℕ => (t + 1).choose 2) := by
    intro a b hab
    simp only
    have h2a := two_mul_choose_two_succ a
    have h2b := two_mul_choose_two_succ b
    nlinarith [h2a, h2b]
  have hsum : (∑ s ∈ Finset.range ((t + 1).choose 2 + 1),
      (if (s + 1).choose 2 = (t + 1).choose 2 then (-1 : ℤ) ^ s * (2 * s + 1) else 0))
      = (if (t + 1).choose 2 = (t + 1).choose 2 then (-1 : ℤ) ^ t * (2 * t + 1) else 0) := by
    apply Finset.sum_eq_single t
    · intro s _ hst
      by_cases hss : (s + 1).choose 2 = (t + 1).choose 2
      · exfalso; exact hst (hmono.injective hss)
      · rw [ite_eq_right hss]
    · intro ht
      have hle : t ≤ (t + 1).choose 2 := by
        rcases Nat.eq_zero_or_pos t with rfl | hp
        · simp
        · have h2 := two_mul_choose_two_succ t
          nlinarith
      simp [Finset.mem_range] at ht
      omega
  rw [hsum, ite_eq_left rfl]

/-- **Vanishing coefficients of Jacobi's cube series.** Let $J(X)$ be Jacobi's cube series. If a
natural number $b$ is not of the form $t(t+1)/2$ for any natural number $t$, then the coefficient
of $X^b$ in $J(X)$ is $0$. -/
theorem coeff_jacobiCubeSeries_eq_zero {b : ℕ} (hb : ∀ t : ℕ, (t + 1).choose 2 ≠ b) :
    PowerSeries.coeff b jacobiCubeSeries = 0 := by
  unfold jacobiCubeSeries
  rw [PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  rw [ite_eq_right (hb t)]

private theorem tri_ge (t : ℕ) : t ≤ (t + 1).choose 2 ∨ t = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | hp
  · exact Or.inr rfl
  · left
    have h2 := two_mul_choose_two_succ t
    nlinarith

private theorem X_pow_succ_dvd_jacobiCubeSeries_sub_sum (n : ℕ) :
    PowerSeries.X ^ (n + 1) ∣ (jacobiCubeSeries -
      ∑ t ∈ Finset.range (n + 1),
        PowerSeries.C ((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1))
          * PowerSeries.X ^ ((t + 1).choose 2)) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro b hb
  have hb_le : b ≤ n := Nat.lt_succ_iff.mp hb
  have hJ : PowerSeries.coeff b jacobiCubeSeries
      = ∑ t ∈ Finset.range (b + 1),
        (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * (t : ℤ) + 1)
          else 0) := by
    unfold jacobiCubeSeries
    rw [PowerSeries.coeff_mk]
  have hP : PowerSeries.coeff b
        (∑ t ∈ Finset.range (n + 1),
          PowerSeries.C ((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1))
            * PowerSeries.X ^ ((t + 1).choose 2))
      = ∑ t ∈ Finset.range (n + 1),
        (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * (t : ℤ) + 1)
          else 0) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [PowerSeries.coeff_C_mul_X_pow]
    by_cases htb : (t + 1).choose 2 = b
    · have h2 : b = (t + 1).choose 2 := htb.symm
      rw [ite_eq_left h2, ite_eq_left htb]
    · have h2 : ¬ (b = (t + 1).choose 2) := fun h => htb h.symm
      rw [ite_eq_right h2, ite_eq_right htb]
  have hsub : PowerSeries.coeff b
        (jacobiCubeSeries -
          ∑ t ∈ Finset.range (n + 1),
            PowerSeries.C ((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1))
              * PowerSeries.X ^ ((t + 1).choose 2))
      = PowerSeries.coeff b jacobiCubeSeries
        - PowerSeries.coeff b
          (∑ t ∈ Finset.range (n + 1),
            PowerSeries.C ((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1))
              * PowerSeries.X ^ ((t + 1).choose 2)) := by
    rw [map_sub]
  rw [hsub, hJ, hP]
  have hsub2 : Finset.range (b + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  have heq : (∑ t ∈ Finset.range (b + 1),
        (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * (t : ℤ) + 1)
          else 0))
      = (∑ t ∈ Finset.range (n + 1),
        (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * (t : ℤ) + 1)
          else 0)) := by
    apply Finset.sum_subset hsub2
    intro t ht_mem ht_not
    have hlt : t < n + 1 := Finset.mem_range.mp ht_mem
    have hnb : ¬ t < b + 1 := fun h => ht_not (Finset.mem_range.mpr h)
    rw [ite_eq_right]
    intro hTb
    have hle : t ≤ (t + 1).choose 2 := by
      rcases tri_ge t with h | h
      · exact h
      · omega
    omega
  rw [heq, sub_self]

private theorem coeff_qPochFin_succ_sub (M : ℕ) :
    qPochFin (PowerSeries.X : PowerSeries ℤ) (M + 1)
      = qPochFin (PowerSeries.X : PowerSeries ℤ) M
        - PowerSeries.X ^ (M + 1)
          * qPochFin (PowerSeries.X : PowerSeries ℤ) M := by
  rw [qPochFin_succ]
  ring

private theorem coeff_qPochFin_stable_aux (d M k : ℕ) (hdM : d ≤ M) :
    PowerSeries.coeff d (qPochFin (PowerSeries.X : PowerSeries ℤ) (M + k))
      = PowerSeries.coeff d
        (qPochFin (PowerSeries.X : PowerSeries ℤ) M) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hMk : M + (k + 1) = (M + k) + 1 := by omega
      have hle : ¬ (M + k) + 1 ≤ d := by omega
      rw [hMk, coeff_qPochFin_succ_sub, map_sub,
        PowerSeries.coeff_X_pow_mul', ite_eq_right hle, sub_zero]
      exact ih

private theorem coeff_qPochFin_stable (d M M' : ℕ) (hdM : d ≤ M)
    (hMM' : M ≤ M') :
    PowerSeries.coeff d (qPochFin (PowerSeries.X : PowerSeries ℤ) M')
      = PowerSeries.coeff d
        (qPochFin (PowerSeries.X : PowerSeries ℤ) M) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMM'
  exact coeff_qPochFin_stable_aux d M k hdM

/-- Truncation: `X^(M+1)` divides `E - P_M` in `ℤ⟦X⟧`. -/
private theorem X_pow_succ_dvd_pentagonalSeries_sub_qPochFin (M : ℕ) :
    PowerSeries.X ^ (M + 1)
      ∣ (PowerSeries.pentagonalSeries ℤ
        - qPochFin (PowerSeries.X : PowerSeries ℤ) M) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro d hd
  have hdM : d ≤ M := by omega
  rw [map_sub]
  have hev : ∀ᶠ s : Finset ℕ in Filter.atTop,
      (∏ n ∈ s, (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ)).coeff d
        = (PowerSeries.pentagonalSeries ℤ).coeff d :=
    PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ d
  rw [Filter.eventually_atTop] at hev
  obtain ⟨s0, hs0⟩ := hev
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s0
  have hsub : s0 ⊆ Finset.range (N + M) :=
    hN.trans (Finset.range_subset_range.mpr (Nat.le_add_right N M))
  have hcoeff := hs0 (Finset.range (N + M)) hsub
  have hstab := coeff_qPochFin_stable d M (N + M) hdM (Nat.le_add_left M N)
  have hPE : qPochFin (PowerSeries.X : PowerSeries ℤ) (N + M)
      = ∏ n ∈ Finset.range (N + M),
        (1 - PowerSeries.X ^ (n + 1)) := rfl
  rw [hPE] at hstab
  have heq : (PowerSeries.pentagonalSeries ℤ).coeff d
      = PowerSeries.coeff d
        (qPochFin (PowerSeries.X : PowerSeries ℤ) M) :=
    hcoeff.symm.trans hstab
  rw [heq, sub_self]

private theorem qPochFin_X_ne_zero (m : ℕ) :
    qPochFin (PowerSeries.X : PowerSeries ℤ) m ≠ 0 := by
  unfold qPochFin
  rw [Finset.prod_ne_zero_iff]
  intro i _ hcon
  have hX : PowerSeries.coeff 0
      ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) = 0 := by
    rw [PowerSeries.coeff_X_pow]
    exact ite_eq_right (by omega : ¬ (0 : ℕ) = i + 1)
  have h1 : PowerSeries.coeff 0
      (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ) = 1 := by
    rw [map_sub, hX, sub_zero, PowerSeries.coeff_one]
    exact ite_eq_left rfl
  rw [hcon] at h1
  simp at h1

private theorem gaussBinom_symm (M k : ℕ) (h : k ≤ M) :
    gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
      = gaussBinom (PowerSeries.X : PowerSeries ℤ) M (M - k) := by
  have h1 := gaussBinom_mul_qPochFin_mul_qPochFin
    (PowerSeries.X : PowerSeries ℤ) M k h
  have hkM : M - (M - k) = k := Nat.sub_sub_self h
  have h2 := gaussBinom_mul_qPochFin_mul_qPochFin
    (PowerSeries.X : PowerSeries ℤ) M (M - k) (Nat.sub_le M k)
  rw [hkM] at h2
  have hW : qPochFin (PowerSeries.X : PowerSeries ℤ) k
      * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k) ≠ 0 :=
    mul_ne_zero (qPochFin_X_ne_zero k) (qPochFin_X_ne_zero (M - k))
  have heq : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
      = gaussBinom (PowerSeries.X : PowerSeries ℤ) M (M - k)
        * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)) := by
    have e1 : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
          * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
            * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
        = qPochFin (PowerSeries.X : PowerSeries ℤ) M := by
      have hexp : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
            * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
              * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
          = gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
            * qPochFin (PowerSeries.X : PowerSeries ℤ) k
            * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k) := by
        ring
      rw [hexp, h1]
    have e2 : gaussBinom (PowerSeries.X : PowerSeries ℤ) M (M - k)
          * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
            * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
        = qPochFin (PowerSeries.X : PowerSeries ℤ) M := by
      have hexp : gaussBinom (PowerSeries.X : PowerSeries ℤ) M (M - k)
            * (qPochFin (PowerSeries.X : PowerSeries ℤ) k
              * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
          = gaussBinom (PowerSeries.X : PowerSeries ℤ) M (M - k)
            * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)
            * qPochFin (PowerSeries.X : PowerSeries ℤ) k := by
        ring
      rw [hexp, h2]
    rw [e1, e2]
  exact mul_right_cancel₀ hW heq

private theorem gaussBinom_mul_qPochFin_eq_prod (M k : ℕ) (h : k ≤ M) :
    gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
      * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)
      = ∏ i ∈ Finset.range (M - k),
        (1 - PowerSeries.X ^ (k + 1 + i)) := by
  have h1 := gaussBinom_mul_qPochFin_mul_qPochFin
    (PowerSeries.X : PowerSeries ℤ) M k h
  have hsplit : qPochFin (PowerSeries.X : PowerSeries ℤ) M
      = qPochFin (PowerSeries.X : PowerSeries ℤ) k
        * ∏ i ∈ Finset.range (M - k),
          (1 - PowerSeries.X ^ (k + 1 + i)) := by
    have hMk : M = k + (M - k) := (Nat.add_sub_cancel' h).symm
    unfold qPochFin
    conv_lhs => rw [hMk]
    rw [Finset.prod_range_add]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have he : (k + i) + 1 = k + 1 + i := by omega
    change (1 : PowerSeries ℤ) - PowerSeries.X ^ ((k + i) + 1)
      = 1 - PowerSeries.X ^ (k + 1 + i)
    rw [he]
  have key : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)
        * qPochFin (PowerSeries.X : PowerSeries ℤ) k
      = (∏ i ∈ Finset.range (M - k),
          (1 - PowerSeries.X ^ (k + 1 + i)))
        * qPochFin (PowerSeries.X : PowerSeries ℤ) k := by
    have hcomm : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)
          * qPochFin (PowerSeries.X : PowerSeries ℤ) k
        = gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k) := by
      ring
    rw [hcomm, h1, hsplit]
    ring
  exact mul_right_cancel₀ (qPochFin_X_ne_zero k) key

private theorem X_pow_succ_dvd_prod_sub_one (k K : ℕ) :
    PowerSeries.X ^ (k + 1)
      ∣ ((∏ i ∈ Finset.range K,
          (1 - PowerSeries.X ^ (k + 1 + i) : PowerSeries ℤ)) - 1) := by
  induction K with
  | zero =>
      rw [Finset.prod_range_zero, sub_self]
      exact dvd_zero _
  | succ K ih =>
      rw [Finset.prod_range_succ]
      have hexp : ∀ A t : PowerSeries ℤ, A * (1 - t) - 1
          = (A - 1) - A * t := by
        intro A t
        ring
      rw [hexp]
      have hpow : (PowerSeries.X : PowerSeries ℤ) ^ (k + 1 + K)
          = PowerSeries.X ^ (k + 1) * PowerSeries.X ^ K := by
        rw [← pow_add]
      rw [hpow]
      have hdiv : PowerSeries.X ^ (k + 1)
          ∣ (∏ i ∈ Finset.range K,
              (1 - PowerSeries.X ^ (k + 1 + i) : PowerSeries ℤ))
            * (PowerSeries.X ^ (k + 1) * PowerSeries.X ^ K) := by
        have hrw : (∏ i ∈ Finset.range K,
                (1 - PowerSeries.X ^ (k + 1 + i) : PowerSeries ℤ))
              * (PowerSeries.X ^ (k + 1) * PowerSeries.X ^ K)
            = ((∏ i ∈ Finset.range K,
                (1 - PowerSeries.X ^ (k + 1 + i) : PowerSeries ℤ))
              * PowerSeries.X ^ K) * PowerSeries.X ^ (k + 1) := by
          ring
        rw [hrw]
        exact dvd_mul_left _ _
      exact dvd_sub ih hdiv

/-- Gaussian binomials tend to `1 / E`: if `2 * k ≤ M` then
`X^(k+1)` divides `G(M, k) * E - 1`. -/
private theorem X_pow_succ_dvd_gaussBinom_mul_pentagonalSeries_sub_one
    (M k : ℕ) (h : 2 * k ≤ M) :
    PowerSeries.X ^ (k + 1)
      ∣ (gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * PowerSeries.pentagonalSeries ℤ - 1) := by
  have hle : k ≤ M - k := by omega
  have hN4 := X_pow_succ_dvd_pentagonalSeries_sub_qPochFin (M - k)
  have hpow_le : k + 1 ≤ (M - k) + 1 := by omega
  have hfirst : PowerSeries.X ^ (k + 1)
      ∣ gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * (PowerSeries.pentagonalSeries ℤ
          - qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k)) :=
    (pow_dvd_pow _ hpow_le).trans (hN4.mul_left _)
  have hGP := gaussBinom_mul_qPochFin_eq_prod M k (by omega : k ≤ M)
  have hsecond : PowerSeries.X ^ (k + 1)
      ∣ (gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k) - 1) := by
    rw [hGP]
    exact X_pow_succ_dvd_prod_sub_one k (M - k)
  have hdecomp : gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * PowerSeries.pentagonalSeries ℤ - 1
      = gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
        * (PowerSeries.pentagonalSeries ℤ
          - qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k))
        + (gaussBinom (PowerSeries.X : PowerSeries ℤ) M k
          * qPochFin (PowerSeries.X : PowerSeries ℤ) (M - k) - 1) := by
    ring
  rw [hdecomp]
  exact dvd_add hfirst hsecond

private noncomputable def finiteJacobiU (n : ℕ) :
    Polynomial (PowerSeries ℤ) :=
  ∏ i ∈ Finset.range n,
    ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
      * Polynomial.X)
      * (Polynomial.X
        - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))

private noncomputable def finiteJacobiPoly (n : ℕ) :
    Polynomial (PowerSeries ℤ) :=
  (1 - Polynomial.X) * finiteJacobiU n

private theorem finiteJacobiPoly_comp_C_mul_X (n : ℕ) :
    (finiteJacobiPoly n).comp
        (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n) * Polynomial.X)
      = Polynomial.C ((-1) ^ n * PowerSeries.X ^ ((n + 1).choose 2))
        * ∏ j ∈ Finset.range (2 * n + 1),
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ j)
            * Polynomial.X) := by
  set q : Polynomial (PowerSeries ℤ) :=
    Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n) * Polynomial.X
    with hq
  have hF1 : ∀ i : ℕ, ((1 - Polynomial.C
      ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) * Polynomial.X)).comp q
      = 1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i))
        * Polynomial.X := by
    intro i
    rw [hq, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    have hpow : (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)
          * (PowerSeries.X : PowerSeries ℤ) ^ n
        = (PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i) := by
      rw [← pow_add]
      congr 1
      omega
    have hC : Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
          * (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
            * Polynomial.X)
        = Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i))
          * Polynomial.X := by
      rw [← mul_assoc, ← Polynomial.C_mul, hpow]
    rw [hC]
  have hF2 : ∀ i : ℕ, i < n →
      ((Polynomial.X - Polynomial.C
        ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))).comp q
      = -(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
        * (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
          * Polynomial.X) := by
    intro i hi
    rw [hq, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hpow : (PowerSeries.X : PowerSeries ℤ) ^ n
        = (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)
          * (PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, Polynomial.C_mul]
    ring
  have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (i + 1)
      = (m + 1).choose 2 := by
    intro m
    induction m with
    | zero =>
        rw [Finset.sum_range_zero]
        decide
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h := Nat.choose_succ_succ' (m + 1) 1
        rw [Nat.choose_one_right] at h
        have h2 : (1 : ℕ) + 1 = 2 := rfl
        rw [h2] at h
        omega
  have hscalar : ∏ i ∈ Finset.range n,
        (-(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))
      = Polynomial.C
        ((-1) ^ n * PowerSeries.X ^ ((n + 1).choose 2)) := by
    have hC : ∀ i : ℕ, -(Polynomial.C
          ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
        = Polynomial.C (-((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) := by
      intro i
      simp
    have hZ : ∏ i ∈ Finset.range n,
          (-((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
        = (-1) ^ n * PowerSeries.X ^ ((n + 1).choose 2) := by
      have hneg : ∀ i : ℕ, (-((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
          = (-1) * (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) := by
        intro i
        ring
      simp only [hneg, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range, Finset.prod_pow_eq_pow_sum, hsum n]
    simp only [hC, ← map_prod]
    rw [hZ]
  have hreflect : ∏ i ∈ Finset.range n,
        (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
          * Polynomial.X)
      = ∏ i ∈ Finset.range n,
        (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ i)
          * Polynomial.X) := by
    have h := Finset.prod_range_reflect
      (fun j : ℕ => 1 - Polynomial.C
        ((PowerSeries.X : PowerSeries ℤ) ^ j) * Polynomial.X) n
    exact h
  have hsplit : ∏ j ∈ Finset.range (2 * n + 1),
        (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ j)
          * Polynomial.X)
      = (∏ i ∈ Finset.range n,
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ i)
            * Polynomial.X))
        * ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
            * Polynomial.X)
          * ∏ i ∈ Finset.range n,
            (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i))
              * Polynomial.X)) := by
    have h2n : 2 * n + 1 = n + (n + 1) := by omega
    rw [h2n, Finset.prod_range_add]
    congr 1
    rw [Finset.prod_range_succ']
    have hg0 : (1 - Polynomial.C
          ((PowerSeries.X : PowerSeries ℤ) ^ (n + 0)) * Polynomial.X)
        = 1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
          * Polynomial.X := by
      rw [Nat.add_zero]
    have hcongr : (∏ j ∈ Finset.range n,
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + (j + 1)))
            * Polynomial.X))
        = ∏ j ∈ Finset.range n,
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + j))
            * Polynomial.X) := by
      apply Finset.prod_congr rfl
      intro j _
      have he : n + (j + 1) = n + 1 + j := by omega
      rw [he]
    rw [hcongr, hg0]
    ring
  unfold finiteJacobiPoly finiteJacobiU
  rw [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_comp, Polynomial.prod_comp]
  have hinner : ∀ i ∈ Finset.range n,
      ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
        * Polynomial.X)
        * (Polynomial.X - Polynomial.C
          ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))).comp q
      = (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i))
          * Polynomial.X)
        * (-(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
          * (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
            * Polynomial.X)) := by
    intro i hi
    rw [Polynomial.mul_comp, hF1 i, hF2 i (Finset.mem_range.mp hi)]
  have hprod : (∏ i ∈ Finset.range n,
        ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
          * Polynomial.X)
          * (Polynomial.X - Polynomial.C
            ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))).comp q)
      = ∏ i ∈ Finset.range n,
        ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n + 1 + i))
            * Polynomial.X)
          * (-(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
            * (1 - Polynomial.C
              ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
              * Polynomial.X))) :=
    Finset.prod_congr rfl hinner
  rw [hprod, Finset.prod_mul_distrib]
  have hF2split : (∏ i ∈ Finset.range n,
        (-(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
          * (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
            * Polynomial.X)))
      = (∏ i ∈ Finset.range n,
          (-(Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))))
        * ∏ i ∈ Finset.range n,
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (n - 1 - i))
            * Polynomial.X) :=
    Finset.prod_mul_distrib
  rw [hF2split, hscalar, hreflect, hsplit, hq]
  ring

private def jacobiExponent (n k : ℕ) : ℕ :=
  (n + 1 - k).choose 2 + (k - n).choose 2

private theorem jacobiExponent_add_mul (n k : ℕ) :
    jacobiExponent n k + n * k
      = (n + 1).choose 2 + k.choose 2 := by
  have h2c : ∀ a : ℕ, 2 * a.choose 2 = a * (a - 1) := by
    intro a
    cases a with
    | zero => decide
    | succ a =>
        have h := two_mul_choose_two_succ a
        have hs : (a + 1) - 1 = a := Nat.add_sub_cancel a 1
        rw [hs, h]
        ring
  suffices h : 2 * ((n + 1 - k).choose 2) + 2 * ((k - n).choose 2)
      + 2 * (n * k)
      = 2 * ((n + 1).choose 2) + 2 * (k.choose 2) by
    unfold jacobiExponent
    omega
  rw [h2c, h2c, h2c, h2c]
  by_cases hkn : k ≤ n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    cases k with
    | zero =>
        have s1 : 0 + d + 1 - 0 = d + 1 := by omega
        have s2 : d + 1 - 1 = d := by omega
        have s3 : 0 - (0 + d) = 0 := by omega
        have s4 : (0 + d + 1) - 1 = 0 + d := by omega
        have s5 : (0 : ℕ) - 1 = 0 := by omega
        rw [s1, s2, s3, s4, s5]
        ring
    | succ k =>
        have t1 : k + 1 + d + 1 - (k + 1) = d + 1 := by omega
        have t2 : d + 1 - 1 = d := by omega
        have t3 : (k + 1) - (k + 1 + d) = 0 := by omega
        have t4 : (k + 1 + d + 1) - 1 = k + 1 + d := by omega
        have t5 : (k + 1) - 1 = k := by omega
        rw [t1, t2, t3, t4, t5]
        ring
  · have hnk : n + 1 ≤ k := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    have u1 : n + 1 - (n + 1 + d) = 0 := by omega
    have u2 : (n + 1 + d) - n = d + 1 := by omega
    have u3 : d + 1 - 1 = d := by omega
    have u4 : (n + 1) - 1 = n := by omega
    have u5 : (n + 1 + d) - 1 = n + d := by omega
    rw [u1, u2, u3, u4, u5]
    ring

private theorem jacobiExponent_symm (n k : ℕ) (h : k ≤ 2 * n + 1) :
    jacobiExponent n (2 * n + 1 - k) = jacobiExponent n k := by
  unfold jacobiExponent
  have e1 : n + 1 - (2 * n + 1 - k) = k - n := by omega
  have e2 : (2 * n + 1 - k) - n = n + 1 - k := by omega
  rw [e1, e2]
  exact add_comm _ _

private theorem jacobiExponent_sub (n m : ℕ) (h : m ≤ n) :
    jacobiExponent n (n - m) = (m + 1).choose 2 := by
  unfold jacobiExponent
  have e1 : n + 1 - (n - m) = m + 1 := by omega
  have e2 : (n - m) - n = 0 := by omega
  have hc0 : (0 : ℕ).choose 2 = 0 := by decide
  rw [e1, e2, hc0, add_zero]

private noncomputable def jacobiCoeff (n k : ℕ) : PowerSeries ℤ :=
  (-1) ^ (n + k) * PowerSeries.X ^ (jacobiExponent n k)
    * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1) k

private theorem finiteJacobiPoly_eq_sum (n : ℕ) :
    finiteJacobiPoly n
      = ∑ k ∈ Finset.range (2 * n + 1 + 1),
        Polynomial.C (jacobiCoeff n k) * Polynomial.X ^ k := by
  have hr : (PowerSeries.X : PowerSeries ℤ) ^ n
      ∈ nonZeroDivisors (PowerSeries ℤ) :=
    mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero n PowerSeries.X_ne_zero)
  have hsign2 : ∀ k : ℕ, (-1 : PowerSeries ℤ) ^ n
        * (-1 : PowerSeries ℤ) ^ k = (-1 : PowerSeries ℤ) ^ (n + k) := by
    intro k
    rw [← pow_add]
  have hexp : ∀ k : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((n + 1).choose 2)
        * PowerSeries.X ^ (k.choose 2)
      = PowerSeries.X ^ (jacobiExponent n k)
        * PowerSeries.X ^ (n * k) := by
    intro k
    rw [← pow_add, ← pow_add, jacobiExponent_add_mul n k]
  have hSterm : ∀ k : ℕ, (Polynomial.C (jacobiCoeff n k)
        * Polynomial.X ^ k).comp
        (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
          * Polynomial.X)
      = Polynomial.C (jacobiCoeff n k
        * (PowerSeries.X : PowerSeries ℤ) ^ (n * k))
        * Polynomial.X ^ k := by
    intro k
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, ← pow_mul,
      ← mul_assoc, ← Polynomial.C_mul]
  have hRothe := prod_one_add_mul_pow_eq_sum_gaussBinom
    (Polynomial.C (PowerSeries.X : PowerSeries ℤ))
    (-Polynomial.X) (2 * n + 1)
  have hfactor : ∀ j : ℕ, (1 - Polynomial.C
        ((PowerSeries.X : PowerSeries ℤ) ^ j) * Polynomial.X)
      = 1 + (-Polynomial.X)
        * (Polynomial.C (PowerSeries.X : PowerSeries ℤ)) ^ j := by
    intro j
    rw [← Polynomial.C_pow]
    ring
  have hprod : ∏ j ∈ Finset.range (2 * n + 1),
        (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ j)
          * Polynomial.X)
      = ∑ k ∈ Finset.range (2 * n + 1 + 1),
        gaussBinom (Polynomial.C (PowerSeries.X : PowerSeries ℤ))
          (2 * n + 1) k
          * (Polynomial.C (PowerSeries.X : PowerSeries ℤ)) ^ (k.choose 2)
          * (-Polynomial.X) ^ k := by
    have hcongr : (∏ j ∈ Finset.range (2 * n + 1),
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ j)
            * Polynomial.X))
        = ∏ j ∈ Finset.range (2 * n + 1),
          (1 + (-Polynomial.X)
            * (Polynomial.C (PowerSeries.X : PowerSeries ℤ)) ^ j) :=
      Finset.prod_congr rfl (fun j _ => hfactor j)
    rw [hcongr]
    exact hRothe
  have hGmap : ∀ k : ℕ, gaussBinom
        (Polynomial.C (PowerSeries.X : PowerSeries ℤ)) (2 * n + 1) k
      = Polynomial.C (gaussBinom (PowerSeries.X : PowerSeries ℤ)
        (2 * n + 1) k) := by
    intro k
    exact (map_gaussBinom _ _ _ _).symm
  have htermV : ∀ k : ℕ, Polynomial.C
        ((-1) ^ n * PowerSeries.X ^ ((n + 1).choose 2))
        * (gaussBinom (Polynomial.C (PowerSeries.X : PowerSeries ℤ))
          (2 * n + 1) k
          * (Polynomial.C (PowerSeries.X : PowerSeries ℤ)) ^ (k.choose 2)
          * (-Polynomial.X) ^ k)
      = Polynomial.C (jacobiCoeff n k
        * (PowerSeries.X : PowerSeries ℤ) ^ (n * k))
        * Polynomial.X ^ k := by
    intro k
    rw [hGmap k, ← Polynomial.C_pow]
    have hneg : (-Polynomial.X) ^ k
        = ((-1 : Polynomial (PowerSeries ℤ))) ^ k * Polynomial.X ^ k := by
      have hbase : (-Polynomial.X : Polynomial (PowerSeries ℤ))
          = (-1) * Polynomial.X := by ring
      rw [hbase, mul_pow]
    rw [hneg]
    have hC1 : ((-1 : Polynomial (PowerSeries ℤ))) ^ k
        = Polynomial.C (((-1 : PowerSeries ℤ)) ^ k) := by
      have h1 : (-1 : Polynomial (PowerSeries ℤ))
          = Polynomial.C (-1 : PowerSeries ℤ) := by simp
      rw [h1, ← Polynomial.C_pow]
    rw [hC1, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul,
      ← mul_assoc, ← Polynomial.C_mul]
    congr 1
    congr 1
    unfold jacobiCoeff
    have hsplit : (((-1 : PowerSeries ℤ) ^ n
          * PowerSeries.X ^ ((n + 1).choose 2))
          * (gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1) k
            * PowerSeries.X ^ (k.choose 2)))
          * (-1 : PowerSeries ℤ) ^ k
        = (((-1 : PowerSeries ℤ) ^ n * (-1 : PowerSeries ℤ) ^ k)
          * (PowerSeries.X ^ ((n + 1).choose 2)
            * PowerSeries.X ^ (k.choose 2)))
          * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1) k := by
      ring
    rw [hsplit, hsign2 k, hexp k]
    ring
  have hVS : (finiteJacobiPoly n).comp
        (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
          * Polynomial.X)
      = (∑ k ∈ Finset.range (2 * n + 1 + 1),
        Polynomial.C (jacobiCoeff n k) * Polynomial.X ^ k).comp
        (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
          * Polynomial.X) := by
    rw [finiteJacobiPoly_comp_C_mul_X n, hprod, Finset.mul_sum,
      Polynomial.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hSterm k]
    exact htermV k
  have hcomp : (finiteJacobiPoly n
        - ∑ k ∈ Finset.range (2 * n + 1 + 1),
          Polynomial.C (jacobiCoeff n k) * Polynomial.X ^ k).comp
        (Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ n)
          * Polynomial.X)
      = 0 := by
    rw [Polynomial.sub_comp, hVS, sub_self]
  have heq := (Polynomial.comp_C_mul_X_eq_zero_iff hr).mp hcomp
  exact sub_eq_zero.mp heq

private theorem neg_one_pow_succ_two_mul (t : ℕ) :
    (-1 : PowerSeries ℤ) ^ (2 * t + 1) = -1 := by
  have hsq : (-1 : PowerSeries ℤ) ^ 2 = 1 := by ring
  rw [pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]

private theorem neg_one_pow_two_mul (t : ℕ) :
    (-1 : PowerSeries ℤ) ^ (2 * t) = 1 := by
  have hsq : (-1 : PowerSeries ℤ) ^ 2 = 1 := by ring
  rw [pow_mul, hsq, one_pow]

/-- Finite Jacobi identity: `P_n^2` as a weighted Gaussian binomial sum. -/
private theorem qPochFin_sq_eq_sum_gaussBinom (n : ℕ) :
    qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2
      = ∑ m ∈ Finset.range (n + 1),
        PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
          * PowerSeries.X ^ ((m + 1).choose 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1)
            (n - m) := by
  have hfac : ∀ i : ℕ, (((1 - Polynomial.C
        ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) * Polynomial.X)
        * (Polynomial.X - Polynomial.C
          ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))).eval 1)
      = (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
        * (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) := by
    intro i
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_one]
  have hU1 : (finiteJacobiU n).eval 1
      = qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2 := by
    unfold finiteJacobiU
    rw [Polynomial.eval_prod]
    have hprod : (∏ i ∈ Finset.range n,
          (((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
            * Polynomial.X)
            * (Polynomial.X - Polynomial.C
              ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))).eval 1))
        = ∏ i ∈ Finset.range n,
          ((1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
            * (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) :=
      Finset.prod_congr rfl (fun i _ => hfac i)
    rw [hprod, Finset.prod_mul_distrib]
    have hP : qPochFin (PowerSeries.X : PowerSeries ℤ) n
        = ∏ i ∈ Finset.range n, (1 - PowerSeries.X ^ (i + 1)) := rfl
    rw [hP, pow_two]
  have hVL : Polynomial.derivative (finiteJacobiPoly n)
      = Polynomial.derivative (1 - Polynomial.X) * finiteJacobiU n
        + (1 - Polynomial.X)
          * Polynomial.derivative (finiteJacobiU n) := by
    unfold finiteJacobiPoly
    rw [Polynomial.derivative_mul]
  have hVeval : (Polynomial.derivative (finiteJacobiPoly n)).eval 1
      = -(qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2) := by
    rw [hVL]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, hU1]
    simp
  have hVR : (Polynomial.derivative (finiteJacobiPoly n)).eval 1
      = ∑ k ∈ Finset.range (2 * n + 1 + 1),
        jacobiCoeff n k * (k : PowerSeries ℤ) := by
    rw [finiteJacobiPoly_eq_sum n, Polynomial.derivative_sum,
      Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    simp
  have hkey : (∑ k ∈ Finset.range (2 * n + 1 + 1),
        jacobiCoeff n k * (k : PowerSeries ℤ))
      = -(qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2) :=
    hVR.symm.trans hVeval
  have hsplit : ∑ k ∈ Finset.range (2 * n + 1 + 1),
        jacobiCoeff n k * (k : PowerSeries ℤ)
      = (∑ i ∈ Finset.range (n + 1),
          jacobiCoeff n i * (i : PowerSeries ℤ))
        + ∑ i ∈ Finset.range (n + 1),
          jacobiCoeff n (n + 1 + i)
            * (((n + 1 + i : ℕ)) : PowerSeries ℤ) := by
    have h2n : 2 * n + 1 + 1 = (n + 1) + (n + 1) := by omega
    rw [h2n, Finset.sum_range_add]
  have hrefl : (∑ i ∈ Finset.range (n + 1),
        jacobiCoeff n (n + 1 + i)
          * (((n + 1 + i : ℕ)) : PowerSeries ℤ))
      = ∑ j ∈ Finset.range (n + 1),
        jacobiCoeff n (2 * n + 1 - j)
          * ((((2 * n + 1 - j : ℕ))) : PowerSeries ℤ) := by
    have h2 : (∑ j ∈ Finset.range (n + 1),
          jacobiCoeff n (n + 1 + (n + 1 - 1 - j))
            * ((((n + 1 + (n + 1 - 1 - j) : ℕ))) : PowerSeries ℤ))
        = ∑ j ∈ Finset.range (n + 1),
          jacobiCoeff n (2 * n + 1 - j)
            * ((((2 * n + 1 - j : ℕ))) : PowerSeries ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n + 1 := Finset.mem_range.mp hj
      have e1 : n + 1 + (n + 1 - 1 - j) = 2 * n + 1 - j := by omega
      rw [e1]
    have h3 : (∑ i ∈ Finset.range (n + 1),
          jacobiCoeff n (n + 1 + i)
            * ((((n + 1 + i : ℕ))) : PowerSeries ℤ))
        = ∑ j ∈ Finset.range (n + 1),
          jacobiCoeff n (n + 1 + (n + 1 - 1 - j))
            * ((((n + 1 + (n + 1 - 1 - j) : ℕ))) : PowerSeries ℤ) := by
      have h := Finset.sum_range_reflect
        (fun i : ℕ => jacobiCoeff n (n + 1 + i)
          * ((((n + 1 + i : ℕ))) : PowerSeries ℤ)) (n + 1)
      exact h.symm
    exact h3.trans h2
  have hpair : ∀ i : ℕ, i ≤ n →
      jacobiCoeff n i * (i : PowerSeries ℤ)
        + jacobiCoeff n (2 * n + 1 - i)
          * ((((2 * n + 1 - i : ℕ))) : PowerSeries ℤ)
      = -((((2 * (n - i) + 1 : ℕ)) : PowerSeries ℤ)
        * jacobiCoeff n i) := by
    intro i hi
    have hG : gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1)
          (2 * n + 1 - i)
        = gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1) i := by
      have h1 : 2 * n + 1 - i ≤ 2 * n + 1 := Nat.sub_le _ _
      have h2 := gaussBinom_symm (2 * n + 1) (2 * n + 1 - i) h1
      have h3 : 2 * n + 1 - (2 * n + 1 - i) = i := by omega
      rw [h3] at h2
      exact h2
    have he : jacobiExponent n (2 * n + 1 - i)
        = jacobiExponent n i :=
      jacobiExponent_symm n i (by omega : i ≤ 2 * n + 1)
    have hsignexp : n + (2 * n + 1 - i)
        = (n + i) + (2 * (n - i) + 1) := by omega
    have hsign : (-1 : PowerSeries ℤ) ^ (n + (2 * n + 1 - i))
        = -(-1 : PowerSeries ℤ) ^ (n + i) := by
      rw [hsignexp, pow_add, neg_one_pow_succ_two_mul, mul_neg, mul_one]
    have ha : jacobiCoeff n (2 * n + 1 - i)
        = -jacobiCoeff n i := by
      unfold jacobiCoeff
      rw [he, hG, hsign]
      ring
    rw [ha]
    have hNat : i + (2 * (n - i) + 1) = 2 * n + 1 - i := by omega
    have hAB : (i : PowerSeries ℤ)
          + ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
        = ((((2 * n + 1 - i : ℕ))) : PowerSeries ℤ) := by
      rw [← Nat.cast_add, hNat]
    linear_combination (jacobiCoeff n i) * hAB
  have hpair_sum : ∑ k ∈ Finset.range (2 * n + 1 + 1),
        jacobiCoeff n k * (k : PowerSeries ℤ)
      = -(∑ i ∈ Finset.range (n + 1),
        ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n i) := by
    rw [hsplit, hrefl, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i ≤ n := by
      have hlt : i < n + 1 := Finset.mem_range.mp hi
      omega
    exact hpair i hiN
  have hsum_eq : (∑ i ∈ Finset.range (n + 1),
        ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n i)
      = qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2 := by
    have h := hkey.symm.trans hpair_sum
    exact neg_injective h.symm
  have hrefl2 : (∑ i ∈ Finset.range (n + 1),
        ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n i)
      = ∑ m ∈ Finset.range (n + 1),
        ((((2 * m + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n (n - m) := by
    have h2 : (∑ j ∈ Finset.range (n + 1),
          ((((2 * (n - (n - j)) + 1 : ℕ))) : PowerSeries ℤ)
            * jacobiCoeff n (n - j))
        = ∑ m ∈ Finset.range (n + 1),
          ((((2 * m + 1 : ℕ))) : PowerSeries ℤ)
            * jacobiCoeff n (n - m) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n + 1 := Finset.mem_range.mp hj
      have e : n - (n - j) = j := by omega
      rw [e]
    have h3 : (∑ i ∈ Finset.range (n + 1),
          ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
            * jacobiCoeff n i)
        = ∑ j ∈ Finset.range (n + 1),
          ((((2 * (n - (n - j)) + 1 : ℕ))) : PowerSeries ℤ)
            * jacobiCoeff n (n - j) := by
      have h := Finset.sum_range_reflect
        (fun i : ℕ => ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n i) (n + 1)
      have e : ∀ j : ℕ, n + 1 - 1 - j = n - j := fun j => by omega
      simp only [e] at h
      exact h.symm
    exact h3.trans h2
  have htermC : ∀ m : ℕ, m ≤ n →
      ((((2 * m + 1 : ℕ))) : PowerSeries ℤ)
        * jacobiCoeff n (n - m)
      = PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
        * PowerSeries.X ^ ((m + 1).choose 2)
        * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1)
          (n - m) := by
    intro m hm
    have hsign : (-1 : PowerSeries ℤ) ^ (n + (n - m))
        = (-1 : PowerSeries ℤ) ^ m := by
      have he : n + (n - m) = m + 2 * (n - m) := by omega
      rw [he, pow_add, neg_one_pow_two_mul, mul_one]
    have hexp : jacobiExponent n (n - m) = (m + 1).choose 2 :=
      jacobiExponent_sub n m hm
    have ha : jacobiCoeff n (n - m)
        = (-1 : PowerSeries ℤ) ^ m
          * PowerSeries.X ^ ((m + 1).choose 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1)
            (n - m) := by
      unfold jacobiCoeff
      rw [hsign, hexp]
    rw [ha]
    have hCval : PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
        = ((((2 * m + 1 : ℕ))) : PowerSeries ℤ)
          * (-1 : PowerSeries ℤ) ^ m := by
      have e1 : PowerSeries.C (((-1 : ℤ) ^ m : ℤ))
          = (-1 : PowerSeries ℤ) ^ m := by
        have h1 : PowerSeries.C (-1 : ℤ)
            = (-1 : PowerSeries ℤ) := by simp
        rw [← h1, ← map_pow]
      have e2 : PowerSeries.C ((2 * (m : ℤ) + 1 : ℤ))
          = ((((2 * m + 1 : ℕ))) : PowerSeries ℤ) := by
        have h2 : ((2 * (m : ℤ) + 1 : ℤ))
            = ((((2 * m + 1 : ℕ))) : ℤ) := by
          push_cast
          ring
        rw [h2, map_natCast]
      have e3 := map_mul (PowerSeries.C)
        (((-1 : ℤ) ^ m : ℤ)) ((2 * (m : ℤ) + 1 : ℤ))
      rw [e3, e1, e2]
      ring
    rw [hCval]
    ring
  calc qPochFin (PowerSeries.X : PowerSeries ℤ) n ^ 2
      = ∑ i ∈ Finset.range (n + 1),
        ((((2 * (n - i) + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n i := hsum_eq.symm
    _ = ∑ m ∈ Finset.range (n + 1),
        ((((2 * m + 1 : ℕ))) : PowerSeries ℤ)
          * jacobiCoeff n (n - m) := hrefl2
    _ = ∑ m ∈ Finset.range (n + 1),
        PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
          * PowerSeries.X ^ ((m + 1).choose 2)
          * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1)
            (n - m) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact htermC m (by
          have hlt : m < n + 1 := Finset.mem_range.mp hm
          omega)

/-- **Jacobi's cube identity.** Let $E(X) = \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2}$ be
Euler's pentagonal series and $J(X) = \sum_{t \ge 0} (-1)^t (2t+1) X^{t(t+1)/2}$ Jacobi's cube
series, both in $\mathbb{Z}[[X]]$. Then $E(X)^3 = J(X)$. -/
theorem pentagonalSeries_pow_three :
    PowerSeries.pentagonalSeries ℤ ^ 3 = jacobiCubeSeries := by
  ext d
  set S : PowerSeries ℤ := ∑ m ∈ Finset.range (d + 1),
    PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
      * PowerSeries.X ^ ((m + 1).choose 2) with hS
  have hdecomp : PowerSeries.pentagonalSeries ℤ ^ 3 - jacobiCubeSeries
      = PowerSeries.pentagonalSeries ℤ
          * (PowerSeries.pentagonalSeries ℤ ^ 2
            - qPochFin (PowerSeries.X : PowerSeries ℤ) d ^ 2)
        + (PowerSeries.pentagonalSeries ℤ
            * qPochFin (PowerSeries.X : PowerSeries ℤ) d ^ 2 - S)
        + (S - jacobiCubeSeries) := by
    ring
  have hterm1 : PowerSeries.X ^ (d + 1)
      ∣ PowerSeries.pentagonalSeries ℤ
        * (PowerSeries.pentagonalSeries ℤ ^ 2
          - qPochFin (PowerSeries.X : PowerSeries ℤ) d ^ 2) := by
    have hsq : PowerSeries.pentagonalSeries ℤ ^ 2
          - qPochFin (PowerSeries.X : PowerSeries ℤ) d ^ 2
        = (PowerSeries.pentagonalSeries ℤ
          - qPochFin (PowerSeries.X : PowerSeries ℤ) d)
          * (PowerSeries.pentagonalSeries ℤ
            + qPochFin (PowerSeries.X : PowerSeries ℤ) d) := by
      ring
    rw [hsq]
    have hN4 := X_pow_succ_dvd_pentagonalSeries_sub_qPochFin d
    exact (hN4.mul_right _).mul_left _
  have hterm2 : PowerSeries.X ^ (d + 1)
      ∣ (PowerSeries.pentagonalSeries ℤ
        * qPochFin (PowerSeries.X : PowerSeries ℤ) d ^ 2 - S) := by
    have hN8 := qPochFin_sq_eq_sum_gaussBinom d
    rw [hS, hN8, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro m hm
    have hmN : m ≤ d := by
      have hlt : m < d + 1 := Finset.mem_range.mp hm
      omega
    have hterm : PowerSeries.pentagonalSeries ℤ
          * (PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
            * PowerSeries.X ^ ((m + 1).choose 2)
            * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * d + 1)
              (d - m))
          - PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
            * PowerSeries.X ^ ((m + 1).choose 2)
        = (PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
            * PowerSeries.X ^ ((m + 1).choose 2))
          * (gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * d + 1)
              (d - m)
            * PowerSeries.pentagonalSeries ℤ - 1) := by
      ring
    rw [hterm]
    have hNd := X_pow_succ_dvd_gaussBinom_mul_pentagonalSeries_sub_one
      (2 * d + 1) (d - m) (by omega : 2 * (d - m) ≤ 2 * d + 1)
    have hXpow : PowerSeries.X ^ ((m + 1).choose 2)
        ∣ PowerSeries.C (((-1 : ℤ) ^ m * (2 * (m : ℤ) + 1)))
          * PowerSeries.X ^ ((m + 1).choose 2) :=
      dvd_mul_left _ _
    have hmul := mul_dvd_mul hXpow hNd
    have htri : m ≤ (m + 1).choose 2 := by
      rcases tri_ge m with h | h
      · exact h
      · omega
    have hle : d + 1 ≤ ((m + 1).choose 2) + ((d - m) + 1) := by omega
    have hXle : (PowerSeries.X : PowerSeries ℤ) ^ (d + 1)
        ∣ PowerSeries.X ^ (((m + 1).choose 2) + ((d - m) + 1)) :=
      pow_dvd_pow _ hle
    have hpow : (PowerSeries.X : PowerSeries ℤ)
          ^ (((m + 1).choose 2) + ((d - m) + 1))
        = PowerSeries.X ^ ((m + 1).choose 2)
          * PowerSeries.X ^ ((d - m) + 1) := pow_add _ _ _
    rw [hpow] at hXle
    exact hXle.trans hmul
  have hterm3 : PowerSeries.X ^ (d + 1) ∣ (S - jacobiCubeSeries) := by
    have hN9 := X_pow_succ_dvd_jacobiCubeSeries_sub_sum d
    rw [← hS] at hN9
    have hneg : S - jacobiCubeSeries
        = -(jacobiCubeSeries - S) := by
      rw [neg_sub]
    rw [hneg]
    exact dvd_neg.mpr hN9
  have hdiv : PowerSeries.X ^ (d + 1)
      ∣ (PowerSeries.pentagonalSeries ℤ ^ 3 - jacobiCubeSeries) := by
    rw [hdecomp]
    exact dvd_add (dvd_add hterm1 hterm2) hterm3
  rw [PowerSeries.X_pow_dvd_iff] at hdiv
  have h0 := hdiv d (Nat.lt_succ_self d)
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

private theorem five_dvd_coeff_pentagonalSeries_pow_four (m : ℕ) :
    (5 : ℤ) ∣ PowerSeries.coeff (5 * m + 4)
      (PowerSeries.pentagonalSeries ℤ ^ 4) := by
  have hE4 : PowerSeries.pentagonalSeries ℤ ^ 4
      = PowerSeries.pentagonalSeries ℤ * jacobiCubeSeries := by
    have h4 : (4 : ℕ) = 3 + 1 := rfl
    rw [h4, pow_succ', pentagonalSeries_pow_three]
  rw [hE4, PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  intro ab hab
  obtain ⟨a, b⟩ := ab
  have hmem : a + b = 5 * m + 4 := Finset.mem_antidiagonal.mp hab
  by_cases ha : a ∈ Set.range pentagonal
  · by_cases hb : ∃ t : ℕ, (t + 1).choose 2 = b
    · obtain ⟨t, rfl⟩ := hb
      obtain ⟨k, rfl⟩ := ha
      have h5 : 5 ∣ pentagonal k + (t + 1).choose 2 + 1 := by omega
      have h2t := five_dvd_two_mul_add_one_of_pentagonal_add_triangle
        k t h5
      have htri := coeff_jacobiCubeSeries_triangle t
      rw [htri]
      have h51 : (5 : ℤ) ∣ (2 * (t : ℤ) + 1) := by
        have h51' : (5 : ℤ) ∣ ((((2 * t + 1 : ℕ))) : ℤ) :=
          Int.natCast_dvd_natCast.mpr h2t
        have hcast : ((((2 * t + 1 : ℕ))) : ℤ) = 2 * (t : ℤ) + 1 := by
          push_cast
          ring
        rw [hcast] at h51'
        exact h51'
      have hmid : (5 : ℤ) ∣ (-1 : ℤ) ^ t * (2 * (t : ℤ) + 1) :=
        h51.trans (dvd_mul_left (2 * (t : ℤ) + 1) ((-1 : ℤ) ^ t))
      exact hmid.mul_left _
    · have hJ0 : PowerSeries.coeff b jacobiCubeSeries = 0 :=
        coeff_jacobiCubeSeries_eq_zero (fun t ht => hb ⟨t, ht⟩)
      rw [hJ0, mul_zero]
      exact dvd_zero _
  · have hE0 : PowerSeries.coeff a (PowerSeries.pentagonalSeries ℤ) = 0 :=
      PowerSeries.coeff_pentagonalSeries_eq_zero ℤ ha
    rw [hE0, zero_mul]
    exact dvd_zero _

/-- **Partition congruences from a power of Euler's series.** Let $p$ be a prime, let $r < p$ be
a natural number, and let $E(X) = \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2}$ be Euler's
pentagonal series in $\mathbb{Z}[[X]]$. If $p$ divides the coefficient of $X^{pm+r}$ in
$E(X)^{p-1}$ for every natural number $m$, then $p$ divides the number of partitions of $pm + r$
for every natural number $m$. -/
theorem dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow
    (p r : ℕ) [Fact (Nat.Prime p)] (hr : r < p)
    (hvan : ∀ m : ℕ, (p : ℤ)
      ∣ PowerSeries.coeff (p * m + r)
        (PowerSeries.pentagonalSeries ℤ ^ (p - 1))) (m : ℕ) :
    p ∣ Fintype.card (Nat.Partition (p * m + r)) := by
  have hprime : Nat.Prime p := Fact.out
  have hppos : 0 < p := hprime.pos
  have hp0 : p ≠ 0 := hppos.ne'
  set φ := PowerSeries.map (Int.castRingHom (ZMod p)) with hφ
  set Ebar : PowerSeries (ZMod p) :=
    φ (PowerSeries.pentagonalSeries ℤ) with hEbar
  set Pbar : PowerSeries (ZMod p) :=
    φ (PowerSeries.mk
      (fun n => (((partitionFunction n : ℕ)) : ℤ))) with hPbar
  have hPE := mk_partitionFunction_mul_pentagonalSeries
  have h1 : Pbar * Ebar = 1 := by
    rw [hPbar, hEbar, ← map_mul, hPE, map_one]
  have h2 : Ebar ^ p = Ebar.expand p hp0 := by
    have hF : PowerSeries.map (frobenius (ZMod p) p)
          (Ebar.expand p hp0) = Ebar ^ p :=
      PowerSeries.map_frobenius_expand _ _
    rw [ZMod.frobenius_zmod p, PowerSeries.map_id] at hF
    exact hF.symm
  have h3 : (Pbar.expand p hp0) * (Ebar.expand p hp0) = 1 := by
    rw [← map_mul, h1, map_one]
  have hEpow : Ebar ^ p * Pbar.expand p hp0 = 1 := by
    rw [h2, mul_comm]
    exact h3
  have h4 : Pbar = Ebar ^ (p - 1) * Pbar.expand p hp0 := by
    have step1 : Pbar = Pbar * (Ebar ^ p * Pbar.expand p hp0) := by
      rw [hEpow, mul_one]
    have hpsucc : Ebar ^ p = Ebar ^ (p - 1) * Ebar := by
      have hgen : ∀ a : PowerSeries (ZMod p), ∀ q : ℕ, 1 ≤ q →
          a ^ q = a ^ (q - 1) * a := by
        intro a q hq
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
        rw [show k.succ - 1 = k by omega, show k.succ = k + 1 from rfl,
          pow_succ]
      exact hgen Ebar p hppos
    have step2 : Pbar * (Ebar ^ p * Pbar.expand p hp0)
        = (Pbar * Ebar) * (Ebar ^ (p - 1) * Pbar.expand p hp0) := by
      rw [hpsucc]
      ring
    nth_rewrite 1 [step1]
    rw [step2, h1, one_mul]
  have h5 : ∀ m : ℕ, PowerSeries.coeff (p * m + r) (Ebar ^ (p - 1))
      = 0 := by
    intro m
    have hmap : Ebar ^ (p - 1)
        = φ (PowerSeries.pentagonalSeries ℤ ^ (p - 1)) := by
      rw [hEbar, ← map_pow]
    rw [hmap, hφ, PowerSeries.coeff_map]
    have hdv := hvan m
    have h0 : ((PowerSeries.coeff (p * m + r)
        (PowerSeries.pentagonalSeries ℤ ^ (p - 1)) : ℤ) : ZMod p)
        = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdv
    exact h0
  have h6 : ∀ m : ℕ, PowerSeries.coeff (p * m + r)
        (Ebar ^ (p - 1) * Pbar.expand p hp0) = 0 := by
    intro m
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    obtain ⟨a, b⟩ := ab
    have hmem : a + b = p * m + r := Finset.mem_antidiagonal.mp hab
    by_cases hdiv : p ∣ b
    · obtain ⟨j, rfl⟩ := hdiv
      have hle : p * j ≤ p * m + r := by omega
      have hlt : p * j < p * (m + 1) := by
        have hmp : p * m + r < p * (m + 1) := by
          have hpm : p * (m + 1) = p * m + p := by ring
          omega
        omega
      have hjm : j < m + 1 := by
        by_contra hcon
        push Not at hcon
        have hle2 : p * (m + 1) ≤ p * j :=
          mul_le_mul_of_nonneg_left hcon (Nat.zero_le p)
        omega
      have hjm' : j ≤ m := by omega
      have hsplit : p * m = p * j + p * (m - j) := by
        have hmj : m = j + (m - j) := (Nat.add_sub_cancel' hjm').symm
        conv_lhs => rw [hmj]
        rw [mul_add]
      have ha : a = p * (m - j) + r := by omega
      have hF0 : PowerSeries.coeff a (Ebar ^ (p - 1)) = 0 := by
        rw [ha]
        exact h5 (m - j)
      rw [hF0, zero_mul]
    · have hG0 : PowerSeries.coeff b (Pbar.expand p hp0) = 0 :=
        PowerSeries.coeff_expand_of_not_dvd p hp0 _ hdiv
      rw [hG0, mul_zero]
  have hcoeff : PowerSeries.coeff (p * m + r) Pbar
      = (((partitionFunction (p * m + r) : ℕ)) : ZMod p) := by
    rw [hPbar, hφ, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact map_natCast _ _
  have hP0 : PowerSeries.coeff (p * m + r) Pbar = 0 := by
    rw [h4]
    exact h6 m
  rw [hcoeff] at hP0
  simpa [partitionFunction] using (ZMod.natCast_eq_zero_iff _ _).mp hP0

/-- **Ramanujan's congruence modulo 5.** For every natural number $m$, the number of partitions
of $5m + 4$ is divisible by $5$.

Proves `Wanted` entry `ramanujan_partition_congruence_mod_five`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, JIS 27 (2024), Art. 24.1.6, lines 801–804.
Live source: https://cs.uwaterloo.ca/journals/JIS/VOL27/Bhatnagar/bhat4.tex
-/
theorem ramanujan_partition_congruence_mod_five (m : ℕ) :
    Fintype.card (Nat.Partition (5 * m + 4)) ≡ 0 [MOD 5] := by
  have hfact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 := @dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow
    5 4 hfact (by omega : 4 < 5)
    (fun m => by
      have h41 : (5 : ℕ) - 1 = 4 := rfl
      rw [h41]
      exact five_dvd_coeff_pentagonalSeries_pow_four m) m
  rw [Nat.modEq_zero_iff_dvd]
  exact h5

private theorem seven_dvd_two_mul_add_one_of_triangle_add_triangle
    (s t m : ℕ)
    (h : (s + 1).choose 2 + (t + 1).choose 2 = 7 * m + 5) :
    7 ∣ 2 * s + 1 := by
  have htri_s : (2 : ZMod 7) * ((((s + 1).choose 2 : ℕ)) : ZMod 7)
      = (s : ZMod 7) * ((s : ZMod 7) + 1) := by
    have h2S := two_mul_choose_two_succ s
    have hcc : ((((2 * (s + 1).choose 2 : ℕ))) : ZMod 7)
        = ((((s * (s + 1) : ℕ))) : ZMod 7) := by
      rw [h2S]
    push_cast at hcc ⊢
    simpa using hcc
  have htri_t : (2 : ZMod 7) * ((((t + 1).choose 2 : ℕ)) : ZMod 7)
      = (t : ZMod 7) * ((t : ZMod 7) + 1) := by
    have h2T := two_mul_choose_two_succ t
    have hcc : ((((2 * (t + 1).choose 2 : ℕ))) : ZMod 7)
        = ((((t * (t + 1) : ℕ))) : ZMod 7) := by
      rw [h2T]
    push_cast at hcc ⊢
    simpa using hcc
  have hsum : ((((s + 1).choose 2 : ℕ)) : ZMod 7)
      + ((((t + 1).choose 2 : ℕ)) : ZMod 7) = 5 := by
    have hcast : ((((s + 1).choose 2 + (t + 1).choose 2 : ℕ)) : ZMod 7)
        = ((((7 * m + 5 : ℕ))) : ZMod 7) := by
      rw [h]
    have hRHS : ((((7 * m + 5 : ℕ))) : ZMod 7) = 5 := by
      have h7 : (7 : ZMod 7) = 0 := by
        decide
      push_cast
      rw [h7, zero_mul, zero_add]
    rw [hRHS] at hcast
    push_cast at hcast
    simpa using hcast
  have hsq : (2 * (s : ZMod 7) + 1) ^ 2 + (2 * (t : ZMod 7) + 1) ^ 2
      = 0 := by
    have heq : (2 * (s : ZMod 7) + 1) ^ 2 + (2 * (t : ZMod 7) + 1) ^ 2
        = 8 * ((((s + 1).choose 2 : ℕ)) : ZMod 7)
          + 8 * ((((t + 1).choose 2 : ℕ)) : ZMod 7) + 2 := by
      linear_combination -4 * htri_s - 4 * htri_t
    have heq2 : 8 * ((((s + 1).choose 2 : ℕ)) : ZMod 7)
          + 8 * ((((t + 1).choose 2 : ℕ)) : ZMod 7) + 2 = 0 := by
      have h8 : 8 * ((((s + 1).choose 2 : ℕ)) : ZMod 7)
            + 8 * ((((t + 1).choose 2 : ℕ)) : ZMod 7) + 2
          = 8 * (((((s + 1).choose 2 : ℕ)) : ZMod 7)
            + ((((t + 1).choose 2 : ℕ)) : ZMod 7)) + 2 := by
        ring
      rw [h8, hsum]
      decide
    rw [heq]
    exact heq2
  have key : ∀ a b : ZMod 7, a ^ 2 + b ^ 2 = 0 → a = 0 := by
    decide
  have hfin : 2 * (s : ZMod 7) + 1 = 0 := key _ _ hsq
  have hzero : ((((2 * s + 1 : ℕ))) : ZMod 7) = 0 := by
    push_cast
    simpa using hfin
  rwa [ZMod.natCast_eq_zero_iff] at hzero

private theorem seven_dvd_coeff_pentagonalSeries_pow_six (m : ℕ) :
    (7 : ℤ) ∣ PowerSeries.coeff (7 * m + 5)
      (PowerSeries.pentagonalSeries ℤ ^ 6) := by
  have hE6 : PowerSeries.pentagonalSeries ℤ ^ 6
      = jacobiCubeSeries ^ 2 := by
    have h6 : (6 : ℕ) = 3 * 2 := rfl
    rw [h6, pow_mul, pentagonalSeries_pow_three]
  rw [hE6, pow_two, PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  intro ab hab
  obtain ⟨i, j⟩ := ab
  have hmem : i + j = 7 * m + 5 := Finset.mem_antidiagonal.mp hab
  by_cases hi : ∃ s : ℕ, (s + 1).choose 2 = i
  · by_cases hj : ∃ t : ℕ, (t + 1).choose 2 = j
    · obtain ⟨s, rfl⟩ := hi
      obtain ⟨t, rfl⟩ := hj
      have h7 : 7 ∣ 2 * s + 1 :=
        seven_dvd_two_mul_add_one_of_triangle_add_triangle s t m hmem
      have htri_s := coeff_jacobiCubeSeries_triangle s
      have htri_t := coeff_jacobiCubeSeries_triangle t
      rw [htri_s, htri_t]
      have h71 : (7 : ℤ) ∣ (2 * (s : ℤ) + 1) := by
        have h71' : (7 : ℤ) ∣ ((((2 * s + 1 : ℕ))) : ℤ) :=
          Int.natCast_dvd_natCast.mpr h7
        have hcast : ((((2 * s + 1 : ℕ))) : ℤ) = 2 * (s : ℤ) + 1 := by
          push_cast
          ring
        rw [hcast] at h71'
        exact h71'
      have hmid : (7 : ℤ) ∣ (-1 : ℤ) ^ s * (2 * (s : ℤ) + 1) :=
        dvd_mul_of_dvd_right h71 _
      exact dvd_mul_of_dvd_left hmid _
    · have hJ0 : PowerSeries.coeff j jacobiCubeSeries = 0 :=
        coeff_jacobiCubeSeries_eq_zero (fun t ht => hj ⟨t, ht⟩)
      rw [hJ0, mul_zero]
      exact dvd_zero _
  · have hJ0 : PowerSeries.coeff i jacobiCubeSeries = 0 :=
      coeff_jacobiCubeSeries_eq_zero (fun s hs => hi ⟨s, hs⟩)
    rw [hJ0, zero_mul]
    exact dvd_zero _

/-- **Ramanujan's congruence modulo 7.** For every natural number $m$, the number of partitions
of $7m + 5$ is divisible by $7$.

Proves `Wanted` entry `ramanujan_partition_congruence_mod_seven`.

Source: S. Ramanujan, "Some properties of p(n), the number of partitions of n",
Proceedings of the Cambridge Philosophical Society 19 (1919), 207–210,
where the congruence is stated and proved.
The proof follows Ramanujan's argument there: the sixth power of Euler's product
is the square of Jacobi's cube series, and a sum of two squares divisible by 7
has both terms divisible by 7.
-/
theorem ramanujan_partition_congruence_mod_seven (m : ℕ) :
    Fintype.card (Nat.Partition (7 * m + 5)) ≡ 0 [MOD 7] := by
  have hfact : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have h7 := @dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow
    7 5 hfact (by omega : 5 < 7)
    (fun m => by
      have h61 : (7 : ℕ) - 1 = 6 := rfl
      rw [h61]
      exact seven_dvd_coeff_pentagonalSeries_pow_six m) m
  rw [Nat.modEq_zero_iff_dvd]
  exact h7

end MetaMathlibExt
end
