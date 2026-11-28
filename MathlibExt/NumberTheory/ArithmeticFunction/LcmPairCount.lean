/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Counting pairs by their least common multiple

The ordered pairs `(a, b)` with `lcm(a, b) = n` are in bijection with the divisors of `n²`,
via `(a, b) ↦ a · (n / b)`, so there are `d(n²)` of them. Writing a pair as
`(g a', g b')` with `g = gcd(a, b)` shows that the pairs with `lcm(a, b) ≤ z` number
`O(z (log z)³)`.

## Main statements

* `Nat.card_filter_lcm_eq_card_divisors_sq`: `#{(a, b) : lcm(a, b) = n} = d(n²)` for `n ≠ 0`.
* `Nat.card_filter_lcm_le`: `#{(a, b) : lcm(a, b) ≤ z} ≤ 20 z (log z)³` for `z ≥ 2`.
-/

@[expose] public section

open Finset

namespace Nat

/-- For `n ≠ 0`, the number of ordered pairs `(a, b)` with `lcm(a, b) = n` is `d(n²)`, the number
of divisors of `n²`. (Such pairs consist of divisors of `n`.) -/
theorem card_filter_lcm_eq_card_divisors_sq {n : ℕ} (hn : n ≠ 0) :
    #{q ∈ n.divisors ×ˢ n.divisors | Nat.lcm q.1 q.2 = n} = #(n ^ 2).divisors := by
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  refine Finset.card_bij' (fun q _ => q.1 * (n / q.2))
    (fun m _ => (Nat.gcd m n, n * Nat.gcd m n / m)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hq
    obtain ⟨⟨⟨ha, -⟩, hb, -⟩, -⟩ := hq
    refine Nat.mem_divisors.2 ⟨?_, hn2⟩
    rw [sq]
    exact Nat.mul_dvd_mul ha (Nat.div_dvd_of_dvd hb)
  · intro m hm
    obtain ⟨hm, -⟩ := Nat.mem_divisors.1 hm
    have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hn2 hm
    set g := Nat.gcd m n with hg
    have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hn
    -- `m ∣ n g`, since `m ∣ gcd(n², n m) = n gcd(n, m)`
    have hmng : m ∣ n * g := by
      have h := Nat.dvd_gcd (by rwa [sq] at hm : m ∣ n * n) (Dvd.intro_left n rfl : m ∣ n * m)
      rwa [Nat.gcd_mul_left, Nat.gcd_comm] at h
    set c := n * g / m with hc
    have hcm : c * m = n * g := Nat.div_mul_cancel hmng
    have hcn : c * (m / g) = n := by
      have hgm : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
      have : c * (m / g) * g = n * g := by
        calc c * (m / g) * g = c * (g * (m / g)) := by ring
          _ = n * g := by rw [hgm, hcm]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg0) this
    have hc0 : c ≠ 0 := fun h => by rw [h, zero_mul] at hcn; exact hn hcn.symm
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    refine ⟨⟨⟨Nat.gcd_dvd_right _ _, hn⟩, Dvd.intro _ hcn, hn⟩, ?_⟩
    -- `lcm(g, c) = n`, checked one prime at a time
    refine Nat.eq_of_factorization_eq (Nat.lcm_ne_zero hg0 hc0) hn fun p => ?_
    have hfm := (Nat.factorization_le_iff_dvd hm0 hn2).2 hm p
    have hfc : c.factorization p = n.factorization p + g.factorization p - m.factorization p := by
      rw [hc, Nat.factorization_div hmng, Nat.factorization_mul hn hg0]
      simp
    rw [Nat.factorization_lcm hg0 hc0, Finsupp.sup_apply, hfc, hg,
      Nat.factorization_gcd hm0 hn, Finsupp.inf_apply]
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfm
    omega
  · rintro ⟨a, b⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hq
    obtain ⟨⟨⟨ha, -⟩, hb, -⟩, hl⟩ := hq
    have ha0 : a ≠ 0 := fun h => by subst h; simp at hl; exact hn hl.symm
    have hb0 : b ≠ 0 := fun h => by subst h; simp at hl; exact hn hl.symm
    have hnb0 : n / b ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hb)
      (Nat.pos_of_ne_zero hb0)).ne'
    have hm0 : a * (n / b) ≠ 0 := mul_ne_zero ha0 hnb0
    have hmax : ∀ p, n.factorization p = max (a.factorization p) (b.factorization p) := by
      intro p
      rw [← hl, Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply]
    have hga : Nat.gcd (a * (n / b)) n = a := by
      refine Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_right hn) ha0 fun p => ?_
      rw [Nat.factorization_gcd hm0 hn, Finsupp.inf_apply, Nat.factorization_mul ha0 hnb0,
        Nat.factorization_div hb, Finsupp.add_apply, Finsupp.tsub_apply]
      have := hmax p
      omega
    simp only [hga, Prod.mk.injEq, true_and]
    refine Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) ?_
    rw [show b * (a * (n / b)) = a * (b * (n / b)) by ring, Nat.mul_div_cancel' hb, mul_comm]
  · intro m hm
    obtain ⟨hm, -⟩ := Nat.mem_divisors.1 hm
    have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hn2 hm
    set g := Nat.gcd m n with hg
    have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hn
    have hmng : m ∣ n * g := by
      have h := Nat.dvd_gcd (by rwa [sq] at hm : m ∣ n * n) (Dvd.intro_left n rfl : m ∣ n * m)
      rwa [Nat.gcd_mul_left, Nat.gcd_comm] at h
    have hgm : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
    have hcm : n * g / m * m = n * g := Nat.div_mul_cancel hmng
    have hcn : n * g / m * (m / g) = n := by
      have : n * g / m * (m / g) * g = n * g := by
        calc n * g / m * (m / g) * g = n * g / m * (g * (m / g)) := by ring
          _ = n * g := by rw [hgm, hcm]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg0) this
    have hc0 : n * g / m ≠ 0 := fun h => by rw [h, zero_mul] at hcn; exact hn hcn.symm
    change g * (n / (n * g / m)) = m
    rw [Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hc0) hcn.symm, hgm]

/-- `gcd a b * (a / gcd a b) * (b / gcd a b) = lcm a b`. -/
private theorem gcd_mul_div_gcd_mul_div_gcd_eq_lcm (a b : ℕ) :
    Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) = Nat.lcm a b := by
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)]
  change a * (b / Nat.gcd a b) = a * b / Nat.gcd a b
  exact (Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)).symm

/-- `(a, b) ↦ ((gcd a b, a / gcd a b), b / gcd a b)` is injective. -/
private theorem gcd_div_gcd_injective :
    Function.Injective
      (fun q : ℕ × ℕ => ((Nat.gcd q.1 q.2, q.1 / Nat.gcd q.1 q.2), q.2 / Nat.gcd q.1 q.2)) := by
  intro p q hpq
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨⟨h1, h2⟩, h3⟩ := hpq
  have e1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  have e2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
  have e3 := Nat.mul_div_cancel' (Nat.gcd_dvd_left q.1 q.2)
  have e4 := Nat.mul_div_cancel' (Nat.gcd_dvd_right q.1 q.2)
  ext
  · rw [← e1, ← e3, h2, h1]
  · rw [← e2, ← e4, h3, h1]

/-- The number of pairs `(d₁, d₂)` of positive integers with `lcm(d₁, d₂) ≤ z` is at most
`20 z (log z)³` for `z ≥ 2`. (Both entries are at most `lcm(d₁, d₂) ≤ z`.) -/
theorem card_filter_lcm_le {z : ℝ} (hz : 2 ≤ z) :
    ((#{q ∈ Icc 1 ⌊z⌋₊ ×ˢ Icc 1 ⌊z⌋₊ | (Nat.lcm q.1 q.2 : ℝ) ≤ z} : ℕ) : ℝ) ≤
      20 * z * Real.log z ^ 3 := by
  set N := ⌊z⌋₊ with hN
  have hz0 : 0 < z := by linarith
  have hNz : (N : ℝ) ≤ z := Nat.floor_le hz0.le
  set T := ((Icc 1 N ×ˢ Icc 1 N) ×ˢ Icc 1 N).filter
    (fun t : (ℕ × ℕ) × ℕ => t.1.1 * t.1.2 * t.2 ≤ N) with hT
  have h1 : (#{q ∈ Icc 1 N ×ˢ Icc 1 N | (Nat.lcm q.1 q.2 : ℝ) ≤ z}) ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun q : ℕ × ℕ => ((Nat.gcd q.1 q.2, q.1 / Nat.gcd q.1 q.2), q.2 / Nat.gcd q.1 q.2)) ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at hq
      obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, hl⟩ := hq
      have hlN : Nat.lcm q.1 q.2 ≤ N := Nat.le_floor hl
      have hg : 0 < Nat.gcd q.1 q.2 := Nat.gcd_pos_of_pos_left _ ha1
      have hab := gcd_mul_div_gcd_mul_div_gcd_eq_lcm q.1 q.2
      have ha0 : 0 < q.1 / Nat.gcd q.1 q.2 := Nat.div_pos (Nat.gcd_le_left _ ha1) hg
      have hb0 : 0 < q.2 / Nat.gcd q.1 q.2 := Nat.div_pos (Nat.gcd_le_right _ hb1) hg
      simp only [hT, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq]
      refine ⟨⟨⟨⟨hg, ?_⟩, ha0, ?_⟩, hb0, ?_⟩, hab.le.trans hlN⟩
      · exact (Nat.gcd_le_left _ ha1).trans ha2
      · exact (Nat.div_le_self _ _).trans ha2
      · exact (Nat.div_le_self _ _).trans hb2
    · exact gcd_div_gcd_injective.injOn
  have h2 : (T.card : ℝ) ≤
      ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, z * (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) := by
    rw [hT, Finset.card_filter, Finset.sum_product]
    push_cast
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    have hga : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Icc 1 N).filter (fun b => p.1 * p.2 * b ≤ N) ⊆ Icc 1 (N / (p.1 * p.2)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
      exact ⟨hb.1.1, (Nat.le_div_iff_mul_le hga).2 (by linarith [hb.2])⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at hc
    calc (((Icc 1 N).filter (fun b => p.1 * p.2 * b ≤ N)).card : ℝ)
        ≤ ((N / (p.1 * p.2) : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ (N : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ z / ((p.1 * p.2 : ℕ) : ℝ) := by gcongr
      _ = _ := by push_cast; field_simp
  have hH : ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) ≤ 1 + Real.log z := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simp only [one_div]
    refine h.trans ?_
    have : (0 : ℝ) < N := by
      have : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    gcongr
  have h3 : ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, z * (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ))
      = z * (∑ n ∈ Icc 1 N, (1 / (n : ℝ))) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : 0.69 < Real.log z := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz
    linarith
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) := Finset.sum_nonneg fun _ _ => by positivity
  have hsq : (∑ n ∈ Icc 1 N, (1 / (n : ℝ))) ^ 2 ≤ (1 + Real.log z) ^ 2 := by gcongr
  have hfin : (1 + Real.log z) ^ 2 ≤ 20 * Real.log z ^ 3 := by
    have h0 : 0 < Real.log z := by linarith
    have h2 : 0.69 * Real.log z < Real.log z ^ 2 := by nlinarith
    have h3 : 0.69 * Real.log z ^ 2 < Real.log z ^ 3 := by nlinarith
    nlinarith
  calc _ ≤ (T.card : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ z * (20 * Real.log z ^ 3) := by gcongr; exact hsq.trans hfin
    _ = _ := by ring

end Nat
