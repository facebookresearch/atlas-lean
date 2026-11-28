/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 12

Recurrence F(r+1, n) = n F(r, n) + F(r+1, n+1)/a for ∑ (n+k)^(r+k)/(aᵏ k!).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry12

noncomputable def F (r : ℤ) (n a : ℂ) : ℂ :=
  ∑' k : ℕ, (n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))

private theorem aux_summ (s : ℤ) (n a : ℂ)
    (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ s ≤ -2)) :
    Summable (fun k : ℕ => (n + (k : ℂ)) ^ (s + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) :=
  (Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general s n a ha).of_norm

private theorem aux_pointwise (r : ℤ) (n a : ℂ) (k : ℕ)
    (ha0 : a ≠ 0)
    (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
    (n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))
      = n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
      + (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) := by
  have hden : a ^ k * (k.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k ha0) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  have hzk : (n + (k : ℂ)) ^ (r + 1 + (k : ℤ))
      = (n + (k : ℂ)) ^ (r + (k : ℤ)) * (n + (k : ℂ)) := by
    by_cases h0 : n + (k : ℂ) = 0
    · have he : 0 ≤ r + (k : ℤ) :=
        not_lt.mp (fun hlt => absurd h0 (hn k hlt))
      by_cases he0 : r + (k : ℤ) = 0
      · have hL : (n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) = 0 := by
          have h1 : r + 1 + (k : ℤ) = 1 := by omega
          rw [h0, h1, zpow_one]
        have hR : (n + (k : ℂ)) ^ (r + (k : ℤ)) * (n + (k : ℂ)) = 0 := by
          rw [h0, he0, zpow_zero, one_mul]
        rw [hL, hR]
      · have he1 : r + 1 + (k : ℤ) ≠ 0 := by omega
        rw [h0, zero_zpow _ he1, zero_zpow _ he0, zero_mul]
    · have h1 : r + 1 + (k : ℤ) = (r + (k : ℤ)) + 1 := by ring
      rw [h1, zpow_add_one₀ h0]
  have hsplit : (n + (k : ℂ)) ^ (r + (k : ℤ)) * (n + (k : ℂ))
      = n * (n + (k : ℂ)) ^ (r + (k : ℤ))
        + (k : ℂ) * (n + (k : ℂ)) ^ (r + (k : ℤ)) := by
    ring
  rw [hzk, hsplit, add_div]
  congr 1
  · field_simp
  · field_simp

private theorem aux_shift (r : ℤ) (n a : ℂ) (ha0 : a ≠ 0)
    (Hh : Summable (fun k : ℕ =>
      (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))))) :
    ∑' k : ℕ, (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
      = ∑' k : ℕ, (n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ (k + 1) * (k.factorial : ℂ)) := by
  have hsucc : ∀ k : ℕ,
      (fun k : ℕ => (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))) (k + 1)
      = (fun k : ℕ => (n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ (k + 1) * (k.factorial : ℂ))) k := by
    intro k
    simp only
    have hfact : ((k + 1).factorial : ℂ) = ((k.factorial : ℂ)) * ((k : ℂ) + 1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_comm]
    have hcast1 : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
    have hcast2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have hden1 : a ^ (k + 1) * (k.factorial : ℂ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ha0) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
    have hkk : ((k : ℂ) + 1) ≠ 0 := by
      have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      rwa [hcast1] at hne
    rw [hcast1, hcast2]
    have e1 : r + ((k : ℤ) + 1) = (r + 1 + (k : ℤ)) := by ring
    rw [e1]
    have e2 : n + ((k : ℂ) + 1) = n + 1 + (k : ℂ) := by ring
    rw [e2]
    rw [hfact]
    field_simp
  have h_eq := Hh.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_mul, zero_add] at h_eq
  rw [h_eq]
  apply tsum_congr
  intro k
  exact hsucc k

private theorem aux_g (r : ℤ) (n a : ℂ) (ha0 : a ≠ 0) (k : ℕ) :
    (n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ (k + 1) * (k.factorial : ℂ))
      = (1 / a) * ((n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) := by
  have hden : a ^ k * (k.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k ha0) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  field_simp
  ring

private theorem main_assemble (r : ℤ) (n a : ℂ)
    (ha0 : a ≠ 0)
    (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0)
    (S2 : Summable (fun k : ℕ => (n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))))
    (S4 : Summable (fun k : ℕ => (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))))) :
    F (r + 1) n a = n * F r n a + (1 / a) * F (r + 1) (n + 1) a := by
  have pw : ∀ k : ℕ,
      (n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))
      = n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
        + (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) :=
    fun k => aux_pointwise r n a k ha0 hn
  have e1 : (∑' k : ℕ, (n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
      = ∑' k : ℕ, (n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
        + (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))) :=
    tsum_congr pw
  have Sv : Summable (fun k : ℕ => n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))) :=
    S2.mul_left n
  have e2 : (∑' k : ℕ, (n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))
        + (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))))
      = (∑' k : ℕ, n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))))
        + ∑' k : ℕ, (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) :=
    Sv.tsum_add S4
  have e3 : (∑' k : ℕ, n * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))))
      = n * ∑' k : ℕ, (n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)) :=
    tsum_mul_left
  have e4a := aux_shift r n a ha0 S4
  have e4b : (∑' k : ℕ, (n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ (k + 1) * (k.factorial : ℂ)))
      = (1 / a) * ∑' k : ℕ, (n + 1 + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    exact aux_g r n a ha0 k
  show F (r + 1) n a = n * F r n a + (1 / a) * F (r + 1) (n + 1) a
  unfold F
  rw [e1, e2, e3, e4a, e4b]

/-- **Ramanujan's recurrence for the series in Entry 12.** Fix a complex number $a$. For an
integer $r$ and a complex number $n$, let
$$F_r(n) = \sum_{k=0}^{\infty} \frac{(n+k)^{r+k}}{a^k\, k!},$$
where the sum is taken to be $0$ if the series is not summable. Suppose that $|a| > e$, or that
$a = e$ and $r \le -2$, and that $n + k \ne 0$ for every natural number $k$ with $r + k < 0$.
Then
$$F_{r+1}(n) = n F_r(n) + \frac{1}{a} F_{r+1}(n+1).$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) and Entry 12,
    printed pp. 66-67 / PDF pp. 76-77.
Proves `Wanted` entry `ramanujan_part1_ch3_entry12`.
-/
theorem ramanujan_part1_ch3_entry12 (r : ℤ) (n a : ℂ)
    (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
    (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
    F (r + 1) n a = n * F r n a + (1 / a) * F (r + 1) (n + 1) a := by
  have ha0 : a ≠ 0 := by
    apply norm_pos_iff.mp
    rcases ha with hgt | ⟨heq, hle⟩
    · exact lt_trans (Real.exp_pos 1) hgt
    · rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1)]
      exact Real.exp_pos 1
  have hS2 : Summable (fun k : ℕ => (n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))) :=
    (aux_summ (r - 1) n a (ha.imp id fun h => ⟨h.1, by linarith [h.2]⟩)).congr fun k => by
      rw [sub_add_cancel]
  have hS4 : Summable (fun k : ℕ => (k : ℂ) * ((n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ)))) :=
    ((aux_summ r n a ha).sub (hS2.mul_left n)).congr fun k => by
      rw [aux_pointwise r n a k ha0 hn]
      ring
  exact main_assemble r n a ha0 hn hS2 hS4

end Entry12

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
