/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# A weighted sum of prime reciprocals

The sum `∑_{p ≤ x/2} 1 / (p log(x/p))` appears in the Selberg-sieve treatment of the
Goldbach and twin-prime problems. Splitting `1/log(x/p) = (log p / log(x/p) + 1) / log x`
and grouping the primes by `⌊log(x/p)⌋`, Chebyshev's bound and Mertens' second theorem show
that it is `O(log log x / log x)`.

## Main statements

* `Nat.sum_primesLE_inv_mul_log_div_le`: `∑_{p ≤ x/2} 1/(p log(x/p)) ≤ C log log x / log x`
  for `x ≥ 3`.
-/

@[expose] public section

open Finset

namespace Nat

/-- `∑_{p ≤ x/2} 1/(p log(x/p)) = O(log log x / log x)`: there is `C` with
`∑_{p ≤ x/2} 1/(p log(x/p)) ≤ C log log x / log x` for every real `x ≥ 3`. -/
theorem sum_primesLE_inv_mul_log_div_le :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      ∑ p ∈ primesLE ⌊x / 2⌋₊, (1 : ℝ) / (p * Real.log (x / p)) ≤
        C * Real.log (Real.log x) / Real.log x := by
  obtain ⟨C₁, hMer⟩ : ∃ C : ℝ, ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤ Real.log (Real.log z) + C := by
    obtain ⟨C, hC⟩ := Chebyshev.abs_sum_primesLE_inv_sub_log_log_le
    exact ⟨C, fun z hz => by linarith [(abs_le.mp (hC z hz)).2]⟩
  set C₀ := max C₁ 0 with hC₀def
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact Real.exp_one_lt_three
  set c0 := Real.log (Real.log 3) with hc0def
  have hc0 : 0 < c0 := Real.log_pos hlog3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K' := Real.exp 1 * Real.log 4 with hK'def
  have hK' : 0 ≤ K' := by positivity
  set K := K' * (1 / Real.log 2 + 1) with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨(K' + 1) + (K + C₀) / c0, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 < L := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hx)
  have hL0 : 0 < L := by linarith
  have hLL : c0 ≤ Real.log L := Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hx)
  set P := primesLE ⌊x / 2⌋₊ with hPdef
  have hmemP : ∀ p ∈ P, p.Prime ∧ (2 : ℝ) ≤ p ∧ (p : ℝ) ≤ x / 2 := by
    intro p hp
    rw [hPdef, mem_primesLE] at hp
    refine ⟨hp.2, by exact_mod_cast hp.2.two_le, ?_⟩
    exact (Nat.le_floor_iff (by positivity)).mp hp.1
  -- the logarithm `log (x / p)` is at least `log 2`
  have hlxp : ∀ p ∈ P, Real.log 2 ≤ Real.log (x / p) := by
    intro p hp
    obtain ⟨-, h2, hpx⟩ := hmemP p hp
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by linarith)]; linarith
  -- split each term
  have hsplit : ∀ p ∈ P, (1 : ℝ) / (p * Real.log (x / p)) =
      (1 / L) * (Real.log p / (p * Real.log (x / p)) + 1 / p) := by
    intro p hp
    obtain ⟨-, h2, hpx⟩ := hmemP p hp
    have hl := hlxp p hp
    have hl0 : 0 < Real.log (x / p) := by linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hdec : Real.log (x / p) = L - Real.log p := Real.log_div hx0.ne' hp0.ne'
    rw [hdec] at hl0 ⊢
    field_simp
    ring
  -- second sum: Mertens
  have hS2 : ∑ p ∈ P, (1 : ℝ) / p ≤ Real.log L + C₀ := by
    refine le_trans ?_ ((hMer x (by linarith)).trans (by linarith [le_max_left C₁ 0]))
    simp only [one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, -, hpx⟩ := hmemP p hp
      exact mem_primesLE.mpr ⟨Nat.le_floor (by linarith), hpp⟩
    · intros; positivity
  -- first sum
  set M := ⌊L⌋₊ with hMdef
  set g : ℕ → ℝ := fun m => if m = 0 then 1 / Real.log 2 else 1 / (m : ℝ) with hgdef
  have hg0 : ∀ m, 0 ≤ g m := by
    intro m; simp only [hgdef]; split_ifs <;> positivity
  have hS1 : ∑ p ∈ P, Real.log p / (p * Real.log (x / p)) ≤ K + K' * Real.log L := by
    have hmaps : ∀ p ∈ P, ⌊Real.log (x / p)⌋₊ ∈ Finset.range (M + 1) := by
      intro p hp
      obtain ⟨-, h2, hpx⟩ := hmemP p hp
      rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.floor_le_floor
      exact Real.log_le_log (_root_.div_pos hx0 (by linarith))
        (_root_.div_le_self hx0.le (by linarith))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ m ∈ Finset.range (M + 1),
        ∑ p ∈ P with ⌊Real.log (x / ((p : ℕ) : ℝ))⌋₊ = m, Real.log p / (p * Real.log (x / p)) ≤
          K' * g m := by
      intro m _
      calc ∑ p ∈ P with ⌊Real.log (x / ((p : ℕ) : ℝ))⌋₊ = m, Real.log p / (p * Real.log (x / p))
          ≤ ∑ p ∈ P with ⌊Real.log (x / ((p : ℕ) : ℝ))⌋₊ = m,
              (Real.exp (m + 1) / x * g m) * Real.log p := by
            apply Finset.sum_le_sum
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hpP, hpm⟩ := hp
            obtain ⟨-, h2, hpx⟩ := hmemP p hpP
            have hl := hlxp p hpP
            have hp0 : (0 : ℝ) < p := by linarith
            have hl0 : 0 < Real.log (x / p) := by linarith
            have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
            have h1 : 1 / (p : ℝ) ≤ Real.exp (m + 1) / x := by
              have : Real.log (x / p) < m + 1 := by rw [← hpm]; exact Nat.lt_floor_add_one _
              have := (Real.log_lt_iff_lt_exp (_root_.div_pos hx0 hp0)).mp this
              rw [div_lt_iff₀ hp0] at this
              rw [div_le_div_iff₀ hp0 hx0]; linarith
            have h2' : 1 / Real.log (x / p) ≤ g m := by
              simp only [hgdef]
              split_ifs with hm0
              · exact one_div_le_one_div_of_le hlog2 hl
              · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
                apply one_div_le_one_div_of_le (by linarith)
                rw [← hpm]; exact Nat.floor_le hl0.le
            have : Real.log p / (p * Real.log (x / p)) =
                (1 / p) * (1 / Real.log (x / p)) * Real.log p := by
              field_simp
            rw [this]
            apply mul_le_mul_of_nonneg_right _ hlogp
            exact mul_le_mul h1 h2' (by positivity) (by positivity)
        _ ≤ (Real.exp (m + 1) / x * g m) *
              ∑ p ∈ primesLE ⌊x / Real.exp m⌋₊, Real.log p := by
            rw [← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (hg0 m))
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              rw [Finset.mem_filter] at hp
              obtain ⟨hpP, hpm⟩ := hp
              obtain ⟨hpp, h2, hpx⟩ := hmemP p hpP
              rw [mem_primesLE]
              refine ⟨Nat.le_floor ?_, hpp⟩
              have hp0 : (0 : ℝ) < p := by linarith
              have : (m : ℝ) ≤ Real.log (x / p) := by
                rw [← hpm]; exact Nat.floor_le (by linarith [hlxp p hpP])
              have := (Real.le_log_iff_exp_le (_root_.div_pos hx0 hp0)).mp this
              rw [le_div_iff₀ hp0] at this
              rw [le_div_iff₀ (Real.exp_pos _)]; linarith
            · intro p hp _
              have := (mem_primesLE.mp hp).2.one_lt
              exact Real.log_nonneg (by exact_mod_cast this.le)
        _ ≤ (Real.exp (m + 1) / x * g m) * (Real.log 4 * (x / Real.exp m)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (hg0 m))
            rw [← Chebyshev.theta_eq_sum_primesLE]
            exact Chebyshev.theta_le_log4_mul_x (by positivity)
        _ = K' * g m := by
            rw [hK'def, Real.exp_add]; field_simp
    have hgsum : ∑ m ∈ Finset.range (M + 1), g m ≤ 1 / Real.log 2 + 1 + Real.log L := by
      rw [Finset.sum_range_succ']
      have hg00 : g 0 = 1 / Real.log 2 := by simp [hgdef]
      have hH : ∑ i ∈ Finset.range M, g (i + 1) = (harmonic M : ℝ) := by
        simp only [harmonic, hgdef]
        push_cast
        simp [one_div]
      have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hL1.le)
      have hlogM : Real.log M ≤ Real.log L :=
        Real.log_le_log (by exact_mod_cast hM1) (Nat.floor_le hL0.le)
      have := harmonic_le_one_add_log M
      rw [hH, hg00]
      linarith
    calc ∑ m ∈ Finset.range (M + 1), ∑ p ∈ P with ⌊Real.log (x / ((p : ℕ) : ℝ))⌋₊ = m,
          Real.log p / (p * Real.log (x / p))
        ≤ ∑ m ∈ Finset.range (M + 1), K' * g m := Finset.sum_le_sum hfib
      _ = K' * ∑ m ∈ Finset.range (M + 1), g m := by rw [Finset.mul_sum]
      _ ≤ K' * (1 / Real.log 2 + 1 + Real.log L) := mul_le_mul_of_nonneg_left hgsum hK'
      _ = K + K' * Real.log L := by rw [hKdef]; ring
  calc ∑ p ∈ P, (1 : ℝ) / (p * Real.log (x / p))
      = (1 / L) * (∑ p ∈ P, Real.log p / (p * Real.log (x / p)) + ∑ p ∈ P, (1 : ℝ) / p) := by
        rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (1 / L) * ((K + C₀) + (K' + 1) * Real.log L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ (1 / L) * (((K' + 1) + (K + C₀) / c0) * Real.log L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : K + C₀ ≤ (K + C₀) / c0 * Real.log L := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
          exact mul_le_mul_of_nonneg_left hLL (by positivity)
        nlinarith
    _ = ((K' + 1) + (K + C₀) / c0) * Real.log L / L := by ring

end Nat
