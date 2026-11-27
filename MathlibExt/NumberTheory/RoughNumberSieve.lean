/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.NumberTheory.RoughNumbers

/-!
# Sieve bound for integers without small prime factors

`MetaMathlibExt.card_minFac_gt_le_div_log` bounds the count of integers up to `x` whose least
prime factor exceeds `y`. We bound their reciprocal sum by multiplying by the harmonic sum up to
`y`, and pass to the counting function using Chebyshev's bound for the von Mangoldt function.
-/

namespace MetaMathlibExt

open Finset Real
open scoped ArithmeticFunction

namespace card_minFac_gt_le_div_log

private def roughUpTo (N k : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (·.IsRough k)

private theorem coprime_small {m a k : ℕ} (hm : m.IsRough k) (ha : a ∈ Icc 1 k) :
    m.Coprime a := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpa
  exact (hm.lt_of_prime_dvd hp hpm).not_ge ((Nat.le_of_dvd (mem_Icc.mp ha).1 hpa).trans
    (mem_Icc.mp ha).2)

-- Each product of a rough number and a positive integer at most k determines both factors.
private theorem rough_mul_injOn (N k : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (roughUpTo N k ×ˢ Icc 1 k : Finset _) := by
  rintro ⟨m, a⟩ hma ⟨n, b⟩ hnb (heq : m * a = n * b)
  obtain ⟨hm, ha⟩ := mem_product.mp hma
  obtain ⟨hn, hb⟩ := mem_product.mp hnb
  have hmn : m ∣ n := (coprime_small (mem_filter.mp hm).2 hb).dvd_of_dvd_mul_right
    (heq ▸ dvd_mul_right m a)
  have hnm : n ∣ m := (coprime_small (mem_filter.mp hn).2 ha).dvd_of_dvd_mul_right
    (heq.symm ▸ dvd_mul_right n b)
  obtain rfl := Nat.dvd_antisymm hmn hnm
  exact Prod.ext rfl (Nat.mul_left_cancel (mem_filter.mp hm).2.pos heq)

private theorem reciprocal_sum_mul_harmonic (N k : ℕ) :
    (∑ m ∈ roughUpTo N k, (m : ℝ)⁻¹) * harmonic k ≤ harmonic (N * k) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [sum_mul_sum, ← sum_product']
  apply sum_le_sum_of_injOn (fun p : ℕ × ℕ => p.1 * p.2) (rough_mul_injOn N k)
  · intro t ht
    obtain ⟨⟨m, a⟩, h, rfl⟩ := mem_image.mp ht
    obtain ⟨hm, ha⟩ := mem_product.mp h
    obtain ⟨hm₁, hm₂⟩ := mem_Icc.mp (mem_filter.mp hm).1
    obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨Nat.mul_pos hm₁ ha₁, Nat.mul_le_mul hm₂ ha₂⟩
  · intro p _
    simp [mul_comm]
  · intros
    positivity

-- In log n = ∑_{md=n} Λ(d), every cofactor m is rough if n is rough.
private theorem sum_log_le_sum_psi (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∑ n ∈ roughUpTo ⌊x⌋₊ k, log n ≤ ∑ m ∈ roughUpTo ⌊x⌋₊ k, Chebyshev.psi (x / m) := by
  have hexpand (n : ℕ) : log n = ∑ p ∈ n.divisorsAntidiagonal, Λ p.2 := by
    rw [Nat.sum_divisorsAntidiagonal' (fun _ d => Λ d), ArithmeticFunction.vonMangoldt_sum]
  simp_rw [hexpand, Chebyshev.psi]
  rw [sum_sigma', sum_sigma']
  apply sum_le_sum_of_injOn (fun p : (Σ _ : ℕ, ℕ × ℕ) => (⟨p.2.1, p.2.2⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨n, a, b⟩ hn ⟨n', a', b'⟩ hn' h
    obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by simpa using h
    have h₁ := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hn).2).1
    have h₂ := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hn').2).1
    obtain rfl : n = n' := h₁.symm.trans h₂
    rfl
  · intro t ht
    obtain ⟨⟨n, a, b⟩, hn, rfl⟩ := mem_image.mp ht
    obtain ⟨hn, hab⟩ := mem_sigma.mp hn
    obtain ⟨hn, hrough⟩ := mem_filter.mp hn
    obtain ⟨heq, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    change a * b = n at heq
    subst n
    have ha : 0 < a := Nat.pos_of_ne_zero fun h => hne (by simp [h])
    have hb : 0 < b := Nat.pos_of_ne_zero fun h => hne (by simp [h])
    have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
    have hle := (mem_Icc.mp hn).2
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, (Nat.le_mul_of_pos_right _ hb).trans hle⟩,
      hrough.of_dvd (dvd_mul_right a b) ha.ne'⟩, mem_Ioc.mpr ⟨hb, ?_⟩⟩
    apply (Nat.le_floor_iff (div_nonneg hx ha'.le)).mpr
    rw [le_div_iff₀ ha', mul_comm]
    exact_mod_cast (Nat.le_floor_iff hx).mp hle
  · intros
    rfl
  · intros
    exact ArithmeticFunction.vonMangoldt_nonneg

private theorem card_mul_log_le (x : ℝ) (hx : 0 < x) (k : ℕ) :
    ((roughUpTo ⌊x⌋₊ k).card : ℝ) * log x ≤
      8 * x * ∑ m ∈ roughUpTo ⌊x⌋₊ k, (m : ℝ)⁻¹ := by
  let S := roughUpTo ⌊x⌋₊ k
  have hlog := sum_log_le_sum_psi x hx.le k
  calc
    (S.card : ℝ) * log x = ∑ _n ∈ S, log x := by simp
    _ ≤ ∑ n ∈ S, (log n + x / n) := by
      apply sum_le_sum
      intro n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast (mem_filter.mp hn).2.pos
      have h := log_le_sub_one_of_pos (div_pos hx hn')
      rw [log_div hx.ne' hn'.ne'] at h
      linarith
    _ ≤ ∑ n ∈ S, (Chebyshev.psi (x / n) + x / n) := by
      simpa only [sum_add_distrib, add_le_add_iff_right] using hlog
    _ ≤ ∑ n ∈ S, 8 * x * (n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n _
      have ht : 0 ≤ x / n := by positivity
      have h := Chebyshev.psi_le_const_mul_self ht
      have h4 := log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      rw [show 8 * x * (n : ℝ)⁻¹ = 8 * (x / n) by ring]
      nlinarith [mul_nonneg (show 0 ≤ 3 - log 4 by linarith) ht]
    _ = _ := by rw [mul_sum]

end card_minFac_gt_le_div_log

open card_minFac_gt_le_div_log

/-- **Sieve bound for integers without small prime factors.** Write $p(n)$ for the least prime
factor of an integer $n \ge 2$, and set $p(1) = 1$. There is a constant $C$ such that for all real
$x$ and $y$ with $2 \le y \le x$, the number of integers $1 \le n \le x$ with $p(n) > y$ is at
most $C x / \log y$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 2 (`fq-2024-luca09162024rev2-lem-2`),
quoted from Tenenbaum, page 397. -/
public theorem card_minFac_gt_le_div_log :
    ∃ C : ℝ, ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => y < (Nat.minFac n : ℝ))).card ≤
        C * x / Real.log y := by
  refine ⟨32, fun x y hy hxy => ?_⟩
  have hx : 2 ≤ x := hy.trans hxy
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 < y := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hly : 0 < log y := log_pos (by linarith)
  let S := roughUpTo ⌊x⌋₊ ⌊y⌋₊
  have hsub : ((Icc 1 ⌊x⌋₊).filter (fun n => y < (Nat.minFac n : ℝ))) ⊆ S := by
    intro n hn
    obtain ⟨hn, hmin⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn, Nat.ne_of_gt (mem_Icc.mp hn).1, fun p hp hdvd => ?_⟩
    have h := Nat.minFac_le_of_dvd hp.two_le hdvd
    exact (Nat.floor_lt hy₀.le).mpr (hmin.trans_le (by exact_mod_cast h))
  have hcard := card_mul_log_le x hx₀ ⌊y⌋₊
  have hrecip : (∑ m ∈ S, (m : ℝ)⁻¹) * log y ≤ 4 * log x := calc
    _ ≤ (∑ m ∈ S, (m : ℝ)⁻¹) * harmonic ⌊y⌋₊ := by
      gcongr
      exact log_le_harmonic_floor y hy₀.le
    _ ≤ harmonic (⌊x⌋₊ * ⌊y⌋₊) :=
      reciprocal_sum_mul_harmonic _ _
    _ ≤ 1 + log (⌊x⌋₊ * ⌊y⌋₊ : ℕ) := harmonic_le_one_add_log _
    _ ≤ 1 + log (x * y) := by
      have hx' := Nat.floor_pos.mpr (show 1 ≤ x by linarith)
      have hy' := Nat.floor_pos.mpr (show 1 ≤ y by linarith)
      push_cast
      gcongr
      · exact Nat.floor_le hx₀.le
      · exact Nat.floor_le hy₀.le
    _ ≤ 4 * log x := by
      rw [log_mul hx₀.ne' hy₀.ne']
      have h₂ := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith [log_le_log (by norm_num : (0 : ℝ) < 2) hx, log_le_log hy₀ hxy]
  apply (le_div_iff₀ hly).mpr
  apply (mul_le_mul_iff_left₀ hlx).mp
  calc
    _ ≤ (S.card : ℝ) * log y * log x := by
      gcongr
    _ = ((S.card : ℝ) * log x) * log y := by ring
    _ ≤ (8 * x * ∑ m ∈ S, (m : ℝ)⁻¹) * log y :=
      mul_le_mul_of_nonneg_right hcard hly.le
    _ = (8 * x) * ((∑ m ∈ S, (m : ℝ)⁻¹) * log y) := by ring
    _ ≤ (8 * x) * (4 * log x) := by gcongr
    _ = _ := by ring

end MetaMathlibExt
