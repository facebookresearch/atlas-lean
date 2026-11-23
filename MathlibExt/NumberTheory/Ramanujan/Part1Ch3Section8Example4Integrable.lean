/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 4

Interval integrability of a scaled EGF-type integrand on [0,1].
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example4Integrable

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

/-- **Generalized Bell function extended to $n = -1$.** For an integer $n \ge -1$ and a complex
number $x$, $f(n, x) = 1$ if $n = -1$, and otherwise $f(n, x)$ is the generalized Bell function
$F(0, 1, x; n) = e^{-x} \sum_{k \ge 0} (k + 1)^n x^{k + 1} / k!$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 4 and its
correction, printed pp. 51--52 / PDF pp. 61--62. -/
noncomputable def f (n : { n : ℤ // -1 ≤ n }) (x : ℂ) : ℂ :=
  if n.val = -1 then 1 else generalizedBellGenerating 0 1 x n.val.toNat

@[simp]
theorem f_neg_one (h : (-1 : ℤ) ≤ -1) (x : ℂ) : f ⟨-1, h⟩ x = 1 := by
  simp [f]

@[simp]
theorem f_natCast (k : ℕ) (h : (-1 : ℤ) ≤ k) (x : ℂ) :
    f ⟨k, h⟩ x = generalizedBellGenerating 0 1 x k := by
  have hk : (k : ℤ) ≠ -1 := by omega
  simp [f, hk]

private lemma real_pow_le_aux (k j : ℕ) : ((j : ℝ) + 1) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ j := by
  have hle : ((j : ℝ) + 1) ≤ (2 ^ j : ℕ) := by
    have h : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h2 ⊢
    linarith
  calc ((j : ℝ) + 1) ^ k ≤ ((2 ^ j : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) hle k
    _ = (((2 : ℝ) ^ j) ^ k) := by push_cast; ring_nf
    _ = (((2 : ℝ) ^ k) ^ j) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (((2 ^ k : ℕ) : ℝ) ^ j) := by push_cast; ring_nf

private lemma summable_bound_aux (k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)) := by
  have hbase : Summable (fun j : ℕ => R * (((2 ^ k : ℕ) : ℝ) * R) ^ j / (Nat.factorial j : ℝ)) := by
    have h := Real.summable_pow_div_factorial (((2 ^ k : ℕ) : ℝ) * R)
    have := h.mul_left R
    simpa [mul_div_assoc, mul_comm, mul_left_comm] using this
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hbase
  intro j
  have hle := real_pow_le_aux k j
  have hfact : (0 : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hRpow : (0 : ℝ) ≤ R ^ (j + 1) := pow_nonneg hR _
  have h2 : ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)
      ≤ ((2 ^ k : ℕ) : ℝ) ^ j * R ^ (j + 1) / (Nat.factorial j : ℝ) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hRpow) hfact
  calc ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)
        ≤ ((2 ^ k : ℕ) : ℝ) ^ j * R ^ (j + 1) / (Nat.factorial j : ℝ) := h2
      _ = R * (((2 ^ k : ℕ) : ℝ) * R) ^ j / (Nat.factorial j : ℝ) := by
        rw [mul_pow, pow_succ']
        ring

private lemma cont_each_aux (k : ℕ) (x : ℂ) (j : ℕ) :
    Continuous (fun t : ℝ => (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
      (↑(Nat.factorial j) : ℂ)) := by
  apply Continuous.div_const
  apply Continuous.mul continuous_const
  apply Continuous.pow
  apply Continuous.mul Complex.continuous_ofReal continuous_const

private lemma norm_bound_aux (k : ℕ) (x : ℂ) (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) / (↑(Nat.factorial j) : ℂ)‖
      ≤ ((j : ℝ) + 1) ^ k * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ) := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have habs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]; exact ht1
  have hR : 0 ≤ ‖x‖ := norm_nonneg _
  have hcoeff : ‖(↑((j + 1) ^ k : ℕ) : ℂ)‖ = ((j : ℝ) + 1) ^ k := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  have hfactC : ‖(↑(Nat.factorial j) : ℂ)‖ = (Nat.factorial j : ℝ) := by
    rw [Complex.norm_natCast]
  have hy : ‖((t : ℂ) * x)‖ ≤ ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖x‖ ≤ 1 * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right habs hR
      _ = ‖x‖ := one_mul _
  have hyPow : ‖(((t : ℂ) * x) ^ (j + 1))‖ ≤ ‖x‖ ^ (j + 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hy _
  rw [norm_div, norm_mul, hcoeff, hfactC]
  have hfact_nonneg : (0 : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hmul : ((j : ℝ) + 1) ^ k * ‖(((t : ℂ) * x) ^ (j + 1))‖
      ≤ ((j : ℝ) + 1) ^ k * ‖x‖ ^ (j + 1) := by
    exact mul_le_mul_of_nonneg_left hyPow (by positivity)
  exact div_le_div_of_nonneg_right hmul hfact_nonneg

set_option backward.proofsInPublic true in
/-- **Integrability of the scaled generalized Bell integrand on $[0, 1]$.** Let $f$ be the
generalized Bell function extended to $n = -1$. For every natural number $m$ and every complex
number $x$, the complex-valued function $t \mapsto x f(m - 1, t x)$ of a real variable $t$ is
interval integrable on $[0, 1]$ with respect to Lebesgue measure.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 4 and its
    correction, printed pp. 51--52 / PDF pp. 61--62.
Proves `Wanted` entry `ramanujan_part1_ch3_section8_example4_integrable`.
-/
theorem ramanujan_part1_ch3_section8_example4_integrable (m : ℕ) (x : ℂ) :
    IntervalIntegrable (fun t : ℝ => x * f ⟨(m : ℤ) - 1,
        by omega⟩ ((t : ℂ) * x)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  cases m with
  | zero =>
    have hn : (⟨((0 : ℕ) : ℤ) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val = -1 := by
      simp
    have hfun : (fun t : ℝ => x * f ⟨((0 : ℕ) : ℤ) - 1, by omega⟩ ((t : ℂ) * x))
        = (fun _ : ℝ => x * 1) := by
      funext t
      simp [f]
    rw [hfun]
    exact continuousOn_const
  | succ k =>
    have hval : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val = (k : ℤ) := by
      push_cast
      ring
    have hn_ne : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val ≠ -1 := by
      rw [hval]
      omega
    have htoNat : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val.toNat = k := by
      rw [hval]
      exact Int.toNat_natCast k
    have hfun : (fun t : ℝ => x * f ⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ ((t : ℂ) * x))
        = (fun t : ℝ => x * (Complex.exp (-((t : ℂ) * x)) *
          ∑' (j : ℕ), (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
            (↑(Nat.factorial j) : ℂ))) := by
      funext t
      simp [f, generalizedBellGenerating]
    rw [hfun]
    have hS : ContinuousOn
        (fun t : ℝ => ∑' (j : ℕ), (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
          (↑(Nat.factorial j) : ℂ)) (Set.Icc 0 1) := by
      apply continuousOn_tsum (fun j => (cont_each_aux k x j).continuousOn)
        (summable_bound_aux k ‖x‖ (norm_nonneg _))
      intro j t ht
      exact norm_bound_aux k x j t ht
    have hexp : ContinuousOn (fun t : ℝ => Complex.exp (-((t : ℂ) * x))) (Set.Icc 0 1) := by
      apply Continuous.continuousOn
      fun_prop
    exact continuousOn_const.mul (hexp.mul hS)

end Section8Example4Integrable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
