/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import MathlibExt.Analysis.SpecialFunctions.Log.Zelinsky
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith

/-! # Prime reciprocal sums of odd perfect and primitive non-deficient numbers

Lower bound on the prime reciprocal sum of a primitive non-deficient number in terms of
its least prime factor and abundancy surplus, after Joshua Zelinsky, *The Sum of the
Reciprocals of the Prime Divisors of an Odd Perfect or Odd Primitive Non-deficient
Number*, INTEGERS 25 (2025), Article A59 (arXiv:2402.14234v5), Proposition 3.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

/-- Derivative of `t ↦ log (1 + t) - t + t ^ 2 / 2`: `x ^ 2 / (1 + x)`. -/
private theorem hasDerivAt_phi (x : ℝ) (hx : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun t => Real.log (1 + t) - t + t ^ 2 / 2) (x ^ 2 / (1 + x)) x := by
  have hne : (1 : ℝ) + x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt (fun t => Real.log (1 + t)) ((1 + x)⁻¹) x := by
    have hcomp := (Real.hasDerivAt_log hne).comp x ((hasDerivAt_id x).const_add 1)
    simpa [Function.comp_def] using hcomp
  have hsub := hlog.sub (hasDerivAt_id x)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
    have h := (hasDerivAt_pow 2 x).div_const 2
    simpa using h
  have hadd := hsub.add hsq
  have hval : (1 + x)⁻¹ - 1 + x = x ^ 2 / (1 + x) := by field_simp; ring
  rw [hval] at hadd
  exact hadd

/-- Quadratic lower bound for the logarithm: `s - s ^ 2 / 2 ≤ log (1 + s)` for `s ≥ 0`. -/
private theorem sub_sq_div_two_le_log_one_add {s : ℝ} (hs : 0 ≤ s) :
    s - s ^ 2 / 2 ≤ Real.log (1 + s) := by
  let φ : ℝ → ℝ := fun t => Real.log (1 + t) - t + t ^ 2 / 2
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hdiff : DifferentiableOn ℝ φ (Set.Icc 0 s) := by
    intro x hx
    have hx1 : (0 : ℝ) < 1 + x := by
      have hx0 : (0 : ℝ) ≤ x := hx.1
      linarith
    exact (hasDerivAt_phi x hx1).differentiableAt.differentiableWithinAt
  have hge : ∀ x ∈ interior (Set.Icc (0 : ℝ) s), (0 : ℝ) ≤ deriv φ x := by
    rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_phi x (by linarith [hx.1])).deriv]
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    exact div_nonneg (sq_nonneg x) hx1.le
  have h := (convex_Icc (0 : ℝ) s).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuousOn (hdiff.mono interior_subset) hge 0 (Set.left_mem_Icc.mpr hs) s
    (Set.right_mem_Icc.mpr hs) hs
  rw [hφ0] at h
  simp only [φ, zero_mul] at h
  linarith

/-- Derivative of the surplus remainder `T ↦ log (2 + T) - log 2 - T / 2 + T ^ 2 / 4`. -/
private theorem hasDerivAt_sig (x : ℝ) (hx : (0 : ℝ) < 2 + x) :
    HasDerivAt (fun t => Real.log (2 + t) - Real.log 2 - t / 2 + t ^ 2 / 4)
      (x * (x + 1) / (2 * (2 + x))) x := by
  have hne : (2 : ℝ) + x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt (fun t => Real.log (2 + t)) ((2 + x)⁻¹) x := by
    have hcomp := (Real.hasDerivAt_log hne).comp x ((hasDerivAt_id x).const_add 2)
    simpa [Function.comp_def] using hcomp
  have hadd := ((hlog.sub_const (Real.log 2)).sub
    ((hasDerivAt_id x).div_const 2)).add ((hasDerivAt_pow 2 x).div_const 4)
  have hval : ((2 + x)⁻¹ - 1 / 2) + ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 4
      = x * (x + 1) / (2 * (2 + x)) := by
    norm_num
    field_simp
    ring
  rw [hval] at hadd
  exact hadd

/-- The surplus remainder `log (2 + S) - log 2 - S / 2 + S ^ 2 / 4` is nonnegative for `S ≥ -1`. -/
private theorem slack_nonneg {S : ℝ} (hS : -1 ≤ S) :
    0 ≤ Real.log (2 + S) - Real.log 2 - S / 2 + S ^ 2 / 4 := by
  rcases le_total (0 : ℝ) S with h0 | h0
  · have hA := sub_sq_div_two_le_log_one_add (show (0 : ℝ) ≤ S / 2 by linarith)
    have hlog : Real.log (2 + S) - Real.log 2 = Real.log (1 + S / 2) := by
      have h2 : (2 : ℝ) + S ≠ 0 := by linarith
      rw [← Real.log_div h2 (by norm_num)]
      congr 1
      field_simp
    have hsq : (S / 2) ^ 2 / 2 = S ^ 2 / 8 := by ring
    have hnn : (0 : ℝ) ≤ S ^ 2 / 8 := div_nonneg (sq_nonneg S) (by norm_num)
    rw [hlog]
    linarith
  · let σ : ℝ → ℝ := fun t => Real.log (2 + t) - Real.log 2 - t / 2 + t ^ 2 / 4
    have hσ0 : σ 0 = 0 := by simp [σ]
    have hdiff : DifferentiableOn ℝ σ (Set.Icc S 0) := by
      intro x hx
      have hx2 : (0 : ℝ) < 2 + x := by
        have hxS : S ≤ x := hx.1
        linarith
      exact (hasDerivAt_sig x hx2).differentiableAt.differentiableWithinAt
    have hle : ∀ x ∈ interior (Set.Icc S 0), deriv σ x ≤ 0 := by
      rw [interior_Icc]
      intro x hx
      rw [(hasDerivAt_sig x (by linarith [hx.1, hS])).deriv]
      have hx0 : x < 0 := hx.2
      have hxS : S < x := hx.1
      have hx1 : (0 : ℝ) < x + 1 := by linarith
      have hx2 : (0 : ℝ) < 2 * (2 + x) := by
        have : (0 : ℝ) < 2 + x := by linarith
        positivity
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx0.le hx1.le) hx2.le
    have h := (convex_Icc S 0).image_sub_le_mul_sub_of_deriv_le
      hdiff.continuousOn (hdiff.mono interior_subset) hle S (Set.left_mem_Icc.mpr h0) 0
      (Set.right_mem_Icc.mpr h0) h0
    rw [hσ0] at h
    simp only [σ, zero_mul] at h
    linarith

/-- Quadratic minorant of the surplus remainder: `S ^ 2 / 8 ≤ slack S` for `S ≥ 0`. -/
private theorem sq_div_eight_le_slack {S : ℝ} (hS : 0 ≤ S) :
    S ^ 2 / 8 ≤ Real.log (2 + S) - Real.log 2 - S / 2 + S ^ 2 / 4 := by
  have hA := sub_sq_div_two_le_log_one_add (show (0 : ℝ) ≤ S / 2 by linarith)
  have hlog : Real.log (2 + S) - Real.log 2 = Real.log (1 + S / 2) := by
    have h2 : (2 : ℝ) + S ≠ 0 := by linarith
    rw [← Real.log_div h2 (by norm_num)]
    congr 1
    field_simp
  have hsq : (S / 2) ^ 2 / 2 = S ^ 2 / 8 := by ring
  rw [hlog]
  linarith

/-- Derivative of `t ↦ t ^ 2 / 2 + t ^ 3 / 3 / (1 - t) + log (1 - t) + t`. -/
private theorem hasDerivAt_psi (x : ℝ) (hx1 : x < 1) :
    HasDerivAt (fun t => t ^ 2 / 2 + t ^ 3 / 3 / (1 - t) + Real.log (1 - t) + t)
      (x ^ 3 / (3 * (1 - x) ^ 2)) x := by
  have hne : (1 : ℝ) - x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
    have h := (hasDerivAt_pow 2 x).div_const 2
    simpa using h
  have hnum : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (x ^ 2) x := by
    have h := (hasDerivAt_pow 3 x).div_const 3
    simpa using h
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    have h := (hasDerivAt_id' x).const_sub (1 : ℝ)
    simpa using h
  have hdiv := hnum.div hden hne
  have hlog : HasDerivAt (fun t => Real.log (1 - t)) ((1 - x)⁻¹ * -1) x := by
    have hcomp := (Real.hasDerivAt_log hne).comp x hden
    simpa [Function.comp_def] using hcomp
  have h := ((h1.add hdiv).add hlog).add (hasDerivAt_id x)
  have hval : x + (x ^ 2 * (1 - x) - x ^ 3 / 3 * -1) / (1 - x) ^ 2 + (1 - x)⁻¹ * -1 + 1
      = x ^ 3 / (3 * (1 - x) ^ 2) := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Cubic upper bound for `-log (1 - x) - x` on `[0, 1)`. -/
private theorem excess_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / 2 + x ^ 3 / 3 / (1 - x) := by
  let ψ : ℝ → ℝ := fun t => t ^ 2 / 2 + t ^ 3 / 3 / (1 - t) + Real.log (1 - t) + t
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hdiff : DifferentiableOn ℝ ψ (Set.Icc 0 x) := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    exact (hasDerivAt_psi t ht1).differentiableAt.differentiableWithinAt
  have hge : ∀ t ∈ interior (Set.Icc (0 : ℝ) x), (0 : ℝ) ≤ deriv ψ t := by
    rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_psi t (lt_of_lt_of_le ht.2 hx1.le)).deriv]
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : (0 : ℝ) < 1 - t := by linarith [lt_of_lt_of_le ht.2 hx1.le]
    exact div_nonneg (pow_nonneg ht0.le 3) (mul_nonneg (by norm_num) (sq_nonneg (1 - t)))
  have h := (convex_Icc (0 : ℝ) x).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuousOn (hdiff.mono interior_subset) hge 0 (Set.left_mem_Icc.mpr hx0) x
    (Set.right_mem_Icc.mpr hx0) hx0
  rw [hψ0] at h
  simp only [ψ, zero_mul] at h
  linarith

/-- Per-prime excess of `log (p / (p - 1))` over `1 / p`. -/
private theorem log_div_sub_one_sub_inv_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)
      ≤ 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have h1p : (1 : ℝ) / p < 1 := (div_lt_one hp0).mpr hp1
  have h := excess_le (show (0 : ℝ) ≤ 1 / p by positivity) h1p
  have hlog : -Real.log (1 - 1 / (p : ℝ)) = Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpm : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := hp1
      linarith
    have heq : (1 : ℝ) - 1 / p = ((p : ℝ) - 1) / p := by field_simp
    rw [heq, ← Real.log_inv]
    congr 1
    field_simp
  have hrhs : (1 / (p : ℝ)) ^ 2 / 2 + (1 / (p : ℝ)) ^ 3 / 3 / (1 - 1 / (p : ℝ))
      = 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1))) := by
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith [hp1]
    field_simp
  rw [hlog, hrhs] at h
  linarith [h]

/-- Weierstrass product inequality: `1 + ∑ x ≤ ∏ (1 + x)` for nonnegative `x`. -/
private theorem one_add_sum_le_prod (s : Finset ℕ) (x : ℕ → ℝ) :
    (∀ i ∈ s, 0 ≤ x i) → 1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction with
  | empty => intro; simp
  | insert a s has ih =>
    intro hx
    have hx' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have ha : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx'
    have h1 : (0 : ℝ) ≤ 1 + x a := by linarith
    have h2 : (0 : ℝ) ≤ ∏ i ∈ s, (1 + x i) - (1 + ∑ i ∈ s, x i) := by
      linarith [ih hx']
    have h3 : (0 : ℝ) ≤ x a * ∑ i ∈ s, x i := mul_nonneg ha hsum
    rw [Finset.sum_insert has, Finset.prod_insert has]
    nlinarith [mul_nonneg h1 h2, h3]

/-- The product formula for `H(n)`: `abundancySup n`, coerced to `ℝ`, is the real product
of `p / (p - 1)` over the prime factors `p` of `n`. -/
private theorem abundancySup_cast (n : ℕ) :
    ((abundancySup n : ℚ) : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  unfold abundancySup
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _
  push_cast
  ring_nf

/-- Each factor `p / (p - 1)` is at least one for `p ≥ 2`. -/
private theorem one_le_div_sub_one {p : ℝ} (hp : 2 ≤ p) : 1 ≤ p / (p - 1) := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  rw [le_div_iff₀ hp1]
  linarith

/-- The product `H(n)` is at least one. -/
private theorem one_le_abundancySup (n : ℕ) :
    1 ≤ ((abundancySup n : ℚ) : ℝ) := by
  rw [abundancySup_cast]
  apply Finset.one_le_prod₀
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  exact one_le_div_sub_one hp2

/-- Per-prime excess bounded by half the square of `1 / (p - 1)`. -/
private theorem log_div_sub_one_sub_inv_le_sq {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ) ≤ (1 / ((p : ℝ) - 1)) ^ 2 / 2 := by
  have h := log_div_sub_one_sub_inv_le hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hle : 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1)))
      ≤ (1 / ((p : ℝ) - 1)) ^ 2 / 2 := by
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpm0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have e1 : 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1)))
        = (3 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
      field_simp
      ring
    have e2 : (1 / ((p : ℝ) - 1)) ^ 2 / 2 = 1 / (2 * ((p : ℝ) - 1) ^ 2) := by
      field_simp
    have d1 : (0 : ℝ) < 6 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) :=
      mul_pos (mul_pos (by norm_num) (pow_pos hp0 2)) hpm0
    have d2 : (0 : ℝ) < 2 * ((p : ℝ) - 1) ^ 2 :=
      mul_pos (by norm_num) (pow_pos hpm0 2)
    have h41 : (0 : ℝ) < 4 * (p : ℝ) - 1 := by linarith
    rw [e1, e2, div_le_div_iff₀ d1 d2]
    nlinarith [mul_nonneg hpm0.le h41.le]
  linarith [h, hle]

/-- The excess bound at `p = 2` from Zelinsky's `25 / 32` lemma. -/
private theorem log_two_sub_half_le : Real.log 2 - 1 / (2 : ℝ) ≤ 25 / 128 := by
  have h := log_one_add_one_div_sub_one_le 2 (by norm_num)
  norm_num at h
  linarith [h]

/-- Excess estimate when `2` divides `n`: the odd part is controlled by the surplus. -/
private theorem excess_le_of_mem_two {n : ℕ} (hmem : 2 ∈ n.primeFactors) :
    ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ 25 / 128 + (Real.log ((abundancySup n : ℚ) : ℝ) - Real.log 2
        - (((abundancySup n : ℚ) : ℝ) - 2) / 2
        + (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 4) := by
  classical
  set O := n.primeFactors.erase 2 with hOdef
  have hmem' := Nat.mem_primeFactors.mp hmem
  have hn0 : n ≠ 0 := hmem'.2.2
  have hprime : ∀ p ∈ O, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have h2ge : ∀ p ∈ O, 2 ≤ (p : ℝ) :=
    fun p hp => by exact_mod_cast (hprime p hp).two_le
  have hx_nonneg : ∀ p ∈ O, (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) :=
    fun p hp => by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith [h2ge p hp]
      positivity
  rw [← Finset.add_sum_erase _ _ hmem]
  have he2 : Real.log (((2 : ℕ) : ℝ) / ((((2 : ℕ) : ℝ)) - 1)) - 1 / (((2 : ℕ) : ℝ))
      ≤ 25 / 128 := by
    norm_num
    linarith [log_two_sub_half_le]
  have hsum : ∑ p ∈ O, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ ∑ p ∈ O, (1 / ((p : ℝ) - 1)) ^ 2 / 2 := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    exact log_div_sub_one_sub_inv_le_sq hp2
  have hHO : ((abundancySup n : ℚ) : ℝ)
      = 2 * ∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) := by
    have h2 : (((2 : ℕ) : ℝ)) / ((((2 : ℕ) : ℝ)) - 1) = 2 := by norm_num
    rw [abundancySup_cast, ← Finset.mul_prod_erase _ _ hmem, hOdef, h2]
  have hHO1 : (1 : ℝ) ≤ ∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) := by
    apply Finset.one_le_prod₀
    intro p hp
    exact one_le_div_sub_one (h2ge p hp)
  have hfactor : ∀ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hpm : (p : ℝ) - 1 ≠ 0 := by
      have := h2ge p hp
      linarith
    field_simp
    ring
  have hW := one_add_sum_le_prod O (fun p => 1 / ((p : ℝ) - 1)) hx_nonneg
  rw [← Finset.prod_congr rfl hfactor] at hW
  have hsum_nonneg : (0 : ℝ) ≤ ∑ p ∈ O, 1 / ((p : ℝ) - 1) :=
    Finset.sum_nonneg hx_nonneg
  have hle : ∑ p ∈ O, 1 / ((p : ℝ) - 1)
      ≤ ∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) - 1 := by linarith [hW]
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hx_nonneg
  have hsq2 : (∑ p ∈ O, 1 / ((p : ℝ) - 1)) ^ 2
      ≤ (∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) - 1) ^ 2 :=
    pow_le_pow_left₀ hsum_nonneg hle 2
  have hdiv : ∑ p ∈ O, (1 / ((p : ℝ) - 1)) ^ 2 / 2
      = (∑ p ∈ O, (1 / ((p : ℝ) - 1)) ^ 2) / 2 := by
    rw [Finset.sum_div]
  have hS : ((abundancySup n : ℚ) : ℝ) - 2
      = 2 * (∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) - 1) := by
    rw [hHO]; ring
  have hS0 : (0 : ℝ) ≤ ((abundancySup n : ℚ) : ℝ) - 2 := by
    rw [hS]
    have := hHO1
    linarith
  have h8 := sq_div_eight_le_slack (S := ((abundancySup n : ℚ) : ℝ) - 2) hS0
  have h2S : 2 + (((abundancySup n : ℚ) : ℝ) - 2) = ((abundancySup n : ℚ) : ℝ) := by
    ring
  rw [h2S] at h8
  have hsq8 : (∑ p ∈ O, (1 / ((p : ℝ) - 1)) ^ 2) / 2
      ≤ (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 8 := by
    have hstar : (∑ p ∈ O, (1 / ((p : ℝ) - 1)) ^ 2)
        ≤ (∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) - 1) ^ 2 := le_trans hsq hsq2
    have h8eq : (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 8
        = (∏ p ∈ O, (p : ℝ) / ((p : ℝ) - 1) - 1) ^ 2 / 2 := by
      rw [hS]; ring
    rw [h8eq]
    linarith [hstar]
  rw [hdiv] at hsum
  linarith [hsum, hsq8, h8, he2]

/-- Prime factors of an odd number are odd. -/
private theorem odd_of_mem_primeFactors_of_odd {n p : ℕ} (hodd : Odd n)
    (hp : p ∈ n.primeFactors) : Odd p := by
  have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  rcases Nat.even_or_odd p with hev | hod
  · exfalso
    obtain ⟨r, hr⟩ := hev
    have h2p : 2 ∣ p := ⟨r, by omega⟩
    have h2n : 2 ∣ n := dvd_trans h2p hpdvd
    obtain ⟨k, hk⟩ := hodd
    omega
  · exact hod

/-- Excess estimate for odd `n` with least prime factor `3`. -/
private theorem excess_le_of_minFac_eq_three {n : ℕ} (hodd : Odd n) (hmf : n.minFac = 3) :
    ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ 25 / 192 + (Real.log ((abundancySup n : ℚ) : ℝ) - Real.log 2
        - (((abundancySup n : ℚ) : ℝ) - 2) / 2
        + (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 4) := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.minFac_zero] at hmf
    norm_num at hmf
  have h3mem : 3 ∈ n.primeFactors := by
    have hdvd : 3 ∣ n := by rw [← hmf]; exact Nat.minFac_dvd n
    exact Nat.Prime.mem_primeFactors (p := 3) (by decide) hdvd hn0
  set P' := n.primeFactors.erase 3 with hP'def
  have hprime : ∀ p ∈ P', p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hpodd : ∀ p ∈ P', Odd p :=
    fun p hp => odd_of_mem_primeFactors_of_odd hodd (Finset.mem_of_mem_erase hp)
  have hp5 : ∀ p ∈ P', 5 ≤ p := by
    intro p hp
    have hp2 := (hprime p hp).two_le
    have hne2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpodd 2 hp
      omega
    have hne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
    obtain ⟨k, hk⟩ := hpodd p hp
    omega
  have hx_nonneg : ∀ p ∈ P', (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) :=
    fun p hp => by
      have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5 p hp
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
  rw [← Finset.add_sum_erase _ _ h3mem, ← hP'def]
  have he3 : Real.log ((((3 : ℕ) : ℝ)) / ((((3 : ℕ) : ℝ)) - 1)) - 1 / (((3 : ℕ) : ℝ))
      ≤ 1 / 12 := by
    have h := log_div_sub_one_sub_inv_le (p := 3) (by norm_num)
    norm_num at h ⊢
    linarith [h]
  have hterm : ∀ p ∈ P', Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)
      ≤ 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have h := log_div_sub_one_sub_inv_le hp2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp2)
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by
      have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5 p hp
      linarith
    have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpm' : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm
    have e1 : 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1)))
        = (3 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
      field_simp
      ring
    have e3 : 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))
        = (3 * (p : ℝ)) / (6 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
      field_simp
      ring
    have dpos : (0 : ℝ) < 6 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) :=
      mul_pos (mul_pos (by norm_num) (pow_pos hp0 2)) hpm
    have hle : 1 / (p : ℝ) ^ 2 * (1 / 2 + 1 / (3 * ((p : ℝ) - 1)))
        ≤ 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
      rw [e1, e3, div_le_div_iff_of_pos_right dpos]
      linarith [hp0]
    linarith [h, hle]
  have hsum : ∑ p ∈ P', (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ (∑ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1))) / 2 := by
    have hle := Finset.sum_le_sum hterm
    have hterm2 : ∀ p ∈ P', 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))
        = (1 / ((p : ℝ) * ((p : ℝ) - 1))) / 2 := by
      intro p hp
      rw [div_div]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm2, ← Finset.sum_div] at hle
    exact hle
  have hH : ((abundancySup n : ℚ) : ℝ)
      = (3 / 2) * ∏ p ∈ P', (p : ℝ) / ((p : ℝ) - 1) := by
    have h3 : (((3 : ℕ) : ℝ)) / ((((3 : ℕ) : ℝ)) - 1) = 3 / 2 := by norm_num
    rw [abundancySup_cast, ← Finset.mul_prod_erase _ _ h3mem, hP'def, h3]
  have hU5 : ∑ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (∑ p ∈ P', 1 / ((p : ℝ) - 1)) / 5 := by
    have hterm5 : ∀ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (1 / ((p : ℝ) - 1)) / 5 := by
      intro p hp
      have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5 p hp
      have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have e : (1 / ((p : ℝ) - 1)) / 5 = 1 / (5 * ((p : ℝ) - 1)) := by
        rw [div_div]; congr 1; ring
      rw [e]
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [mul_nonneg (sub_nonneg.mpr hp5r) hpm.le]
    have hle := Finset.sum_le_sum hterm5
    rw [← Finset.sum_div] at hle
    exact hle
  have hW := one_add_sum_le_prod P' (fun p => 1 / ((p : ℝ) - 1)) hx_nonneg
  have hfactor : ∀ p ∈ P', (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5 p hp
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← Finset.prod_congr rfl hfactor] at hW
  have hHge : (1 : ℝ) + 5 * ∑ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∏ p ∈ P', (p : ℝ) / ((p : ℝ) - 1) := by
    linarith [hW, hU5]
  have hSge : (15 * ∑ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1))) / 2 - 1 / 2
      ≤ ((abundancySup n : ℚ) : ℝ) - 2 := by
    rw [hH]
    linarith [hHge]
  have hH1 : (1 : ℝ) ≤ ((abundancySup n : ℚ) : ℝ) := one_le_abundancySup n
  set U' := ∑ p ∈ P', 1 / ((p : ℝ) * ((p : ℝ) - 1)) with hU'def
  have hE : ∑ p ∈ P', (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)) ≤ U' / 2 := hsum
  have h2S : 2 + (((abundancySup n : ℚ) : ℝ) - 2) = ((abundancySup n : ℚ) : ℝ) := by
    ring
  rcases lt_or_ge U' (3 / 32) with hU | hU
  · have hslack := slack_nonneg (S := ((abundancySup n : ℚ) : ℝ) - 2) (by linarith [hH1])
    rw [h2S] at hslack
    linarith [hE, he3, hslack, hU]
  · have hApos : (0 : ℝ) < 15 * U' / 2 - 1 / 2 := by linarith [hU]
    have hS0 : (0 : ℝ) ≤ ((abundancySup n : ℚ) : ℝ) - 2 := by linarith [hSge, hApos]
    have h8 := sq_div_eight_le_slack (S := ((abundancySup n : ℚ) : ℝ) - 2) hS0
    rw [h2S] at h8
    have hA2 : (15 * U' / 2 - 1 / 2) ^ 2 / 8
        ≤ (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 8 := by
      have hsq := pow_le_pow_left₀ hApos.le hSge 2
      linarith [hsq]
    have hsos : U' / 2 - 3 / 64 - (15 * U' / 2 - 1 / 2) ^ 2 / 8 ≤ 0 := by
      nlinarith [sq_nonneg (U' - 23 / 225)]
    linarith [hE, he3, h8, hA2, hsos]

/-- Reciprocal squares over odd numbers are bounded by a telescoping sum. -/
private theorem odd_sq_sum_le {P : Finset ℕ} {m : ℕ} (hmpos : 0 < m) (hoddm : Odd m)
    (hmem : ∀ p ∈ P, m ≤ p) (hodd : ∀ p ∈ P, Odd p) :
    ∑ p ∈ P, 1 / (p : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 + 1 / (2 * (m : ℝ)) := by
  classical
  have hmposr : (0 : ℝ) < m := by exact_mod_cast hmpos
  by_cases hP : P = ∅
  · rw [hP, Finset.sum_empty]
    positivity
  · have hne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
    have hrep : ∀ p ∈ P, p = m + 2 * ((p - m) / 2) := by
      intro p hp
      obtain ⟨i, hi⟩ := Nat.Odd.sub_odd (hodd p hp) hoddm
      have hle := hmem p hp
      omega
    set N := P.sum id + 1 with hNdef
    have hbound : ∀ p ∈ P, (p - m) / 2 < N := by
      intro p hp
      have h1 : (p - m) / 2 ≤ p := by omega
      have h2 : p ≤ P.sum id := by
        have h := Finset.single_le_sum (s := P) (f := id) (a := p)
          (fun i _ => Nat.zero_le i) hp
        simpa using h
      omega
    have hinj : Set.InjOn (fun p => (p - m) / 2) (↑P : Set ℕ) := by
      intro x hx y hy hxy
      have hxP : x ∈ P := Finset.mem_coe.mp hx
      have hyP : y ∈ P := Finset.mem_coe.mp hy
      have hx2 := hrep x hxP
      have hy2 := hrep y hyP
      have hxy2 : (x - m) / 2 = (y - m) / 2 := hxy
      rw [hx2, hy2, hxy2]
    have himg : P.image (fun p => (p - m) / 2) ⊆ Finset.range N := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hbound p hp)
    have hcongr : ∀ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2
        = 1 / (((m : ℝ) + 2 * ((((p - m) / 2 : ℕ)) : ℝ)) ^ 2) := by
      intro p hp
      have hcast : (p : ℝ) = (m : ℝ) + 2 * ((((p - m) / 2 : ℕ)) : ℝ) := by
        have h3 : (p : ℝ) = ((m + 2 * ((p - m) / 2) : ℕ) : ℝ) := by
          exact_mod_cast hrep p hp
        rw [h3]
        norm_cast
      rw [hcast]
    have hterm : ∀ i : ℕ, 1 / (((m : ℝ) + 2 * ((i : ℝ) + 1)) ^ 2)
        ≤ (1 / 2) * ((1 / ((m : ℝ) + 2 * (i : ℝ)))
          - (1 / ((m : ℝ) + 2 * ((i : ℝ) + 1)))) := by
      intro i
      have hA : (0 : ℝ) < (m : ℝ) + 2 * (i : ℝ) := by positivity
      have hB : (0 : ℝ) < (m : ℝ) + 2 * ((i : ℝ) + 1) := by positivity
      have hAB : (m : ℝ) + 2 * (i : ℝ) ≤ (m : ℝ) + 2 * ((i : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (i : ℝ) := by positivity
        linarith
      have e : (1 / 2) * ((1 / ((m : ℝ) + 2 * (i : ℝ)))
          - (1 / ((m : ℝ) + 2 * ((i : ℝ) + 1))))
          = 1 / (((m : ℝ) + 2 * (i : ℝ)) * ((m : ℝ) + 2 * ((i : ℝ) + 1))) := by
        field_simp
        ring
      rw [e]
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hAB)]
    have htail : ∀ Nn : ℕ, 1 ≤ Nn →
        ∑ i ∈ Finset.range Nn, 1 / (((m : ℝ) + 2 * (i : ℝ)) ^ 2)
          ≤ 1 / (m : ℝ) ^ 2 + 1 / (2 * (m : ℝ)) := by
      intro Nn hNn
      obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nn ≠ 0)
      rw [Finset.sum_range_succ']
      have h0 : (1 : ℝ) / (((m : ℝ) + 2 * (((0 : ℕ) : ℝ))) ^ 2) = 1 / (m : ℝ) ^ 2 := by
        norm_num
      rw [h0]
      have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N') => hterm i)
      have hsumhalf : ∑ i ∈ Finset.range N', (1 / 2) * ((1 / ((m : ℝ) + 2 * (i : ℝ)))
          - (1 / ((m : ℝ) + 2 * ((i : ℝ) + 1))))
          = (1 / 2) * ((1 / (m : ℝ)) - (1 / ((m : ℝ) + 2 * ((N' : ℕ) : ℝ)))) := by
        have htel := Finset.sum_range_sub' (fun i => 1 / ((m : ℝ) + 2 * (i : ℝ))) N'
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero] at htel
        rw [← Finset.mul_sum, htel]
      have hfn : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2 * ((N' : ℕ) : ℝ)) := by positivity
      rw [hsumhalf] at hle
      have hfin : (1 / 2) * ((1 / (m : ℝ)) - (1 / ((m : ℝ) + 2 * ((N' : ℕ) : ℝ))))
          ≤ 1 / (2 * (m : ℝ)) := by
        have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmposr
        field_simp
        linarith [hfn, hmposr, mul_nonneg hfn hmposr.le]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hle, hfin]
    calc ∑ p ∈ P, 1 / (p : ℝ) ^ 2
        = ∑ p ∈ P, 1 / (((m : ℝ) + 2 * ((((p - m) / 2 : ℕ)) : ℝ)) ^ 2) :=
          Finset.sum_congr rfl hcongr
      _ = ∑ i ∈ P.image (fun p => (p - m) / 2),
            1 / (((m : ℝ) + 2 * ((i : ℝ))) ^ 2) :=
          (Finset.sum_image (s := P) (g := fun p => (p - m) / 2)
            (f := fun (i : ℕ) => 1 / (((m : ℝ) + 2 * ((i : ℝ))) ^ 2)) hinj).symm
      _ ≤ ∑ i ∈ Finset.range N, 1 / (((m : ℝ) + 2 * ((i : ℝ))) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => by positivity)
      _ ≤ 1 / (m : ℝ) ^ 2 + 1 / (2 * (m : ℝ)) := htail N (by omega)

/-- Excess estimate for odd `n` with least prime factor at least `5`. -/
private theorem excess_le_of_minFac_ge_five {n : ℕ} (hodd : Odd n) (hn2 : 2 ≤ n)
    (hmf : 5 ≤ n.minFac) :
    ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ 25 / (64 * (n.minFac : ℝ)) + (Real.log ((abundancySup n : ℚ) : ℝ) - Real.log 2
        - (((abundancySup n : ℚ) : ℝ) - 2) / 2
        + (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 4) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hminmem : n.minFac ∈ n.primeFactors :=
    Nat.Prime.mem_primeFactors (Nat.minFac_prime hn1) (Nat.minFac_dvd n) hn0
  have hmodd : Odd n.minFac := odd_of_mem_primeFactors_of_odd hodd hminmem
  have hprime : ∀ p ∈ n.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpodd : ∀ p ∈ n.primeFactors, Odd p :=
    fun p hp => odd_of_mem_primeFactors_of_odd hodd hp
  have hge : ∀ p ∈ n.primeFactors, n.minFac ≤ p := by
    intro p hp
    have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    exact Nat.minFac_le_of_dvd (hprime p hp).two_le hpdvd
  have hH1 : (1 : ℝ) ≤ ((abundancySup n : ℚ) : ℝ) := one_le_abundancySup n
  have hslack : 0 ≤ Real.log ((abundancySup n : ℚ) : ℝ) - Real.log 2
      - (((abundancySup n : ℚ) : ℝ) - 2) / 2
      + (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 4 := by
    have h := slack_nonneg (S := ((abundancySup n : ℚ) : ℝ) - 2) (by linarith [hH1])
    have h2S : 2 + (((abundancySup n : ℚ) : ℝ) - 2) = ((abundancySup n : ℚ) : ℝ) := by
      ring
    rw [h2S] at h
    exact h
  have hcoeff : ∀ p ∈ n.primeFactors, Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)
      ≤ (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1))) * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have h := log_div_sub_one_sub_inv_le hp2
    have hpm : n.minFac ≤ p := hge p hp
    have hm5 : (5 : ℝ) ≤ n.minFac := by exact_mod_cast hmf
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast le_trans hmf hpm
    have hpm0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hmm0 : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
    have hle1 : (1 : ℝ) / (3 * ((p : ℝ) - 1)) ≤ 1 / (3 * ((n.minFac : ℝ) - 1)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hcast : (n.minFac : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpm
        linarith
    have hpos : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
    have h3 : (1 / (p : ℝ) ^ 2) * (1 / 2 + 1 / (3 * ((p : ℝ) - 1)))
        ≤ (1 / (p : ℝ) ^ 2) * (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith [hle1]) hpos
    have hring : (1 / (p : ℝ) ^ 2) * (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1)))
        = (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1))) * (1 / (p : ℝ) ^ 2) := by ring
    rw [hring] at h3
    linarith [h, h3]
  have hE : ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1)))
        * ∑ p ∈ n.primeFactors, 1 / (p : ℝ) ^ 2 := by
    have hle := Finset.sum_le_sum hcoeff
    rw [← Finset.mul_sum] at hle
    exact hle
  obtain ⟨k, hk⟩ := hmodd
  have hsplit : n.minFac = 5 ∨ 7 ≤ n.minFac := by omega
  rcases hsplit with h5 | h7
  · have hQsplit : ∑ p ∈ n.primeFactors, 1 / (p : ℝ) ^ 2
        = ∑ p ∈ n.primeFactors.filter (· ≤ 5), 1 / (p : ℝ) ^ 2
          + ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5), 1 / (p : ℝ) ^ 2 := by
      have h := Finset.sum_filter_add_sum_filter_not n.primeFactors (· ≤ 5)
        (fun p => 1 / (p : ℝ) ^ 2)
      exact h.symm
    have hsmall : ∑ p ∈ n.primeFactors.filter (· ≤ 5), 1 / (p : ℝ) ^ 2 ≤ 1 / 25 := by
      have hsub : n.primeFactors.filter (· ≤ 5) ⊆ ({5} : Finset ℕ) := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        have h5le : 5 ≤ p := by
          have hle := hge p hp.1
          omega
        simp only [Finset.mem_singleton]
        omega
      calc ∑ p ∈ n.primeFactors.filter (· ≤ 5), 1 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ ({5} : Finset ℕ), 1 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ = 1 / 25 := by norm_num [Finset.sum_singleton]
    have hbig : ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5), 1 / (p : ℝ) ^ 2
        ≤ 1 / 49 + 1 / 14 := by
      have hmem7 : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5), 7 ≤ p := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        have hpgt : 6 ≤ p := by omega
        obtain ⟨j, hj⟩ := hpodd p hp.1
        omega
      have hoddf : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ 5), Odd p :=
        fun p hp => hpodd p (Finset.mem_of_mem_filter p hp)
      have h := odd_sq_sum_le (P := n.primeFactors.filter (fun p => ¬ p ≤ 5)) (m := 7)
        (by norm_num) ⟨3, rfl⟩ hmem7 hoddf
      norm_num at h ⊢
      linarith [h]
    have hQ : ∑ p ∈ n.primeFactors, 1 / (p : ℝ) ^ 2 ≤ 1 / 25 + 1 / 49 + 1 / 14 := by
      rw [hQsplit]
      linarith [hsmall, hbig]
    have hC5 : (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1))) = 7 / 12 := by
      rw [h5]
      norm_num
    have hnum : (7 / 12 : ℝ) * (1 / 25 + 1 / 49 + 1 / 14) ≤ 25 / 320 := by norm_num
    have hbud : (25 : ℝ) / (64 * (n.minFac : ℝ)) = 25 / 320 := by
      rw [h5]
      norm_num
    rw [hC5] at hE
    rw [hbud]
    have hE2 : ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
        ≤ (7 / 12) * (1 / 25 + 1 / 49 + 1 / 14) := by
      have hmul := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 7 / 12)
      linarith [hE, hmul]
    linarith [hE2, hnum, hslack]
  · have hQ := odd_sq_sum_le (P := n.primeFactors) (m := n.minFac) (by omega) ⟨k, hk⟩ hge
      hpodd
    have hm7 : (7 : ℝ) ≤ n.minFac := by exact_mod_cast h7
    have hmpos : (0 : ℝ) < n.minFac := by linarith
    have hmm : (0 : ℝ) < (n.minFac : ℝ) - 1 := by linarith
    have hCnn : (0 : ℝ) ≤ 1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1)) := by positivity
    have hE2 : ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
        ≤ (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1)))
          * (1 / (n.minFac : ℝ) ^ 2 + 1 / (2 * (n.minFac : ℝ))) := by
      have hmul := mul_le_mul_of_nonneg_left hQ hCnn
      linarith [hE, hmul]
    have hCbound : (1 / 2 + 1 / (3 * ((n.minFac : ℝ) - 1)))
          * (1 / (n.minFac : ℝ) ^ 2 + 1 / (2 * (n.minFac : ℝ)))
          ≤ 25 / (64 * (n.minFac : ℝ)) := by
      have eC : (1 / 2 : ℝ) + 1 / (3 * ((n.minFac : ℝ) - 1))
          = (3 * (n.minFac : ℝ) - 1) / (6 * ((n.minFac : ℝ) - 1)) := by
        field_simp
        ring
      have eQ : (1 / (n.minFac : ℝ) ^ 2) + (1 / (2 * (n.minFac : ℝ)))
          = ((n.minFac : ℝ) + 2) / (2 * (n.minFac : ℝ) ^ 2) := by
        field_simp
        ring
      have d1 : (0 : ℝ) < 6 * ((n.minFac : ℝ) - 1) * (2 * (n.minFac : ℝ) ^ 2) :=
        mul_pos (mul_pos (by norm_num) hmm) (mul_pos (by norm_num) (pow_pos hmpos 2))
      have d2 : (0 : ℝ) < 64 * (n.minFac : ℝ) := by positivity
      rw [eC, eQ, div_mul_div_comm, div_le_div_iff₀ d1 d2]
      nlinarith [sq_nonneg ((n.minFac : ℝ) - 7), hm7, hmpos]
    linarith [hE2, hCbound, hslack]

/-- **Lower bound on the prime reciprocal sum of a primitive non-deficient number.** Let $n$ be a
primitive non-deficient number with least prime factor $p_1$, let $T(n) = \sum_{p \mid n} 1/p$
and $H(n) = \prod_{p \mid n} p/(p-1)$, with the sum and product over the primes $p$ dividing $n$,
and let $S = H(n) - 2$ be the surplus of $n$. Then
$T(n) \ge \log 2 - \frac{25}{64 p_1} + \frac{S}{2} - \frac{S^2}{4}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 3 (`integers-2025-A59-prop-3`). -/
public theorem primitiveNondeficient_primeReciprocalSum_ge
    (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    Real.log 2 - 25 / (64 * (n.minFac : ℝ)) + ((abundancySup n : ℝ) - 2) / 2 -
        ((abundancySup n : ℝ) - 2) ^ 2 / 4 ≤
      ∑ p ∈ n.primeFactors, (1 : ℝ) / p := by
  classical
  have hne : ∀ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) ≠ 0 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      linarith
    exact ne_of_gt (div_pos hp0 hp1)
  have hlogH : Real.log ((abundancySup n : ℚ) : ℝ)
      = ∑ p ∈ n.primeFactors, (1 : ℝ) / p
        + ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)) := by
    rw [abundancySup_cast, Real.log_prod hne, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  suffices hE : ∑ p ∈ n.primeFactors, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ))
      ≤ 25 / (64 * (n.minFac : ℝ)) + (Real.log ((abundancySup n : ℚ) : ℝ) - Real.log 2
        - (((abundancySup n : ℚ) : ℝ) - 2) / 2
        + (((abundancySup n : ℚ) : ℝ) - 2) ^ 2 / 4) by
    linarith [hlogH, hE]
  by_cases hn0 : n = 0
  · subst hn0
    rw [Nat.primeFactors_zero, Finset.sum_empty]
    have hH : ((abundancySup 0 : ℚ) : ℝ) = 1 := by
      rw [abundancySup_cast, Nat.primeFactors_zero, Finset.prod_empty]
    rw [hH, Nat.minFac_zero]
    norm_num [Real.log_one]
    have h2 := log_one_add_one_div_sub_one_le 2 (by norm_num)
    norm_num at h2
    linarith [h2]
  · by_cases hn1 : n = 1
    · subst hn1
      rw [Nat.primeFactors_one, Finset.sum_empty]
      have hH : ((abundancySup 1 : ℚ) : ℝ) = 1 := by
        rw [abundancySup_cast, Nat.primeFactors_one, Finset.prod_empty]
      rw [hH, Nat.minFac_one]
      norm_num [Real.log_one]
      have h2 := log_one_add_one_div_sub_one_le 2 (by norm_num)
      norm_num at h2
      linarith [h2]
    · have hn2 : 2 ≤ n := by omega
      by_cases h2mem : 2 ∈ n.primeFactors
      · have hmf2 : n.minFac = 2 := (Nat.minFac_eq_two_iff n).2 (Nat.dvd_of_mem_primeFactors h2mem)
        have hE2 := excess_le_of_mem_two h2mem
        have hbud : (25 : ℝ) / (64 * (((2 : ℕ)) : ℝ)) = 25 / 128 := by norm_num
        rw [hmf2, hbud]
        exact hE2
      · have hodd : Odd n := by
          rcases Nat.even_or_odd n with hev | hod
          · exfalso
            obtain ⟨k, hk⟩ := hev
            have h2dvd : 2 ∣ n := ⟨k, by omega⟩
            have hmem : 2 ∈ n.primeFactors :=
              Nat.Prime.mem_primeFactors (p := 2) (by decide) h2dvd (by omega)
            exact h2mem hmem
          · exact hod
        have hminmem : n.minFac ∈ n.primeFactors :=
          Nat.Prime.mem_primeFactors (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
            (by omega)
        have hmodd : Odd n.minFac := odd_of_mem_primeFactors_of_odd hodd hminmem
        obtain ⟨k, hk⟩ := hmodd
        have hmf3 : 3 ≤ n.minFac := by
          have h2le := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
          omega
        rcases (by omega : n.minFac = 3 ∨ 5 ≤ n.minFac) with h3 | h5
        · have hE3 := excess_le_of_minFac_eq_three hodd h3
          have hbud : (25 : ℝ) / (64 * (((3 : ℕ)) : ℝ)) = 25 / 192 := by norm_num
          rw [h3, hbud]
          exact hE3
        · exact excess_le_of_minFac_ge_five hodd hn2 h5

end MetaMathlibExt
