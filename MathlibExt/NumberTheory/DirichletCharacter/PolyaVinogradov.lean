/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.NumberTheory.DirichletCharacter.GaussSum

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Pólya–Vinogradov inequality

Let `χ` be a nontrivial Dirichlet character modulo `q`. The **Pólya–Vinogradov inequality**
states that every character sum over an interval satisfies

`|∑_{a ≤ n < b} χ n| ≪ √q log q`,

with an absolute implied constant. For primitive `χ` we expand `χ` in additive characters
using the Gauss sum `τ(χ̄)` (whose absolute value is `√q`), and bound the resulting geometric
sums by cosecants. A nontrivial character is induced by a primitive character of conductor
`f ∣ q`, and sieving out the primes dividing `q` but not `f` transfers the bound.

## Main statements

* `Complex.norm_sum_Ico_exp_mul_I_le`: `‖∑_{a ≤ n < b} e^{2 i θ n}‖ ≤ 1 / |sin θ|`.
* `DirichletCharacter.norm_sum_Ico_stdAddChar_mul_le`: the additive-character version.
* `DirichletCharacter.IsPrimitive.norm_sum_Ico_le`: for primitive `χ ≠ 1`,
  `‖∑_{a ≤ n < b} χ n‖ ≤ √q (1 + log q)`.
* `DirichletCharacter.norm_sum_Icc_le`: for every `χ ≠ 1`,
  `‖∑_{1 ≤ n ≤ N} χ n‖ ≤ 2 √q (1 + log q)`.
* `DirichletCharacter.norm_sum_Ico_le_sqrt_mul_one_add_log`: for every `χ ≠ 1`,
  `‖∑_{a ≤ n < b} χ n‖ ≤ 4 √q (1 + log q)`.
* `DirichletCharacter.norm_sum_Ico_le_sqrt_mul_log`: the classical form
  `‖∑_{a ≤ n < b} χ n‖ ≤ 10 √q log q`.
-/

@[expose] public section

open Finset Real

namespace Complex

/-- **Geometric sums of unimodular numbers are bounded by a cosecant.** If `sin θ ≠ 0`, then
`‖∑_{a ≤ n < b} e^{2 i θ n}‖ ≤ 1 / |sin θ|`. -/
theorem norm_sum_Ico_exp_mul_I_le {θ : ℝ} (hθ : Real.sin θ ≠ 0) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, exp (2 * θ * n * I)‖ ≤ 1 / |Real.sin θ| := by
  have hzpow : ∀ n : ℕ, exp (2 * θ * n * I) = (exp (θ * I) * exp (θ * I)) ^ n := by
    intro n
    rw [← exp_add, ← exp_nat_mul]
    congr 1
    ring
  have hwn : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hinv : exp (-(θ : ℂ) * I) * exp (θ * I) = 1 := by rw [← exp_add]; simp
  have hz1 : exp (θ * I) * exp (θ * I) - 1 = exp (θ * I) * (2 * I * (Real.sin θ : ℂ)) := by
    rw [ofReal_sin, sin]
    linear_combination hinv - exp (θ * I) * (exp (-(θ : ℂ) * I) - exp (θ * I)) * I_sq
  set w : ℂ := exp (θ * I)
  set z : ℂ := w * w
  have hzn : ‖z‖ = 1 := by rw [norm_mul, hwn, one_mul]
  have hz1n : ‖z - 1‖ = 2 * |Real.sin θ| := by
    rw [hz1, norm_mul, hwn, norm_mul, norm_mul, norm_I, norm_real]
    norm_num
  have hpos : 0 < 2 * |Real.sin θ| := by positivity
  have key : ‖∑ n ∈ Ico a b, exp (2 * θ * n * I)‖ * (2 * |Real.sin θ|) ≤ 2 := by
    simp_rw [hzpow]
    rcases le_total b a with hba | hab
    · rw [Ico_eq_empty_of_le hba, sum_empty, norm_zero, zero_mul]
      norm_num
    rw [← hz1n, ← norm_mul, geom_sum_Ico_mul _ hab]
    calc ‖z ^ b - z ^ a‖ ≤ ‖z ^ b‖ + ‖z ^ a‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hzn]; norm_num
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (∑ n ∈ Ico a b, exp (2 * θ * n * I))]

end Complex

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The additive character sums `∑_{a ≤ n < b} e(k n / q)` for `0 < k < q` are bounded by
`1 / sin (π k / q)`. -/
theorem norm_sum_Ico_stdAddChar_mul_le {k : ℕ} (hk0 : 0 < k) (hkq : k < q) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, ZMod.stdAddChar ((k : ZMod q) * (n : ZMod q))‖ ≤ 1 / Real.sin (π * k / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (hk0.trans hkq)
  have hkR : (k : ℝ) < q := by exact_mod_cast hkq
  have hk0R : (0 : ℝ) < k := by exact_mod_cast hk0
  have hsin : 0 < Real.sin (π * k / q) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_lt_of_lt_one_right pi_pos ((div_lt_one hq).2 hkR)
  have hrw : ∀ n : ℕ, ZMod.stdAddChar ((k : ZMod q) * (n : ZMod q)) =
      Complex.exp (2 * (π * k / q : ℝ) * n * Complex.I) := by
    intro n
    have : (k : ZMod q) * (n : ZMod q) = (((k * n : ℕ) : ℤ) : ZMod q) := by push_cast; ring
    rw [this, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp_rw [hrw]
  have h := Complex.norm_sum_Ico_exp_mul_I_le hsin.ne' a b
  rwa [abs_of_pos hsin] at h

/-- `2 t (1 - t) ≤ sin (π t)` for `0 ≤ t ≤ 1`. -/
private lemma two_mul_mul_one_sub_le_sin_pi_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * t * (1 - t) ≤ Real.sin (π * t) := by
  rcases le_total t (1 / 2) with h | h
  · have := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [pi_pos])
    have e : 2 / π * (π * t) = 2 * t := by field_simp
    nlinarith
  · have := Real.mul_le_sin (x := π * (1 - t)) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
    have e : 2 / π * (π * (1 - t)) = 2 * (1 - t) := by field_simp
    have e2 : Real.sin (π * (1 - t)) = Real.sin (π * t) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    nlinarith

omit [NeZero q] in
/-- The cosecant sum `∑_{0 < k < q} 1 / sin (π k / q)` is at most `q (1 + log q)`. -/
private lemma sum_inv_sin_le (hq : 1 < q) :
    ∑ k ∈ Ico 1 q, 1 / Real.sin (π * k / q) ≤ q * (1 + Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans hq)
  have hterm : ∀ k ∈ Ico 1 q,
      1 / Real.sin (π * k / q) ≤ q / 2 * (1 / (k : ℝ) + 1 / ((q : ℝ) - k)) := by
    intro k hk
    obtain ⟨hk1, hkq⟩ := mem_Ico.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkR : (k : ℝ) < q := by exact_mod_cast hkq
    set t : ℝ := k / q
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := (div_lt_one hqR).2 hkR
    have hs := two_mul_mul_one_sub_le_sin_pi_mul ht0.le ht1.le
    have hpos : 0 < 2 * t * (1 - t) := by have : 0 < 1 - t := by linarith
                                          positivity
    have harg : π * k / q = π * t := by rw [mul_div_assoc]
    rw [harg]
    calc 1 / Real.sin (π * t) ≤ 1 / (2 * t * (1 - t)) := one_div_le_one_div_of_le hpos hs
      _ = q / 2 * (1 / (k : ℝ) + 1 / ((q : ℝ) - k)) := by
        have : (q : ℝ) - k ≠ 0 := by linarith
        simp only [t]
        field_simp
        ring
  have hrefl : ∑ k ∈ Ico 1 q, 1 / ((q : ℝ) - k) = ∑ k ∈ Ico 1 q, 1 / (k : ℝ) := by
    refine sum_nbij' (fun k ↦ q - k) (fun k ↦ q - k) (fun k hk ↦ ?_) (fun k hk ↦ ?_)
      (fun k hk ↦ ?_) (fun k hk ↦ ?_) (fun k hk ↦ ?_)
    all_goals simp only [mem_Ico] at hk ⊢
    · omega
    · omega
    · omega
    · omega
    · rw [Nat.cast_sub hk.2.le]
  have hharm : ∑ k ∈ Ico 1 q, 1 / (k : ℝ) ≤ 1 + Real.log q := by
    calc ∑ k ∈ Ico 1 q, 1 / (k : ℝ) ≤ ∑ k ∈ Icc 1 q, 1 / (k : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (fun k hk ↦ by
            simp only [mem_Ico, mem_Icc] at hk ⊢; omega) fun _ _ _ ↦ by positivity
      _ = (harmonic q : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
      _ ≤ 1 + Real.log q := harmonic_le_one_add_log q
  calc ∑ k ∈ Ico 1 q, 1 / Real.sin (π * k / q)
      ≤ ∑ k ∈ Ico 1 q, q / 2 * (1 / (k : ℝ) + 1 / ((q : ℝ) - k)) := sum_le_sum hterm
    _ = q * ∑ k ∈ Ico 1 q, 1 / (k : ℝ) := by
        rw [← mul_sum, sum_add_distrib, hrefl]; ring
    _ ≤ q * (1 + Real.log q) := mul_le_mul_of_nonneg_left hharm hqR.le

/-- **The Pólya–Vinogradov inequality for primitive characters.** If `χ` is a primitive
nontrivial Dirichlet character modulo `q`, then every sum of `χ` over an interval satisfies
`‖∑_{a ≤ n < b} χ n‖ ≤ √q (1 + log q)`. -/
theorem IsPrimitive.norm_sum_Ico_le {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, χ n‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  have hq : 1 < q := by
    rcases Nat.lt_or_ge 1 q with h | h
    · exact h
    · exact absurd (level_one' χ (by have := NeZero.ne q; omega)) hχ1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans hq)
  set e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hprim' : (χ⁻¹).IsPrimitive := by
    rwa [IsPrimitive, conductor_inv]
  set τ := gaussSum χ⁻¹ e
  have hτ : ‖τ‖ = Real.sqrt q := norm_gaussSum_stdAddChar_of_isPrimitive hprim'
  -- Expansion of `χ` in additive characters.
  have hsep : ∀ n : ℕ, χ n * τ = ∑ m : ZMod q, χ⁻¹ m * e (m * (n : ZMod q)) := by
    intro n
    have h := gaussSum_mulShift_of_isPrimitive e hprim' (n : ZMod q)
    rw [inv_inv] at h
    rw [← h, gaussSum]
    exact sum_congr rfl fun m _ ↦ by rw [AddChar.mulShift_apply, mul_comm (n : ZMod q) m]
  have hS : (∑ n ∈ Ico a b, χ n) * τ =
      ∑ m : ZMod q, χ⁻¹ m * ∑ n ∈ Ico a b, e (m * (n : ZMod q)) := by
    rw [sum_mul]
    simp_rw [hsep, mul_sum]
    exact sum_comm
  -- Reindex the outer sum by `0 ≤ k < q`.
  have hreindex : ∀ F : ZMod q → ℝ, ∑ m : ZMod q, F m = ∑ k ∈ range q, F k := fun F ↦
    sum_nbij' (fun m ↦ m.val) (fun k ↦ (k : ZMod q)) (fun m _ ↦ by simpa using ZMod.val_lt m)
      (fun _ _ ↦ mem_univ _) (fun m _ ↦ by simp)
      (fun k hk ↦ ZMod.val_cast_of_lt (mem_range.1 hk)) (fun m _ ↦ by simp)
  have hmain : ‖∑ n ∈ Ico a b, χ n‖ * Real.sqrt q ≤ q * (1 + Real.log q) := by
    rw [← hτ, ← norm_mul, hS]
    calc ‖∑ m : ZMod q, χ⁻¹ m * ∑ n ∈ Ico a b, e (m * (n : ZMod q))‖
        ≤ ∑ m : ZMod q, ‖χ⁻¹ m‖ * ‖∑ n ∈ Ico a b, e (m * (n : ZMod q))‖ :=
          (norm_sum_le _ _).trans (le_of_eq (by simp_rw [norm_mul]))
      _ = ∑ k ∈ range q, ‖χ⁻¹ k‖ * ‖∑ n ∈ Ico a b, e ((k : ZMod q) * (n : ZMod q))‖ := hreindex _
      _ = ∑ k ∈ Ico 1 q, ‖χ⁻¹ k‖ * ‖∑ n ∈ Ico a b, e ((k : ZMod q) * (n : ZMod q))‖ := by
          rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
          have h0 : χ⁻¹ ((0 : ℕ) : ZMod q) = 0 := by
            exact MulChar.map_nonunit _ (by
              rw [ZMod.isUnit_iff_coprime]; simp only [Nat.coprime_zero_left]; omega)
          rw [h0, norm_zero, zero_mul, zero_add]
      _ ≤ ∑ k ∈ Ico 1 q, 1 / Real.sin (π * k / q) := by
          refine sum_le_sum fun k hk ↦ ?_
          obtain ⟨hk1, hkq⟩ := mem_Ico.1 hk
          calc ‖χ⁻¹ k‖ * ‖∑ n ∈ Ico a b, e ((k : ZMod q) * (n : ZMod q))‖
              ≤ 1 * (1 / Real.sin (π * k / q)) :=
                mul_le_mul (norm_le_one _ _) (norm_sum_Ico_stdAddChar_mul_le hk1 hkq a b)
                  (norm_nonneg _) zero_le_one
            _ = 1 / Real.sin (π * k / q) := one_mul _
      _ ≤ q * (1 + Real.log q) := sum_inv_sin_le hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hqR
  have hsqsq : (q : ℝ) * (1 + Real.log q) = Real.sqrt q * (1 + Real.log q) * Real.sqrt q := by
    rw [mul_right_comm, Real.mul_self_sqrt hqR.le]
  rw [hsqsq] at hmain
  exact le_of_mul_le_mul_right hmain hsq

/-- Removing the integers divisible by a finite set `Q` of primes from a sum of a Dirichlet
character `ψ` over `[1, N]` multiplies a uniform bound `B` on such sums by at most `2 ^ #Q`. -/
private lemma norm_sum_filter_coprime_le {f : ℕ} (ψ : DirichletCharacter ℂ f) {B : ℝ}
    (hB : ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, ψ n‖ ≤ B) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (N : ℕ) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n ↦ ∀ p ∈ Q, ¬ p ∣ n), ψ n‖ ≤ 2 ^ Q.card * B := by
  classical
  induction Q using Finset.induction_on generalizing N with
  | empty => simpa using hB N
  | insert p Q hpQ ih =>
    have hp : p.Prime := hQ p (mem_insert_self _ _)
    have ihQ := ih (fun r hr ↦ hQ r (mem_insert_of_mem hr))
    have hsplit : ∑ n ∈ (Icc 1 N).filter (fun n ↦ ∀ r ∈ insert p Q, ¬ r ∣ n), ψ n =
        ∑ n ∈ (Icc 1 N).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n), ψ n -
        ψ p * ∑ n ∈ (Icc 1 (N / p)).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n), ψ n := by
      rw [← sum_filter_add_sum_filter_not ((Icc 1 N).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n))
        (fun n ↦ p ∣ n)]
      have himg : ((Icc 1 N).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n)).filter (fun n ↦ p ∣ n) =
          ((Icc 1 (N / p)).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n)).image (p * ·) := by
        ext n
        simp only [mem_filter, mem_Icc, mem_image]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨c, rfl⟩⟩
          refine ⟨c, ⟨⟨?_, ?_⟩, fun r hr hrc ↦ h3 r hr (hrc.mul_left p)⟩, rfl⟩
          · rcases Nat.eq_zero_or_pos c with hc | hc
            · subst hc; omega
            · exact hc
          · rw [Nat.le_div_iff_mul_le hp.pos]; linarith
        · rintro ⟨c, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
          refine ⟨⟨⟨?_, ?_⟩, fun r hr hrc ↦ ?_⟩, ⟨c, rfl⟩⟩
          · have := hp.pos; nlinarith
          · have := (Nat.le_div_iff_mul_le hp.pos).mp h2; linarith
          · have hr' : r.Prime := hQ r (mem_insert_of_mem hr)
            rcases (Nat.Prime.dvd_mul hr').mp hrc with h | h
            · have := (Nat.prime_dvd_prime_iff_eq hr' hp).mp h
              subst this; exact hpQ hr
            · exact h3 r hr h
      have hnot : ((Icc 1 N).filter (fun n ↦ ∀ r ∈ Q, ¬ r ∣ n)).filter (fun n ↦ ¬ p ∣ n) =
          (Icc 1 N).filter (fun n ↦ ∀ r ∈ insert p Q, ¬ r ∣ n) := by
        ext n
        simp only [mem_filter, mem_insert, forall_eq_or_imp]
        tauto
      rw [himg, hnot, sum_image (fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h), mul_sum]
      simp only [Nat.cast_mul, map_mul]
      ring
    rw [hsplit, card_insert_of_notMem hpQ, pow_succ]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := ihQ N
    have h3 := mul_le_mul (norm_le_one ψ (p : ZMod f)) (ihQ (N / p)) (norm_nonneg _) zero_le_one
    linarith

/-- **The Pólya–Vinogradov inequality** for sums over `[1, N]`. For every nontrivial Dirichlet
character `χ` modulo `q`, `‖∑_{1 ≤ n ≤ N} χ n‖ ≤ 2 √q (1 + log q)`. -/
theorem norm_sum_Icc_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ n‖ ≤ 2 * Real.sqrt q * (1 + Real.log q) := by
  classical
  set f := χ.conductor
  set ψ := χ.primitiveCharacter
  have hf0 : f ≠ 0 := χ.conductor_ne_zero
  have hf1 : f ≠ 1 := fun h ↦ hχ (eq_one_iff_conductor_eq_one.mpr h)
  have hfq : f ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast (by omega : 1 ≤ f)
  have : NeZero f := ⟨hf0⟩
  have hψ1 : ψ ≠ 1 := by
    intro h
    have hc : ψ.conductor = f := χ.primitiveCharacter_isPrimitive
    rw [h, conductor_one] at hc
    exact hf1 hc.symm
  set B := Real.sqrt f * (1 + Real.log f)
  have hψB : ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, ψ n‖ ≤ B := by
    intro N
    have hI : Icc 1 N = Ico 1 (N + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
    exact χ.primitiveCharacter_isPrimitive.norm_sum_Ico_le hψ1 _ _
  -- The primes of `q` that do not divide `f`.
  set P := q.primeFactors.filter (fun p ↦ ¬ p ∣ f)
  have hPp : ∀ p ∈ P, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have hrel : ∀ n : ℕ, χ n = if (∀ p ∈ P, ¬ p ∣ n) then ψ n else 0 := by
    intro n
    by_cases hc : Nat.Coprime n q
    · have hP' : ∀ p ∈ P, ¬ p ∣ n := by
        intro p hp hpn
        have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1
        exact (hPp p hp).one_lt.ne'
          (Nat.dvd_one.mp (by rw [← hc.gcd_eq_one]; exact Nat.dvd_gcd hpn hpq))
      rw [ite_eq_left_of_eq_true _ _ (eq_true hP')]
      have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
        (Nat.isCoprime_iff_coprime.mpr hc)
      simpa using this.symm
    · have h0 : χ n = 0 := by
        have := (χ.apply_eq_zero_iff (n : ℤ)).mpr (by rwa [Nat.isCoprime_iff_coprime])
        simpa using this
      rw [h0]
      split_ifs with hP'
      · symm
        have hnc : ¬ IsCoprime (n : ℤ) (f : ℤ) := by
          rw [Nat.isCoprime_iff_coprime]
          intro hcf
          obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (hc : Nat.gcd n q ≠ 1)
          have hpn := hpd.trans (Nat.gcd_dvd_left n q)
          have hpq := hpd.trans (Nat.gcd_dvd_right n q)
          have hpf : ¬ p ∣ f := fun h ↦ hp.one_lt.ne'
            (Nat.dvd_one.mp (by rw [← hcf.gcd_eq_one]; exact Nat.dvd_gcd hpn h))
          exact hP' p (by simp [P, hp, hpq, hq0, hpf]) hpn
        have := (ψ.apply_eq_zero_iff (n : ℤ)).mpr hnc
        simpa using this
      · rfl
  have hS : ∑ n ∈ Icc 1 N, χ n = ∑ n ∈ (Icc 1 N).filter (fun n ↦ ∀ p ∈ P, ¬ p ∣ n), ψ n := by
    rw [sum_congr rfl (fun n _ ↦ hrel n), ← sum_filter]
  -- `2 ^ #P √f ≤ 2 √q`, since `∏_{p ∈ P} p * f ∣ q` and `4 ^ #P ≤ 4 ∏_{p ∈ P} p`.
  have hprod : (∏ p ∈ P, p) * f ∣ q := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_
      (prod_primes_dvd q (fun p hp ↦ (hPp p hp).prime)
        (fun p hp ↦ Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)) hfq
    exact Nat.Coprime.prod_left fun p hp ↦
      ((hPp p hp).coprime_iff_not_dvd).mpr (mem_filter.mp hp).2
  have h4 : 4 ^ P.card ≤ 4 * ∏ p ∈ P, p := by
    rw [← prod_filter_mul_prod_filter_not P (fun p ↦ p < 4),
      ← card_filter_add_card_filter_not (s := P) (fun p ↦ p < 4), pow_add]
    have hlo : 4 ^ (P.filter (fun p ↦ p < 4)).card ≤ 4 * ∏ p ∈ P.filter (fun p ↦ p < 4), p := by
      have hsub : P.filter (fun p ↦ p < 4) ∈ ({2, 3} : Finset ℕ).powerset := by
        rw [mem_powerset]
        intro p hp
        rw [mem_filter] at hp
        have h2 := (hPp p hp.1).two_le
        have h3 := hp.2
        interval_cases p <;> simp
      have key : ∀ A ∈ ({2, 3} : Finset ℕ).powerset, 4 ^ A.card ≤ 4 * ∏ p ∈ A, p := by
        decide
      exact key _ hsub
    have hhi : 4 ^ (P.filter (fun p ↦ ¬ p < 4)).card ≤ ∏ p ∈ P.filter (fun p ↦ ¬ p < 4), p :=
      pow_card_le_prod _ _ _ fun p hp ↦ by rw [mem_filter] at hp; omega
    calc _ ≤ (4 * ∏ p ∈ P.filter (fun p ↦ p < 4), p) * ∏ p ∈ P.filter (fun p ↦ ¬ p < 4), p :=
          Nat.mul_le_mul hlo hhi
      _ = _ := by ring
  have hN : (2 ^ P.card) ^ 2 * f ≤ 4 * q := by
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hprod
    calc (2 ^ P.card) ^ 2 * f = 4 ^ P.card * f := by
          rw [← pow_mul, mul_comm P.card 2, pow_mul]; norm_num
      _ ≤ 4 * (∏ p ∈ P, p) * f := Nat.mul_le_mul_right _ h4
      _ = 4 * ((∏ p ∈ P, p) * f) := by ring
      _ ≤ 4 * q := Nat.mul_le_mul_left _ hle
  have hR : ((2 : ℝ) ^ P.card) ^ 2 * f ≤ 4 * q := by exact_mod_cast hN
  have hsq : (2 : ℝ) ^ P.card * Real.sqrt f ≤ 2 * Real.sqrt q := by
    have := Real.sqrt_le_sqrt hR
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
      Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
    exact this
  have hlogf : Real.log f ≤ Real.log q :=
    Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hfq)
  have hlogf0 : 0 ≤ Real.log f := Real.log_nonneg hfR
  rw [hS]
  refine (norm_sum_filter_coprime_le ψ hψB P hPp N).trans ?_
  calc (2 : ℝ) ^ P.card * B = (1 + Real.log f) * ((2 : ℝ) ^ P.card * Real.sqrt f) := by ring
    _ ≤ (1 + Real.log q) * (2 * Real.sqrt q) :=
        mul_le_mul (by linarith) hsq (by positivity) (by linarith)
    _ = 2 * Real.sqrt q * (1 + Real.log q) := by ring

/-- **The Pólya–Vinogradov inequality.** For every nontrivial Dirichlet character `χ` modulo
`q`, every sum of `χ` over an interval satisfies
`‖∑_{a ≤ n < b} χ n‖ ≤ 4 √q (1 + log q)`. -/
theorem norm_sum_Ico_le_sqrt_mul_one_add_log {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (a b : ℕ) : ‖∑ n ∈ Ico a b, χ n‖ ≤ 4 * Real.sqrt q * (1 + Real.log q) := by
  have hq : 1 < q := by
    rcases Nat.lt_or_ge 1 q with h | h
    · exact h
    · exact absurd (level_one' χ (by have := NeZero.ne q; omega)) hχ
  have hB := norm_sum_Icc_le hχ
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  have hpos : 0 ≤ 2 * Real.sqrt q * (1 + Real.log q) :=
    mul_nonneg (by positivity) (by linarith)
  -- `∑_{1 ≤ n < b} χ n` is a sum over `[1, b - 1]`.
  have hIco : ∀ b : ℕ, ‖∑ n ∈ Ico 1 b, χ n‖ ≤ 2 * Real.sqrt q * (1 + Real.log q) := by
    intro b
    have : Ico 1 b = Icc 1 (b - 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [this]
    exact hB _
  rcases le_total b a with hba | hab
  · rw [Ico_eq_empty_of_le hba, sum_empty, norm_zero]
    linarith
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h0 : χ ((0 : ℕ) : ZMod q) = 0 := by
      exact MulChar.map_nonunit _ (by
        rw [ZMod.isUnit_iff_coprime]; simp only [Nat.coprime_zero_left]; omega)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp; linarith
    rw [sum_eq_sum_Ico_succ_bot hb, h0, zero_add]
    linarith [hIco b]
  · have h := sum_Ico_consecutive (fun n : ℕ ↦ χ n) ha hab
    have e : ∑ n ∈ Ico a b, χ n = ∑ n ∈ Ico 1 b, χ n - ∑ n ∈ Ico 1 a, χ n := by
      rw [← h]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith [hIco a, hIco b]

/-- **The Pólya–Vinogradov inequality**, classical form. For every nontrivial Dirichlet
character `χ` modulo `q`, `‖∑_{a ≤ n < b} χ n‖ ≤ 10 √q log q`. -/
theorem norm_sum_Ico_le_sqrt_mul_log {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, χ n‖ ≤ 10 * Real.sqrt q * Real.log q := by
  have hq : 1 < q := by
    rcases Nat.lt_or_ge 1 q with h | h
    · exact h
    · exact absurd (level_one' χ (by have := NeZero.ne q; omega)) hχ
  have hlog2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hl : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  refine (norm_sum_Ico_le_sqrt_mul_one_add_log hχ a b).trans ?_
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  nlinarith

end DirichletCharacter
