/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import all MathlibExt.NumberTheory.Recurrences.FibonacciGeneratingFunctionValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer values of the Fibonacci generating function inside its radius of convergence

The radius is the positive fixed point of the map sending one consecutive-term ratio to the
next. This decreasing map alternates the ratios across the fixed point.

## References

* Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
  Fibonacci Polynomials*, The Fibonacci Quarterly 62(2) (2024), 157–172,
  Theorems 1.1 and 1.4 and Corollary 1.6.
* Andrew Bulawa and Whan Ki Lee, *Integer Values of Generating Functions for the Fibonacci and
  Related Sequences*, The Fibonacci Quarterly 55(1) (2017), 74–81, Theorem 1.1.
* Daniel S. Hong, *When Is the Generating Function of the Fibonacci Numbers an Integer?*,
  The College Mathematics Journal 46(2) (2015), 110–112, for the original Fibonacci question.
* Prapanpong Pongsriiam, *Integral Values of the Generating Functions of Fibonacci and Lucas
  Numbers*, The College Mathematics Journal 48(2) (2017), 97–101, for the independent result
  for the classical Fibonacci sequence.
-/

namespace MetaMathlibExt

open Polynomial fibonacciGenFun_eval_isInt_iff

local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

private lemma cast_ratio_succ {a b : ℕ} (ha : 0 < a) (i : ℕ) :
    (ratio a b (i + 1) : ℝ) = 1 / ((a : ℝ) + b * (ratio a b i : ℝ)) := by
  have hi : (F a b (i + 1) : ℝ) ≠ 0 := by exact_mod_cast (fib_pos ha i).ne'
  have hden : (a : ℝ) + b * ((F a b i : ℝ) / F a b (i + 1)) =
      (a * (F a b (i + 1) : ℝ) + b * (F a b i : ℝ)) / F a b (i + 1) := by
    field_simp
  simp only [ratio, Rat.cast_div, Rat.cast_intCast]
  rw [show i + 1 + 1 = i + 2 by rfl, fib_step, hden, one_div_div]
  push_cast
  rfl

private lemma cast_ratio_nonneg {a b : ℕ} (ha : 0 < a) (i : ℕ) :
    0 ≤ (ratio a b i : ℝ) := by
  cases i with
  | zero => simp [ratio, F]
  | succ i =>
    have hp : 0 < (F a b (i + 1) : ℚ) := by exact_mod_cast fib_pos ha i
    have hq : 0 < (F a b (i + 1 + 1) : ℚ) := by exact_mod_cast fib_pos ha (i + 1)
    exact_mod_cast (show 0 ≤ ratio a b (i + 1) from (div_pos hp hq).le)

/-- **Integer values of the generalized Fibonacci generating function in its interval of
convergence.** Let $a$ and $b$ be positive integers with $b \mid a$, and let
$F_i(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$, $F_1 = 1$ and
$F_{i+2} = ax\,F_{i+1} + b\,F_i$ for all $i \ge 0$. For a rational number $q$ with
$|q| < 2 / (a + \sqrt{a^2 + 4b})$, the radius of convergence of the power series of
$t / (1 - at - bt^2)$, the number $q / (1 - aq - bq^2)$ is an integer if and only if
$q = F_{2i}(1) / F_{2i+1}(1)$ for some $i \in \mathbb{N}$.

The source attributes this result (its Theorem 1.1) to Bulawa and Lee.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.6
(`fq-2024-tsuno05142024-cor-1.6`) and Theorem 1.1 (`fq-2024-tsuno05142024-thm-1.1`). -/
public theorem fibonacciGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ,
        q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) := by
  rw [fibonacciGenFun_eval_isInt_iff ha hb hba]
  change ((∃ i, q = ratio a b i) ∨ ∃ i : ℕ, 0 < i ∧ q = -(F a b (i + 1) : ℚ) / (b * F a b i)) ↔
    ∃ i, q = ratio a b (2 * i)
  let s := Real.sqrt ((a : ℝ) ^ 2 + 4 * b)
  let r : ℝ := 2 / (a + s)
  change |(q : ℝ)| < r at hq
  have ha₁ : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha' : (0 : ℝ) < a := by positivity
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hs₂ : s ^ 2 = (a : ℝ) ^ 2 + 4 * b := Real.sq_sqrt (by positivity)
  have hs : (a : ℝ) < s := by
    by_contra! h
    nlinarith only [hs₂, hb', mul_nonneg (sub_nonneg.mpr h) (add_nonneg ha'.le hs₀)]
  have hsum : 0 < (a : ℝ) + s := by positivity
  have hr : 0 < r := div_pos (by norm_num) hsum
  have hr₁ : r < 1 := (div_lt_iff₀ hsum).2 (by linarith)
  have hfixed : r = 1 / ((a : ℝ) + b * r) := by
    apply (eq_div_iff (by positivity)).2
    dsimp [r]
    field_simp [hsum.ne']
    nlinarith only [hs₂]
  have hden (i : ℕ) : 0 < (a : ℝ) + b * (ratio a b i : ℝ) :=
    add_pos_of_pos_of_nonneg ha' (mul_nonneg hb'.le (cast_ratio_nonneg ha i))
  -- Applying the ratio update switches sides of the fixed point.
  have hparity (i : ℕ) : if i % 2 = 0 then (ratio a b i : ℝ) < r else r < (ratio a b i : ℝ) := by
    induction i with
    | zero => simpa [ratio, F] using hr
    | succ i ih =>
      rw [cast_ratio_succ ha]
      by_cases hi : i % 2 = 0
      · rw [ite_eq_left hi] at ih
        rw [ite_eq_right (show (i + 1) % 2 ≠ 0 by omega), hfixed]
        exact one_div_lt_one_div_of_lt (hden i)
          (add_lt_add_right (mul_lt_mul_of_pos_left ih hb') _)
      · rw [ite_eq_right hi] at ih
        rw [ite_eq_left (show (i + 1) % 2 = 0 by omega), hfixed]
        exact one_div_lt_one_div_of_lt (by positivity)
          (add_lt_add_right (mul_lt_mul_of_pos_left ih hb') _)
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, hi, hqi⟩)
    · rw [abs_of_nonneg (cast_ratio_nonneg ha i)] at hq
      have hi : i % 2 = 0 := by
        by_contra! hi
        have hodd := hparity i
        rw [ite_eq_right hi] at hodd
        exact (not_lt_of_gt hodd) hq
      exact ⟨i / 2, congrArg (ratio a b) (by omega)⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      rw [← reflect_ratio] at hqi
      have ha_b : (b : ℝ) ≤ a := by exact_mod_cast Nat.le_of_dvd ha hba
      have hbound : (b : ℝ) * (ratio a b (i + 1) : ℝ) ≤ 1 := by
        rw [cast_ratio_succ ha, mul_one_div]
        exact (div_le_one (hden i)).2
          (ha_b.trans (le_add_of_nonneg_right (mul_nonneg hb'.le (cast_ratio_nonneg ha i))))
      have hp : 0 < (b : ℝ) * (ratio a b (i + 1) : ℝ) := by
        rw [cast_ratio_succ ha]
        exact mul_pos hb' (one_div_pos.mpr (hden i))
      have hlarge : (1 : ℝ) ≤ |(q : ℝ)| := by
        rw [hqi, reflect]
        push_cast
        rw [neg_div, abs_neg, abs_of_nonneg (one_div_pos.mpr hp).le]
        exact (le_div_iff₀ hp).2 (by simpa using hbound)
      exact ((not_lt_of_ge hlarge) (hq.trans hr₁)).elim
  · rintro ⟨i, hi⟩
    exact Or.inl ⟨2 * i, hi⟩

end MetaMathlibExt
