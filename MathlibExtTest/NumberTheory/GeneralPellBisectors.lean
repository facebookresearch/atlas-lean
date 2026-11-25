/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum.RealSqrt

namespace MetaMathlibExt

/-- `d = 5`, `z = 2`: `x² - 5 y² = ±2` has no integral solution. -/
example (x y : ℤ) : |x ^ 2 - 5 * y ^ 2| ≠ 2 :=
  abs_sq_sub_mul_sq_ne_of_two_mod_four 5 2 rfl rfl x y

#print axioms abs_sq_sub_mul_sq_ne_of_two_mod_four

-- The difference is negative and the first coordinate is negative.
example : Even (-2 : ℤ) ∧ Even (2 : ℤ) :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight 5 16 rfl rfl (-2) 2 (by decide)

-- A negative coefficient in the same residue class gives a positive difference.
example : Even (2 : ℤ) ∧ Even (-2 : ℤ) :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight (-3) 16 rfl rfl 2 (-2) (by decide)

-- The boundary value z = 0 requires no positivity hypothesis.
example (x y : ℤ) (h : x ^ 2 = 5 * y ^ 2) : Even x ∧ Even y :=
  even_of_abs_sq_sub_mul_sq_zero_mod_eight 5 0 rfl rfl x y (by rw [h, sub_self, abs_zero])

-- The horizontal line and the line of slope 3/4 have an external bisector of slope -3.
example : ((0 : ℝ) - (-3)) ^ 2 * ((3 / 4) ^ 2 + 1) =
    (3 / 4 - (-3)) ^ 2 * (0 ^ 2 + 1) := by
  apply bisector_slope_equation 0 (3 / 4) (-3) <;> norm_num

-- The Pell points (1, 1) and (1/7, 5/7) admit both the slope 1/2 and its negative reciprocal.
example (c : ℚ) (hc : c ∈ ({1 / 2, -2} : Set ℚ)) :
    ∃ u v : ℚ, 1 ^ 2 - 2 * u ^ 2 = -1 ∧ (1 / 7) ^ 2 - 2 * v ^ 2 = -1 ∧
      ((u + v ≠ 0 ∧ c = (1 * v + u * (1 / 7)) / (u + v)) ∨
        (1 * v + u * (1 / 7) ≠ 0 ∧ c = -(u + v) / (1 * v + u * (1 / 7)))) := by
  apply bisector_equation_rat_solution_negPell 2 (by decide) Int.prime_two.squarefree
      1 (1 / 7) c (by norm_num) _ ⟨1, by norm_num⟩ ⟨5 / 7, by norm_num⟩
  rcases hc with rfl | rfl <;> norm_num

#print axioms bisector_equation_rat_solution_negPell

-- The Pell solutions (1, 1) and (7, 5) give bisector slopes 2 and -1/2.
example : ∀ c ∈ ({2, -1 / 2} : Set ℚ),
    (1 - c) ^ 2 * (7 ^ 2 + 1) = (7 - c) ^ 2 * (1 ^ 2 + 1) := by
  have h := bisector_equation_form_three 2 1 1 7 5 (by norm_num) (by norm_num)
  rintro c (rfl | rfl)
  · have hc : (1 * 5 + 1 * 7 : ℚ) / (1 + 5) = 2 := by norm_num
    simpa only [hc] using h.1 (by norm_num)
  · have hc : -(1 + 5 : ℚ) / (1 * 5 + 1 * 7) = -1 / 2 := by norm_num
    simpa only [hc] using h.2 (by norm_num)

-- Opposite second coordinates make the first denominator zero. The second formula gives 0.
example : ((1 : ℚ) - 0) ^ 2 * ((-1) ^ 2 + 1) = (-1 - 0) ^ 2 * (1 ^ 2 + 1) := by
  have h := bisector_equation_form_three 2 1 1 (-1) (-1) (by norm_num) (by norm_num)
  simpa only [add_neg_cancel, neg_zero, zero_div] using h.2 (by norm_num)

-- `1² - 2 · 1² = -1` and `3² - 2 · 1² = 7` with `3` and `2 · 1` coprime give a strictly primitive
-- solution of `x² - 2 y² = -7` (for instance `(5, 4)`).
example : ∃ x y : ℤ, IsCoprime x (2 * y) ∧ x ^ 2 - 2 * y ^ 2 = -7 :=
  strictlyPrimitive_neg 2 (by norm_num) Int.prime_two.squarefree 7 (by norm_num)
    ⟨1, 1, by norm_num⟩ ⟨3, 1, ⟨1, -1, by norm_num⟩, by norm_num⟩

-- A negative value: `2² - 5 · 1² = -1` itself is strictly primitive, so `x² - 5 y² = 1` has a
-- strictly primitive solution.
example : ∃ x y : ℤ, IsCoprime x (5 * y) ∧ x ^ 2 - 5 * y ^ 2 = 1 := by
  simpa only [neg_neg] using strictlyPrimitive_neg 5 (by norm_num)
    (Int.prime_ofNat_iff.mpr Nat.prime_five).squarefree (-1) (by norm_num)
    ⟨2, 1, by norm_num⟩ ⟨2, 1, ⟨-2, 1, by norm_num⟩, by norm_num⟩

#print axioms strictlyPrimitive_neg

-- The solvability of `x² - d y² = -1` cannot be dropped: for `d = 3`, `1² - 3 · 1² = -2` with `1`
-- and `3 · 1` coprime, but `x² - 3 y² = 2` has no integral solution, as squares are `0` or `1`
-- modulo `3`.
example : IsCoprime (1 : ℤ) (3 * 1) ∧ (1 : ℤ) ^ 2 - 3 * 1 ^ 2 = -2 ∧
    ¬ ∃ x y : ℤ, IsCoprime x (3 * y) ∧ x ^ 2 - 3 * y ^ 2 = 2 := by
  refine ⟨isCoprime_one_left, by norm_num, ?_⟩
  rintro ⟨x, y, -, h⟩
  have hx : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
    rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with ht | ht | ht <;>
      simp [pow_two, Int.mul_emod, ht]
  omega

-- The factors `1 + √3` and `4 + √3` have norms `-2` and `13`. Their product is `7 + 5√3`.
example : IsCoprime (7 : ℤ) (3 * 5) ∧ |(⟨7, 5⟩ : ℤ√3).norm| = 26 := by
  let a : Fin 2 → ℤ√3 := ![⟨1, 1⟩, ⟨4, 1⟩]
  have h := strictlyPrimitive_prod 3 (by decide)
    (Int.prime_ofNat_iff.mpr Nat.prime_three).squarefree ![2, 13] (by decide) (by decide)
    (fun _ ↦ 1) a (by decide) (by decide)
  rw [Fin.prod_univ_two, Fin.prod_univ_two] at h
  exact h

-- The empty family gives the strictly primitive unit of norm one.
example (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (a : Fin 0 → ℤ√d) :
    IsCoprime (∏ i, a i).re (d * (∏ i, a i).im) ∧ |(∏ i, a i).norm| = 1 := by
  simpa using strictlyPrimitive_prod d hd hsq Fin.elim0 (fun i ↦ i.elim0) (fun i ↦ i.elim0)
    Fin.elim0 a (fun i ↦ i.elim0) (fun i ↦ i.elim0)

#print axioms strictlyPrimitive_prod

-- The comparison of the negative Pell sequences holds for every index, for
-- `d = 2` with fundamental solution `(1, 1)`.
example (n : ℕ) : negPellG 2 n ≤ negPellF 2 n :=
  (negPellG_le_negPellF 2 (by norm_num) ⟨1, 1, by norm_num⟩ n).1

-- At `n = 0` the inequality is strict: `g_0 = 0` while `f_0 = 1`.
example : ¬(negPellF 2 0 = negPellG 2 0) := by
  intro h
  have hiff := (negPellG_le_negPellF 2 (by norm_num) ⟨1, 1, by norm_num⟩ 0).2.mp h
  omega

-- The equality case `d = 2`, `n = 1`: both coordinates are `1`.
example : negPellF 2 1 = negPellG 2 1 :=
  (negPellG_le_negPellF 2 (by norm_num) ⟨1, 1, by norm_num⟩ 1).2.mpr ⟨rfl, rfl⟩

-- Another value of `d`: `x^2 - 5 y^2 = -1` has solution `(2, 1)`.
example (n : ℕ) : negPellG 5 n ≤ negPellF 5 n :=
  (negPellG_le_negPellF 5 (by norm_num) ⟨2, 1, by norm_num⟩ n).1

#print axioms negPellG_le_negPellF

end MetaMathlibExt
