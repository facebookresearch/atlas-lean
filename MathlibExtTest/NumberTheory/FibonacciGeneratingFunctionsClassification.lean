/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciGeneratingFunctionsClassification
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- Knapp's Example 14 uses the negative square root M = -5 at k = 2.
example : IsGibonacciGood 14 1 (3 / 2) := by
  have h := (gibonacci_good_families_classification 14 1 (by decide)).1 (-5) 2
    (by decide) (by decide)
  convert h using 1; norm_num

-- The soundness direction also applies outside the search bound: here M = -16.
example : IsGibonacciGood 14 1 1 := by
  have h := (gibonacci_good_families_classification 14 1 (by decide)).1 (-16) (-1)
    (by decide) (by decide)
  convert h using 1; norm_num

-- On the Lucas orbit the absolute value of the quadratic denominator is always 5.
private theorem lucasOrbit_fraction {v : ℤ × ℤ} (hv : v ∈ fibonacciPairOrbit (2, 1)) :
    v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ 1 - (v.1 : ℚ) / v.2 - ((v.1 : ℚ) / v.2) ^ 2 ≠ 0 := by
  let d (w : ℤ × ℤ) := w.2 ^ 2 - w.1 * w.2 - w.1 ^ 2
  have hiter (f : ℤ × ℤ → ℤ × ℤ) (hf : ∀ w, d (f w) = -d w) (n : ℕ) :
      |d (f^[n] (2, 1))| = 5 := by
    induction n with
    | zero =>
      change |d (2, 1)| = 5
      decide
    | succ n ih => simpa only [Function.iterate_succ_apply', hf, abs_neg] using ih
  have hnorm : |d v| = 5 := by
    rcases hv with ⟨n, rfl | rfl⟩
    · exact hiter fibonacciPairStep (fun _ => by dsimp [d, fibonacciPairStep]; ring) n
    · exact hiter fibonacciPairStepBack (fun _ => by dsimp [d, fibonacciPairStepBack]; ring) n
  have hnotsq (z : ℤ) (hz : z ^ 2 = 5) : False :=
    (by norm_num : ¬ IsSquare (5 : ℤ)) ⟨z, by simpa only [pow_two] using hz.symm⟩
  have hp : v.1 ≠ 0 := by
    intro hp
    exact hnotsq v.2 (by simpa [d, hp, abs_of_nonneg (sq_nonneg v.2)] using hnorm)
  have hq : v.2 ≠ 0 := by
    intro hq
    exact hnotsq v.1 (by simpa [d, hq, abs_of_nonneg (sq_nonneg v.1)] using hnorm)
  refine ⟨hp, hq, ?_⟩
  have hq' : (v.2 : ℚ) ≠ 0 := by exact_mod_cast hq
  have hd : d v ≠ 0 := by intro h; simp [h] at hnorm
  have hd' : (d v : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [show 1 - (v.1 : ℚ) / v.2 - ((v.1 : ℚ) / v.2) ^ 2 = (d v : ℚ) / (v.2 : ℚ) ^ 2 by
    dsimp [d]; push_cast; field_simp]
  exact div_ne_zero hd' (pow_ne_zero _ hq')

-- With a = b = 5, G has constant nonzero numerator and D = 25.
example : ∃ v ∈ fibonacciPairOrbit (2, 1), ∃ M N : ℤ,
    5 * M ^ 2 ≤ 25 ∧ M ^ 2 + 3 * M * N + N ^ 2 = 25 := by
  have hgood : IsGibonacciGood 5 5 ((2 : ℚ) / 1) :=
    ⟨by norm_num, -1, by norm_num [gibonacciGeneratingValue]⟩
  have hexcept (v : ℤ × ℤ) (hv : v ∈ fibonacciPairOrbit (2, 1)) (_ : v.2 ≠ 0) :
      (v.1 : ℚ) / v.2 ≠ 0 ∧ gibonacciGeneratingValue 5 5 ((v.1 : ℚ) / v.2) ≠ 0 := by
    obtain ⟨hp, hq, hd⟩ := lucasOrbit_fraction hv
    refine ⟨div_ne_zero (by exact_mod_cast hp) (by exact_mod_cast hq), ?_⟩
    exact div_ne_zero (by norm_num) hd
  obtain ⟨v, hv, _, M, _, N, _, _, hpos, hquad, _, _⟩ :=
    (gibonacci_good_families_classification 5 5 (by decide)).2 2 1
      (by decide) (by decide) hgood hexcept
  exact ⟨v, hv, M, N, by simpa using hpos (by decide), by simpa using hquad⟩

-- With a = 0 and b = 5, G is nonzero at each Lucas ratio and D = -25.
example : ∃ v ∈ fibonacciPairOrbit (2, 1), ∃ M N : ℤ,
    M ^ 2 ≤ 25 ∧ M ^ 2 + 3 * M * N + N ^ 2 = -25 := by
  have hgood : IsGibonacciGood 0 5 ((2 : ℚ) / 1) :=
    ⟨by norm_num, -2, by norm_num [gibonacciGeneratingValue]⟩
  have hexcept (v : ℤ × ℤ) (hv : v ∈ fibonacciPairOrbit (2, 1)) (_ : v.2 ≠ 0) :
      (v.1 : ℚ) / v.2 ≠ 0 ∧ gibonacciGeneratingValue 0 5 ((v.1 : ℚ) / v.2) ≠ 0 := by
    obtain ⟨hp, hq, hd⟩ := lucasOrbit_fraction hv
    have hx : (v.1 : ℚ) / v.2 ≠ 0 := div_ne_zero (by exact_mod_cast hp) (by exact_mod_cast hq)
    refine ⟨hx, ?_⟩
    simpa [gibonacciGeneratingValue] using div_ne_zero (mul_ne_zero (by norm_num : (5 : ℚ) ≠ 0) hx) hd
  obtain ⟨v, hv, _, M, _, N, _, hneg, _, hquad, _, _⟩ :=
    (gibonacci_good_families_classification 0 5 (by decide)).2 2 1
      (by decide) (by decide) hgood hexcept
  exact ⟨v, hv, M, N, by simpa using hneg (by decide), by simpa using hquad⟩
