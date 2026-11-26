/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciGeneratingFunctions
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example (a b : ℤ) : IsGibonacciGood a b 0 := by
  simpa using isGibonacciGood_fib_div a b 0

example (a b : ℤ) : IsGibonacciGood a b (2 / 3) :=
  isGibonacciGood_fib_div a b 3

-- For seeds (2, -2), the second family includes zero and resumes after the zero term.
example : IsGibonacciGood 2 (-2) 0 := by
  have h := (isGibonacciGood_standard_values 2 (-2)).2 1 (by decide)
  norm_num [gibonacciNumber] at h ⊢
  exact h

example : IsGibonacciGood 2 (-2) (-(3 / 2)) := by
  have h := (isGibonacciGood_standard_values 2 (-2)).2 5 (by decide)
  norm_num [gibonacciNumber] at h ⊢
  exact h

-- The initial shifted ratio may be negative and its terms need not be coprime.
example : IsGibonacciGood 4 6 (-(3 / 2)) := by
  have h := isGibonacciGood_shifted_ratio 4 6 0 (by decide)
  norm_num [gibonacciNumber] at h ⊢
  exact h

-- The pair (4, 8) occurs after the zero in -4, 4, 0, 4, 4, 8.
example : IsGibonacciGood 4 4 (1 / 2) := by
  have h := isGibonacciGood_shifted_ratio 4 4 4 (by decide)
  norm_num [gibonacciNumber] at h ⊢
  exact h

-- Both steps from 1/3 must preserve integrality with quadratic denominator 5.
example : IsGibonacciGood 1 3 (3 / 4) ∧ IsGibonacciGood 1 3 2 := by
  have h : IsGibonacciGood 1 3 (1 / 3) :=
    ⟨by norm_num, 3, by norm_num [gibonacciGeneratingValue]⟩
  obtain ⟨hf, hb⟩ := isGibonacciGood_transform 1 3 1 3 (by decide) (by decide) h
  norm_num at hf hb
  exact ⟨hf, hb⟩

-- At zero only the forward step is defined.
example (a b : ℤ) : IsGibonacciGood a b 1 := by
  have hf := (isGibonacciGood_transform a b 0 1 (by decide) (by decide)
    (by simpa using isGibonacciGood_zero a b)).1 (by decide)
  simpa using hf

-- At -1 only the backward step is defined.
example (a b : ℤ) : IsGibonacciGood a b (-2) := by
  have h : IsGibonacciGood a b (-1) := by
    refine ⟨by norm_num, 2 * a - b, ?_⟩
    push_cast
    simp [gibonacciGeneratingValue]
    ring
  have hb := (isGibonacciGood_transform a b (-1) 1 (by decide) (by decide) (by simpa using h)).2
  norm_num at hb
  exact hb

-- Goodness at 1/3 gives both congruences modulo 5.
example : ∃ u v : ℤ, 2 * u ≡ 1 [ZMOD 5] ∧ v ≡ 1 [ZMOD 5] ∧
    1 ≡ -3 * u [ZMOD 5] ∧ 1 ≡ -9 * v [ZMOD 5] := by
  have h : IsGibonacciGood 1 3 (1 / 3) :=
    ⟨by norm_num, 3, by norm_num [gibonacciGeneratingValue]⟩
  simpa using (isGibonacciGood_iff 1 3 1 3 (by decide) (by decide) (by decide)).mp h

-- For 2/1 the quadratic denominator is -5, but the congruences use modulus 5.
example : IsGibonacciGood 1 3 2 := by
  have h := (isGibonacciGood_iff 1 3 2 1 (by decide) (by decide) (by decide)).mpr
    ⟨-1, 3, by decide, by decide, by decide, by decide⟩
  simpa using h

-- A different seed fails the residue test at 1/3.
example : ¬ IsGibonacciGood 1 1 (1 / 3) := by
  intro h
  obtain ⟨_, v, _, hv, _, ha⟩ :=
    (isGibonacciGood_iff 1 1 1 3 (by decide) (by decide) (by decide)).mp h
  have hv' : v ≡ 1 [ZMOD 5] := by simpa using hv
  have ha' : (1 : ℤ) ≡ -3 * v [ZMOD 5] := by simpa using ha
  exact (by decide : ¬ (1 : ℤ) ≡ -3 [ZMOD 5])
    (ha'.trans (by simpa using hv'.mul_left (-3)))

-- For p = 0 the modulus is 1, so p still has a witness in the congruence formulation.
example : IsGibonacciGood 2 3 0 := by
  have h := (isGibonacciGood_iff 2 3 0 (-1) (by decide) (by decide) (by decide)).mpr
    ⟨0, 0, by decide, by decide, by decide, by decide⟩
  simpa using h

-- Consecutive indices give opposite signs for the denominator.
example : gibonacciGeneratingValue (-2) 5 (1 / 2) = 6 := by
  norm_num [gibonacciGeneratingValue]

example : gibonacciGeneratingValue (-2) 5 (2 / 3) = -24 := by
  norm_num [gibonacciGeneratingValue]

example : (2, 3) ∈ fibonacciPairOrbit (0, 1) :=
  ⟨3, Or.inl rfl⟩

example : (-1, 1) ∈ fibonacciPairOrbit (0, 1) :=
  ⟨2, Or.inr rfl⟩

example : knappM 1 11 1 2 = 58 := by
  norm_num [knappM]

end MetaMathlibExt
