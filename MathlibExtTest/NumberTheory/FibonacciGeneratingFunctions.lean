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

-- Lucas ratios are all good for (1, 3), using the two congruences modulo 5.
example : ∀ n : ℕ, gibonacciNumber 2 1 (n + 1) ≠ 0 →
    IsGibonacciGood 1 3 ((gibonacciNumber 2 1 n : ℚ) / gibonacciNumber 2 1 (n + 1)) :=
  ((isGibonacciGood_ratios_infinite_iff 2 1 (by decide)).2 1 3).mpr
    ⟨-1, 3, by decide, by decide, by decide, by decide⟩

-- In -1, 1, 0, 1, 1, 2, the ratio at n = 4 is defined despite the zero at index 2.
example (a b : ℤ) : IsGibonacciGood a b (1 / 2) := by
  have h := ((isGibonacciGood_ratios_infinite_iff (-1) 1 (by decide)).2 a b).mpr
    (by
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> norm_num [Int.modEq_one])
  have h₄ := h 4 (by decide)
  norm_num [gibonacciNumber] at h₄
  exact h₄

-- The singleton-ratio obstruction at 1/3 precludes a good family for (1, 1).
example : ¬ ∀ n : ℕ, gibonacciNumber 1 3 (n + 1) ≠ 0 →
    IsGibonacciGood 1 1 ((gibonacciNumber 1 3 n : ℚ) / gibonacciNumber 1 3 (n + 1)) := by
  intro h
  obtain ⟨_, v, _, hv, _, ha⟩ := ((isGibonacciGood_ratios_infinite_iff 1 3 (by decide)).2 1 1).mp h
  have hv' : v ≡ 1 [ZMOD 5] := by simpa using hv
  have ha' : (1 : ℤ) ≡ -3 * v [ZMOD 5] := by simpa using ha
  exact (by decide : ¬ (1 : ℤ) ≡ -3 [ZMOD 5])
    (ha'.trans (by simpa using hv'.mul_left (-3)))

-- The infinitude assertion also applies when the initial denominator is zero.
example : Set.Infinite {ab : ℤ × ℤ | ∀ n : ℕ, gibonacciNumber 1 0 (n + 1) ≠ 0 →
    IsGibonacciGood ab.1 ab.2 ((gibonacciNumber 1 0 n : ℚ) / gibonacciNumber 1 0 (n + 1))} :=
  (isGibonacciGood_ratios_infinite_iff 1 0 (by decide)).1

-- Consecutive indices give opposite signs for the denominator.
example : gibonacciGeneratingValue (-2) 5 (1 / 2) = 6 := by
  norm_num [gibonacciGeneratingValue]

example : gibonacciGeneratingValue (-2) 5 (2 / 3) = -24 := by
  norm_num [gibonacciGeneratingValue]

example : (2, 3) ∈ fibonacciPairOrbit (0, 1) :=
  ⟨3, Or.inl rfl⟩

example : (-1, 1) ∈ fibonacciPairOrbit (0, 1) :=
  ⟨2, Or.inr rfl⟩

-- One forward step from (-6, 4) and one backward step from (4, 6) give the same ratio.
example :
    (-2 : ℚ) ∈ {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-6, 4), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} ∧
    (-2 : ℚ) ∈ {x : ℚ | ∃ w ∈ fibonacciPairOrbit (4, 6), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1} := by
  constructor
  · exact ⟨(4, -2), (mem_fibonacciPairOrbit_iff _ _).mpr ⟨1, Or.inl (by decide)⟩,
      by decide, by norm_num⟩
  · exact ⟨(2, 4), (mem_fibonacciPairOrbit_iff _ _).mpr ⟨1, Or.inr (by decide)⟩,
      by decide, by norm_num⟩

-- Two backward steps from (-6, 4) match two forward steps from (4, 6).
example :
    (-8 / 5 : ℚ) ∈ {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-6, 4), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} ∧
    (-8 / 5 : ℚ) ∈ {x : ℚ | ∃ w ∈ fibonacciPairOrbit (4, 6), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1} := by
  constructor
  · exact ⟨(-16, 10), (mem_fibonacciPairOrbit_iff _ _).mpr ⟨2, Or.inr (by decide)⟩,
      by decide, by norm_num⟩
  · exact ⟨(10, 16), (mem_fibonacciPairOrbit_iff _ _).mpr ⟨2, Or.inl (by decide)⟩,
      by decide, by norm_num⟩

-- For zero seeds both denominator restrictions exclude every orbit pair.
example :
    {x : ℚ | ∃ v ∈ fibonacciPairOrbit (0, 0), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} = ∅ ∧
    {x : ℚ | ∃ w ∈ fibonacciPairOrbit (0, 0), w.1 ≠ 0 ∧ x = -(w.2 : ℚ) / w.1} = ∅ := by
  have orbit_zero {v : ℤ × ℤ} (hv : v ∈ fibonacciPairOrbit (0, 0)) : v = (0, 0) := by
    rcases (mem_fibonacciPairOrbit_iff _ _).mp hv with ⟨n, rfl | rfl⟩
    · exact Function.iterate_fixed (f := fibonacciPairStep) (by decide) n
    · exact Function.iterate_fixed (f := fibonacciPairStepBack) (by decide) n
  constructor <;> apply Set.eq_empty_iff_forall_notMem.mpr <;>
    rintro x ⟨v, hv, hne, _⟩ <;> cases orbit_zero hv <;> exact hne rfl

-- A client can transport the backward-orbit ratio to the shifted family.
example : (-2 : ℚ) ∈
    {x : ℚ | ∃ v ∈ fibonacciPairOrbit (-6, 4), v.2 ≠ 0 ∧ x = (v.1 : ℚ) / v.2} := by
  rw [gibonacci_shifted_ratios_eq_negated_ratios 4 6]
  exact ⟨(2, 4), (mem_fibonacciPairOrbit_iff _ _).mpr ⟨1, Or.inr (by decide)⟩,
    by decide, by norm_num⟩

example : knappM 1 11 1 2 = 58 := by
  norm_num [knappM]

end MetaMathlibExt
