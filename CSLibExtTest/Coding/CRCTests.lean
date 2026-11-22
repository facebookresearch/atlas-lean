/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.CRC
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Tests for cyclic redundancy checks

The running example is CRC-3 with generator `g = X^3 + X + 1` over `F₂`: three terms, constant
term 1, so it detects every single-bit error and every burst of length at most 3. Two degenerate
generators show that both hypotheses are needed.
-/

namespace Cslib.CodingTheory.CRCTests

open Polynomial Cslib.CodingTheory CRC

/-- The CRC-3 generator `X^3 + X + 1`. -/
noncomputable def g : (ZMod 2)[X] := X ^ 3 + X + 1

theorem coeff_g_zero : g.coeff 0 = 1 := by simp [g, coeff_X, coeff_one]

theorem coeff_g_three : g.coeff 3 = 1 := by simp [g, coeff_X, coeff_one]

theorem natDegree_g : g.natDegree = 3 := by
  unfold g
  compute_degree!

theorem two_le_card_support_g : 2 ≤ g.support.card :=
  Finset.one_lt_card.mpr ⟨0, by simp [mem_support_iff, coeff_g_zero], 3,
    by simp [mem_support_iff, coeff_g_three], by decide⟩

theorem not_X_dvd_g : ¬X ∣ g := by
  rw [X_dvd_iff, coeff_g_zero]
  exact one_ne_zero

/-- Every codeword is a multiple of `g`, and the message sits above the 3 check bits. -/
example (m : (ZMod 2)[X]) : g ∣ encode g m := dvd_encode g m

example (m : (ZMod 2)[X]) (i : ℕ) : (encode g m).coeff (i + 3) = m.coeff i := by
  rw [← natDegree_g, coeff_encode_add (by rintro h; simpa [h] using coeff_g_zero) m]

/-- Over `F₂` the encoder appends the remainder. -/
example (m : (ZMod 2)[X]) : encode g m = m * X ^ g.natDegree + m * X ^ g.natDegree % g :=
  encode_eq_add g m

/-- **CRC-3 detects every single-bit error and every burst of length at most 3.** -/
example (m : (ZMod 2)[X]) :
    (∀ a : ZMod 2, a ≠ 0 → ∀ i, ¬g ∣ encode g m + C a * X ^ i) ∧
      ∀ e, IsBurstLE e g.natDegree → ¬g ∣ encode g m + e :=
  detects two_le_card_support_g not_X_dvd_g m

/-- The error `X^5 + X^3` (bits 3 and 5 flipped) is confined to positions 3, 4, 5, so it is a
burst of length 3 and CRC-3 catches it. -/
example (m : (ZMod 2)[X]) : ¬g ∣ encode g m + (X ^ 5 + X ^ 3) := by
  have hne : (X ^ 5 + X ^ 3 : (ZMod 2)[X]) ≠ 0 := by
    intro h
    have := congrArg (coeff · 3) h
    simp [coeff_X_pow] at this
  have hb : IsBurstLE (X ^ 5 + X ^ 3 : (ZMod 2)[X]) 3 := by
    refine isBurstLE_of_support hne (i := 3) fun j hj ↦ ?_
    rw [mem_support_iff] at hj
    by_cases h5 : j = 5
    · omega
    by_cases h3 : j = 3
    · omega
    simp [coeff_X_pow, h5, h3] at hj
  rw [dvd_encode_add_iff]
  exact not_dvd_of_isBurstLE not_X_dvd_g hb natDegree_g.ge

/-- **A one-term generator misses single-bit errors**: with `g = X^3`, flipping bit 3 of any
codeword goes undetected. -/
example (m : (ZMod 2)[X]) : (X ^ 3 : (ZMod 2)[X]) ∣ encode (X ^ 3) m + C 1 * X ^ 3 := by
  rw [dvd_encode_add_iff]
  exact dvd_mul_left _ _

/-- **A generator divisible by `X` misses short bursts**: with `g = X^2 + X`, the burst `X(X + 1)`
of length 2 equals `g` and goes undetected. -/
example (m : (ZMod 2)[X]) : (X ^ 2 + X : (ZMod 2)[X]) ∣ encode (X ^ 2 + X) m + X * (X + 1) := by
  rw [dvd_encode_add_iff]
  exact ⟨1, by ring⟩

example : IsBurstLE (X * (X + 1) : (ZMod 2)[X]) 2 :=
  ⟨1, X + 1, by rw [pow_one], by simp, by
    rw [show (X + 1 : (ZMod 2)[X]) = X + C 1 by simp, natDegree_X_add_C]
    omega⟩

/-- A concrete codeword: `X^3 mod (X^3 + X + 1) = X + 1`, so the message `1` encodes to `g`
itself, `1011` with the message bit followed by the check bits `011`. -/
theorem X_pow_three_mod_g : (X ^ 3 : (ZMod 2)[X]) % g = X + 1 := by
  have hmonic : g.Monic := by
    unfold Monic
    rw [leadingCoeff, natDegree_g, coeff_g_three]
  have hdeg : (X + 1 : (ZMod 2)[X]).degree < g.degree := by
    rw [degree_eq_natDegree hmonic.ne_zero, natDegree_g,
      show (X + 1 : (ZMod 2)[X]) = X + C 1 by simp, degree_X_add_C]
    decide
  rw [mod_def, hmonic.leadingCoeff, inv_one, C_1, mul_one]
  refine ((div_modByMonic_unique 1 (X + 1) hmonic ⟨?_, hdeg⟩).2)
  unfold g
  have h1 : (X : (ZMod 2)[X]) + X = 0 := CharTwo.add_self_eq_zero X
  have h2 : (1 : (ZMod 2)[X]) + 1 = 0 := CharTwo.add_self_eq_zero 1
  linear_combination h1 + h2

example : encode g 1 = g := by
  rw [encode_eq_add, natDegree_g, one_mul, X_pow_three_mod_g]
  unfold g
  ring

/-- The constant generator `1` has `X ∤ 1` but only one term, and misses every error: the
two-terms hypothesis is independent of `X ∤ g`. -/
example (m e : (ZMod 2)[X]) : (1 : (ZMod 2)[X]) ∣ encode 1 m + e := one_dvd _

example : ¬X ∣ (1 : (ZMod 2)[X]) := by
  rw [X_dvd_iff, coeff_one_zero]
  exact one_ne_zero

/-- The bound `deg g` is sharp: `g` itself is a burst of length 4 that CRC-3 misses. -/
example : IsBurstLE g 4 :=
  ⟨0, g, by rw [pow_zero, one_mul], by rw [coeff_g_zero]; exact one_ne_zero,
    by rw [natDegree_g]; omega⟩

example (m : (ZMod 2)[X]) : g ∣ encode g m + g := by
  rw [dvd_encode_add_iff]

end Cslib.CodingTheory.CRCTests
