/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsAdicComplete_of_isNilpotent.lean` and
`P2M/Sol/S_IsAdicComplete_of_isNilpotent.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness at nilpotent ideals

A ring is adically complete at a nilpotent ideal: the `I`-adic topology is
discrete, so every Cauchy sequence is eventually constant.
-/

@[expose] public section

universe u

/-- A ring is adically complete at a nilpotent ideal. -/
theorem IsAdicComplete.of_isNilpotent {R : Type u} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) : IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  have : IsHausdorff I R := ⟨fun x hx => by
    have h := hx N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hN] at h
    exact h⟩
  have : IsPrecomplete I R := ⟨fun {f} hf => ⟨f N, fun n => by
    rcases le_or_gt n N with hn | hn
    · exact hf hn
    · have hzero : (I ^ n • ⊤ : Ideal R) = ⊥ := by
        rw [smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
        exact Ideal.pow_le_pow_right hn.le
      rw [SModEq.sub_mem, hzero, Ideal.mem_bot, sub_eq_zero]
      have h := hf hn.le
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hN, Ideal.zero_eq_bot, Ideal.mem_bot,
        sub_eq_zero] at h
      exact h.symm⟩⟩
  exact ⟨⟩
