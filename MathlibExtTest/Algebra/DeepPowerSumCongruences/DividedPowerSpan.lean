/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerSpan
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.ZMod.Basic

open MetaMathlibExt

-- The two generators overlap in the first coordinate, where the mixed term in
-- their squared sum is nonzero (8 modulo 16).
example : IsDividedPowerIdeal
    (Ideal.span ({(2, 0), (2, 2)} : Set (ZMod 16 × ZMod 16))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA (n : ℕ) (hn : ¬ 2 ∣ n) : IsUnit (n : ZMod 16 × ZMod 16) := by
    have hu : IsUnit (n : ZMod 16) :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 4) Nat.prime_two (by decide)).mpr hn
    exact Prod.isUnit_iff.mpr ⟨hu, hu⟩
  apply (isDividedPowerIdeal_span_iff hA _).mpr
  intro a ha
  refine ⟨a, Ideal.subset_span ha, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> decide

-- In characteristic three the generator 1 fails the necessary condition.
example : ¬ IsDividedPowerIdeal (Ideal.span {(1 : ZMod 3)}) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA (n : ℕ) : ¬ 3 ∣ n → IsUnit (n : ZMod 3) :=
    (CharP.isUnit_natCast_iff Nat.prime_three).mpr
  intro h
  obtain ⟨c, _, hc⟩ := (isDividedPowerIdeal_span_iff hA _).mp h 1 (Set.mem_singleton _)
  exact one_ne_zero (by simpa only [one_pow, CharP.cast_eq_zero (ZMod 3) 3, zero_mul] using hc)
