/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.PrimePow
import MathlibExt.NumberTheory.ArithmeticFunction.Antimultiplicative

namespace MetaMathlibExt.dirichletUnits_multiplicative_antimultiplicative_subgroups

open ArithmeticFunction

private def oneAnd (m : ℕ) (hm : m ≠ 0) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 1 ∨ n = m then 1 else 0, by simp [hm.symm]⟩

-- Vanishing on all primes alone cannot detect a nonzero value at a prime square.
example : (∀ p, p.Prime → oneAnd 4 (by decide) p = 0) ∧
    ¬ IsAntimultiplicative (oneAnd 4 (by decide)) := by
  constructor
  · intro p hp
    have hp₄ : p ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) hp
    simp [oneAnd, hp.ne_one, hp₄]
  · intro h
    have h₄ := h.2 2 2 Nat.prime_two (by decide)
    change oneAnd 4 (by decide) 4 = 0 at h₄
    simp [oneAnd] at h₄

-- A unit can be nonzero at 6 while vanishing at every positive power of a prime.
example : ∃ u : (ArithmeticFunction ℝ)ˣ, IsAntimultiplicative (u : ArithmeticFunction ℝ) ∧
    IsAntimultiplicative (↑u⁻¹ : ArithmeticFunction ℝ) ∧ u ≠ 1 := by
  let f := oneAnd 6 (by decide)
  have hf : IsAntimultiplicative f := by
    refine ⟨by simp [f, oneAnd], fun p k hp hk => ?_⟩
    have h₆ : p ^ k ≠ 6 := by
      intro h
      have hpp : IsPrimePow (6 : ℕ) := ⟨p, k, hp.prime, hk, h⟩
      obtain ⟨q, _, hq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpp
      have htwo : 2 = q := hq 2 ⟨Nat.prime_two, by decide⟩
      have hthree : 3 = q := hq 3 ⟨Nat.prime_three, by decide⟩
      exact (by decide : (2 : ℕ) ≠ 3) (htwo.trans hthree.symm)
    simp [f, oneAnd, hp.ne_one, hk.ne', h₆]
  obtain ⟨u, hu⟩ := isUnit_iff_isUnit_apply_one.mpr (hf.1 ▸ isUnit_one)
  obtain ⟨_, _, UA, _, _, hUA, _, _, _⟩ :=
    dirichletUnits_multiplicative_antimultiplicative_subgroups
  have huA : u ∈ UA := (hUA u).mpr (hu ▸ hf)
  refine ⟨u, (hUA u).mp huA, (hUA _).mp (UA.inv_mem huA), ?_⟩
  intro h
  have hf₆ : f 6 = 0 := by rw [← hu, h, Units.val_one, one_apply_ne (by decide)]
  simp [f, oneAnd] at hf₆

end MetaMathlibExt.dirichletUnits_multiplicative_antimultiplicative_subgroups
