/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectDickson
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Lattice

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectDickson

open MetaMathlibExt

-- No odd perfect number has zero distinct prime divisors.
example : {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = 0} = ∅ := by
  ext N
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hperf, hcard⟩
  rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with rfl | rfl
  · exact (by decide : ¬ Nat.Perfect 0) hperf
  · exact (by decide : ¬ Nat.Perfect 1) hperf

-- Finiteness for an exact count gives a bound on the numbers themselves.
example (m : ℕ) :
    ∃ B : ℕ, ∀ N : ℕ, Odd N → N.Perfect → N.primeFactors.card = m → N ≤ B := by
  obtain ⟨B, hB⟩ := (finite_setOf_oddPerfect_card_primeFactors_eq m).bddAbove
  exact ⟨B, fun N hodd hperfect hm => hB (a := N) ⟨hodd, hperfect, hm⟩⟩

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectDickson
