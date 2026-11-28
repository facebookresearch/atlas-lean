/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectDickson
import Mathlib.Data.Set.Finite.Lattice

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectDickson

open MetaMathlibExt

-- The finiteness theorem does not require a positive prime-factor count.
example : {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = 0}.Finite :=
  finite_setOf_oddPerfect_card_primeFactors_eq 0

-- Finiteness for an exact count gives a bound on the numbers themselves.
example (m : ℕ) :
    ∃ B : ℕ, ∀ N : ℕ, Odd N → N.Perfect → N.primeFactors.card = m → N ≤ B := by
  obtain ⟨B, hB⟩ := (finite_setOf_oddPerfect_card_primeFactors_eq m).bddAbove
  exact ⟨B, fun N hodd hperfect hm => hB (a := N) ⟨hodd, hperfect, hm⟩⟩

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectDickson
