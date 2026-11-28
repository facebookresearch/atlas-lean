/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.LocalGlobal

/-! # Tests for `MathlibExt.NumberTheory.Rat.LocalGlobal` -/

namespace MathlibExtTest.RatLocalGlobal

open Rat Rat.Place

-- A rational number that is a square in `ℝ` and in every `ℚ_[p]` is a square in `ℚ`.
example (r : ℚ) (hreal : IsSquare (r : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], IsSquare (r : ℚ_[p])) : IsSquare r :=
  isSquare_of_isSquare_real_of_forall_isSquare_padic hreal hpadic

-- Contrapositive form: a rational non-square fails to be a square at some place.
example (r : ℚ) (hr : ¬IsSquare r) :
    ¬IsSquare (r : ℝ) ∨ ∃ (p : ℕ) (_ : Fact p.Prime), ¬IsSquare (r : ℚ_[p]) := by
  by_contra h
  simp only [not_or, not_exists, not_not] at h
  exact hr (isSquare_of_isSquare_real_of_forall_isSquare_padic h.1 fun p _ => h.2 p ‹_›)

-- Weak approximation at the infinite place and the place `2`.
example (x : (v : ({.infinite, .finite ⟨2, Nat.prime_two⟩} : Finset Place)) → CompletedField v.1) :
    ∃ q : ℚ, ∀ v, ‖embedding v.1 q - x v‖ < 1 / 1000 :=
  exists_forall_norm_sub_lt _ x (by norm_num)

-- The diagonal image of `ℚ` is dense in every finite product of completions.
example (S : Finset Place) : DenseRange (fun (q : ℚ) (v : S) => embedding v.1 q) :=
  denseRange_embedding_pi S

-- Distinct places give inequivalent absolute values.
example :
    ¬(Place.infinite.absoluteValue).IsEquiv (Place.finite ⟨3, Nat.prime_three⟩).absoluteValue :=
  absoluteValue_not_isEquiv (by simp)

-- `3/5` has numerator and denominator prime to `2`, so it is a `2`-adic unit.
example : ‖((3 / 5 : ℚ) : ℚ_[2])‖ = 1 :=
  Padic.norm_ratCast_eq_one_of_not_dvd (by norm_num [Rat.num_div_eq_of_coprime,
    Rat.den_div_eq_of_coprime])

end MathlibExtTest.RatLocalGlobal
