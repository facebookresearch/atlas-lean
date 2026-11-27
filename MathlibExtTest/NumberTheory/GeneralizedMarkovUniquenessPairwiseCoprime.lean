/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.GCD.Basic
import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessPairwiseCoprime

/-!
# Tests for pairwise coprimality of generalized Markov triples

These tests apply pairwise coprimality to a concrete generalized Markov triple and show that
any common divisor of two entries is one.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.3 (citing Gyoda and
Matsushita, Corollary 8).
-/

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessPairwiseCoprime

open MetaMathlibExt

example : Nat.gcd 13 217 = 1 ∧ Nat.gcd 217 3 = 1 ∧ Nat.gcd 13 3 = 1 := by
  have h : IsGenMarkovTriple 1 13 217 3 := by
    unfold IsGenMarkovTriple
    decide
  exact h.pairwise_coprime

example {k a b c d : ℕ} (h : IsGenMarkovTriple k a b c) (hda : d ∣ a) (hdc : d ∣ c) :
    d = 1 :=
  Nat.eq_one_of_dvd_coprimes h.pairwise_coprime.2.2 hda hdc

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessPairwiseCoprime
