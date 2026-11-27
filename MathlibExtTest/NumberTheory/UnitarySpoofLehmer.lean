/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.UnitarySpoofLehmer

/-!
# Tests for Lehmer's lemma for unitary spoof factorizations
-/

open MetaMathlibExt

-- The empty multiset extends to the factorization 3 · 3 with positive sign.
example : ((3 : ℤ) - 2) * (3 - 2) = 1 := by
  exact sub_eq_zero.mp (unitary_spoof_lehmer_lemma 0 2 1 3 3
    (Or.inl rfl) (by decide) (by decide))

-- A negative base gives a negative-sign example with two distinct added factors.
example : ((-4 : ℤ) + 3) * (-10 + 3) = 7 := by
  exact sub_eq_zero.mp (unitary_spoof_lehmer_lemma {-2} 1 (-1) 4 10
    (Or.inr rfl) (by decide) (by decide))
