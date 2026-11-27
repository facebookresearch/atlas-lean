/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.PowAlgebraic

@[expose] public section

-- exactSource consumer: the original binders apply verbatim.
example {E F : Type*} [Field E] [Field F] [Algebra E F] [Algebra.IsAlgebraic E F]
    (O : ValuationSubring F) {g : F} (hg : g ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : E, c ≠ 0 ∧
      O.valuation (g ^ n) = O.valuation (algebraMap E F c) :=
  ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic O hg

-- Boundary: the hypothesis `g ≠ 0` matters; for `g = 0` no such data exist.
example {E F : Type*} [Field E] [Field F] [Algebra E F] [Algebra.IsAlgebraic E F]
    (O : ValuationSubring F) :
    ¬ ∃ n : ℕ, 0 < n ∧ ∃ c : E, c ≠ 0 ∧
      O.valuation ((0 : F) ^ n) = O.valuation (algebraMap E F c) := by
  rintro ⟨n, hn, c, hc, h⟩
  rw [zero_pow hn.ne', map_zero] at h
  have : O.valuation (algebraMap E F c) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero (algebraMap E F)).mpr hc)
  exact this h.symm
