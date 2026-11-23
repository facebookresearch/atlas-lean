/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.IntegralRepresentation

@[expose] public section

/-- Source-shaped consumer: the original binders, in the original order. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x :=
  A.exists_integral_mul_eq_of_liesOverPrime hq hA a ha

/-- Boundary: the conclusion need not hold with `s = 1` and `x = a` when
`a` is not integral, so the scaling element matters. In particular, a
transcendental choice is unavailable here because every element of
`AlgebraicClosure ℚ` is algebraic, hence integral after the scaling
provided by the theorem. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧
        IsIntegral ℤ (a * (s : AlgebraicClosure ℚ)) := by
  obtain ⟨x, s, hs, hxs⟩ := A.exists_integral_mul_eq_of_liesOverPrime hq hA a ha
  exact ⟨s, hs, hxs ▸ x.2⟩
