/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.KatzBettiBounds

/-! # Tests for compact supports and the affine schemes of Katz's bound

The affine scheme of a system of equations is a scheme over the base field, with coordinate ring
the quotient by the ideal they generate; compact-support reductions are compatible with the
transitions for every prime; Katz's constant evaluates as stated.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.KatzBettiBounds

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
open MathlibExt.AlgebraicGeometry.KatzBettiBounds

universe u

variable {k : Type u} [Field k] {N r : ℕ} (F : Fin r → MvPolynomial (Fin N) k)

example : equationsIdeal F = Ideal.span (Set.range F) := rfl

example (j : Fin r) : Ideal.Quotient.mk (equationsIdeal F) (F j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)

example : (affineVariety F).left = Spec (.of (affineCoordinateRing F)) := rfl

/-- Katz's constant `6 · 2^r · (3 + r d)^(N + 1)`, e.g. for two equations of degree two in the
plane. -/
example : katzBound 2 2 2 = 6 * 4 * 7 ^ 3 := rfl

example (ell : ℕ) [Fact ell.Prime] {X : Over (Spec (.of k))} (c : ClosedCompactification X)
    (n s : ℕ) (x : integralCompactSupport ell c n) :
    compactTransition ell c n s (compactReduction ell c n (s + 1) x) =
      compactReduction ell c n s x :=
  compactReductionsCommute ell c n s x

end MathlibExtTest.AlgebraicGeometry.KatzBettiBounds
