/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.FinrankAlong

@[expose] public section

open AlgebraicCurve

/-- Consumer with the original binders: abstract degeneracy data with
the two factorizations and equal first-factor degrees. -/
example {K F M T : Type*} [Field K] [Field F] [Field M] [Field T]
    [Algebra K F] [Algebra K M] [Algebra K T]
    (incl subst : F →ₐ[K] T) (common : M →ₐ[K] T)
    (alpha beta : F →ₐ[K] M)
    (hincl : incl = common.comp alpha) (hsubst : subst = common.comp beta)
    (hab : finrankAlong alpha = finrankAlong beta) :
    finrankAlong incl = finrankAlong subst :=
  ModularCurve.finrankAlong_x1LevelInclBar_eq_finrankAlong_x1LevelSubstBar
    incl subst common alpha beta hincl hsubst hab

/-- The degree along the identity is one. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] :
    finrankAlong (AlgHom.id K F) = Module.finrank F F :=
  rfl

/-- Boundary case: if the first factors have different degrees, the
conclusion can fail, for instance for the identity against a
quadratic extension composed with the identity. -/
example : finrankAlong (Algebra.ofId ℚ ℚ) = 1 := by
  show Module.finrank ℚ ℚ = 1
  exact Module.finrank_self ℚ
