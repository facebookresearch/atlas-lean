/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PadicNeronModels

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.PadicNeronModels

open CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

-- p-adic Néron models are the general finite-type Néron models over `ℤ_p ⊂ ℚ_p`, so the
-- general extension API applies.
example (A : Over (genericBase p)) :
    NeronModel p A = NeronModels.FiniteTypeNeronModel (PadicInt p) (Padic p) A :=
  rfl

noncomputable example {A : Over (genericBase p)} (N : NeronModel p A) (Y : Over (trait p))
    [Smooth Y.hom] :
    (Y ⟶ N.model) ≃ ((genericFunctor p).obj Y ⟶ A) :=
  N.homEquiv Y

-- The generic-fibre functor is the general one.
example : genericFunctor p = SemistableModels.genericFunctor (PadicInt p) (Padic p) := rfl

-- Integral points are the general ones.
example (N : Over (trait p)) : IntegralPoint p N = NeronModels.IntegralPoint (PadicInt p) N :=
  rfl

-- Reduction sends an integral point to a point of the special fibre over `𝔽_p`.
example (N : Over (trait p)) (q : IntegralPoint p N) :
    (reducePoint p N q).1 ≫ ((specialFunctor p).obj N).hom = 𝟙 _ :=
  (reducePoint p N q).2

end MathlibExt.AlgebraicGeometry.PadicNeronModels
