/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.NormalCrossingsModels
import MathlibExt.AlgebraicGeometry.VanishingIdeal

set_option autoImplicit false

/-! Tests for strict normal crossings boundaries and reduced pullback boundaries. -/

open AlgebraicGeometry CategoryTheory MathlibExt.AlgebraicGeometry.NormalCrossingsModels

universe u

-- A point lies on the reduced pullback boundary exactly when its image lies on the boundary.
example {X Y : Scheme.{u}} (f : Y ⟶ X) (D : X.IdealSheafData) (y : Y) :
    y ∈ (reducedPullbackBoundary f D).support ↔ f y ∈ D.support := by
  rw [reducedPullbackBoundary_support]
  rfl

-- Pulling back along the identity keeps the support.
example {X : Scheme.{u}} (D : X.IdealSheafData) :
    (reducedPullbackBoundary (𝟙 X) D).support = D.support := by
  ext x
  rw [reducedPullbackBoundary_support]
  rfl

-- The reduced pullback boundary is a reduced subscheme, as a strict normal crossings boundary
-- must be, even when the scheme-theoretic pullback is not reduced.
example {X Y : Scheme.{u}} (f : Y ⟶ X) (D : X.IdealSheafData) :
    IsReduced (reducedPullbackBoundary f D).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _

-- The empty boundary (unit ideal) has strict normal crossings.
example {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    IsStrictNormalCrossings X (⊤ : X.left.IdealSheafData) :=
  isStrictNormalCrossings_of_support_eq_bot rfl

-- So does the reduced pullback of an empty boundary.
example {k : Type u} [Field k] (X Y : Over (Spec (.of k))) (f : Y ⟶ X) :
    IsStrictNormalCrossings Y (reducedPullbackBoundary f.left (⊤ : X.left.IdealSheafData)) :=
  isStrictNormalCrossings_of_support_eq_bot (by
    ext y
    rw [reducedPullbackBoundary_support]
    simp)

-- A strict normal crossings boundary is reduced and has strict local equations.
example {k : Type u} [Field k] (X : Over (Spec (.of k))) (D : X.left.IdealSheafData)
    (h : IsStrictNormalCrossings X D) : IsReduced D.subscheme ∧ StrictStalkCrossings D :=
  ⟨h.1, h.2.1⟩

-- At each boundary point the local equation is a product of a nonempty initial segment of a
-- regular system of parameters of the regular ambient stalk.
example {X : Scheme.{u}} (D : X.IdealSheafData) (h : StrictStalkCrossings D)
    (y : D.subscheme) : IsRegularLocalRing (X.presheaf.stalk (D.subschemeι y)) :=
  (h y).1
