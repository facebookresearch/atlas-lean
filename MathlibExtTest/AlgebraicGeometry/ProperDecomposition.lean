/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProperDecomposition

@[expose] public section

/-!
# Tests for proper images and the semismall defect

The normalized image is the derived direct image of the constant sheaf in
degree `-d`, the constructible package keeps that object, the defect bound is
monotone in the defect and is a bound on the Krull dimension of the actual
fiber product, and point fibers are scheme pullbacks along complex points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ProperDecomposition

namespace MathlibExtTest.AlgebraicGeometry.ProperDecomposition

attribute [local instance] HasDerivedCategory.standard

variable {X Y : PerverseSheaves.ComplexScheme} (f : X ⟶ Y)

/-- The normalized image is `Rf_*` applied to `ℚ_X` placed in degree `-d`. -/
example (d : ℕ) :
    normalizedDirectImage X Y f d =
      (ConstructibleComplexes.derivedPushforwardPlus ℚ f).obj
        ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X))
          (-(d : ℤ))).obj (rationalConstantSheaf (space X))) :=
  rfl

/-- The constructible package has the normalized image as its object. -/
example (d : ℕ) (hK : boundedConstructible Y (normalizedDirectImage X Y f d)) :
    (constructibleImage X Y f d hK).obj = normalizedDirectImage X Y f d :=
  rfl

/-- The defect bound is monotone in the defect. -/
example (d r r' : ℕ) (h : DefectLE f d r) (hr : r ≤ r') : DefectLE f d r' := by
  unfold DefectLE at h ⊢
  refine h.trans (WithBot.coe_le_coe.mpr ?_)
  exact add_le_add le_rfl (Nat.cast_le (α := ℕ∞) |>.mpr hr)

/-- The defect bound is a bound on the Krull dimension of `X ×_Y X`. -/
example (d r : ℕ) :
    DefectLE f d r ↔
      topologicalKrullDim (pullback f.left f.left : Scheme.{0}) ≤
        ((d + r : ℕ∞) : WithBot ℕ∞) :=
  Iff.rfl

/-- The fiber over a complex point is the pullback along that point. -/
example (p : space Y) : pointFiber f p = pullback f.left p.hom := rfl

end MathlibExtTest.AlgebraicGeometry.ProperDecomposition
