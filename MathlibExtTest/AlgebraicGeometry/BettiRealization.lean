/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BettiFunctoriality

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.BettiRealization` and
`MathlibExt.AlgebraicGeometry.BettiFunctoriality` -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.BettiFunctoriality

namespace MathlibExtTest.AlgebraicGeometry.BettiRealization

attribute [local instance] HasDerivedCategory.standard

variable (Z : TopCat.{0}) {i j : ℤ}

/-- Betti cohomology is a rational vector space. -/
example (n : ℤ) : Module ℚ (Cohomology Z n) := inferInstance

/-- Degree casts along equal degrees compose, and the cast along `rfl` is the
identity. -/
example {m : ℤ} (x : Cohomology Z m) : cohomologyCast rfl x = x := by simp

example {l m n : ℤ} (h : l = m) (h' : m = n) (x : Cohomology Z l) :
    cohomologyCast h' (cohomologyCast h x) = cohomologyCast (h.trans h') x := by
  subst h h'
  rfl

/-- The cup product vanishes when either factor does. -/
example (y : Cohomology Z j) : cup Z (0 : Cohomology Z i) y = 0 := by
  simp [cup]

example (x : Cohomology Z i) : cup Z x (0 : Cohomology Z j) = 0 := by
  simp [cup]

/-- The two linear maps are the cup product with a fixed factor. -/
example (x : Cohomology Z i) (y : Cohomology Z j) : cupLeft Z y x = cup Z x y := rfl
example (x : Cohomology Z i) (y : Cohomology Z j) : cupRight Z x y = cup Z x y := rfl

/-- The cup product is rational-bilinear. -/
example (r : ℚ) (x : Cohomology Z i) (y : Cohomology Z j) :
    cup Z (r • x) y = r • cup Z x y :=
  (cupLeft Z y).map_smul r x

example (x : Cohomology Z i) (y y' : Cohomology Z j) :
    cup Z x (y + y') = cup Z x y + cup Z x y' :=
  (cupRight Z x).map_add y y'

variable {Z} {W : TopCat.{0}} (f : Z ⟶ W)

/-- Derived inverse image fixes the rational unit and commutes with shifts. -/
example : (derivedPullback ℚ f).obj (rationalUnit W) ≅ rationalUnit Z :=
  unitInverseImageIso f

example : (derivedPullback ℚ f).CommShift ℤ := inferInstance

/-- Pullback on Betti cohomology is rational-linear. -/
example (n : ℤ) (a b : Cohomology W n) :
    cohomologyPullback f n (a + b) = cohomologyPullback f n a + cohomologyPullback f n b :=
  map_add _ a b

example (n : ℤ) : cohomologyPullback f n 0 = 0 := map_zero _

/-- Pullback fixes the unit class, and is derived inverse image of shifted
morphisms conjugated by the unit comparison. -/
example : cohomologyPullback f 0 (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (rationalUnit W))) =
    ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (rationalUnit Z)) :=
  cohomologyPullback_mk₀_id f

example (n : ℤ) (a : Cohomology W n) :
    cohomologyPullback f n a = (unitInverseImageIso f).inv ≫
      ShiftedHom.map a (derivedPullback ℚ f) ≫
        (shiftFunctor (RationalDerived Z) n).map (unitInverseImageIso f).hom :=
  cohomologyPullback_apply f n a

/-- The cup product is the composition of shifted morphisms. -/
example {i j : ℤ} (x : Cohomology Z i) (y : Cohomology Z j) :
    cup Z x y = ShiftedHom.comp x y (add_comm j i) :=
  rfl

/-- Inverse image of the constant sheaf functor is the constant sheaf functor. -/
example : constantFunctor W ⋙ pullback ℚ f ≅ constantFunctor Z := constantPullbackIso f

end MathlibExtTest.AlgebraicGeometry.BettiRealization

end
