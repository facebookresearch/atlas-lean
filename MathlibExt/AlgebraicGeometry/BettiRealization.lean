/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

@[expose] public noncomputable section

/-!
# Rational Betti coefficients and Yoneda products

The coefficient object is the constant rational sheaf in the actual derived
category on the analytification topology. Cohomology consists of its shifted
endomorphisms. The product below is shifted composition, rather than an
unspecified multiplication on a named cohomology carrier.

The imported analytification retains its AxiomMath/Weil source and license
notice. These definitions use Mathlib's derived category and linear structure
directly. Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, §2.6.
-/

namespace MathlibExt.AlgebraicGeometry.BettiRealization

open CategoryTheory CategoryTheory.Limits TopCat
open MathlibExt.AlgebraicGeometry.PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- Rational sheaves inherit the scalar action on natural transformations. -/
instance rationalSheafLinear (Z : TopCat.{0}) : Linear ℚ (RationalSheaf Z) := by
  change Linear ℚ (CategoryTheory.Sheaf
    (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ))
  unfold CategoryTheory.Sheaf
  infer_instance

/-- The constant rational coefficient complex in degree zero. -/
abbrev rationalUnit (Z : TopCat.{0}) : RationalDerived Z :=
  (DerivedCategory.singleFunctor _ 0).obj (rationalConstantSheaf Z)

/-- Rational Betti cohomology as actual derived morphisms. -/
abbrev Cohomology (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  rationalUnit Z ⟶ (rationalUnit Z)⟦n⟧

/-- Its rational module is the module on actual derived morphisms. -/
instance cohomologyModule (Z : TopCat.{0}) (n : ℤ) : Module ℚ (Cohomology Z n) :=
  inferInstanceAs (Module ℚ (rationalUnit Z ⟶ (rationalUnit Z)⟦n⟧))

/-- Cup product in the order given by Yoneda composition. -/
def cup (Z : TopCat.{0}) {i j : ℤ}
    (x : Cohomology Z i) (y : Cohomology Z j) : Cohomology Z (i + j) :=
  x ≫ (shiftFunctor (RationalDerived Z) i).map y ≫
    (shiftFunctorAdd' (RationalDerived Z) j i (i + j)
      (add_comm j i)).inv.app (rationalUnit Z)

/-- The product is rational-linear in its first argument. -/
def cupLeft (Z : TopCat.{0}) {i j : ℤ} (y : Cohomology Z j) :
    Cohomology Z i →ₗ[ℚ] Cohomology Z (i + j) where
  toFun x := cup Z x y
  map_add' x x' := by simp [cup, Preadditive.add_comp]
  map_smul' r x := by simp [cup, Linear.smul_comp]

/-- The product is rational-linear in its second argument. -/
def cupRight (Z : TopCat.{0}) {i j : ℤ} (x : Cohomology Z i) :
    Cohomology Z j →ₗ[ℚ] Cohomology Z (i + j) where
  toFun y := cup Z x y
  map_add' y y' := by simp [cup, Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]
  map_smul' r y := by simp [cup, Functor.map_smul, Linear.comp_smul,
    Linear.smul_comp]

end MathlibExt.AlgebraicGeometry.BettiRealization
