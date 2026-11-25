/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Integral Betti cohomology with its fixed Yoneda cup product

The coefficient object is the actual constant integer sheaf in the actual
derived category of integer-module sheaves on a given topological space.
Cohomology is its shifted endomorphism module. Cup product is actual
shifted composition, with both integer-linear maps proved.

Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, Section2.6.
These are integral versions of the existing rational Betti definitions;
no rationalization, free cohomology carrier or chosen pairing is supplied.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralBetti

open CategoryTheory CategoryTheory.Limits TopCat

attribute [local instance] HasDerivedCategory.standard

abbrev IntegerSheaf (Z : TopCat.{0}) := TopCat.Sheaf (ModuleCat.{0} ℤ) Z
abbrev IntegerDerived (Z : TopCat.{0}) := DerivedCategory (IntegerSheaf Z)

instance integerSheafLinear (Z : TopCat.{0}) : Linear ℤ (IntegerSheaf Z) := by
  change Linear ℤ (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℤ))
  unfold CategoryTheory.Sheaf
  infer_instance

/-- The actual constant integer coefficient sheaf. -/
abbrev integerConstantSheaf (Z : TopCat.{0}) : IntegerSheaf Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

abbrev integerUnit (Z : TopCat.{0}) : IntegerDerived Z :=
  (DerivedCategory.singleFunctor _ 0).obj (integerConstantSheaf Z)

abbrev Cohomology (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  integerUnit Z ⟶ (integerUnit Z)⟦n⟧

instance cohomologyModule (Z : TopCat.{0}) (n : ℤ) : Module ℤ (Cohomology Z n) :=
  inferInstanceAs (Module ℤ (integerUnit Z ⟶ (integerUnit Z)⟦n⟧))

/-- Integral cup product is the actual shifted Yoneda composition. -/
def cup (Z : TopCat.{0}) {i j : ℤ}
    (x : Cohomology Z i) (y : Cohomology Z j) : Cohomology Z (i + j) :=
  x ≫ (shiftFunctor (IntegerDerived Z) i).map y ≫
    (shiftFunctorAdd' (IntegerDerived Z) j i (i + j) (add_comm j i)).inv.app (integerUnit Z)

def cupLeft (Z : TopCat.{0}) {i j : ℤ} (y : Cohomology Z j) :
    Cohomology Z i →ₗ[ℤ] Cohomology Z (i + j) where
  toFun x := cup Z x y
  map_add' x x' := by simp [cup, Preadditive.add_comp]
  map_smul' r x := by simp [cup, Linear.smul_comp]

def cupRight (Z : TopCat.{0}) {i j : ℤ} (x : Cohomology Z i) :
    Cohomology Z j →ₗ[ℤ] Cohomology Z (i + j) where
  toFun y := cup Z x y
  map_add' y y' := by simp [cup, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r y := by simp [cup, Functor.map_smul, Linear.comp_smul, Linear.smul_comp]

end MathlibExt.AlgebraicGeometry.IntegralBetti
