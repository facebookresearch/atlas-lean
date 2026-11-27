/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
public import MathlibExt.CategoryTheory.AdjunctionLinear

/-!
# Native Betti cohomology with a specified coefficient field

This extends the completed rational Betti constructions to the same
native sheaf and derived-category operations over any coefficient field.
The coefficient unit is the actual constant sheaf. Cups are shifted
composition, and pullback is the native exact inverse image with the
constant-sheaf adjunction comparison.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoefficientBettiModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Opposite
open ConstructibleComplexes
attribute [local instance] HasDerivedCategory.standard

variable (k : Type) [Field k]

instance sheafLinear (Z : TopCat.{0}) : Linear k (CoefficientSheaf k Z) := by
  change Linear k (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k))
  unfold CategoryTheory.Sheaf
  infer_instance

abbrev constant (Z : TopCat.{0}) : ModuleCat.{0} k ⥤ CoefficientSheaf k Z :=
  constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)

abbrev coefficientUnit (Z : TopCat.{0}) : CoefficientDerived k Z :=
  (DerivedCategory.singleFunctor _ 0).obj ((constant k Z).obj (ModuleCat.of k k))

abbrev Cohomology (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  coefficientUnit k Z ⟶ (coefficientUnit k Z)⟦n⟧

instance cohomologyModule (Z : TopCat.{0}) (n : ℤ) : Module k (Cohomology k Z n) :=
  inferInstanceAs (Module k (coefficientUnit k Z ⟶ (coefficientUnit k Z)⟦n⟧))

instance directImageLinear {Z W : TopCat.{0}} (f : Z ⟶ W) :
    Functor.Linear k (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f) where
  map_smul _a _r := rfl

/-- The native inverse image is linear by its actual adjunction with direct image. -/
instance inverseImageSheafLinear {Z W : TopCat.{0}} (f : Z ⟶ W) :
    Functor.Linear k (pullback k f) :=
  MathlibExt.CategoryTheory.linear_leftAdjoint k
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f)

def unitClass (Z : TopCat.{0}) : Cohomology k Z 0 :=
  (shiftFunctorZero (CoefficientDerived k Z) ℤ).inv.app (coefficientUnit k Z)

def cup (Z : TopCat.{0}) {i j : ℤ} (x : Cohomology k Z i) (y : Cohomology k Z j) :
    Cohomology k Z (i+j) :=
  x ≫ (shiftFunctor (CoefficientDerived k Z) i).map y ≫
    (shiftFunctorAdd' (CoefficientDerived k Z) j i (i+j) (add_comm j i)).inv.app
      (coefficientUnit k Z)

/-- Cup is an actual bilinear map, with the original native Yoneda product. -/
def cupBilinear (Z : TopCat.{0}) (i j : ℤ) :
    Cohomology k Z i →ₗ[k] Cohomology k Z j →ₗ[k] Cohomology k Z (i+j) where
  toFun x := {
    toFun := cup k Z x
    map_add' y y' := by simp [cup, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
    map_smul' r y := by simp [cup, Functor.map_smul, Linear.comp_smul, Linear.smul_comp] }
  map_add' x x' := by ext y; simp [cup, Preadditive.add_comp]
  map_smul' r x := by ext y; simp [cup, Linear.smul_comp]

def constantPullbackIso {Z W : TopCat.{0}} (f : Z ⟶ W) :
    constant k W ⋙ pullback k f ≅ constant k Z := by
  let a := (constantSheafAdj (Opens.grothendieckTopology W) (ModuleCat.{0} k)
    (isTerminalTop (α := Opens W))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f)
  let b := constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} k)
    (isTerminalTop (α := Opens Z))
  exact a.leftAdjointUniq b

def unitInverseImageIso {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback k f).obj (coefficientUnit k W) ≅ coefficientUnit k Z :=
  ((pullback k f).mapDerivedCategorySingleFunctor 0).app ((constant k W).obj (ModuleCat.of k k)) ≪≫
    (DerivedCategory.singleFunctor (CoefficientSheaf k Z) 0).mapIso
      ((constantPullbackIso k f).app (ModuleCat.of k k))

instance inverseImageCommShift {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback k f).CommShift ℤ := by
  dsimp [derivedPullback]
  infer_instance

instance inverseImageAdditive {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (derivedPullback k f).Additive := by
  dsimp [derivedPullback]
  infer_instance

instance inverseImageLinear {Z W : TopCat.{0}} (f : Z ⟶ W) :
    Functor.Linear k (derivedPullback k f) := by
  dsimp [derivedPullback]
  infer_instance

/-- Pullback on actual derived morphisms uses the exact prescribed coefficient comparison. -/
def cohomologyPullback {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℤ) :
    Cohomology k W n →ₗ[k] Cohomology k Z n where
  toFun a := (unitInverseImageIso k f).inv ≫ (derivedPullback k f).map a ≫
    ((derivedPullback k f).commShiftIso n).hom.app (coefficientUnit k W) ≫
      (shiftFunctor (CoefficientDerived k Z) n).map (unitInverseImageIso k f).hom
  map_add' a b := by simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r a := by simp [Functor.map_smul, Linear.comp_smul, Linear.smul_comp]

/-- Pullback preserves the unit class. -/
theorem cohomologyPullback_unitClass {Z W : TopCat.{0}} (f : Z ⟶ W) :
    cohomologyPullback k f 0 (unitClass k W) = unitClass k Z := by
  simp only [cohomologyPullback, unitClass, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Functor.commShiftIso_zero]
  simp [Functor.CommShift.isoZero]
  have hn := (shiftFunctorZero (CoefficientDerived k Z) ℤ).inv.naturality
    (unitInverseImageIso k f).hom
  simp only [Functor.id_obj, Functor.id_map] at hn
  rw [← hn, Iso.inv_hom_id_assoc]

end MathlibExt.AlgebraicGeometry.CoefficientBettiModels
