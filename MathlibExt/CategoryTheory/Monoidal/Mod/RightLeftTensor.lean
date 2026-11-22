/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ScalarUnitTensor

/-!
Actual noncommutative right-left module tensor functors.

All objects and maps below use the existing monadic balanced tensor. The
standard right-module carrier is `Mod (D := C) (mop A)`. In particular no
commutative conversion, supplied quotient, or model conclusion is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The unwrapped original right module action. -/
abbrev rightAction (N : RightModuleFree.Carrier A) : N.X ⊗ A ⟶ N.X := N.mod.smul

theorem rightAction_unit (N : RightModuleFree.Carrier A) :
    (N.X ◁ η[A]) ≫ rightAction N = (ρ_ N.X).hom := by
  exact ModObj.one_smul (M := MonoidalOpposite.mop A) N.X

theorem rightAction_assoc (N : RightModuleFree.Carrier A) :
    (α_ N.X A A).hom ≫ (N.X ◁ μ[A]) ≫ rightAction N =
      (rightAction N ▷ A) ≫ rightAction N := by
  have h := ModObj.mul_smul (M := MonoidalOpposite.mop A) N.X
  change (N.X ◁ μ[A]) ≫ rightAction N =
    (α_ N.X A A).inv ≫ (rightAction N ▷ A) ≫ rightAction N at h
  rw [h, Iso.hom_inv_id_assoc]

theorem rightAction_map {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    (f.hom ▷ A) ≫ rightAction N' = rightAction N ≫ f.hom := by
  exact (IsModHom.smul_hom (A := MonoidalOpposite.mop A) (f := f.hom)).symm

/-- The existing tensor monad module of an actual standard right module. -/
def rightMonad (N : RightModuleFree.Carrier A) : Monad.RightModule (Monad.tensorMonad A) C :=
  Monad.rightModuleOfRightAction N.X A (rightAction N)
    (rightAction_unit N) (rightAction_assoc N)

/-- This is the original underlying tensor functor, with its original action. -/
theorem rightMonad_functor (N : RightModuleFree.Carrier A) :
    (rightMonad N).functor = tensorLeft N.X := rfl

theorem rightMonad_action (N : RightModuleFree.Carrier A) (X : C) :
    (rightMonad N).action.app X =
      (α_ N.X A X).inv ≫ (rightAction N ▷ X) := rfl

/-- Actual right module morphisms induce the already defined compatible monadic maps. -/
def rightMonadMap {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    rightMonad N ⟶ rightMonad N' :=
  Monad.rightModuleHomOfRightComp f.hom (rightAction_map f)

theorem rightMonadMap_app {N N' : RightModuleFree.Carrier A}
    (f : N ⟶ N') (X : C) : (rightMonadMap f).f.app X = f.hom ▷ X := rfl

@[simp] theorem rightMonadMap_id (N : RightModuleFree.Carrier A) :
    rightMonadMap (𝟙 N) = 𝟙 (rightMonad N) := by
  ext X
  change (𝟙 N.X) ▷ X = 𝟙 (N.X ⊗ X)
  exact id_whiskerRight N.X X

theorem rightMonadMap_comp {N N' N'' : RightModuleFree.Carrier A}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    rightMonadMap (f ≫ g) = rightMonadMap f ≫ rightMonadMap g := by
  ext X
  change (f.hom ≫ g.hom) ▷ X = (f.hom ▷ X) ≫ (g.hom ▷ X)
  exact comp_whiskerRight f.hom g.hom X

/-- The original carrier/action conversion is functorial on all right modules. -/
def rightMonadic : RightModuleFree.Carrier A ⥤ Monad.RightModule (Monad.tensorMonad A) C where
  obj := rightMonad
  map := rightMonadMap
  map_id := rightMonadMap_id
  map_comp := rightMonadMap_comp

/-- The original left module, placed at the terminal indexing category. -/
abbrev leftMonad (M : Mod C A) := CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.inputModule M

/-- The monad map induced by the original left-module action. -/
def leftMonadMap {M M' : Mod C A} (f : M ⟶ M') : leftMonad M ⟶ leftMonad M' :=
  Monad.leftPointModuleHomOfIsModHom f.hom

theorem leftMonadMap_app {M M' : Mod C A} (f : M ⟶ M')
    (a : Discrete PUnit.{1}) : (leftMonadMap f).f.app a = f.hom := rfl

@[simp] theorem leftMonadMap_id (M : Mod C A) :
    leftMonadMap (𝟙 M) = 𝟙 (leftMonad M) :=
  Monad.leftPointModuleHomOfIsModHom_id A M.X

theorem leftMonadMap_comp {M M' M'' : Mod C A} (f : M ⟶ M') (g : M' ⟶ M'') :
    leftMonadMap (f ≫ g) = leftMonadMap f ≫ leftMonadMap g :=
  (Monad.leftPointModuleHomOfIsModHom_comp f.hom g.hom).symm

section Tensor

variable [HasColimitsOfSize.{0, 0} C]

/-- The actual balanced right-left tensor, evaluated at the unique index. -/
abbrev tensorObject (N : RightModuleFree.Carrier A) (M : Mod C A) : C :=
  (Monad.monoidalBalancedTensor N.X A M.X (rightAction N)
    (rightAction_unit N) (rightAction_assoc N)).obj CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point

/-- The original degree-zero quotient map, before imposing either action. -/
abbrev projection (N : RightModuleFree.Carrier A) (M : Mod C A) :
    N.X ⊗ M.X ⟶ tensorObject N M :=
  (Monad.balancedTensorπ (Monad.tensorMonad A) (rightMonad N) (leftMonad M)).app
    CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point

/-- The map of actual coequalizers induced by the two original module maps. -/
def tensorMap {N N' : RightModuleFree.Carrier A} {M M' : Mod C A}
    (f : N ⟶ N') (g : M ⟶ M') : tensorObject N M ⟶ tensorObject N' M' :=
  (Monad.balancedTensorMap (rightMonadMap f) (leftMonadMap g)).app
    CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point

theorem tensorMap_projection {N N' : RightModuleFree.Carrier A} {M M' : Mod C A}
    (f : N ⟶ N') (g : M ⟶ M') :
    projection N M ≫ tensorMap f g = (f.hom ⊗ₘ g.hom) ≫ projection N' M' := by
  have h := congrArg (fun f => f.app CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point)
    (Monad.balancedTensorMap_π (rightMonadMap f) (leftMonadMap g))
  change projection N M ≫ tensorMap f g =
    (Monad.barMap (rightMonadMap f) (leftMonadMap g) 0).app CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point ≫
      projection N' M' at h
  change projection N M ≫ tensorMap f g =
    ((N.X ◁ g.hom) ≫ (f.hom ▷ M'.X)) ≫ projection N' M' at h
  simpa only [tensorHom_def'] using h

@[simp] theorem tensorMap_id (N : RightModuleFree.Carrier A) (M : Mod C A) :
    tensorMap (𝟙 N) (𝟙 M) = 𝟙 (tensorObject N M) := by
  unfold tensorMap
  rw [rightMonadMap_id, leftMonadMap_id, Monad.balancedTensorMap_id]
  rfl

theorem tensorMap_comp {N N' N'' : RightModuleFree.Carrier A} {M M' M'' : Mod C A}
    (f : N ⟶ N') (f' : N' ⟶ N'') (g : M ⟶ M') (g' : M' ⟶ M'') :
    tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g' := by
  unfold tensorMap
  rw [rightMonadMap_comp, leftMonadMap_comp, ← Monad.balancedTensorMap_comp]
  rfl

/-- Relative tensor with a fixed actual left module, on every right coefficient. -/
def rightTensorFunctor (M : Mod C A) : RightModuleFree.Carrier A ⥤ C where
  obj N := tensorObject N M
  map f := tensorMap f (𝟙 M)
  map_id N := tensorMap_id N M
  map_comp f g := by
    simpa only [Category.id_comp] using tensorMap_comp f g (𝟙 M) (𝟙 M)

/-- Relative tensor with a fixed actual right coefficient, on every left module. -/
def leftTensorFunctor (N : RightModuleFree.Carrier A) : Mod C A ⥤ C where
  obj M := tensorObject N M
  map g := tensorMap (𝟙 N) g
  map_id M := tensorMap_id N M
  map_comp f g := by
    simpa only [Category.id_comp] using tensorMap_comp (𝟙 N) (𝟙 N) f g

theorem rightTensorFunctor_projection (M : Mod C A)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    projection N M ≫ (rightTensorFunctor M).map f =
      (f.hom ▷ M.X) ≫ projection N' M := by
  change projection N M ≫ tensorMap f (𝟙 M) = _
  simpa only [Mod.id_hom', tensorHom_def, whiskerLeft_id, Category.comp_id] using
    tensorMap_projection f (𝟙 M)

theorem leftTensorFunctor_projection (N : RightModuleFree.Carrier A)
    {M M' : Mod C A} (g : M ⟶ M') :
    projection N M ≫ (leftTensorFunctor N).map g =
      (N.X ◁ g.hom) ≫ projection N M' := by
  change projection N M ≫ tensorMap (𝟙 N) g = _
  simpa only [Mod.id_hom', tensorHom_def', id_whiskerRight, Category.comp_id] using
    tensorMap_projection (𝟙 N) g

/-- The same bifunctor is functorial in the left module without changing any quotient. -/
def rightTensorNatural {M M' : Mod C A} (g : M ⟶ M') :
    rightTensorFunctor M ⟶ rightTensorFunctor M' where
  app N := tensorMap (𝟙 N) g
  naturality N N' f := by
    change tensorMap f (𝟙 M) ≫ tensorMap (𝟙 N') g =
      tensorMap (𝟙 N) g ≫ tensorMap f (𝟙 M')
    rw [← tensorMap_comp, ← tensorMap_comp]
    simp only [Category.comp_id, Category.id_comp]

/-- Functorial variation in right coefficients retains the complete left functor. -/
def leftTensorNatural {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    leftTensorFunctor N ⟶ leftTensorFunctor N' where
  app M := tensorMap f (𝟙 M)
  naturality M M' g := by
    change tensorMap (𝟙 N) g ≫ tensorMap f (𝟙 M') =
      tensorMap f (𝟙 M) ≫ tensorMap (𝟙 N') g
    rw [← tensorMap_comp, ← tensorMap_comp]
    simp only [Category.comp_id, Category.id_comp]

section Scalar

variable {B : C} [MonObj B]

omit [HasColimitsOfSize.{0, 0} C] in
theorem scalar_rightMonad (p : A ⟶ B) [IsMonHom p] :
    rightMonad (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficient p) =
      CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.coefficientModule p :=
  rfl

omit [HasColimitsOfSize.{0, 0} C] in
theorem scalar_rightMonadMap (p : A ⟶ B) [IsMonHom p] :
    rightMonadMap (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficientMap p) =
      CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.coefficientMap p :=
  rfl

/-- The general tensor object at a scalar bimodule is the already normalized original object. -/
theorem scalar_tensorObject (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    tensorObject (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficient p) M =
      CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.tensorObject p M :=
  rfl

/-- The relative tensor functor specializes to the actual original scalar coefficient map. -/
theorem scalar_rightTensorFunctor_map (p : A ⟶ B) [IsMonHom p] (M : Mod C A) :
    (rightTensorFunctor M).map (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficientMap p) =
      CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.tensorMap p M := by
  change (Monad.balancedTensorMap
    (rightMonadMap (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficientMap p)) (leftMonadMap (𝟙 M))).app
    CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point = _
  rw [leftMonadMap_id]
  rfl

end Scalar
end Tensor
end CategoryTheory.Mod.RightLeftTensor
