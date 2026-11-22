/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.Basic
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoidFunctor
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ModuleGeneratorLaws
import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation

/-!
# Modules and the sphere on the existing generic symmetric-spectrum carrier

The sphere Day monoid constructed from `T` supplies the scalar object of the
existing `SymmetricSpectrum` carrier. Its regular module is the sphere spectrum.
The complete level actions and module morphisms use the actual Day generators.
Free at an index and evaluation use the `CategoryTheory.Mod.day*` API.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The constructed sphere monoid belongs to the unchanged generic sequence carrier. -/
def genericSphereMonoidOnSymmetricSequence (T : V) : CommMon (SymmetricSequence V) :=
  genericSphereDayMonoid T

/-- The actual regular sphere module on the existing generic spectrum carrier. -/
def genericSphereSpectrum (T : V) : SymmetricSpectrum (genericSphereDayMonoid T) :=
  Mod.regular (genericSphereDayMonoid T).X

/-- The regular sphere has the full original sphere sequence as its carrier. -/
theorem genericSphereSpectrum_carrier (T : V) :
    (genericSphereSpectrum T).X = (genericSphereDayMonoid T).X := rfl

/-- Every sphere-spectrum level is the original ordered tensor power. -/
theorem genericSphereSpectrum_level (T : V) (A : I) :
    (genericSphereSpectrum T).X.functor.obj A = tensorPowObj T A.of.len := rfl

/-- The regular sphere's action is precisely its constructed Day multiplication. -/
theorem genericSphereSpectrum_action (T : V) :
    (genericSphereSpectrum T).mod.smul = (genericSphereDayMonoid T).mon.mul := rfl

/-- Construct an existing spectrum from its whole Day action and the two module equations. -/
def genericSpectrumOfAction (T : V) (X : SymmetricSequence V)
    (a : (genericSphereDayMonoid T).X ⊗ X ⟶ X)
    (hunit : (genericSphereDayMonoid T).mon.one ▷ X ≫ a = (λ_ X).hom)
    (hmul : (genericSphereDayMonoid T).mon.mul ▷ X ≫ a =
      (α_ (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X X).hom ≫
        (genericSphereDayMonoid T).X ◁ a ≫ a) :
    SymmetricSpectrum (genericSphereDayMonoid T) where
  X := X
  mod := { smul := a, one_smul := hunit, mul_smul := hmul }

/-- The action constructor preserves its entire supplied sequence. -/
theorem genericSpectrumOfAction_carrier (T : V) (X : SymmetricSequence V)
    (a : (genericSphereDayMonoid T).X ⊗ X ⟶ X)
    (hunit : (genericSphereDayMonoid T).mon.one ▷ X ≫ a = (λ_ X).hom)
    (hmul : (genericSphereDayMonoid T).mon.mul ▷ X ≫ a =
      (α_ (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X X).hom ≫
        (genericSphereDayMonoid T).X ◁ a ≫ a) :
    (genericSpectrumOfAction T X a hunit hmul).X = X := rfl

/-- The action constructor preserves its actual supplied action. -/
theorem genericSpectrumOfAction_smul (T : V) (X : SymmetricSequence V)
    (a : (genericSphereDayMonoid T).X ⊗ X ⟶ X)
    (hunit : (genericSphereDayMonoid T).mon.one ▷ X ≫ a = (λ_ X).hom)
    (hmul : (genericSphereDayMonoid T).mon.mul ▷ X ≫ a =
      (α_ (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X X).hom ≫
        (genericSphereDayMonoid T).X ◁ a ≫ a) :
    (genericSpectrumOfAction T X a hunit hmul).mod.smul = a := rfl

/-- The coefficient-first action at every pair of finite indices. -/
def genericSpectrumPairAction (T : V) (M : SymmetricSpectrum (genericSphereDayMonoid T))
    (A B : I) :
    (genericSphereDayMonoid T).X.functor.obj A ⊗ M.X.functor.obj B ⟶
      M.X.functor.obj (A ⊗ B) :=
  (DayFunctor.η (genericSphereDayMonoid T).X M.X).app (A, B) ≫
    M.mod.smul.natTrans.app (A ⊗ B)

/-- Every finite output label is retained after the whole pair action. -/
def genericSpectrumArrowAction (T : V) (M : SymmetricSpectrum (genericSphereDayMonoid T))
    (A B : I) {C : I} (f : A ⊗ B ⟶ C) :
    (genericSphereDayMonoid T).X.functor.obj A ⊗ M.X.functor.obj B ⟶ M.X.functor.obj C :=
  genericSpectrumPairAction T M A B ≫ M.X.functor.map f

/-- The pair action is natural in both full finite-index arrows. -/
theorem genericSpectrumPairAction_natural (T : V)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) {A A' B B' : I}
    (f : A ⟶ A') (g : B ⟶ B') :
    ((genericSphereDayMonoid T).X.functor.map f ⊗ₘ M.X.functor.map g) ≫
      genericSpectrumPairAction T M A' B' =
    genericSpectrumPairAction T M A B ≫ M.X.functor.map (f ⊗ₘ g) := by
  have hη := (DayFunctor.η (genericSphereDayMonoid T).X M.X).naturality
    ((f, g) : (A, B) ⟶ (A', B'))
  simp only [externalProductBifunctor_obj_map, Functor.comp_map,
    tensor_map, ← tensorHom_def] at hη
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ M.mod.smul.natTrans.app (A' ⊗ B')) hη).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t =>
          (DayFunctor.η (genericSphereDayMonoid T).X M.X).app (A, B) ≫ t)
          (M.mod.smul.natTrans.naturality (f ⊗ₘ g))).trans (Category.assoc _ _ _).symm)))

/-- The actual empty sphere block acts through the original two unitors. -/
theorem genericSpectrumPairAction_unit (T : V)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) (A : I) :
    genericSpectrumPairAction T M (𝟙_ I) A =
      (λ_ (M.X.functor.obj A)).hom ≫ M.X.functor.map (λ_ A).inv := by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.modulePairUnit
    (C₀ := I) (V₀ := V) (D₀ := DayFunctor I V)
    (genericSphereDayMonoid T).X M.X A
  change ((DayFunctor.ν I V ≫ (genericSphereDayMonoid T).mon.one.natTrans.app (𝟙_ I)) ▷
      M.X.functor.obj A) ≫ genericSpectrumPairAction T M (𝟙_ I) A =
    (λ_ (M.X.functor.obj A)).hom ≫ M.X.functor.map (λ_ A).inv at h
  have hi := congrArg (fun t => (t ▷ M.X.functor.obj A) ≫
      genericSpectrumPairAction T M (𝟙_ I) A) (genericSphereDayMonoid_unit T)
  have hz : (𝟙 (𝟙_ V) ▷ M.X.functor.obj A) ≫
      genericSpectrumPairAction T M (𝟙_ I) A = genericSpectrumPairAction T M (𝟙_ I) A :=
    (congrArg (fun t => t ≫ genericSpectrumPairAction T M (𝟙_ I) A)
      (id_whiskerRight (𝟙_ V) (M.X.functor.obj A))).trans (Category.id_comp _)
  exact hz.symm.trans (hi.symm.trans h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- All sphere blocks act associatively through the original power and index associators. -/
theorem genericSpectrumPairAction_assoc (T : V)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) (A B C : I) :
    (tensorPowObj_add T A.of.len B.of.len).inv ▷ M.X.functor.obj C ≫
      genericSpectrumPairAction T M (A ⊗ B) C =
    (α_ ((genericSphereDayMonoid T).X.functor.obj A)
      ((genericSphereDayMonoid T).X.functor.obj B) (M.X.functor.obj C)).hom ≫
      (genericSphereDayMonoid T).X.functor.obj A ◁ genericSpectrumPairAction T M B C ≫
      genericSpectrumPairAction T M A (B ⊗ C) ≫ M.X.functor.map (α_ A B C).inv := by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.modulePairMul
    (C₀ := I) (V₀ := V) (D₀ := DayFunctor I V)
    (genericSphereDayMonoid T).X M.X A B C
  have hμ := congrArg (fun t => (t ▷ M.X.functor.obj C) ≫
      genericSpectrumPairAction T M (A ⊗ B) C)
    (genericSphereDayMonoid_multiplication T A B)
  have hιobj (F : DayFunctor I V) :
      (LawfulDayConvolutionMonoidalCategoryStruct.ι I V (DayFunctor I V)).obj F = F.functor := rfl
  have hιmap {F G : DayFunctor I V} (f : F ⟶ G) :
      (LawfulDayConvolutionMonoidalCategoryStruct.ι I V (DayFunctor I V)).map f = f.natTrans := rfl
  have h' :
      ((DayFunctor.η (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X).app (A, B) ≫
        (genericSphereDayMonoid T).mon.mul.natTrans.app (A ⊗ B)) ▷ M.X.functor.obj C ≫
        genericSpectrumPairAction T M (A ⊗ B) C =
      (α_ ((genericSphereDayMonoid T).X.functor.obj A)
        ((genericSphereDayMonoid T).X.functor.obj B) (M.X.functor.obj C)).hom ≫
        (genericSphereDayMonoid T).X.functor.obj A ◁ genericSpectrumPairAction T M B C ≫
        genericSpectrumPairAction T M A (B ⊗ C) ≫ M.X.functor.map (α_ A B C).inv := by
    simpa only [genericSpectrumPairAction, DayFunctor.η, hιobj, hιmap, Category.assoc] using! h
  exact hμ.symm.trans h'

/-- Every original spectrum morphism intertwines all whole pair actions. -/
theorem genericSpectrumPairAction_morphism (T : V)
    {M N : SymmetricSpectrum (genericSphereDayMonoid T)} (f : M ⟶ N) (A B : I) :
    genericSpectrumPairAction T M A B ≫ f.hom.natTrans.app (A ⊗ B) =
      ((genericSphereDayMonoid T).X.functor.obj A ◁ f.hom.natTrans.app B) ≫
        genericSpectrumPairAction T N A B := by
  have hc := congrArg (fun t =>
      (DayFunctor.η (genericSphereDayMonoid T).X M.X).app (A, B) ≫
        t.natTrans.app (A ⊗ B))
    (IsModHom.smul_hom (A := (genericSphereDayMonoid T).X) (f := f.hom))
  have hη := DayFunctor.tensorHom_η (𝟙 (genericSphereDayMonoid T).X) f.hom A B
  simp only [DayFunctor.id_natTrans, NatTrans.id_app, id_tensorHom] at hη
  exact (Category.assoc _ _ _).trans
    (hc.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ N.mod.smul.natTrans.app (A ⊗ B)) hη).trans
        (Category.assoc _ _ _))))

/-- The sphere's full pair action is the original ordered tensor-power comparison. -/
theorem genericSphereSpectrum_pairAction (T : V) (A B : I) :
    genericSpectrumPairAction T (genericSphereSpectrum T) A B =
      (tensorPowObj_add T A.of.len B.of.len).inv :=
  genericSphereDayMonoid_multiplication T A B

/-- All finite levels determine a spectrum morphism on the unchanged module carrier. -/
theorem genericSpectrumHom_ext (T : V)
    {M N : SymmetricSpectrum (genericSphereDayMonoid T)} (f g : M ⟶ N)
    (h : ∀ A : I, f.hom.natTrans.app A = g.hom.natTrans.app A) : f = g := by
  apply Mod.hom_ext f g
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext A
  exact h A

/-- The actual free-at-index spectrum functor using the constructed sphere monoid. -/
def genericSpectrumFreeAt (T : V) (A : I) : V ⥤ SymmetricSpectrum (genericSphereDayMonoid T) :=
  Mod.dayFreeAt (genericSphereDayMonoid T).X A

/-- The actual level-evaluation functor on this same spectrum carrier. -/
def genericSpectrumEvaluation (T : V) (A : I) : SymmetricSpectrum (genericSphereDayMonoid T) ⥤ V :=
  Mod.dayEvaluation (genericSphereDayMonoid T).X A

/-- Evaluation retains every original level object. -/
theorem genericSpectrumEvaluation_obj (T : V) (A : I)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) :
    (genericSpectrumEvaluation T A).obj M = M.X.functor.obj A := rfl

/-- Evaluation retains every original spectrum morphism component. -/
theorem genericSpectrumEvaluation_map (T : V) (A : I)
    {M N : SymmetricSpectrum (genericSphereDayMonoid T)} (f : M ⟶ N) :
    (genericSpectrumEvaluation T A).map f = f.hom.natTrans.app A := rfl

/-- Free-at-index and evaluation are genuinely adjoint on the constructed sphere-module carrier. -/
def genericSpectrumFreeAtEvaluationAdjunction (T : V) (A : I) :
    genericSpectrumFreeAt T A ⊣ genericSpectrumEvaluation T A :=
  Mod.dayFreeAtEvaluationAdjunction (genericSphereDayMonoid T).X A

/-- The full adjunction's left triangle holds at every base object and finite index. -/
theorem genericSpectrumFreeAtEvaluation_left_triangle (T : V) (A : I) (X : V) :
    (genericSpectrumFreeAt T A).map
        ((genericSpectrumFreeAtEvaluationAdjunction T A).unit.app X) ≫
      (genericSpectrumFreeAtEvaluationAdjunction T A).counit.app
        ((genericSpectrumFreeAt T A).obj X) =
      𝟙 ((genericSpectrumFreeAt T A).obj X) :=
  (genericSpectrumFreeAtEvaluationAdjunction T A).left_triangle_components X

/-- The full adjunction's right triangle holds at every spectrum and finite index. -/
theorem genericSpectrumFreeAtEvaluation_right_triangle (T : V) (A : I)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) :
    (genericSpectrumFreeAtEvaluationAdjunction T A).unit.app
        ((genericSpectrumEvaluation T A).obj M) ≫
      (genericSpectrumEvaluation T A).map
        ((genericSpectrumFreeAtEvaluationAdjunction T A).counit.app M) =
      𝟙 ((genericSpectrumEvaluation T A).obj M) :=
  (genericSpectrumFreeAtEvaluationAdjunction T A).right_triangle_components M

end CategoryTheory
