/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseUnitor
public import MathlibExt.Algebra.Homology.GradedTensorTower
public import MathlibExt.Algebra.Homology.TensorUnitor
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The actual same-world chain unit comparison

The canonical UniverseTensor dictionary at offset `u` uses `ULift.{u} R`
as unit even when every coefficient carrier has world `u`. The native
same-world ModuleCat dictionary uses `R`. A type synonym fixes the former
dictionary, and the identity carrier functor to the latter has the actual
single-complex up/down unit isomorphism and identity tensor comparisons.

This earns a comparison of these two dictionaries. It does not enlarge
the coefficient-world signature of the existing Künneth collapse theorem.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ComonObj

namespace HomologicalComplex.HomologyCoalgebra

/-- The existing same-world chain category with the fixed lifted-unit
UniverseTensor dictionary. This is an identity carrier type synonym. -/
def LiftedUnitChain (R : Type u) [CommRing R] := ChainComplex (ModuleCat.{u} R) ℕ

namespace LiftedUnitChain

variable {R : Type u} [CommRing R]


instance category : Category (LiftedUnitChain R) := inferInstanceAs (Category (ChainComplex (ModuleCat.{u} R) ℕ))

instance preadditive : Preadditive (LiftedUnitChain R) := inferInstanceAs (Preadditive (ChainComplex (ModuleCat.{u} R)
  ℕ))

instance monoidalCategory : MonoidalCategory (LiftedUnitChain R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{u} R) := ModuleCat.UniverseTensor.tensorStructure.{u,u} (R := R)
  letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,u} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,u} (R := R)
  letI : MonoidalLinear R (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,u} (R := R)
  exact inferInstanceAs (MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ))

instance tensorStructure : MonoidalCategoryStruct (LiftedUnitChain R) :=
  (monoidalCategory (R := R)).toMonoidalCategoryStruct

/-- The identity carrier functor to the ordinary native same-world chain
category. Its monoidal dictionaries are distinguished by the source synonym. -/
def toNative : LiftedUnitChain R ⥤ (ChainComplex (ModuleCat.{u} R) ℕ) where
  obj C := C
  map f := f

instance toNative_additive : (toNative (R := R)).Additive where
  map_add := by intros; rfl

/-- The actual scalar-unit comparison is the single-complex image of the
native module up/down equivalence. -/
def unitIso : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ≅ toNative.obj (𝟙_ (LiftedUnitChain R)) :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).mapIso
    ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toModuleIso)

/-- The tensor comparison has identity components on the actual ordinary
ring tensor modules, and its differential equation is literal. -/
def tensorIso (C D : LiftedUnitChain R) :
    toNative.obj C ⊗ toNative.obj D ≅ toNative.obj (C ⊗ D) :=
  Iso.refl _

theorem unitIso_inv_zero (r : ULift.{u} R) :
    (unitIso (R := R)).inv.f 0
      ((singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R (ULift.{u} R))).inv r) =
    (singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R R)).inv r.down := by
  have h := congrArg (fun f => f r)
    (singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R (ULift.{u} R))).inv_hom_id
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  simp only [unitIso, Functor.mapIso_inv, single_map_f_self,
    CategoryTheory.comp_apply, h]
  rfl

private theorem source_left_inv (C : LiftedUnitChain R) (n : ℕ) (x : (show ChainComplex (ModuleCat.{u} R) ℕ from C).X
  n) :
    (λ_ C).inv.f n x =
      ιTensorObj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of R (ULift.{u} R))) (toNative.obj C) 0 n n (zero_add n)
        (((singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R (ULift.{u} R))).inv
          (ULift.up (1 : R))) ⊗ₜ[R] x) := by
  letI : MonoidalCategoryStruct (ModuleCat.{u} R) := ModuleCat.UniverseTensor.tensorStructure.{u,u} (R := R)
  letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,u} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,u} (R := R)
  letI : MonoidalLinear R (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,u} (R := R)
  change (HomologicalComplex.leftUnitor' (show ChainComplex (ModuleCat.{u} R) ℕ from C)).inv n x = _
  have hformula := congrArg (fun f => f.hom x)
    (HomologicalComplex.leftUnitor'_inv (show ChainComplex (ModuleCat.{u} R) ℕ from C) n)
  rw [hformula]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.UniverseTensor.hom_whiskerRight]
  rw [ModuleCat.UniverseTensor.leftUnitor_inv_apply.{u,u} R ((show ChainComplex (ModuleCat.{u} R) ℕ from C).X n) x]
  rfl

private theorem source_right_inv (C : LiftedUnitChain R) (n : ℕ) (x : (show ChainComplex (ModuleCat.{u} R) ℕ from C).X
  n) :
    (ρ_ C).inv.f n x =
      ιTensorObj (toNative.obj C) ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of R (ULift.{u} R))) n 0 n (add_zero n)
        (x ⊗ₜ[R] ((singleObjXSelf (ComplexShape.down ℕ) 0
          (ModuleCat.of R (ULift.{u} R))).inv (ULift.up (1 : R)))) := by
  letI : MonoidalCategoryStruct (ModuleCat.{u} R) := ModuleCat.UniverseTensor.tensorStructure.{u,u} (R := R)
  letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,u} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,u} (R := R)
  letI : MonoidalLinear R (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,u} (R := R)
  change (HomologicalComplex.rightUnitor' (show ChainComplex (ModuleCat.{u} R) ℕ from C)).inv n x = _
  have hformula := congrArg (fun f => f.hom x)
    (HomologicalComplex.rightUnitor'_inv (show ChainComplex (ModuleCat.{u} R) ℕ from C) n)
  rw [hformula]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.UniverseTensor.hom_whiskerLeft]
  rw [ModuleCat.UniverseTensor.rightUnitor_inv_apply.{u,u} R ((show ChainComplex (ModuleCat.{u} R) ℕ from C).X n) x]
  rfl

/-- The actual up/down chain unit comparison preserves the native left
unit insertion; the source insertion is `ULift.up 1`. -/
theorem left_unitality_inv (C : LiftedUnitChain R) :
    (λ_ (toNative.obj C)).inv = toNative.map (λ_ C).inv ≫ (tensorIso (𝟙_ _) C).inv ≫
      (unitIso (R := R)).inv ▷ toNative.obj C := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (HomologicalComplex.leftUnitor' (toNative.obj C)).inv n x =
    ((HomologicalComplex.tensorHom (unitIso (R := R)).inv (𝟙 (toNative.obj C))).f n)
      ((λ_ C).inv.f n x)
  have hsource := source_left_inv C n (show (show ChainComplex (ModuleCat.{u} R) ℕ from C).X n from x)
  have hs := congrArg (fun z => ((HomologicalComplex.tensorHom (unitIso (R := R)).inv
    (𝟙 (toNative.obj C))).f n).hom z) hsource
  have ht := congrArg (fun f => f
      (((singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R (ULift.{u} R))).inv
        (ULift.up (1 : R))) ⊗ₜ[R] x))
    (ιTensorObj_tensorHom (unitIso (R := R)).inv (𝟙 (toNative.obj C)) 0 n n (zero_add n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom,
    TensorProduct.map_tmul, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply, unitIso_inv_zero, ULift.down_up] at ht
  let z₀ := (singleObjXSelf (ComplexShape.down ℕ) 0
    (ModuleCat.of R (ULift.{u} R))).inv (ULift.up (1 : R))
  have hz' := TensorProduct.map_tmul ((unitIso (R := R)).inv.f 0).hom
    (LinearMap.id : (toNative.obj C).X n →ₗ[R] (toNative.obj C).X n) z₀ x
  have hzv := hz'.trans
    (congrArg₂ (fun a b => a ⊗ₜ[R] b)
      (unitIso_inv_zero (R := R) (ULift.up (1 : R))) (show x = x from rfl))
  have hLeft := congrArg (fun f => f.hom x)
    (HomologicalComplex.leftUnitor'_inv (toNative.obj C) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_whiskerRight,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, LinearMap.rTensor_tmul] at hLeft
  have hι := congrArg (fun z =>
    (ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) (toNative.obj C)
      0 n n (zero_add n)).hom z) hzv
  exact hLeft.trans (hι.symm.trans (hs.trans ht).symm)

/-- The same actual unit comparison preserves the native right insertion. -/
theorem right_unitality_inv (C : LiftedUnitChain R) :
    (ρ_ (toNative.obj C)).inv = toNative.map (ρ_ C).inv ≫ (tensorIso C (𝟙_ _)).inv ≫
      toNative.obj C ◁ (unitIso (R := R)).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (HomologicalComplex.rightUnitor' (toNative.obj C)).inv n x =
    ((HomologicalComplex.tensorHom (𝟙 (toNative.obj C)) (unitIso (R := R)).inv).f n)
      ((ρ_ C).inv.f n x)
  have hsource := source_right_inv C n (show (show ChainComplex (ModuleCat.{u} R) ℕ from C).X n from x)
  have hs := congrArg (fun z => ((HomologicalComplex.tensorHom (𝟙 (toNative.obj C))
    (unitIso (R := R)).inv).f n).hom z) hsource
  have ht := congrArg (fun f => f
      (x ⊗ₜ[R] ((singleObjXSelf (ComplexShape.down ℕ) 0
        (ModuleCat.of R (ULift.{u} R))).inv (ULift.up (1 : R)))))
    (ιTensorObj_tensorHom (𝟙 (toNative.obj C)) (unitIso (R := R)).inv n 0 n (add_zero n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom,
    TensorProduct.map_tmul, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply, unitIso_inv_zero, ULift.down_up] at ht
  let z₀ := (singleObjXSelf (ComplexShape.down ℕ) 0
    (ModuleCat.of R (ULift.{u} R))).inv (ULift.up (1 : R))
  have hz' := TensorProduct.map_tmul
    (LinearMap.id : (toNative.obj C).X n →ₗ[R] (toNative.obj C).X n)
    ((unitIso (R := R)).inv.f 0).hom x z₀
  have hzv := hz'.trans
    (congrArg₂ (fun a b => a ⊗ₜ[R] b)
      (show x = x from rfl) (unitIso_inv_zero (R := R) (ULift.up (1 : R))))
  have hRight := congrArg (fun f => f.hom x)
    (HomologicalComplex.rightUnitor'_inv (toNative.obj C) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_whiskerLeft,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply, LinearMap.lTensor_tmul] at hRight
  have hι := congrArg (fun z =>
    (ιTensorObj (toNative.obj C) (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
      n 0 n (add_zero n)).hom z) hzv
  exact hRight.trans (hι.symm.trans (hs.trans ht).symm)

private theorem cleanupLeft {A : Type*} [Category A] [MonoidalCategory A]
    (X Y Z : A) :
    𝟙 ((X ⊗ Y) ⊗ Z) ≫ 𝟙 (X ⊗ Y) ▷ Z ≫ (α_ X Y Z).hom =
      (α_ X Y Z).hom := by
  simp only [id_whiskerRight, Category.id_comp]

private theorem cleanupRight {A : Type*} [Category A] [MonoidalCategory A]
    (X Y Z : A) (f : (X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)) :
    f ≫ 𝟙 (X ⊗ (Y ⊗ Z)) ≫ X ◁ 𝟙 (Y ⊗ Z) = f := by
  simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- The identity carrier functor earns its native monoidal structure from
the actual unit comparison and identity tensor components. -/
def monoidal : (toNative (R := R)).Monoidal :=
  (Functor.CoreMonoidal.mk' unitIso tensorIso
    (μIso_inv_natural_left := by
      intros
      apply HomologicalComplex.hom_ext
      intro n
      dsimp only [tensorIso, toNative, HomologicalComplex.comp_f]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (μIso_inv_natural_right := by
      intros
      apply HomologicalComplex.hom_ext
      intro n
      dsimp only [tensorIso, toNative, HomologicalComplex.comp_f]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (oplax_associativity := by
      intro X Y Z
      let aS : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
        (tensorStructure (R := R)).associator X Y Z
      change 𝟙 ((toNative.obj X ⊗ toNative.obj Y) ⊗ toNative.obj Z) ≫
          𝟙 (toNative.obj X ⊗ toNative.obj Y) ▷ toNative.obj Z ≫
          (α_ (toNative.obj X) (toNative.obj Y) (toNative.obj Z)).hom =
        toNative.map aS.hom ≫
          𝟙 (toNative.obj X ⊗ (toNative.obj Y ⊗ toNative.obj Z)) ≫
          toNative.obj X ◁ 𝟙 (toNative.obj Y ⊗ toNative.obj Z)
      have ha : (α_ (toNative.obj X) (toNative.obj Y) (toNative.obj Z)).hom =
          toNative.map aS.hom := by rfl
      exact (cleanupLeft (toNative.obj X) (toNative.obj Y) (toNative.obj Z)).trans
        (ha.trans (cleanupRight (toNative.obj X) (toNative.obj Y)
          (toNative.obj Z) (toNative.map aS.hom)).symm))
    (oplax_left_unitality := left_unitality_inv)
    (oplax_right_unitality := right_unitality_inv)).toMonoidal

/-- The actual source Koszul chain interchange under the fixed lifted-unit
module dictionary. -/
def sourceBraiding (C D : LiftedUnitChain R) : C ⊗ D ≅ D ⊗ C := by
  letI : MonoidalCategoryStruct (ModuleCat.{u} R) := ModuleCat.UniverseTensor.tensorStructure.{u,u} (R := R)
  letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,u} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,u} (R := R)
  letI : MonoidalLinear R (ModuleCat.{u} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,u} (R := R)
  letI : SymmetricCategory (ModuleCat.{u} R) := ModuleCat.UniverseTensor.symmetricCategory.{u,u} (R := R)
  exact HomologicalComplex.koszulTensorBraidingIso
    (show ChainComplex (ModuleCat.{u} R) ℕ from C)
    (show ChainComplex (ModuleCat.{u} R) ℕ from D)

/-- Identity tensor components preserve the actual source and target
Koszul signs; both module interchanges are the original tensor commutation. -/
@[reassoc]
theorem tensorIso_braiding (C D : LiftedUnitChain R) :
    (tensorIso C D).hom ≫ toNative.map (sourceBraiding C D).hom =
      (koszulTensorBraidingIso (toNative.obj C) (toNative.obj D)).hom ≫ (tensorIso D C).hom := by
  change 𝟙 (toNative.obj C ⊗ toNative.obj D) ≫ toNative.map (sourceBraiding C D).hom =
    (koszulTensorBraidingIso (toNative.obj C) (toNative.obj D)).hom ≫
      𝟙 (toNative.obj D ⊗ toNative.obj C)
  have hb : toNative.map (sourceBraiding C D).hom =
      (koszulTensorBraidingIso (toNative.obj C) (toNative.obj D)).hom := by
    unfold sourceBraiding
    rfl
  exact (Category.id_comp _).trans (hb.trans (Category.comp_id _).symm)

/-- Native comonoid transport converts a fixed lifted-unit chain comonoid
to the native same-world dictionary. -/
def nativeComonFunctor : Comon (LiftedUnitChain R) ⥤ Comon (ChainComplex (ModuleCat.{u} R) ℕ) := by
  letI : (toNative (R := R)).Monoidal := monoidal
  exact toNative.mapComon

attribute [local instance] ComonObj.instTensorUnit

/-- The actual up unit comparison is a native comonoid isomorphism from
the native scalar unit to the transported lifted scalar unit. -/
theorem unitIsoIsComonHom :
    letI : (toNative (R := R)).Monoidal := monoidal
    letI : ComonObj (toNative.obj (𝟙_ (LiftedUnitChain R))) :=
      Functor.obj.instComonObj (𝟙_ (LiftedUnitChain R)) toNative
    IsComonHom (unitIso (R := R)).hom := by
  letI : (toNative (R := R)).Monoidal := monoidal
  letI : ComonObj (toNative.obj (𝟙_ (LiftedUnitChain R))) :=
    Functor.obj.instComonObj (𝟙_ (LiftedUnitChain R)) toNative
  exact
    { hom_counit := by
        change unitIso.hom ≫ (toNative.map (𝟙 _) ≫ unitIso.inv) = 𝟙 _
        simp
      hom_comul := by
        change unitIso.hom ≫ toNative.map (λ_ (𝟙_ (LiftedUnitChain R))).inv ≫
          (tensorIso (𝟙_ _) (𝟙_ _)).inv =
          (λ_ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))).inv ≫ (unitIso.hom ⊗ₘ unitIso.hom)
        rw [← Functor.LaxMonoidal.left_unitality_inv]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [leftUnitor_inv_naturality_assoc]
        simp only [Category.assoc, ← tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id, tensorHom_def]
        have hε : Functor.LaxMonoidal.ε (toNative (R := R)) = (unitIso (R := R)).hom := rfl
        have hμ : Functor.LaxMonoidal.μ (toNative (R := R))
            (𝟙_ (LiftedUnitChain R)) (𝟙_ (LiftedUnitChain R)) =
          (tensorIso (𝟙_ (LiftedUnitChain R)) (𝟙_ (LiftedUnitChain R))).hom := rfl
        simp only [hε, hμ, tensorIso, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
        exact congrArg (fun z => (λ_ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))).inv ≫ z)
          (whisker_exchange (unitIso (R := R)).hom (unitIso (R := R)).hom) }

/-- An actual lifted-unit chain coaugmentation becomes an actual native
same-world coaugmentation through the earned up map. -/
def nativeCoaug (C : LiftedUnitChain R) (η : 𝟙_ (LiftedUnitChain R) ⟶ C) :
    𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ toNative.obj C := unitIso.hom ≫ toNative.map η

/-- The converted coaugmentation preserves the actual converted comonoid
structure, without additional coaugmentation-law inputs. -/
theorem nativeCoaugIsComonHom (C : LiftedUnitChain R) [ComonObj C]
    (η : 𝟙_ (LiftedUnitChain R) ⟶ C) [IsComonHom η] :
    letI : (toNative (R := R)).Monoidal := monoidal
    letI : ComonObj (toNative.obj C) := Functor.obj.instComonObj C toNative
    IsComonHom (nativeCoaug C η) := by
  letI : (toNative (R := R)).Monoidal := monoidal
  letI : ComonObj (toNative.obj (𝟙_ (LiftedUnitChain R))) :=
    Functor.obj.instComonObj (𝟙_ (LiftedUnitChain R)) toNative
  letI : ComonObj (toNative.obj C) := Functor.obj.instComonObj C toNative
  letI : IsComonHom (unitIso (R := R)).hom := unitIsoIsComonHom (R := R)
  letI : IsComonHom (toNative.map η) := Functor.map.instIsComon_Hom toNative η
  unfold nativeCoaug
  infer_instance

/-- The native same-world scalar unit is explicitly up/down, including on
the original degree-zero scalar coordinate. -/
theorem unitIso_inv_zero_coordinate :
    (unitIso (R := R)).inv.f 0 =
      (singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R (ULift.{u} R))).hom ≫
        ModuleCat.ofHom (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap ≫
          (singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R R)).inv := by
  simp only [unitIso, Functor.mapIso_inv, single_map_f_self]
  rfl

end LiftedUnitChain

end HomologicalComplex.HomologyCoalgebra
