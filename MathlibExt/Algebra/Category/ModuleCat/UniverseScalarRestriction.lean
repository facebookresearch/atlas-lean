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

public import MathlibExt.Algebra.Category.ModuleCat.RingEquivTensorUniverse
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Scalar restriction from a lifted ring

For a ring in universe `u`, its lift to universe `max u v` permits the
native tensor structure there. Scalar restriction transports that structure
to modules over the original ring. The unit is the lifted ring, and the
unit comparison uses the canonical linear equivalence of its carrier.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]

/-- The actual coefficient ring in the actual common carrier world. -/
abbrev LiftedRing : Type (max u v) := ULift.{v} R

/-- The original scalar module category with the fixed offset-v unit dictionary. -/
def Modules := ModuleCat.{max u v} R


instance category : Category (Modules.{u,v} R) := inferInstanceAs (Category (ModuleCat.{max u v} R))
instance coeSort : CoeSort (Modules.{u,v} R) (Type (max u v)) :=
  ⟨fun M => (show ModuleCat.{max u v} R from M).carrier⟩
instance addCommGroup (M : Modules.{u,v} R) : AddCommGroup M :=
  (show ModuleCat.{max u v} R from M).isAddCommGroup
instance module (M : Modules.{u,v} R) : Module R M :=
  (show ModuleCat.{max u v} R from M).isModule
instance concreteCategory : ConcreteCategory (Modules.{u,v} R) (fun M N => M →ₗ[R] N) :=
  inferInstanceAs (ConcreteCategory (ModuleCat.{max u v} R) (fun M N => M →ₗ[R] N))
instance preadditive : Preadditive (Modules.{u,v} R) := inferInstanceAs (Preadditive (ModuleCat.{max u v} R))
instance abelian : Abelian (Modules.{u,v} R) := inferInstanceAs (Abelian (ModuleCat.{max u v} R))
instance linear : Linear R (Modules.{u,v} R) :=
  inferInstanceAs (Linear R (ModuleCat.{max u v} R))
instance tensorStructure : MonoidalCategoryStruct (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
instance monoidalCategory : MonoidalCategory (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
instance monoidalPreadditive : MonoidalPreadditive (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
instance monoidalLinear : MonoidalLinear R (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
instance symmetricCategory : SymmetricCategory (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.symmetricCategory.{u,v} (R := R)

/-- The actual up ring equivalence; the scalar ring is not replaced in the target. -/
def scalarEquiv : R ≃+* (LiftedRing.{u,v} R) := (ULift.ringEquiv : (LiftedRing.{u,v} R) ≃+* R).symm

/-- Native scalar restriction to the original ring, in the actual common world. -/
def toOriginal : ModuleCat.{max u v} (LiftedRing.{u,v} R) ⥤ (Modules.{u,v} R) := ModuleCat.restrictScalars
  (scalarEquiv.{u,v} R).toRingHom

instance toOriginal_additive : (toOriginal.{u,v} R).Additive where
  map_add := by intros; rfl

instance toOriginal_isEquivalence : (toOriginal.{u,v} R).IsEquivalence := by
  unfold toOriginal
  exact ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (scalarEquiv.{u,v} R)

instance toOriginal_preservesHomology : (toOriginal.{u,v} R).PreservesHomology := by
  infer_instance


/-- The actual offset-v unit map uses the identity on the lifted carrier,
with scalar compatibility checked through the actual up multiplication. -/
def unitIso : 𝟙_ (Modules.{u,v} R) ≅
    (toOriginal.{u,v} R).obj (𝟙_ (ModuleCat.{max u v} (LiftedRing.{u,v} R))) := by
  let X : Modules.{u,v} R := 𝟙_ (Modules.{u,v} R)
  let Y : Modules.{u,v} R :=
    (toOriginal.{u,v} R).obj (𝟙_ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))
  let e : X ≃ₗ[R] Y :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by cases x; rfl }
  exact e.toModuleIso

@[simp]
theorem unitIso_hom_value (x : ULift.{v} R) : (unitIso.{u,v} R).hom x = x := rfl

@[simp]
theorem unitIso_inv_value (x : ULift.{v} R) : (unitIso.{u,v} R).inv x = x := rfl

/-- The native balanced tensor comparison uses both original factor values,
with the actual low and high scalar rings. -/
def tensorIso (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) : (toOriginal.{u,v} R).obj M ⊗
  (toOriginal.{u,v} R).obj N ≅ (toOriginal.{u,v} R).obj (M ⊗ N) :=
  ModuleCat.RingEquivUniverse.tensorIso.{u,max u v,0} (scalarEquiv.{u,v} R) M N

@[simp]
theorem tensorIso_hom_tmul (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R))
    (m : (toOriginal.{u,v} R).obj M) (n : (toOriginal.{u,v} R).obj N) :
    (tensorIso.{u,v} R M N).hom (m ⊗ₜ[R] n) = m ⊗ₜ[(LiftedRing.{u,v} R)] n :=
  ModuleCat.RingEquivUniverse.tensorIso_hom_tmul (scalarEquiv.{u,v} R) M N m n

@[simp]
theorem tensorIso_inv_tmul (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) (m : M) (n : N) :
    (tensorIso.{u,v} R M N).inv (m ⊗ₜ[(LiftedRing.{u,v} R)] n) =
      (show (toOriginal.{u,v} R).obj M from m) ⊗ₜ[R]
        (show (toOriginal.{u,v} R).obj N from n) :=
  ModuleCat.RingEquivUniverse.tensorIso_inv_tmul (scalarEquiv.{u,v} R) M N m n

@[reassoc]
theorem tensorIso_naturality {M N M' N' : ModuleCat.{max u v} (LiftedRing.{u,v} R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((toOriginal.{u,v} R).map f ⊗ₘ (toOriginal.{u,v} R).map g) ≫ (tensorIso.{u,v} R M' N').hom =
      (tensorIso.{u,v} R M N).hom ≫ (toOriginal.{u,v} R).map (f ⊗ₘ g) :=
  ModuleCat.RingEquivUniverse.tensorIso_naturality (scalarEquiv.{u,v} R) f g

/-- The actual module scalar restriction is strong monoidal. Its tensor,
unit and associator laws are checked on original pure tensors. -/
def monoidal : (toOriginal.{u,v} R).Monoidal :=
  (show (toOriginal.{u,v} R).CoreMonoidal from
    { εIso := unitIso.{u,v} R
      μIso := tensorIso.{u,v} R
      μIso_hom_natural_left := fun f M => by
        have ht := congrArg (fun z => (toOriginal.{u,v} R).map f ⊗ₘ z)
          ((toOriginal.{u,v} R).map_id M)
        have hw := ht.trans (tensorHom_id ((toOriginal.{u,v} R).map f)
          ((toOriginal.{u,v} R).obj M))
        exact (congrArg (fun z => z ≫ (tensorIso.{u,v} R _ M).hom) hw).symm.trans
          (tensorIso_naturality.{u,v} R f (𝟙 M))
      μIso_hom_natural_right := fun M f => by
        have ht := congrArg (fun z => z ⊗ₘ (toOriginal.{u,v} R).map f)
          ((toOriginal.{u,v} R).map_id M)
        have hw := ht.trans (id_tensorHom ((toOriginal.{u,v} R).obj M)
          ((toOriginal.{u,v} R).map f))
        exact (congrArg (fun z => z ≫ (tensorIso.{u,v} R M _).hom) hw).symm.trans
          (tensorIso_naturality.{u,v} R (𝟙 M) f)
      associativity := fun M N P => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro m n p
        rfl
      left_unitality := fun M => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro r m
        cases r
        rfl
      right_unitality := fun M => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m r
        cases r
        rfl }).toMonoidal

/-- The same actual tensor comparison preserves the native symmetric
module interchange; no new sign convention is introduced. -/
@[reassoc]
theorem tensorIso_braiding (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) :
    (tensorIso.{u,v} R M N).hom ≫ (toOriginal.{u,v} R).map (β_ M N).hom =
      (β_ ((toOriginal.{u,v} R).obj M) ((toOriginal.{u,v} R).obj N)).hom ≫ (tensorIso.{u,v} R N M).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  rfl

end ModuleCat.UniverseScalarRestriction
