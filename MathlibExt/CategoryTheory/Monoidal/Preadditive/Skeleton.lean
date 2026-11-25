/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import MathlibExt.CategoryTheory.Preadditive.Skeleton

/-!
# Semiring structure on the skeleton of a preadditive monoidal category

A preadditive monoidal category `C` with `MonoidalPreadditive`, a zero object,
and binary biproducts gives a semiring on `Skeleton C`. Addition is induced by
biproduct and multiplication by tensor, with the zero object and tensor unit
as zero and one. If `C` is braided, the semiring is commutative.

An additive strong monoidal functor between two categories satisfying these
semiring hypotheses induces a semiring homomorphism on their skeleta.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Skeleton

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- In a preadditive monoidal category with `MonoidalPreadditive`, a zero object,
and binary biproducts, the skeleton is a semiring with addition by biproduct and
multiplication by tensor. The zero object and tensor unit give zero and one. -/
noncomputable instance instSemiring : Semiring (Skeleton C) :=
  { Skeleton.instAddCommMonoid (C := C), Skeleton.instMonoid (C := C) with
    left_distrib := fun X Y Z => by
      have : (tensorLeft X.out).Additive := inferInstance
      have : (tensorLeft X.out).PreservesZeroMorphisms := inferInstance
      have : Limits.PreservesFiniteBiproducts (tensorLeft X.out) := inferInstance
      have : Limits.PreservesBiproductsOfShape WalkingPair (tensorLeft X.out) := inferInstance
      have : Limits.PreservesBinaryBiproducts (tensorLeft X.out) :=
        Limits.preservesBinaryBiproducts_of_preservesBiproducts (tensorLeft X.out)
      have hx : toSkeleton X.out = X := toSkeleton_fromSkeleton_obj X
      have hy : toSkeleton Y.out = Y := toSkeleton_fromSkeleton_obj Y
      have hz : toSkeleton Z.out = Z := toSkeleton_fromSkeleton_obj Z
      have hyz : toSkeleton (Y.out ⊞ Z.out) = Y + Z := rfl
      have h_left : toSkeleton (X.out ⊗ (Y.out ⊞ Z.out)) = X * (Y + Z) := by
        calc toSkeleton (X.out ⊗ (Y.out ⊞ Z.out))
            = toSkeleton X.out * toSkeleton (Y.out ⊞ Z.out) := toSkeleton_tensorObj _ _
          _ = X * (Y + Z) := by rw [hx, hyz]
      have h_right : toSkeleton ((X.out ⊗ Y.out) ⊞ (X.out ⊗ Z.out)) = X * Y + X * Z := by
        calc toSkeleton ((X.out ⊗ Y.out) ⊞ (X.out ⊗ Z.out))
            = toSkeleton (X.out ⊗ Y.out) + toSkeleton (X.out ⊗ Z.out) := toSkeleton_biprod _ _
          _ = toSkeleton X.out * toSkeleton Y.out + toSkeleton X.out * toSkeleton Z.out := by
                rw [toSkeleton_tensorObj, toSkeleton_tensorObj]
          _ = X * Y + X * Z := by rw [hx, hy, hz]
      calc X * (Y + Z)
          = toSkeleton (X.out ⊗ (Y.out ⊞ Z.out)) := h_left.symm
        _ = toSkeleton ((X.out ⊗ Y.out) ⊞ (X.out ⊗ Z.out)) :=
            congr_toSkeleton_of_iso ((tensorLeft X.out).mapBiprod Y.out Z.out)
        _ = X * Y + X * Z := h_right
    right_distrib := fun X Y Z => by
      have : (tensorRight Z.out).Additive := inferInstance
      have : (tensorRight Z.out).PreservesZeroMorphisms := inferInstance
      have : Limits.PreservesFiniteBiproducts (tensorRight Z.out) := inferInstance
      have : Limits.PreservesBiproductsOfShape WalkingPair (tensorRight Z.out) := inferInstance
      have : Limits.PreservesBinaryBiproducts (tensorRight Z.out) :=
        Limits.preservesBinaryBiproducts_of_preservesBiproducts (tensorRight Z.out)
      have hx : toSkeleton X.out = X := toSkeleton_fromSkeleton_obj X
      have hy : toSkeleton Y.out = Y := toSkeleton_fromSkeleton_obj Y
      have hz : toSkeleton Z.out = Z := toSkeleton_fromSkeleton_obj Z
      have hxy : toSkeleton (X.out ⊞ Y.out) = X + Y := rfl
      have h_left : toSkeleton ((X.out ⊞ Y.out) ⊗ Z.out) = (X + Y) * Z := by
        calc toSkeleton ((X.out ⊞ Y.out) ⊗ Z.out)
            = toSkeleton (X.out ⊞ Y.out) * toSkeleton Z.out := toSkeleton_tensorObj _ _
          _ = (X + Y) * Z := by rw [hxy, hz]
      have h_right : toSkeleton ((X.out ⊗ Z.out) ⊞ (Y.out ⊗ Z.out)) = X * Z + Y * Z := by
        calc toSkeleton ((X.out ⊗ Z.out) ⊞ (Y.out ⊗ Z.out))
            = toSkeleton (X.out ⊗ Z.out) + toSkeleton (Y.out ⊗ Z.out) := toSkeleton_biprod _ _
          _ = toSkeleton X.out * toSkeleton Z.out + toSkeleton Y.out * toSkeleton Z.out := by
                rw [toSkeleton_tensorObj, toSkeleton_tensorObj]
          _ = X * Z + Y * Z := by rw [hx, hy, hz]
      calc (X + Y) * Z
          = toSkeleton ((X.out ⊞ Y.out) ⊗ Z.out) := h_left.symm
        _ = toSkeleton ((X.out ⊗ Z.out) ⊞ (Y.out ⊗ Z.out)) :=
            congr_toSkeleton_of_iso ((tensorRight Z.out).mapBiprod X.out Y.out)
        _ = X * Z + Y * Z := h_right
    zero_mul := fun X => by
      have hx : toSkeleton X.out = X := toSkeleton_fromSkeleton_obj X
      have h : toSkeleton ((0 : C) ⊗ X.out) = (0 : Skeleton C) * X := by
        calc toSkeleton ((0 : C) ⊗ X.out)
            = toSkeleton (0 : C) * toSkeleton X.out := toSkeleton_tensorObj _ _
          _ = (0 : Skeleton C) * X := by rw [toSkeleton_zero, hx]
      calc (0 : Skeleton C) * X
          = toSkeleton ((0 : C) ⊗ X.out) := h.symm
        _ = toSkeleton (0 : C) :=
            congr_toSkeleton_of_iso ((tensorRight X.out).mapZeroObject)
        _ = (0 : Skeleton C) := toSkeleton_zero
    mul_zero := fun X => by
      have hx : toSkeleton X.out = X := toSkeleton_fromSkeleton_obj X
      have h : toSkeleton (X.out ⊗ (0 : C)) = X * (0 : Skeleton C) := by
        calc toSkeleton (X.out ⊗ (0 : C))
            = toSkeleton X.out * toSkeleton (0 : C) := toSkeleton_tensorObj _ _
          _ = X * (0 : Skeleton C) := by rw [toSkeleton_zero, hx]
      calc X * (0 : Skeleton C)
          = toSkeleton (X.out ⊗ (0 : C)) := h.symm
        _ = toSkeleton (0 : C) :=
            congr_toSkeleton_of_iso ((tensorLeft X.out).mapZeroObject)
        _ = (0 : Skeleton C) := toSkeleton_zero
  }

section CommSemiring

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]

/-- A braided preadditive monoidal category with `MonoidalPreadditive`, a zero object,
and binary biproducts has a commutative semiring skeleton, with biproduct addition and
tensor multiplication. -/
noncomputable instance instCommSemiring : CommSemiring (Skeleton C) :=
  { Skeleton.instSemiring (C := C), Skeleton.instCommMonoid (C := C) with }

end CommSemiring

section RingHom

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]
  [MonoidalCategory E] [MonoidalPreadditive E]

/-- For preadditive monoidal categories `C` and `D`, each with `MonoidalPreadditive`,
a zero object, and binary biproducts, an additive strong monoidal functor `F : C ⥤ D`
induces a semiring homomorphism sending `toSkeleton X` to `toSkeleton (F.obj X)`. -/
noncomputable def ringHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    Skeleton C →+* Skeleton D :=
  { Skeleton.mapAddMonoidHom (F := F), Skeleton.monoidHom F with }

@[simp]
theorem ringHom_toAddMonoidHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    (Skeleton.ringHom (F := F)).toAddMonoidHom = Skeleton.mapAddMonoidHom (F := F) :=
  rfl

@[simp]
theorem ringHom_toSkeleton (F : C ⥤ D) [F.Additive] [F.Monoidal] (X : C) :
    Skeleton.ringHom (F := F) (toSkeleton X) = toSkeleton (F.obj X) :=
  Skeleton.mapAddMonoidHom_toSkeleton F X

theorem ringHom_id :
    Skeleton.ringHom (F := 𝟭 C) = RingHom.id (Skeleton C) := by
  ext X
  change Skeleton.mapAddMonoidHom (F := 𝟭 C) X = X
  have h : Skeleton.mapAddMonoidHom (F := 𝟭 C) = AddMonoidHom.id (Skeleton C) :=
    Skeleton.mapAddMonoidHom_id
  calc Skeleton.mapAddMonoidHom (F := 𝟭 C) X
      = (AddMonoidHom.id (Skeleton C)) X := by rw [h]
    _ = X := rfl

theorem ringHom_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.Monoidal] [G.Monoidal] :
    Skeleton.ringHom (F := F ⋙ G) =
      (Skeleton.ringHom (F := G)).comp (Skeleton.ringHom (F := F)) := by
  ext X
  change Skeleton.mapAddMonoidHom (F := F ⋙ G) X =
    (Skeleton.mapAddMonoidHom (F := G)).comp (Skeleton.mapAddMonoidHom (F := F)) X
  have h : Skeleton.mapAddMonoidHom (F := F ⋙ G) =
      (Skeleton.mapAddMonoidHom (F := G)).comp (Skeleton.mapAddMonoidHom (F := F)) :=
    Skeleton.mapAddMonoidHom_comp F G
  calc Skeleton.mapAddMonoidHom (F := F ⋙ G) X
      = ((Skeleton.mapAddMonoidHom (F := G)).comp (Skeleton.mapAddMonoidHom (F := F))) X := by
        rw [h]
    _ = (Skeleton.mapAddMonoidHom (F := G)).comp (Skeleton.mapAddMonoidHom (F := F)) X := rfl

theorem ringHom_eq_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [F.Monoidal] [G.Monoidal] (e : F ≅ G) :
    Skeleton.ringHom (F := F) = Skeleton.ringHom (F := G) := by
  ext X
  change Skeleton.mapAddMonoidHom (F := F) X = Skeleton.mapAddMonoidHom (F := G) X
  have h : Skeleton.mapAddMonoidHom (F := F) = Skeleton.mapAddMonoidHom (F := G) :=
    Skeleton.mapAddMonoidHom_eq_of_iso e
  rw [h]

end RingHom

end Skeleton

end CategoryTheory
