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

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive monoid on the skeleton of an additive category

For an additive category `C`, the skeleton `Skeleton C` carries a canonical
`AddCommMonoid` structure with zero given by the class of the zero object and
addition induced by binary biproducts. The concrete hypotheses are
`Preadditive` plus a zero object and binary biproducts.

An additive functor induces an additive monoid homomorphism on skeleta.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Skeleton

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

noncomputable instance instAddCommMonoid : AddCommMonoid (Skeleton C) where
  add X Y := toSkeleton (X.out ⊞ Y.out)
  zero := toSkeleton (0 : C)
  add_assoc X Y Z := by
    have hXY : (toSkeleton (X.out ⊞ Y.out)).out ≅ X.out ⊞ Y.out :=
      fromSkeletonToSkeletonIso _
    have hYZ : (toSkeleton (Y.out ⊞ Z.out)).out ≅ Y.out ⊞ Z.out :=
      fromSkeletonToSkeletonIso _
    have assocLeft : (toSkeleton (X.out ⊞ Y.out)).out ⊞ Z.out ≅ (X.out ⊞ Y.out) ⊞ Z.out :=
      biprod.mapIso hXY (Iso.refl _)
    have assocRight : X.out ⊞ (toSkeleton (Y.out ⊞ Z.out)).out ≅ X.out ⊞ (Y.out ⊞ Z.out) :=
      biprod.mapIso (Iso.refl _) hYZ
    have h₁ : toSkeleton ((toSkeleton (X.out ⊞ Y.out)).out ⊞ Z.out) =
        toSkeleton ((X.out ⊞ Y.out) ⊞ Z.out) :=
      congr_toSkeleton_of_iso assocLeft
    have h₂ : toSkeleton (X.out ⊞ (toSkeleton (Y.out ⊞ Z.out)).out) =
        toSkeleton (X.out ⊞ (Y.out ⊞ Z.out)) :=
      congr_toSkeleton_of_iso assocRight
    have hAssoc : toSkeleton ((X.out ⊞ Y.out) ⊞ Z.out) =
        toSkeleton (X.out ⊞ (Y.out ⊞ Z.out)) :=
      congr_toSkeleton_of_iso (biprod.associator _ _ _)
    calc toSkeleton ((toSkeleton (X.out ⊞ Y.out)).out ⊞ Z.out)
        = toSkeleton ((X.out ⊞ Y.out) ⊞ Z.out) := h₁
      _ = toSkeleton (X.out ⊞ (Y.out ⊞ Z.out)) := hAssoc
      _ = toSkeleton (X.out ⊞ (toSkeleton (Y.out ⊞ Z.out)).out) := h₂.symm
  zero_add X := by
    have h₁ : (toSkeleton (0 : C)).out ≅ (0 : C) := fromSkeletonToSkeletonIso (0 : C)
    have hZero : (0 : C) ⊞ X.out ≅ X.out := (isoZeroBiprod (isZero_zero C)).symm
    have hComb : (toSkeleton (0 : C)).out ⊞ X.out ≅ X.out :=
      (biprod.mapIso h₁ (Iso.refl _)).trans hZero
    calc toSkeleton ((toSkeleton (0 : C)).out ⊞ X.out)
        = toSkeleton X.out := congr_toSkeleton_of_iso hComb
      _ = X := toSkeleton_fromSkeleton_obj X
  add_zero X := by
    have h₁ : (toSkeleton (0 : C)).out ≅ (0 : C) := fromSkeletonToSkeletonIso (0 : C)
    have hZero : X.out ⊞ (0 : C) ≅ X.out := (isoBiprodZero (isZero_zero C)).symm
    have hComb : X.out ⊞ (toSkeleton (0 : C)).out ≅ X.out :=
      (biprod.mapIso (Iso.refl _) h₁).trans hZero
    calc toSkeleton (X.out ⊞ (toSkeleton (0 : C)).out)
        = toSkeleton X.out := congr_toSkeleton_of_iso hComb
      _ = X := toSkeleton_fromSkeleton_obj X
  nsmul n X := n.rec (toSkeleton (0 : C)) (fun _ ih => toSkeleton (ih.out ⊞ X.out))
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_comm X Y :=
    congr_toSkeleton_of_iso (biprod.braiding X.out Y.out)

/-- `toSkeleton` sends biproduct to addition. -/
theorem toSkeleton_biprod (X Y : C) :
    toSkeleton (X ⊞ Y) = toSkeleton X + toSkeleton Y := by
  have hX : X ≅ (toSkeleton X).out := (fromSkeletonToSkeletonIso X).symm
  have hY : Y ≅ (toSkeleton Y).out := (fromSkeletonToSkeletonIso Y).symm
  have h : toSkeleton (X ⊞ Y) = toSkeleton ((toSkeleton X).out ⊞ (toSkeleton Y).out) :=
    congr_toSkeleton_of_iso (biprod.mapIso hX hY)
  calc toSkeleton (X ⊞ Y)
      = toSkeleton ((toSkeleton X).out ⊞ (toSkeleton Y).out) := h
    _ = toSkeleton X + toSkeleton Y := rfl

/-- `toSkeleton` sends zero object to zero. -/
theorem toSkeleton_zero :
    toSkeleton (0 : C) = (0 : Skeleton C) := rfl

end Skeleton

section Map

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]

/-- An additive functor induces an additive monoid homomorphism on skeleta. -/
noncomputable def Skeleton.mapAddMonoidHom
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] :
    Skeleton C →+ Skeleton D where
  toFun := F.mapSkeleton.obj
  map_zero' := by
    have h0 : F.mapSkeleton.obj (toSkeleton (0 : C)) = toSkeleton (F.obj (0 : C)) :=
      F.mapSkeleton_obj_toSkeleton (0 : C)
    calc F.mapSkeleton.obj (0 : Skeleton C)
        = F.mapSkeleton.obj (toSkeleton (0 : C)) := rfl
      _ = toSkeleton (F.obj (0 : C)) := h0
      _ = toSkeleton (0 : D) := congr_toSkeleton_of_iso F.mapZeroObject
      _ = (0 : Skeleton D) := rfl
  map_add' X Y := by
    have : F.PreservesZeroMorphisms := inferInstance
    have : Limits.PreservesFiniteBiproducts F := inferInstance
    have : Limits.PreservesBiproductsOfShape WalkingPair F := inferInstance
    have : Limits.PreservesBiproduct (pairFunction X.out Y.out) F := inferInstance
    have : Limits.PreservesBinaryBiproduct X.out Y.out F :=
      Limits.preservesBinaryBiproduct_of_preservesBiproduct F X.out Y.out
    have hL : F.mapSkeleton.obj (X + Y) = toSkeleton (F.obj (X.out ⊞ Y.out)) := by
      calc F.mapSkeleton.obj (X + Y)
          = F.mapSkeleton.obj (toSkeleton (X.out ⊞ Y.out)) := rfl
        _ = toSkeleton (F.obj (X.out ⊞ Y.out)) := F.mapSkeleton_obj_toSkeleton _
    have hR : F.mapSkeleton.obj X + F.mapSkeleton.obj Y =
        toSkeleton ((F.mapSkeleton.obj X).out ⊞ (F.mapSkeleton.obj Y).out) := rfl
    have isoOutX : (F.mapSkeleton.obj X).out ≅ F.obj X.out :=
      fromSkeletonToSkeletonIso (F.obj X.out)
    have isoOutY : (F.mapSkeleton.obj Y).out ≅ F.obj Y.out :=
      fromSkeletonToSkeletonIso (F.obj Y.out)
    have isoBip : F.obj (X.out ⊞ Y.out) ≅ F.obj X.out ⊞ F.obj Y.out :=
      F.mapBiprod X.out Y.out
    have isoCombined : F.obj X.out ⊞ F.obj Y.out ≅
        (F.mapSkeleton.obj X).out ⊞ (F.mapSkeleton.obj Y).out :=
      biprod.mapIso isoOutX.symm isoOutY.symm
    have isoFinal : F.obj (X.out ⊞ Y.out) ≅
        (F.mapSkeleton.obj X).out ⊞ (F.mapSkeleton.obj Y).out :=
      isoBip.trans isoCombined
    calc F.mapSkeleton.obj (X + Y)
        = toSkeleton (F.obj (X.out ⊞ Y.out)) := hL
      _ = toSkeleton ((F.mapSkeleton.obj X).out ⊞ (F.mapSkeleton.obj Y).out) :=
          congr_toSkeleton_of_iso isoFinal
      _ = F.mapSkeleton.obj X + F.mapSkeleton.obj Y := hR.symm

end Map

namespace Skeleton

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

@[simp]
theorem mapAddMonoidHom_toSkeleton
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (X : C) :
    Skeleton.mapAddMonoidHom (F := F) (toSkeleton X) = toSkeleton (F.obj X) :=
  F.mapSkeleton_obj_toSkeleton X

theorem mapAddMonoidHom_id :
    Skeleton.mapAddMonoidHom (F := 𝟭 C) = AddMonoidHom.id (Skeleton C) := by
  ext X
  calc (mapAddMonoidHom (𝟭 C)) X
      = (mapAddMonoidHom (𝟭 C)) (toSkeleton X.out) :=
        congrArg _ (toSkeleton_fromSkeleton_obj X).symm
    _ = toSkeleton ((𝟭 C).obj X.out) := mapAddMonoidHom_toSkeleton (F := 𝟭 C) X.out
    _ = X := toSkeleton_fromSkeleton_obj X

theorem mapAddMonoidHom_comp
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    {E : Type u₃} [Category.{v₃} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] :
    Skeleton.mapAddMonoidHom (F := F ⋙ G) =
      (Skeleton.mapAddMonoidHom (F := G)).comp (Skeleton.mapAddMonoidHom (F := F)) := by
  ext X
  calc (mapAddMonoidHom (F := F ⋙ G)) X
      = (mapAddMonoidHom (F := F ⋙ G)) (toSkeleton X.out) :=
        congrArg _ (toSkeleton_fromSkeleton_obj X).symm
    _ = toSkeleton ((F ⋙ G).obj X.out) := mapAddMonoidHom_toSkeleton _ _
    _ = toSkeleton (G.obj (F.obj X.out)) := rfl
    _ = (mapAddMonoidHom (F := G)) (toSkeleton (F.obj X.out)) :=
        (mapAddMonoidHom_toSkeleton (F := G) (F.obj X.out)).symm
    _ = (mapAddMonoidHom (F := G)) ((mapAddMonoidHom (F := F)) (toSkeleton X.out)) :=
        congrArg (mapAddMonoidHom (F := G))
          (mapAddMonoidHom_toSkeleton (F := F) X.out).symm
    _ = ((mapAddMonoidHom (F := G)).comp (mapAddMonoidHom (F := F))) X :=
        congrArg (mapAddMonoidHom (F := G))
          (congrArg (mapAddMonoidHom (F := F)) (toSkeleton_fromSkeleton_obj X))

theorem mapAddMonoidHom_eq_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    Skeleton.mapAddMonoidHom (F := F) = Skeleton.mapAddMonoidHom (F := G) := by
  ext X
  calc (mapAddMonoidHom (F := F)) X
      = (mapAddMonoidHom (F := F)) (toSkeleton X.out) :=
        congrArg _ (toSkeleton_fromSkeleton_obj X).symm
    _ = toSkeleton (F.obj X.out) := mapAddMonoidHom_toSkeleton (F := F) X.out
    _ = toSkeleton (G.obj X.out) := congr_toSkeleton_of_iso (e.app X.out)
    _ = (mapAddMonoidHom (F := G)) (toSkeleton X.out) :=
        (mapAddMonoidHom_toSkeleton (F := G) X.out).symm
    _ = (mapAddMonoidHom (F := G)) X := congrArg _ (toSkeleton_fromSkeleton_obj X)

end Skeleton

end CategoryTheory
