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

public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import MathlibExt.CategoryTheory.Preadditive.Skeleton
public import MathlibExt.Algebra.Category.Grp.GrothendieckAddGroup

/-!
# `K₀` of an additive category via its skeleton

For an additive category `C` (Mathlib encodes this with `Preadditive`,
`HasZeroObject`, and `HasBinaryBiproducts`), `Skeleton C` carries
`0 = ⟦0⟧`, `⟦X⟧ + ⟦Y⟧ = ⟦X ⊞ Y⟧`. Every split short complex is admissible
exact in any exact structure, so `⟦X⟧ ↦ K₀.mk X` is an additive monoid
homomorphism. Its Grothendieck extension is the canonical comparison
`GrothendieckAddGroup (Skeleton C) →+ K₀ C`.

For the canonical split exact structure, admissible means split, so
`toSkeleton S.X₂ = toSkeleton S.X₁ + toSkeleton S.X₃` and
`K₀ C →+ GrothendieckAddGroup (Skeleton C)` is defined by `K0.lift`.
The two maps are inverse, giving an `AddCommGrpCat` isomorphism whose
forward map is the Grothendieck extension. Both comparisons are natural
for additive exact functors.
-/

@[expose] public section

open CategoryTheory Limits Preadditive ShortComplex ExactCategory Skeleton
open ZeroObject
open Algebra

universe v u v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

section General

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

/-- Additive monoid map `Skeleton C →+ K₀ C` sending `⟦X⟧` to `K₀.mk X`.
Works for any exact structure because split sequences are admissible. -/
noncomputable def K0.skeletonToK0 : Skeleton C →+ K0 C where
  toFun s := K0.mk ((fromSkeleton C).obj s)
  map_zero' := by
    have iso : (fromSkeleton C).obj (0 : Skeleton C) ≅ (0 : C) := by
      have : (0 : Skeleton C) = toSkeleton (0 : C) := rfl
      rw [this]
      exact fromSkeletonToSkeletonIso (0 : C)
    calc
      K0.mk ((fromSkeleton C).obj (0 : Skeleton C)) = K0.mk (0 : C) :=
        K0.mk_congr_of_iso iso
      _ = 0 := K0.mk_zero
  map_add' X Y := by
    have hAdd : X + Y = toSkeleton ((fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y) := rfl
    have hEq : (fromSkeleton C).obj (X + Y) =
        (fromSkeleton C).obj (toSkeleton ((fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y)) := by
      rw [hAdd]
    have iso₁ : (fromSkeleton C).obj
        (toSkeleton ((fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y)) ≅
        (fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y :=
      fromSkeletonToSkeletonIso _
    have iso : (fromSkeleton C).obj (X + Y) ≅
        (fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y :=
      (eqToIso hEq).trans iso₁
    calc
      K0.mk ((fromSkeleton C).obj (X + Y))
        = K0.mk ((fromSkeleton C).obj X ⊞ (fromSkeleton C).obj Y) :=
          K0.mk_congr_of_iso iso
      _ = K0.mk ((fromSkeleton C).obj X) + K0.mk ((fromSkeleton C).obj Y) :=
          K0.mk_biprod _ _

@[simp]
lemma K0.skeletonToK0_toSkeleton (X : C) :
    K0.skeletonToK0 C (toSkeleton X) = K0.mk X :=
  K0.mk_congr_of_iso (fromSkeletonToSkeletonIso X)

/-- Canonical comparison `GrothendieckAddGroup (Skeleton C) →+ K₀ C` via
`GrothendieckAddGroup.lift`. Valid for any exact structure. -/
noncomputable def K0.grothendieckToK0 :
    GrothendieckAddGroup (Skeleton C) →+ K0 C :=
  GrothendieckAddGroup.lift (K0.skeletonToK0 C)

@[simp]
lemma K0.grothendieckToK0_of_toSkeleton (X : C) :
    K0.grothendieckToK0 C (GrothendieckAddGroup.of (toSkeleton X)) = K0.mk X := by
  calc
    K0.grothendieckToK0 C (GrothendieckAddGroup.of (toSkeleton X))
      = K0.skeletonToK0 C (toSkeleton X) :=
        GrothendieckAddGroup.lift_of (K0.skeletonToK0 C) (toSkeleton X)
    _ = K0.mk X := K0.skeletonToK0_toSkeleton C X

end General

section GeneralNaturality

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]

private theorem K0.skeletonToK0_natural (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (K0.map F).comp (K0.skeletonToK0 C) =
      (K0.skeletonToK0 D).comp (Skeleton.mapAddMonoidHom (F := F)) := by
  ext s : 1
  calc
    (K0.map F) (K0.skeletonToK0 C s) = K0.mk (F.obj ((fromSkeleton C).obj s)) := by
      calc
        (K0.map F) (K0.skeletonToK0 C s) = (K0.map F) (K0.mk ((fromSkeleton C).obj s)) := rfl
        _ = K0.mk (F.obj ((fromSkeleton C).obj s)) := K0.map_mk F ((fromSkeleton C).obj s)
    _ = K0.mk ((fromSkeleton D).obj (Skeleton.mapAddMonoidHom (F := F) s)) := by
        have h : Skeleton.mapAddMonoidHom (F := F) s =
            toSkeleton (F.obj ((fromSkeleton C).obj s)) := by
          calc
            Skeleton.mapAddMonoidHom (F := F) s
              = Skeleton.mapAddMonoidHom (F := F) (toSkeleton ((fromSkeleton C).obj s)) := by
                rw [toSkeleton_fromSkeleton_obj]
            _ = toSkeleton (F.obj ((fromSkeleton C).obj s)) :=
                Skeleton.mapAddMonoidHom_toSkeleton F _
        have iso : (fromSkeleton D).obj (Skeleton.mapAddMonoidHom (F := F) s) ≅
            F.obj ((fromSkeleton C).obj s) := by
          rw [h]
          exact fromSkeletonToSkeletonIso _
        exact K0.mk_congr_of_iso iso.symm

theorem K0.grothendieckToK0_natural (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (K0.map F).comp (K0.grothendieckToK0 C) =
      (K0.grothendieckToK0 D).comp
        (Algebra.GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))) := by
  apply Algebra.GrothendieckAddGroup.hom_ext
  ext s : 1
  calc
    (K0.map F) (K0.grothendieckToK0 C (GrothendieckAddGroup.of s))
      = (K0.map F) (K0.skeletonToK0 C s) := by
        change (K0.map F) ((GrothendieckAddGroup.lift (K0.skeletonToK0 C))
            (GrothendieckAddGroup.of s)) = _
        rw [GrothendieckAddGroup.lift_of]
    _ = K0.skeletonToK0 D (Skeleton.mapAddMonoidHom (F := F) s) :=
        DFunLike.congr_fun (K0.skeletonToK0_natural (F := F)) s
    _ = K0.grothendieckToK0 D
          (GrothendieckAddGroup.of (Skeleton.mapAddMonoidHom (F := F) s)) := by
        change _ = (GrothendieckAddGroup.lift (K0.skeletonToK0 D))
            (GrothendieckAddGroup.of (Skeleton.mapAddMonoidHom (F := F) s))
        rw [← GrothendieckAddGroup.lift_of]
    _ = K0.grothendieckToK0 D
          (Algebra.GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))
            (GrothendieckAddGroup.of s)) := by
        rw [Algebra.GrothendieckAddGroup.map_of]

end GeneralNaturality

section Split

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- The split exact structure as a local instance for this section. -/
local instance : ExactCategory C := ExactCategory.splitExactCategory (C := C)

/-- Inverse `K₀ C →+ GrothendieckAddGroup (Skeleton C)` for the split exact structure. -/
noncomputable def K0.splitK0ToGrothendieck :
    K0 C →+ GrothendieckAddGroup (Skeleton C) :=
  K0.lift (GrothendieckAddGroup.of : Skeleton C → _) (by
    intro S hS
    obtain ⟨s⟩ := hS
    have hEq : toSkeleton S.X₂ = toSkeleton S.X₁ + toSkeleton S.X₃ := by
      calc
        toSkeleton S.X₂ = toSkeleton (S.X₁ ⊞ S.X₃) :=
          congr_toSkeleton_of_iso s.isoBinaryBiproduct
        _ = toSkeleton S.X₁ + toSkeleton S.X₃ := Skeleton.toSkeleton_biprod _ _
    calc
      GrothendieckAddGroup.of (toSkeleton S.X₂)
        = GrothendieckAddGroup.of (toSkeleton S.X₁ + toSkeleton S.X₃) := by rw [hEq]
      _ = GrothendieckAddGroup.of (toSkeleton S.X₁) +
          GrothendieckAddGroup.of (toSkeleton S.X₃) := map_add _ _ _)

@[simp]
private lemma K0.splitK0ToGrothendieck_mk (X : C) :
    K0.splitK0ToGrothendieck C (K0.mk X) =
      GrothendieckAddGroup.of (toSkeleton X) := by
  simp only [K0.splitK0ToGrothendieck, K0.lift_mk]

/-- `AddCommGrpCat` isomorphism for the split exact structure. -/
noncomputable def K0.splitIso :
    AddCommGrpCat.of (GrothendieckAddGroup (Skeleton C)) ≅
    AddCommGrpCat.of (K0 C) where
  hom := AddCommGrpCat.ofHom (K0.grothendieckToK0 C)
  inv := AddCommGrpCat.ofHom (K0.splitK0ToGrothendieck C)
  hom_inv_id := by
    ext : 1
    dsimp
    apply Algebra.GrothendieckAddGroup.hom_ext
    ext s : 1
    calc
      (K0.splitK0ToGrothendieck C) (K0.grothendieckToK0 C (GrothendieckAddGroup.of s))
        = (K0.splitK0ToGrothendieck C) (K0.mk ((fromSkeleton C).obj s)) := by
          change (K0.splitK0ToGrothendieck C) ((GrothendieckAddGroup.lift (K0.skeletonToK0 C))
              (GrothendieckAddGroup.of s)) = _
          rw [GrothendieckAddGroup.lift_of]
          rfl
      _ = GrothendieckAddGroup.of (toSkeleton ((fromSkeleton C).obj s)) := by
          rw [K0.splitK0ToGrothendieck_mk]
      _ = GrothendieckAddGroup.of s := by rw [toSkeleton_fromSkeleton_obj]
  inv_hom_id := by
    ext : 1
    dsimp
    apply K0.hom_ext
    intro X
    calc
      (K0.grothendieckToK0 C).comp (K0.splitK0ToGrothendieck C) (K0.mk X)
        = (K0.grothendieckToK0 C) ((K0.splitK0ToGrothendieck C) (K0.mk X)) := rfl
      _ = (K0.grothendieckToK0 C) (GrothendieckAddGroup.of (toSkeleton X)) := by
          rw [K0.splitK0ToGrothendieck_mk]
      _ = K0.mk X := K0.grothendieckToK0_of_toSkeleton C X
      _ = (AddMonoidHom.id (K0 C)) (K0.mk X) := rfl

@[simp]
lemma K0.splitIso_inv_mk (X : C) :
    (K0.splitIso C).inv (K0.mk X) =
      GrothendieckAddGroup.of (toSkeleton X) := by
  change K0.splitK0ToGrothendieck C (K0.mk X) = _
  exact K0.splitK0ToGrothendieck_mk C X

end Split

end AlgebraicKTheory
