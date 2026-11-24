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

public import MathlibExt.Algebra.Category.Ring.GrothendieckRing
public import MathlibExt.CategoryTheory.ExactCategory.Monoidal
public import MathlibExt.CategoryTheory.Monoidal.Preadditive.Skeleton
public import MathlibExt.KTheory.Exact.K0.MapRing
public import MathlibExt.KTheory.Exact.K0.Split

/-!
# Ring comparison between the Grothendieck ring of the additive skeleton and `K₀`

For a braided additive monoidal category, `Skeleton C` is a commutative semiring
via biproduct addition and tensor multiplication, and
`GrothendieckAddGroup (Skeleton C)` is its Grothendieck ring. For any
tensor-biexact exact structure, the additive map `⟦X⟧ ↦ [X]` is a ring
homomorphism; its Grothendieck lift `GrothendieckAddGroup (Skeleton C) →+* K₀ C`
is the canonical ring comparison. Mathlib encodes the braided additive
monoidal structure via `[Preadditive C] [MonoidalCategory C] [BraidedCategory C]
[MonoidalPreadditive C]` with `HasZeroObject`, `HasBinaryBiproducts`, and
`IsTensorBiexact`.

Naturality holds for additive strong monoidal exact functors, and for the split
exact structure the comparison is a `CommRingCat` isomorphism whose forget is
`K0.splitIso`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory ZeroObject
open Algebra

universe v u v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

section General

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [ExactCategory.IsTensorBiexact C]

/-- Ring homomorphism `Skeleton C →+* K₀ C` sending `⟦X⟧` to `[X]`. -/
noncomputable def K0.skeletonToK0Ring : Skeleton C →+* K0 C where
  toFun s := K0.skeletonToK0 C s
  map_zero' := (K0.skeletonToK0 C).map_zero
  map_add' := (K0.skeletonToK0 C).map_add
  map_one' := by
    calc K0.skeletonToK0 C (1 : Skeleton C)
        = K0.skeletonToK0 C (toSkeleton (𝟙_ C)) := by rw [Skeleton.one_eq (C := C)]
      _ = K0.mk (𝟙_ C) := K0.skeletonToK0_toSkeleton (C := C) _
      _ = (1 : K0 C) := K0.one_eq (C := C)
  map_mul' X Y := by
    have hXY : X * Y = toSkeleton (X.out ⊗ Y.out) := Skeleton.mul_eq X Y
    have hX : toSkeleton X.out = X := toSkeleton_fromSkeleton_obj X
    have hY : toSkeleton Y.out = Y := toSkeleton_fromSkeleton_obj Y
    have isoX : (fromSkeleton C).obj X ≅ X.out := by
      calc (fromSkeleton C).obj X
          = (fromSkeleton C).obj (toSkeleton X.out) := by rw [hX]
        _ ≅ X.out := fromSkeletonToSkeletonIso X.out
    have isoY : (fromSkeleton C).obj Y ≅ Y.out := by
      calc (fromSkeleton C).obj Y
          = (fromSkeleton C).obj (toSkeleton Y.out) := by rw [hY]
        _ ≅ Y.out := fromSkeletonToSkeletonIso Y.out
    have isoXY : (fromSkeleton C).obj (X * Y) ≅ X.out ⊗ Y.out := by
      calc (fromSkeleton C).obj (X * Y)
          = (fromSkeleton C).obj (toSkeleton (X.out ⊗ Y.out)) := by rw [hXY]
        _ ≅ X.out ⊗ Y.out := fromSkeletonToSkeletonIso _
    have isoProd :
        (fromSkeleton C).obj X ⊗ (fromSkeleton C).obj Y ≅ X.out ⊗ Y.out :=
      tensorIso isoX isoY
    have isoAB :
        (fromSkeleton C).obj (X * Y) ≅
          (fromSkeleton C).obj X ⊗ (fromSkeleton C).obj Y :=
      isoXY.trans isoProd.symm
    calc K0.skeletonToK0 C (X * Y)
        = K0.mk ((fromSkeleton C).obj (X * Y)) := rfl
      _ = K0.mk ((fromSkeleton C).obj X ⊗ (fromSkeleton C).obj Y) :=
          K0.mk_congr_of_iso isoAB
      _ = K0.mk ((fromSkeleton C).obj X) * K0.mk ((fromSkeleton C).obj Y) :=
          (K0.mk_mul (C := C) _ _).symm
      _ = K0.skeletonToK0 C X * K0.skeletonToK0 C Y := rfl

@[simp]
lemma K0.skeletonToK0Ring_toAddMonoidHom :
    (K0.skeletonToK0Ring C).toAddMonoidHom = K0.skeletonToK0 C := rfl

@[simp]
lemma K0.skeletonToK0Ring_toSkeleton (X : C) :
    K0.skeletonToK0Ring C (toSkeleton X) = K0.mk X :=
  K0.skeletonToK0_toSkeleton (C := C) X

/-- Canonical ring comparison `GrothendieckAddGroup (Skeleton C) →+* K₀ C`. -/
noncomputable def K0.grothendieckToK0Ring :
    GrothendieckAddGroup (Skeleton C) →+* K0 C :=
  GrothendieckAddGroup.liftRing (K0.skeletonToK0Ring C)

/-- Compatibility with the additive Grothendieck map. -/
@[simp]
lemma K0.grothendieckToK0Ring_toAddMonoidHom :
    (K0.grothendieckToK0Ring C).toAddMonoidHom = K0.grothendieckToK0 C := by
  calc (K0.grothendieckToK0Ring C).toAddMonoidHom
      = GrothendieckAddGroup.lift (K0.skeletonToK0Ring C).toAddMonoidHom :=
        GrothendieckAddGroup.liftRing_toAddMonoidHom _
    _ = GrothendieckAddGroup.lift (K0.skeletonToK0 C) := by
        rw [K0.skeletonToK0Ring_toAddMonoidHom]
    _ = K0.grothendieckToK0 C := rfl

/-- Combined generator: `of (⟦X⟧)` maps to `[X]`. -/
@[simp]
lemma K0.grothendieckToK0Ring_of_toSkeleton (X : C) :
    K0.grothendieckToK0Ring C (GrothendieckAddGroup.of (toSkeleton X)) =
      K0.mk X := by
  calc K0.grothendieckToK0Ring C (GrothendieckAddGroup.of (toSkeleton X))
      = K0.skeletonToK0Ring C (toSkeleton X) :=
        GrothendieckAddGroup.liftRing_of _ _
    _ = K0.mk X := K0.skeletonToK0Ring_toSkeleton (C := C) X

end General

section GeneralNaturality

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [ExactCategory.IsTensorBiexact C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D] [MonoidalCategory D]
  [BraidedCategory D] [MonoidalPreadditive D] [ExactCategory.IsTensorBiexact D]

/-- Naturality for additive strong monoidal exact functors. -/
theorem K0.grothendieckToK0Ring_natural (F : C ⥤ D)
    [F.Additive] [F.Monoidal] [F.IsExact] :
    (K0.mapRing F).comp (K0.grothendieckToK0Ring C) =
      (K0.grothendieckToK0Ring D).comp
        (Algebra.GrothendieckAddGroup.mapRing (Skeleton.ringHom (F := F))) := by
  apply RingHom.toAddMonoidHom_injective
  apply DFunLike.ext
  intro x
  calc (K0.mapRing F) (K0.grothendieckToK0Ring C x)
      = (K0.mapRing F).toAddMonoidHom
          ((K0.grothendieckToK0Ring C).toAddMonoidHom x) := rfl
    _ = K0.map F (K0.grothendieckToK0 C x) := by
        rw [K0.mapRing_toAddMonoidHom, K0.grothendieckToK0Ring_toAddMonoidHom]
    _ = K0.grothendieckToK0 D
          (Algebra.GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F)) x) :=
        DFunLike.congr_fun (K0.grothendieckToK0_natural (F := F)) x
    _ = (K0.grothendieckToK0Ring D).toAddMonoidHom
          ((Algebra.GrothendieckAddGroup.mapRing
            (Skeleton.ringHom (F := F))).toAddMonoidHom x) := by
        rw [K0.grothendieckToK0Ring_toAddMonoidHom,
            Algebra.GrothendieckAddGroup.mapRing_toAddMonoidHom,
            Skeleton.ringHom_toAddMonoidHom]
    _ = K0.grothendieckToK0Ring D
          (Algebra.GrothendieckAddGroup.mapRing (Skeleton.ringHom (F := F)) x) := rfl

end GeneralNaturality

section Split

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]

/-- The split exact structure as a local instance for this section. -/
local instance : ExactCategory C := ExactCategory.splitExactCategory (C := C)

/-- The split biexact structure as a local instance for this section. -/
local instance : ExactCategory.IsTensorBiexact C :=
  ExactCategory.splitIsTensorBiexact C

/-- In the split exact structure, the Grothendieck-ring comparison is a
`CommRingCat` isomorphism. -/
noncomputable def K0.splitRingIso :
    CommRingCat.of (GrothendieckAddGroup (Skeleton C)) ≅
      CommRingCat.of (K0 C) := by
  have hBijective : Function.Bijective (K0.grothendieckToK0Ring C) := by
    have hEq : (K0.grothendieckToK0Ring C :
        GrothendieckAddGroup (Skeleton C) → K0 C) =
        (K0.grothendieckToK0 C :
          GrothendieckAddGroup (Skeleton C) → K0 C) := by
      funext x
      calc (K0.grothendieckToK0Ring C) x
          = (K0.grothendieckToK0Ring C).toAddMonoidHom x := rfl
        _ = K0.grothendieckToK0 C x :=
            DFunLike.congr_fun (K0.grothendieckToK0Ring_toAddMonoidHom C) x
    rw [hEq]
    exact (K0.splitIso C).addCommGroupIsoToAddEquiv.bijective
  exact
    (RingEquiv.ofBijective (K0.grothendieckToK0Ring C) hBijective).toCommRingCatIso

/-- Forward direction on generators. -/
@[simp]
lemma K0.splitRingIso_hom_of_toSkeleton (X : C) :
    (K0.splitRingIso C).hom
        (GrothendieckAddGroup.of (toSkeleton X)) = K0.mk X := by
  change (K0.grothendieckToK0Ring C)
      (GrothendieckAddGroup.of (toSkeleton X)) = K0.mk X
  exact K0.grothendieckToK0Ring_of_toSkeleton C X

/-- Inverse direction on generators. -/
@[simp]
lemma K0.splitRingIso_inv_mk (X : C) :
    (K0.splitRingIso C).inv (K0.mk X) =
      GrothendieckAddGroup.of (toSkeleton X) := by
  rw [← K0.splitRingIso_hom_of_toSkeleton C X]
  exact CommRingCat.inv_hom_apply (K0.splitRingIso C) _

/-- Forgetting multiplication recovers `K0.splitIso`. -/
theorem K0.splitRingIso_forget :
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
        (K0.splitRingIso C) =
      K0.splitIso C := by
  apply Iso.ext
  ext x
  exact DFunLike.congr_fun (K0.grothendieckToK0Ring_toAddMonoidHom C) x

end Split

end AlgebraicKTheory
