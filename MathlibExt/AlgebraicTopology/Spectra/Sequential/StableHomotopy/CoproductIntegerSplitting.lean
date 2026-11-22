/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CoproductIntegerPi

/-!
# The exact original integer coproduct coordinate kernel

The same original right projection factors through the actual integer
cofiber inclusion and the proved collapse Iso. Its kernel is exactly the
image of the original left summand, retaining every original integer map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductIntegerSplittingGeometry

private theorem isoMap_eq_one {A D : GrpCat.{v}} (e : A ≅ D) (a : A) :
    e.hom.hom a = 1 ↔ a = 1 := by
  constructor
  · intro h
    apply e.groupIsoToMulEquiv.injective
    exact h.trans (map_one e.hom.hom).symm
  · rintro rfl
    exact map_one e.hom.hom

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductCofiberGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerExactnessGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (X Y : PointedCGWH.SequentialSpectrum.{u, v}) [IsCofibrant X] [IsCofibrant Y]

/-- The kernel of the actual original right projection is the image of the actual original left inclusion. -/
theorem rightProjection_kernel (q : ℤ) (z : (integerStablePiFunctor q).obj (X ⨿ Y)) :
    ((integerStablePiFunctor q).map (rightProjection X Y)).hom z = 1 ↔
      ∃ x : (integerStablePiFunctor q).obj X,
        ((integerStablePiFunctor q).map (coprod.inl : X ⟶ X ⨿ Y)).hom x = z := by
  let e : (integerStablePiFunctor q).obj ((cofiber (B := B)).obj (arrow X Y)) ≅
      (integerStablePiFunctor q).obj Y :=
    @asIso _ _ _ _ (collapseMap (B := B) X Y q) (collapseMap_isIso (B := B) X Y q)
  have h : ((integerStablePiFunctor q).map (rightProjection X Y)).hom z = 1 ↔
      (inclusionInteger (B := B) q (arrow X Y)).hom z = 1 := by
    rw [← inclusion_collapseMap (B := B) X Y q]
    let a : (integerStablePiFunctor q).obj ((cofiber (B := B)).obj (arrow X Y)) :=
      (inclusionInteger (B := B) q (arrow X Y)).hom z
    exact isoMap_eq_one e a
  exact h.trans (exact_at_target (B := B) q (arrow X Y) z)

/-- The original left projection retains the identity/zero map on the two actual summands. -/
def leftProjection : X ⨿ Y ⟶ X := coprod.desc (𝟙 X) (Diagrams.toZero Y ≫ Diagrams.zeroTo X)

/-- The actual two-projection group hom retains the original whole integer maps. -/
def comparison (q : ℤ) : (integerStablePiFunctor q).obj (X ⨿ Y) →*
    (integerStablePiFunctor q).obj X × (integerStablePiFunctor q).obj Y :=
  ((integerStablePiFunctor q).map (leftProjection X Y)).hom.prod
    ((integerStablePiFunctor q).map (rightProjection X Y)).hom

/-- The original binary coproduct has the full integer stable-pi coordinate equivalence. -/
def equiv (q : ℤ) : (integerStablePiFunctor q).obj (X ⨿ Y) ≃*
    (integerStablePiFunctor q).obj X × (integerStablePiFunctor q).obj Y := by
  let F := integerStablePiFunctor.{u, v} q
  let i := (F.map (coprod.inl : X ⟶ X ⨿ Y)).hom
  let j := (F.map (coprod.inr : Y ⟶ X ⨿ Y)).hom
  let p := (F.map (leftProjection X Y)).hom
  let r := (F.map (rightProjection X Y)).hom
  have hpi : ∀ a, p (i a) = a := by
    intro a
    have h := (F.map_comp (coprod.inl : X ⟶ X ⨿ Y) (leftProjection X Y)).symm.trans
      ((F.congr_map (coprod.inl_desc _ _)).trans (F.map_id X))
    exact ConcreteCategory.congr_hom h a
  have hrj : ∀ b, r (j b) = b := by
    intro b
    have h := (F.map_comp (coprod.inr : Y ⟶ X ⨿ Y) (rightProjection X Y)).symm.trans
      ((F.congr_map (coprod.inr_desc _ _)).trans (F.map_id Y))
    exact ConcreteCategory.congr_hom h b
  have hri : ∀ a, r (i a) = 1 := by
    intro a
    have h := (F.map_comp (coprod.inl : X ⟶ X ⨿ Y) (rightProjection X Y)).symm.trans
      (F.congr_map (coprod.inl_desc _ _))
    exact (ConcreteCategory.congr_hom h a).trans (integerNullMap_apply q X Y a)
  have hpj : ∀ b, p (j b) = 1 := by
    intro b
    have h := (F.map_comp (coprod.inr : Y ⟶ X ⨿ Y) (leftProjection X Y)).symm.trans
      (F.congr_map (coprod.inr_desc _ _))
    exact (ConcreteCategory.congr_hom h b).trans (integerNullMap_apply q Y X b)
  exact MonoidHom.SplitCoordinateExactness.equiv i p j r hpi hrj hri hpj
    (rightProjection_kernel (B := B) X Y q)

/-- The entire binary coproduct coordinate equivalence is the same original projection homomorphism. -/
theorem equiv_hom (q : ℤ) : (equiv (B := B) X Y q).toMonoidHom = comparison X Y q := rfl

/-- The actual left original summand reads as its full first integer coordinate and the trivial second one. -/
theorem equiv_inl (q : ℤ) (x : (integerStablePiFunctor q).obj X) :
    equiv (B := B) X Y q (((integerStablePiFunctor q).map (coprod.inl : X ⟶ X ⨿ Y)).hom x) =
      (x, 1) := by
  apply Prod.ext
  · have h := ((integerStablePiFunctor q).map_comp (coprod.inl : X ⟶ X ⨿ Y) (leftProjection X Y)).symm.trans
      (((integerStablePiFunctor q).congr_map (coprod.inl_desc _ _)).trans
        ((integerStablePiFunctor q).map_id X))
    exact ConcreteCategory.congr_hom h x
  · have h := ((integerStablePiFunctor q).map_comp (coprod.inl : X ⟶ X ⨿ Y) (rightProjection X Y)).symm.trans
      ((integerStablePiFunctor q).congr_map (coprod.inl_desc _ _))
    exact (ConcreteCategory.congr_hom h x).trans (integerNullMap_apply q X Y x)

/-- The actual right original summand reads as the trivial first coordinate and its full second coordinate. -/
theorem equiv_inr (q : ℤ) (y : (integerStablePiFunctor q).obj Y) :
    equiv (B := B) X Y q (((integerStablePiFunctor q).map (coprod.inr : Y ⟶ X ⨿ Y)).hom y) =
      (1, y) := by
  apply Prod.ext
  · have h := ((integerStablePiFunctor q).map_comp (coprod.inr : Y ⟶ X ⨿ Y) (leftProjection X Y)).symm.trans
      ((integerStablePiFunctor q).congr_map (coprod.inr_desc _ _))
    exact (ConcreteCategory.congr_hom h y).trans (integerNullMap_apply q Y X y)
  · have h := ((integerStablePiFunctor q).map_comp (coprod.inr : Y ⟶ X ⨿ Y) (rightProjection X Y)).symm.trans
      (((integerStablePiFunctor q).congr_map (coprod.inr_desc _ _)).trans
        ((integerStablePiFunctor q).map_id Y))
    exact ConcreteCategory.congr_hom h y

end PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductIntegerSplittingGeometry
