/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Actual Hom transport and matching corner; no Quillen/weak outcome assumed.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerRealizationAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerBoundaryProperFaces
import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatching
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Boundary cotensors and matching objects

Boundary cotensors represent the matching objects of the standard-simplex cotensor diagram in
every degree, including zero. The comparison is natural in the target, identifies each
proper-face restriction and the matching map, and realizes the relative matching map as the
corresponding cotensor pullback corner.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.OriginalInnerRealization

private def cotensorUntranspose (K : SSet.{u}) (T Z : SimplicialSpace.{u})
    (f : T ⟶ (innerCotensor K).obj Z) : (innerTensor K).obj T ⟶ Z :=
  InducedCategory.homMk
    (((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
      T.diagram Z.diagram).symm f.hom)

private theorem cotensorUntranspose_scalar {K L : SSet.{u}} (j : K ⟶ L)
    (T Z : SimplicialSpace.{u}) (f : T ⟶ (innerCotensor L).obj Z) :
    cotensorUntranspose K T Z (f ≫ (innerCotensorBifunctor.map j.op).app Z) =
      (innerTensorBifunctor.obj T).map j ≫ cotensorUntranspose L T Z f := by
  apply InducedCategory.hom_ext
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K
  let B := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) L
  apply (A.homEquiv T.diagram Z.diagram).injective
  change A.homEquiv T.diagram Z.diagram
      ((A.homEquiv T.diagram Z.diagram).symm
        (f.hom ≫ (SimplicialPresheaf.scalarCotensor.map j.op).app Z.diagram)) =
    A.homEquiv T.diagram Z.diagram
      ((SimplicialPresheaf.scalarTensor.obj T.diagram).map j ≫
        (B.homEquiv T.diagram Z.diagram).symm f.hom)
  rw [Equiv.apply_symm_apply, rawScalarTransposition]
  dsimp only [B]
  rw [Equiv.apply_symm_apply]

/-- Test maps into the actual inner cotensor are represented by the full enriched Hom.
Both directions are the original pointwise tensor/cotensor transposition. -/
def innerCotensorTestHomEquiv (K : SSet.{u}) (T Z : SimplicialSpace.{u}) :
    (T ⟶ (innerCotensor K).obj Z) ≃
      (K ⟶ (innerHomFunctor.obj (op T)).obj Z) where
  toFun f := innerTensorHomEquiv K T Z
    (InducedCategory.homMk
      (((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
        T.diagram Z.diagram).symm f.hom))
  invFun f := InducedCategory.homMk
    ((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
      T.diagram Z.diagram ((innerTensorHomEquiv K T Z).symm f).hom)
  left_inv f := by
    apply InducedCategory.hom_ext
    simp only [Equiv.symm_apply_apply]
    exact ((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
      T.diagram Z.diagram).apply_symm_apply f.hom
  right_inv f := by
    change innerTensorHomEquiv K T Z
      (InducedCategory.homMk
        (((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
          T.diagram Z.diagram).symm
          ((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv
            T.diagram Z.diagram ((innerTensorHomEquiv K T Z).symm f).hom))) = f
    rw [Equiv.symm_apply_apply]
    exact (innerTensorHomEquiv K T Z).apply_symm_apply f

/-- Scalar restriction is exactly precomposition under the full test Hom equivalence. -/
theorem innerCotensorTestHomEquiv_scalar {K L : SSet.{u}} (j : K ⟶ L)
    (T Z : SimplicialSpace.{u}) (f : T ⟶ (innerCotensor L).obj Z) :
    innerCotensorTestHomEquiv K T Z
        (f ≫ (innerCotensorBifunctor.map j.op).app Z) =
      j ≫ innerCotensorTestHomEquiv L T Z f := by
  change innerTensorHomEquiv K T Z
      (cotensorUntranspose K T Z (f ≫ (innerCotensorBifunctor.map j.op).app Z)) = _
  rw [cotensorUntranspose_scalar, innerTensorHomEquiv_scalar]
  rfl

private def innerBoundaryCotensorCone (n : ℕ) (Z : SimplicialSpace.{u}) :
    Cone (SimplicialObject.matchingDiagram (innerRealizationRightFunctor.obj Z) n) where
  pt := (innerCotensor (SSet.boundary.{u} n : SSet.{u})).obj Z
  π :=
    { app := fun a => (innerCotensorBifunctor.map (properFaceBoundaryInclusion.{u} a).op).app Z
      naturality := by
        intro a b g
        change 𝟙 _ ≫ (innerCotensorBifunctor.map (properFaceBoundaryInclusion b).op).app Z =
          (innerCotensorBifunctor.map (properFaceBoundaryInclusion a).op).app Z ≫
            (innerCotensorBifunctor.map (SSet.stdSimplex.map g.hom.right.unop).op).app Z
        rw [Category.id_comp, ← NatTrans.comp_app, ← innerCotensorBifunctor.map_comp,
          ← op_comp, properFaceBoundaryInclusion_naturality] }

private theorem innerBoundaryCotensor_sections (n : ℕ) (T Z : SimplicialSpace.{u})
    (s : ∀ a : SimplicialObject.matchingIndex n,
      T ⟶ (innerRealizationRightFunctor.obj Z).obj a.obj.right)
    (hs : ∀ {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b),
      s a ≫ (innerRealizationRightFunctor.obj Z).map g.hom.right = s b) :
    ∃! f : T ⟶ (innerBoundaryCotensorCone n Z).pt,
      ∀ a, f ≫ (innerBoundaryCotensorCone n Z).π.app a = s a := by
  let scalar (a : SimplicialObject.matchingIndex n) :=
    innerCotensorTestHomEquiv (SSet.stdSimplex.obj a.obj.right.unop) T Z (s a)
  have compatible {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b) :
      SSet.stdSimplex.map g.hom.right.unop ≫ scalar a = scalar b := by
    exact (innerCotensorTestHomEquiv_scalar
      (SSet.stdSimplex.map g.hom.right.unop) T Z (s a)).symm.trans
        (congrArg (innerCotensorTestHomEquiv (SSet.stdSimplex.obj b.obj.right.unop) T Z)
          (hs g))
  obtain ⟨f, fac, uniq⟩ := properFaceBoundary_sections n
    ((innerHomFunctor.obj (op T)).obj Z) scalar (fun g => compatible g)
  let e := innerCotensorTestHomEquiv (SSet.boundary.{u} n : SSet.{u}) T Z
  refine ⟨e.symm f, ?_, ?_⟩
  · intro a
    apply (innerCotensorTestHomEquiv (SSet.stdSimplex.obj a.obj.right.unop) T Z).injective
    change innerCotensorTestHomEquiv _ T Z
      (e.symm f ≫ (innerCotensorBifunctor.map (properFaceBoundaryInclusion a).op).app Z) =
        scalar a
    rw [innerCotensorTestHomEquiv_scalar]
    change properFaceBoundaryInclusion a ≫ e (e.symm f) = scalar a
    rw [Equiv.apply_symm_apply]
    exact fac a
  · intro g hg
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply uniq
    intro a
    change properFaceBoundaryInclusion a ≫
      innerCotensorTestHomEquiv (SSet.boundary.{u} n : SSet.{u}) T Z g = scalar a
    rw [← innerCotensorTestHomEquiv_scalar]
    exact congrArg (innerCotensorTestHomEquiv _ T Z) (hg a)

private def innerBoundaryCotensorIsLimit (n : ℕ) (Z : SimplicialSpace.{u}) :
    IsLimit (innerBoundaryCotensorCone n Z) := by
  let data (s : Cone (SimplicialObject.matchingDiagram (innerRealizationRightFunctor.obj Z) n)) :=
    innerBoundaryCotensor_sections n s.pt Z (fun a => s.π.app a)
      (fun {a b} g => by
        have h := s.w g
        change s.π.app a ≫ (innerRealizationRightFunctor.obj Z).map g.hom.right =
          s.π.app b at h
        exact h)
  refine
    { lift := fun s => Classical.choose (data s)
      fac := ?_
      uniq := ?_ }
  · intro s a
    exact (Classical.choose_spec (data s)).1 a
  · intro s f hf
    exact (Classical.choose_spec (data s)).2 f hf

/-- The inner boundary cotensor is the entire CSS-valued matching object, including n=0. -/
def innerBoundaryMatchingIso (n : ℕ) (Z : SimplicialSpace.{u}) :
    (innerCotensor (SSet.boundary.{u} n : SSet.{u})).obj Z ≅
      SimplicialObject.matchingObject (innerRealizationRightFunctor.obj Z) n :=
  (innerBoundaryCotensorIsLimit n Z).conePointUniqueUpToIso
    (limit.isLimit (SimplicialObject.matchingDiagram (innerRealizationRightFunctor.obj Z) n))

/-- Every proper-face matching projection is the same original scalar restriction. -/
@[reassoc]
theorem innerBoundaryMatchingIso_π (n : ℕ) (Z : SimplicialSpace.{u})
    (a : SimplicialObject.matchingIndex n) :
    (innerBoundaryMatchingIso n Z).hom ≫
        SimplicialObject.matchingπ (innerRealizationRightFunctor.obj Z) n a =
      (innerCotensorBifunctor.map (properFaceBoundaryInclusion.{u} a).op).app Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ a

/-- Boundary restriction followed by the matching iso is exactly the original matching map. -/
theorem innerBoundaryMatchingIso_boundary (n : ℕ) (Z : SimplicialSpace.{u}) :
    (innerCotensorBifunctor.map (SSet.boundary.{u} n).ι.op).app Z ≫
        (innerBoundaryMatchingIso n Z).hom =
      SimplicialObject.matchingMap (innerRealizationRightFunctor.obj Z) n := by
  apply limit.hom_ext
  intro a
  change ((innerCotensorBifunctor.map (SSet.boundary.{u} n).ι.op).app Z ≫
      (innerBoundaryMatchingIso n Z).hom) ≫
        SimplicialObject.matchingπ (innerRealizationRightFunctor.obj Z) n a =
    SimplicialObject.matchingMap (innerRealizationRightFunctor.obj Z) n ≫
      SimplicialObject.matchingπ (innerRealizationRightFunctor.obj Z) n a
  rw [Category.assoc, innerBoundaryMatchingIso_π, SimplicialObject.matchingMap_π]
  change (innerCotensorBifunctor.map (SSet.boundary n).ι.op).app Z ≫
      (innerCotensorBifunctor.map (properFaceBoundaryInclusion a).op).app Z =
    (innerCotensorBifunctor.map (SSet.stdSimplex.map a.obj.hom.unop).op).app Z
  rw [← NatTrans.comp_app, ← innerCotensorBifunctor.map_comp, ← op_comp,
    properFaceBoundaryInclusion_ι]

/-- The matching map has the exact scalar boundary restriction as its inverse-iso composite. -/
theorem innerBoundaryMatchingIso_matching (n : ℕ) (Z : SimplicialSpace.{u}) :
    SimplicialObject.matchingMap (innerRealizationRightFunctor.obj Z) n ≫
        (innerBoundaryMatchingIso n Z).inv =
      (innerCotensorBifunctor.map (SSet.boundary.{u} n).ι.op).app Z := by
  rw [← innerBoundaryMatchingIso_boundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The complete target map commutes with the matching comparison in every degree. -/
theorem innerBoundaryMatchingIso_naturality_target (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (innerCotensor (SSet.boundary.{u} n : SSet.{u})).map p ≫
        (innerBoundaryMatchingIso n Y).hom =
      (innerBoundaryMatchingIso n X).hom ≫
        (SimplicialObject.matchingObjectFunctor n).map (innerRealizationRightFunctor.map p) := by
  apply limit.hom_ext
  intro a
  change ((innerCotensor (SSet.boundary.{u} n : SSet.{u})).map p ≫
      (innerBoundaryMatchingIso n Y).hom) ≫
        SimplicialObject.matchingπ (innerRealizationRightFunctor.obj Y) n a =
    ((innerBoundaryMatchingIso n X).hom ≫
        (SimplicialObject.matchingObjectFunctor n).map (innerRealizationRightFunctor.map p)) ≫
      SimplicialObject.matchingπ (innerRealizationRightFunctor.obj Y) n a
  rw [Category.assoc, innerBoundaryMatchingIso_π, Category.assoc,
    SimplicialObject.matchingObjectFunctor_map_π, ← Category.assoc,
    innerBoundaryMatchingIso_π]
  exact (innerCotensorBifunctor.map (properFaceBoundaryInclusion.{u} a).op).naturality p

/-- The actual relative matching object supplies the original inner cotensor pullback corner.
Its projection is literally the native relative matching map; both characteristic legs are
retained. -/
def innerBoundaryRelativeMatchingPullbackObjObj (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    innerCotensorBifunctor.PullbackObjObj (SSet.boundary.{u} n).ι p where
  pt := SimplicialObject.relativeMatchingObject (innerRealizationRightFunctor.map p) n
  fst := pullback.snd _ _ ≫ (innerBoundaryMatchingIso n X).inv
  snd := pullback.fst _ _
  isPullback := by
    let h := IsPullback.of_hasPullback
      (SimplicialObject.matchingMap (innerRealizationRightFunctor.obj Y) n)
      ((SimplicialObject.matchingObjectFunctor n).map (innerRealizationRightFunctor.map p))
    exact (h.of_iso (Iso.refl _) (Iso.refl _)
      (innerBoundaryMatchingIso n X).symm (innerBoundaryMatchingIso n Y).symm
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp])
      (by simpa only [Iso.refl_hom, Iso.symm_hom, Category.id_comp] using
        innerBoundaryMatchingIso_matching n Y)
      (by
        change (SimplicialObject.matchingObjectFunctor n).map
            (innerRealizationRightFunctor.map p) ≫ (innerBoundaryMatchingIso n Y).inv =
          (innerBoundaryMatchingIso n X).inv ≫
            (innerCotensor (SSet.boundary.{u} n : SSet.{u})).map p
        apply (cancel_mono (innerBoundaryMatchingIso n Y).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [innerBoundaryMatchingIso_naturality_target]
        simp only [Iso.inv_hom_id_assoc])).flip
  π := SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n
  π_fst := by
    rw [← Category.assoc, SimplicialObject.relativeMatchingMap_snd]
    exact innerBoundaryMatchingIso_matching n X
  π_snd := by
    exact SimplicialObject.relativeMatchingMap_fst (innerRealizationRightFunctor.map p) n

/-- The relative matching arrow and the constructed cotensor-corner arrow are identical. -/
theorem innerBoundaryRelativeMatchingPullbackObjObj_π (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (innerBoundaryRelativeMatchingPullbackObjObj n p).π =
      SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n := rfl

end SimplicialSpace.OriginalInnerRealization
