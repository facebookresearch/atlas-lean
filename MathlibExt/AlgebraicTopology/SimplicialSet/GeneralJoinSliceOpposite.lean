/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinOpposite
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.OppositeSimplex

/-!
# Opposites of the original join slices

Order reversal exchanges the whole join maps defining an under slice
and an over slice. The original diagram restriction is preserved by
the proved literal inclusion equations of the original join.

The source is Lurie's *Higher Topos Theory*, Proposition 1.2.9.2 and
its dual under slice construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

namespace sliceUnder

/-- The original right join cone shape as the opposite of its reversed left join shape. -/
def oppositeShapeIso (K : SSet.{u}) (n : SimplexCategory) :
    stdSimplex.obj n ⋆ K.op ≅ (K ⋆ stdSimplex.obj n).op :=
  (join.flip.obj K.op).mapIso (stdSimplex.opIso n).symm ≪≫
    (joinOppositeIso K (stdSimplex.obj n)).symm

/-- The reversed shape comparison retains the entire original fixed diagram inclusion. -/
@[reassoc]
theorem joinInr_comp_oppositeShapeIso_hom (K : SSet.{u}) (n : SimplexCategory) :
    joinInr (stdSimplex.obj n) K.op ≫ (oppositeShapeIso K n).hom =
      opFunctor.map (joinInl K (stdSimplex.obj n)) := by
  change joinInr (stdSimplex.obj n) K.op ≫
      ((join.map (stdSimplex.opIso n).inv).app K.op ≫
        (joinOppositeIso K (stdSimplex.obj n)).inv) = _
  rw [← Category.assoc, joinInr_comp_map]
  apply (cancel_mono (joinOppositeIso K (stdSimplex.obj n)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    op_joinInl_comp_joinOppositeIso_hom]

/-- The whole reversed shape comparison retains the original join comparison. -/
@[reassoc]
theorem oppositeShapeIso_hom_comp_joinOppositeIso_hom (K : SSet.{u})
    (n : SimplexCategory) :
    (oppositeShapeIso K n).hom ≫ (joinOppositeIso K (stdSimplex.obj n)).hom =
      (join.map (stdSimplex.opIso n).inv).app K.op := by
  change ((join.map (stdSimplex.opIso n).inv).app K.op ≫
    (joinOppositeIso K (stdSimplex.obj n)).inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original shape comparison is natural in the free standard simplex. -/
theorem oppositeShapeIso_hom_naturality (K : SSet.{u}) {n m : SimplexCategory}
    (f : n ⟶ m) :
    (oppositeShapeIso K n).hom ≫
        opFunctor.map ((join.obj K).map (stdSimplex.map (SimplexCategory.rev.map f))) =
      (join.map (stdSimplex.map f)).app K.op ≫ (oppositeShapeIso K m).hom := by
  have hJ : opFunctor.map ((join.obj K).map (stdSimplex.map (SimplexCategory.rev.map f))) ≫
        (joinOppositeIso K (stdSimplex.obj m)).hom =
      (joinOppositeIso K (stdSimplex.obj n)).hom ≫
        (join.map (opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)))).app K.op := by
    simpa only [SimplexCategory.rev_obj, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id] using
        joinOppositeIso_hom_naturality (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map f))
  have hS : (join.map (stdSimplex.opIso n).inv).app K.op ≫
        (join.map (opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)))).app K.op =
      (join.map (stdSimplex.map f)).app K.op ≫ (join.map (stdSimplex.opIso m).inv).app K.op := by
    have h := congrArg (join.flip.obj K.op).map (stdSimplex_opIso_inv_naturality f)
    simp only [CategoryTheory.Functor.map_comp] at h
    change (join.map (stdSimplex.map f)).app K.op ≫
        (join.map (stdSimplex.opIso m).inv).app K.op =
      (join.map (stdSimplex.opIso n).inv).app K.op ≫
        (join.map (opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)))).app K.op at h
    exact h.symm
  apply (cancel_mono (joinOppositeIso K (stdSimplex.obj m)).hom).mp
  calc
    ((oppositeShapeIso K n).hom ≫
        opFunctor.map ((join.obj K).map (stdSimplex.map (SimplexCategory.rev.map f)))) ≫
          (joinOppositeIso K (stdSimplex.obj m)).hom =
      (oppositeShapeIso K n).hom ≫
        (opFunctor.map ((join.obj K).map (stdSimplex.map (SimplexCategory.rev.map f))) ≫
          (joinOppositeIso K (stdSimplex.obj m)).hom) := Category.assoc _ _ _
    _ = (oppositeShapeIso K n).hom ≫
        ((joinOppositeIso K (stdSimplex.obj n)).hom ≫
          (join.map (opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)))).app K.op) := by
            rw [hJ]
    _ = (join.map (stdSimplex.opIso n).inv).app K.op ≫
        (join.map (opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)))).app K.op := by
          rw [← Category.assoc, oppositeShapeIso_hom_comp_joinOppositeIso_hom]
    _ = (join.map (stdSimplex.map f)).app K.op ≫
        (join.map (stdSimplex.opIso m).inv).app K.op := hS
    _ = ((join.map (stdSimplex.map f)).app K.op ≫ (oppositeShapeIso K m).hom) ≫
        (joinOppositeIso K (stdSimplex.obj m)).hom := by
          rw [Category.assoc, oppositeShapeIso_hom_comp_joinOppositeIso_hom]

/-- The whole original under-cone maps correspond bijectively to the reversed over-cone maps. -/
def oppositeHomEquiv (K X : SSet.{u}) (n : SimplexCategory) :
    (K ⋆ stdSimplex.obj n ⟶ X) ≃ (stdSimplex.obj n ⋆ K.op ⟶ X.op) := by
  let e : ((K ⋆ stdSimplex.obj n).op ⟶ X.op) ≃
      (stdSimplex.obj n ⋆ K.op ⟶ X.op) :=
    { toFun g := (oppositeShapeIso K n).hom ≫ g
      invFun g := (oppositeShapeIso K n).inv ≫ g
      left_inv g := by
        change (oppositeShapeIso K n).inv ≫ ((oppositeShapeIso K n).hom ≫ g) = g
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      right_inv g := by
        change (oppositeShapeIso K n).hom ≫ ((oppositeShapeIso K n).inv ≫ g) = g
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] }
  exact SSet.opEquivalence.fullyFaithfulFunctor.homEquiv.trans e

/-- The same bijection retains the literal fixed-diagram condition. -/
def oppositeDegreeEquiv (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) :
    (sliceUnder X f).obj (op n) ≃
      (sliceOver X.op (opFunctor.map f)).obj (op n) :=
  (oppositeHomEquiv K X n).subtypeEquiv (by
    intro g
    change (joinInl K (stdSimplex.obj n) ≫ g = f) ↔
      (joinInr (stdSimplex.obj n) K.op ≫
        ((oppositeShapeIso K n).hom ≫ opFunctor.map g) = opFunctor.map f)
    rw [← Category.assoc, joinInr_comp_oppositeShapeIso_hom,
      ← CategoryTheory.Functor.map_comp]
    exact ⟨fun h => congrArg opFunctor.map h,
      fun h => SSet.opEquivalence.fullyFaithfulFunctor.map_injective h⟩)

/-- The degree correspondence reads the entire original reversed join map. -/
@[simp]
theorem oppositeDegreeEquiv_apply_val (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (sliceUnder X f).obj (op n)) :
    (oppositeDegreeEquiv X f n g).val =
      (oppositeShapeIso K n).hom ≫ opFunctor.map g.val := rfl

end sliceUnder

/-- The opposite of the whole original under slice is the original over slice
of the opposite diagram. -/
def sliceUnderOppositeIso (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    (sliceUnder X f).op ≅ sliceOver X.op (opFunctor.map f) :=
  NatIso.ofComponents
    (fun n => (SSet.opObjEquiv.trans (sliceUnder.oppositeDegreeEquiv X f n.unop)).toIso)
    (by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro g
      apply Subtype.ext
      change (sliceUnder.oppositeShapeIso K m.unop).hom ≫
          opFunctor.map ((join.obj K).map (stdSimplex.map (SimplexCategory.rev.map α.unop)) ≫
            (SSet.opObjEquiv g).val) =
        (join.map (stdSimplex.map α.unop)).app K.op ≫
          ((sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map (SSet.opObjEquiv g).val)
      rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
        sliceUnder.oppositeShapeIso_hom_naturality, Category.assoc])

end SSet

namespace SSet

/-- The actual original ambient map on the opposite whole diagram over-slices. -/
def sliceUnderOppositeAmbientMap {X Y K : SSet.{u}} (f : K ⟶ X) (p : X ⟶ Y) :
    sliceOver X.op (opFunctor.map f) ⟶ sliceOver Y.op (opFunctor.map (f ≫ p)) := by
  let q : Under.mk (opFunctor.map f) ⟶ Under.mk (opFunctor.map (f ≫ p)) :=
    Under.homMk (opFunctor.map p) (opFunctor.map_comp f p).symm
  exact (joinRightDivision K.op).map q

/-- Whole original slice reversal is natural for every actual ambient map
and arbitrary fixed diagram. -/
theorem sliceUnderOppositeIso_hom_ambient_naturality {X Y K : SSet.{u}}
    (f : K ⟶ X) (p : X ⟶ Y) :
    opFunctor.map (sliceUnder.map X f p) ≫ (sliceUnderOppositeIso Y (f ≫ p)).hom =
      (sliceUnderOppositeIso X f).hom ≫ sliceUnderOppositeAmbientMap f p := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  let v : K ⋆ stdSimplex.obj n.unop ⟶ X := (opObjEquiv g).val
  change (sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map (v ≫ p) =
    ((sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map v) ≫ opFunctor.map p
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

end SSet

namespace SSet

namespace sliceUnder

/-- The same reversed shape retains the entire free simplex inclusion. -/
@[reassoc]
theorem joinInl_comp_oppositeShapeIso_hom (K : SSet.{u}) (n : SimplexCategory) :
    joinInl (stdSimplex.obj n) K.op ≫ (oppositeShapeIso K n).hom =
      (stdSimplex.opIso n).inv ≫ opFunctor.map (joinInr K (stdSimplex.obj n)) := by
  apply (cancel_mono (joinOppositeIso K (stdSimplex.obj n)).hom).mp
  rw [Category.assoc, oppositeShapeIso_hom_comp_joinOppositeIso_hom,
    Category.assoc, op_joinInr_comp_joinOppositeIso_hom]
  exact (map_comp_joinInl (stdSimplex.opIso n).inv K.op).symm

/-- The whole shape comparison is natural under restriction of the fixed diagram. -/
theorem oppositeShapeIso_hom_naturality_fixed {K₀ K : SSet.{u}} (i : K₀ ⟶ K)
    (n : SimplexCategory) :
    (oppositeShapeIso K₀ n).hom ≫
        opFunctor.map ((join.map i).app (stdSimplex.obj n)) =
      (join.obj (stdSimplex.obj n)).map (opFunctor.map i) ≫
        (oppositeShapeIso K n).hom := by
  have hJ : opFunctor.map ((join.map i).app (stdSimplex.obj n)) ≫
        (joinOppositeIso K (stdSimplex.obj n)).hom =
      (joinOppositeIso K₀ (stdSimplex.obj n)).hom ≫
        (join.obj (stdSimplex.obj n).op).map (opFunctor.map i) := by
    simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id] using
        joinOppositeIso_hom_naturality i (𝟙 (stdSimplex.obj n))
  apply (cancel_mono (joinOppositeIso K (stdSimplex.obj n)).hom).mp
  rw [Category.assoc, hJ, ← Category.assoc,
    oppositeShapeIso_hom_comp_joinOppositeIso_hom,
    Category.assoc, oppositeShapeIso_hom_comp_joinOppositeIso_hom]
  exact ((join.map (stdSimplex.opIso n).inv).naturality (opFunctor.map i)).symm

end sliceUnder

/-- The opposite-slice map reads the same whole reversed join map in every degree. -/
@[simp]
theorem sliceUnderOppositeIso_hom_app_val (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategoryᵒᵖ) (g : (sliceUnder X f).op.obj n) :
    ((sliceUnderOppositeIso X f).hom.app n g).val =
      (sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map (opObjEquiv g).val :=
  rfl

/-- The original projections commute with the whole opposite-slice isomorphism. -/
@[reassoc]
theorem sliceUnderOppositeIso_hom_proj (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    (sliceUnderOppositeIso X f).hom ≫ sliceOver.proj X.op (opFunctor.map f) =
      opFunctor.map (sliceUnder.proj X f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  change yonedaEquiv (joinInl (stdSimplex.obj n.unop) K.op ≫
      ((sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map (opObjEquiv g).val)) =
    opObjEquiv.symm (yonedaEquiv
      (joinInr K (stdSimplex.obj n.unop) ≫ (opObjEquiv g).val))
  rw [← Category.assoc, sliceUnder.joinInl_comp_oppositeShapeIso_hom,
    Category.assoc, ← CategoryTheory.Functor.map_comp, yonedaEquiv_opposite]

/-- The two literal projections are isomorphic arrows after reversal. -/
def sliceUnderOppositeProjectionArrowIso (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    Arrow.mk (opFunctor.map (sliceUnder.proj X f)) ≅
      Arrow.mk (sliceOver.proj X.op (opFunctor.map f)) :=
  Arrow.isoMk (sliceUnderOppositeIso X f) (Iso.refl X.op)
    (by
      change (sliceUnderOppositeIso X f).hom ≫
        sliceOver.proj X.op (opFunctor.map f) = opFunctor.map (sliceUnder.proj X f) ≫ 𝟙 _
      rw [Category.comp_id]
      exact sliceUnderOppositeIso_hom_proj X f)

/-- Restriction of the original fixed diagram commutes with the entire slice reversal. -/
def sliceUnderOppositeRestrictionArrowIso (X : SSet.{u}) {K₀ K : SSet.{u}}
    (f : K ⟶ X) (i : K₀ ⟶ K) :
    Arrow.mk (opFunctor.map (sliceUnder.restrict X f i)) ≅
      Arrow.mk (sliceOver.restrict X.op (opFunctor.map f) (opFunctor.map i)) := by
  let h := opFunctor.map_comp i f
  let etarget := sliceUnderOppositeIso X (i ≫ f) ≪≫
    eqToIso (congrArg (sliceOver X.op) h)
  refine Arrow.isoMk (sliceUnderOppositeIso X f) etarget ?_
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  have hc := sliceOver.fixedDiagramEq_app_val h n
    ((sliceUnderOppositeIso X (i ≫ f)).hom.app n
      ((opFunctor.map (sliceUnder.restrict X f i)).app n g))
  change (join.obj (stdSimplex.obj n.unop)).map (opFunctor.map i) ≫
      ((sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map (opObjEquiv g).val) =
    ((eqToHom (congrArg (sliceOver X.op) h)).app n
      ((sliceUnderOppositeIso X (i ≫ f)).hom.app n
        ((opFunctor.map (sliceUnder.restrict X f i)).app n g))).val
  rw [hc]
  let v : K ⋆ stdSimplex.obj n.unop ⟶ X := (opObjEquiv g).val
  change (join.obj (stdSimplex.obj n.unop)).map (opFunctor.map i) ≫
      ((sliceUnder.oppositeShapeIso K n.unop).hom ≫ opFunctor.map v) =
    (sliceUnder.oppositeShapeIso K₀ n.unop).hom ≫
      opFunctor.map ((join.map i).app (stdSimplex.obj n.unop) ≫ v)
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← Category.assoc,
    sliceUnder.oppositeShapeIso_hom_naturality_fixed]

end SSet
