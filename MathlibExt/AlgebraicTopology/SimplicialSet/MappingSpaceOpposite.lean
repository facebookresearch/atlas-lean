/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MappingSpaceOppositeSimplex

/-!
# The whole right/opposite-left mapping-space isomorphism

The degreewise comparison intertwines every simplex operator, not only
the faces. It gives a whole simplicial isomorphism and exact naturality
for the same original map and its supplied endpoint vertices.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.MappingSpaceOpposite

variable {X Y : SSet.{u}}

private theorem right_operator (x y : (Δ[0] : SSet.{u}) ⟶ X) {n m : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋m⦌) (σ : (mappingSpaceRight X x y).obj (op ⦋m⦌)) :
    ((mappingSpaceRight.simplexEquivSucc X x y n)
      ((mappingSpaceRight X x y).map φ.op σ)).val =
      SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋0⦌)) ≫
        ((mappingSpaceRight.simplexEquivSucc X x y m) σ).val := by
  change (joinStdSimplexIso n 0).inv ≫
      ((join.map (SSet.stdSimplex.map φ)).app Δ[0] ≫ σ.val) = _
  rw [← Category.assoc, joinStdSimplexIso_inv_comp_join_map_app, Category.assoc]
  rfl

private theorem left_operator (x y : (Δ[0] : SSet.{u}) ⟶ X) {n m : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋m⦌) (σ : (mappingSpaceLeft X x y).obj (op ⦋m⦌)) :
    ((mappingSpaceLeft.simplexEquivSuccStd X x y n)
      ((mappingSpaceLeft X x y).map φ.op σ)).val =
      SSet.stdSimplex.map
        ((zeroAddSuccIso n).inv ≫ AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) φ ≫
          (zeroAddSuccIso m).hom) ≫
        ((mappingSpaceLeft.simplexEquivSuccStd X x y m) σ).val := by
  rw [mappingSpaceLeft.simplexEquivSuccStd_val, mappingSpaceLeft.simplexEquivSuccStd_val,
    mappingSpaceLeft.map_val]
  rw [← Category.assoc (joinStdSimplexIso 0 n).inv,
    joinStdSimplexIso_inv_comp_join_obj_map, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (SSet.stdSimplex.map (zeroAddSuccIso m).hom)
      (SSet.stdSimplex.map (zeroAddSuccIso m).inv),
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem rev_rightShift {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.rev.map
      (AugmentedSimplexCategory.tensorHomOf (SimplexCategory.rev.map φ) (𝟙 ⦋0⦌)) =
      (zeroAddSuccIso n).inv ≫ AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) φ ≫
        (zeroAddSuccIso m).hom := by
  have h := congrArg (fun f => SimplexCategory.rev.map f)
    (MappingSpaceOppositeOperators.rev_normalizedLeftShift φ)
  simpa only [SimplexCategory.rev_map_rev_map] using h.symm

/-- The exact degreewise opposite comparison intertwines every original simplicial operator. -/
theorem mappingSimplexEquiv_naturality (x y : (Δ[0] : SSet.{u}) ⟶ X) {n m : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋m⦌) (σ : (mappingSpaceRight X x y).obj (op ⦋m⦌)) :
    mappingSimplexEquiv X x y n
        ((mappingSpaceRight X x y).map (SimplexCategory.rev.map φ).op σ) =
      (mappingSpaceLeft X.op (vertex y) (vertex x)).map φ.op
        (mappingSimplexEquiv X x y m σ) := by
  apply (mappingSpaceLeft.simplexEquivSuccStd X.op (vertex y) (vertex x) n).injective
  apply Subtype.ext
  rw [mappingSimplexEquiv_readback, right_operator, simplexEquiv_precomp,
    left_operator, mappingSimplexEquiv_readback, rev_rightShift]
  rfl

/-- The whole original right mapping space, reversed, is isomorphic to the left mapping space of the
  opposite original simplicial set. -/
def iso (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    (mappingSpaceRight X x y).op ≅ mappingSpaceLeft X.op (vertex y) (vertex x) :=
  NatIso.ofComponents (fun n =>
    (opObjEquiv.trans (mappingSimplexEquiv X x y n.unop.len)).toIso) (fun α => by
      apply ConcreteCategory.hom_ext
      intro σ
      change mappingSimplexEquiv X x y _
          ((mappingSpaceRight X x y).map (SimplexCategory.rev.map α.unop).op (opObjEquiv σ)) =
        (mappingSpaceLeft X.op (vertex y) (vertex x)).map α
          (mappingSimplexEquiv X x y _ (opObjEquiv σ))
      exact mappingSimplexEquiv_naturality x y α.unop (opObjEquiv σ))

/-- The whole isomorphism retains the exact original opposite standard simplex in every degree. -/
theorem iso_hom_readback (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
    (σ : (mappingSpaceRight X x y).op.obj (op ⦋n⦌)) :
    ((mappingSpaceLeft.simplexEquivSuccStd X.op (vertex y) (vertex x) n)
      ((iso X x y).hom.app _ σ)).val =
      (SSet.stdSimplex.opIso ⦋n + 1⦌).inv ≫
        opFunctor.map ((mappingSpaceRight.simplexEquivSucc X x y n) (opObjEquiv σ)).val := by
  exact (mappingSimplexEquiv_readback X x y n (opObjEquiv σ)).trans
    (simplexEquiv_apply X (n + 1) _)

/-- Equality transport changes only the literal endpoint labels of the same original left mapping space. -/
def leftEndpointIso {x x' y y' : (Δ[0] : SSet.{u}) ⟶ X} (hx : x = x') (hy : y = y') :
    mappingSpaceLeft X x y ≅ mappingSpaceLeft X x' y' :=
  eqToIso (congrArg₂ (mappingSpaceLeft X) hx hy)

private theorem leftEndpointIso_val {x x' y y' : (Δ[0] : SSet.{u}) ⟶ X}
    (hx : x = x') (hy : y = y') (n : ℕ)
    (σ : (mappingSpaceLeft X x y).obj (op ⦋n⦌)) :
    ((mappingSpaceLeft.simplexEquivSuccStd X x' y' n)
      ((leftEndpointIso hx hy).hom.app _ σ)).val =
        ((mappingSpaceLeft.simplexEquivSuccStd X x y n) σ).val := by
  cases hx
  cases hy
  rfl

private theorem left_postcomp (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) (n : ℕ)
    (σ : (mappingSpaceLeft X x y).obj (op ⦋n⦌)) :
    ((mappingSpaceLeft.simplexEquivSuccStd Y (x ≫ f) (y ≫ f) n)
      ((mappingSpaceLeft.map X x y f).app _ σ)).val =
        ((mappingSpaceLeft.simplexEquivSuccStd X x y n) σ).val ≫ f := by
  rw [mappingSpaceLeft.simplexEquivSuccStd_val, mappingSpaceLeft.simplexEquivSuccStd_val,
    mappingSpaceLeft.map_app_val]
  simp only [Category.assoc]

private theorem right_postcomp (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) (n : ℕ)
    (σ : (mappingSpaceRight X x y).obj (op ⦋n⦌)) :
    ((mappingSpaceRight.simplexEquivSucc Y (x ≫ f) (y ≫ f) n)
      ((mappingSpaceRight.map X x y f).app _ σ)).val =
        ((mappingSpaceRight.simplexEquivSucc X x y n) σ).val ≫ f := by
  change (joinStdSimplexIso n 0).inv ≫ (σ.val ≫ f) =
    ((joinStdSimplexIso n 0).inv ≫ σ.val) ≫ f
  exact (Category.assoc _ _ _).symm

/-- The same actual opposite map on left mapping spaces, with only the proved endpoint equality transport. -/
def leftMap (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    mappingSpaceLeft X.op (vertex y) (vertex x) ⟶
      mappingSpaceLeft Y.op (vertex (y ≫ f)) (vertex (x ≫ f)) :=
  mappingSpaceLeft.map X.op (vertex y) (vertex x) (opFunctor.map f) ≫
    (leftEndpointIso (vertex_map y f).symm (vertex_map x f).symm).hom

/-- The whole opposite isomorphism is natural for the same original map and each individual supplied endpoint. -/
theorem iso_naturality (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    opFunctor.map (mappingSpaceRight.map X x y f) ≫ (iso Y (x ≫ f) (y ≫ f)).hom =
      (iso X x y).hom ≫ leftMap x y f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  apply (mappingSpaceLeft.simplexEquivSuccStd Y.op (vertex (y ≫ f)) (vertex (x ≫ f))
    n.unop.len).injective
  apply Subtype.ext
  change ((mappingSpaceLeft.simplexEquivSuccStd Y.op (vertex (y ≫ f)) (vertex (x ≫ f)) _)
      ((iso Y (x ≫ f) (y ≫ f)).hom.app _
        ((opFunctor.map (mappingSpaceRight.map X x y f)).app _ σ))).val =
    ((mappingSpaceLeft.simplexEquivSuccStd Y.op (vertex (y ≫ f)) (vertex (x ≫ f)) _)
      ((leftEndpointIso (vertex_map y f).symm (vertex_map x f).symm).hom.app _
        ((mappingSpaceLeft.map X.op (vertex y) (vertex x) (opFunctor.map f)).app _
          ((iso X x y).hom.app _ σ)))).val
  rw [leftEndpointIso_val, left_postcomp]
  rw [iso_hom_readback, iso_hom_readback]
  simp only [opFunctor_map, Equiv.apply_symm_apply]
  rw [right_postcomp, Functor.map_comp, Category.assoc]

end SSet.MappingSpaceOpposite
