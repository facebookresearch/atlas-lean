/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# The actual right mapping-space functor on two pointed objects

A map under the literal coproduct of two vertices fixes the supplied
source and target. The right mapping spaces therefore form an actual
functor, with their whole original join maps and both endpoint equations.
Its comparison with the existing unwrapped mapping-space map is a whole
arrow isomorphism; no weak-equivalence or fibrancy conclusion is assumed.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.PointedRightMappingSpace

/-- The two individual original endpoint vertices. -/
def endpointPair : SSet.{u} := (Δ[0] : SSet.{u}) ⨿ Δ[0]

/-- The supplied original source vertex of a two-pointed simplicial set. -/
def sourceVertex (P : Under endpointPair.{u}) : (Δ[0] : SSet.{u}) ⟶ P.right :=
  coprod.inl ≫ P.hom

/-- The supplied original target vertex of that same two-pointed simplicial set. -/
def targetVertex (P : Under endpointPair.{u}) : (Δ[0] : SSet.{u}) ⟶ P.right :=
  coprod.inr ≫ P.hom

/-- Every actual pointed map retains the same supplied source boundary. -/
theorem sourceVertex_map {P Q : Under endpointPair.{u}} (f : P ⟶ Q) :
    sourceVertex P ≫ f.right = sourceVertex Q :=
  (Category.assoc _ _ _).trans (congrArg (fun g => coprod.inl ≫ g) (Under.w f))

/-- Every actual pointed map retains the same supplied target boundary. -/
theorem targetVertex_map {P Q : Under endpointPair.{u}} (f : P ⟶ Q) :
    targetVertex P ≫ f.right = targetVertex Q :=
  (Category.assoc _ _ _).trans (congrArg (fun g => coprod.inr ≫ g) (Under.w f))

/-- The actual right mapping object at those two individual original endpoints. -/
def object (P : Under endpointPair.{u}) : SSet.{u} :=
  mappingSpaceRight P.right (sourceVertex P) (targetVertex P)

/-- The actual pointed mapping-space map postcomposes the whole original join simplex. -/
def map {P Q : Under endpointPair.{u}} (f : P ⟶ Q) : object P ⟶ object Q where
  app n := ↾fun σ => ⟨σ.val ≫ f.right, by
    constructor
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ f.right) σ.2.1).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun g => toDeltaZero _ ≫ g) (sourceVertex_map f))))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ f.right) σ.2.2).trans (targetVertex_map f))⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The whole underlying join map is precisely the original postcomposition. -/
theorem map_val {P Q : Under endpointPair.{u}} (f : P ⟶ Q)
    (n : SimplexCategoryᵒᵖ) (σ : (object P).obj n) :
    ((map f).app n σ).val = σ.val ≫ f.right := rfl

/-- Right mapping spaces form a genuine functor on the actual two-pointed category. -/
def functor : Under endpointPair.{u} ⥤ SSet.{u} where
  obj := object
  map := map
  map_id P := by
    ext n σ
    apply Subtype.ext
    exact Category.comp_id _
  map_comp f g := by
    ext n σ
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm

/-- Store the two supplied original vertex maps as their actual coproduct map. -/
def of (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) : Under endpointPair.{u} :=
  Under.mk (coprod.desc x y)

/-- Source readback of the two supplied original endpoints. -/
theorem sourceVertex_of (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    sourceVertex (of X x y) = x := coprod.inl_desc _ _

/-- Target readback of those same original endpoints. -/
theorem targetVertex_of (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    targetVertex (of X x y) = y := coprod.inr_desc _ _

/-- The same original simplicial map between the two actually pointed carriers. -/
def ofMap {X Y : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    of X x y ⟶ of Y (x ≫ f) (y ≫ f) :=
  Under.homMk f (by
    change coprod.desc x y ≫ f = coprod.desc (x ≫ f) (y ≫ f)
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc])

/-- Transport only the two proved endpoint equalities of a genuine right mapping object. -/
def endpointIso {X : SSet.{u}} {x y x' y' : (Δ[0] : SSet.{u}) ⟶ X}
    (hx : x = x') (hy : y = y') : mappingSpaceRight X x y ≅ mappingSpaceRight X x' y' := by
  subst x'
  subst y'
  exact Iso.refl _

/-- Endpoint equality transport leaves the entire individual original join map unchanged. -/
theorem endpointIso_hom_val {X : SSet.{u}} {x y x' y' : (Δ[0] : SSet.{u}) ⟶ X}
    (hx : x = x') (hy : y = y') (n : SimplexCategoryᵒᵖ)
    (σ : (mappingSpaceRight X x y).obj n) :
    ((endpointIso hx hy).hom.app n σ).val = σ.val := by
  subst x'
  subst y'
  rfl

/-- The actual pointed mapping object is the original unwrapped right mapping space. -/
def originalIso (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    functor.obj (of X x y) ≅ mappingSpaceRight X x y :=
  endpointIso (sourceVertex_of X x y) (targetVertex_of X x y)

/-- The pointed/unwrapped comparison retains every whole original join simplex. -/
theorem originalIso_hom_val (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)
    (n : SimplexCategoryᵒᵖ) (σ : (functor.obj (of X x y)).obj n) :
    ((originalIso X x y).hom.app n σ).val = σ.val :=
  endpointIso_hom_val _ _ _ _

/-- The complete comparison square uses exactly the same original mappingSpaceRight.map. -/
theorem originalIso_naturality {X Y : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    (f : X ⟶ Y) :
    functor.map (ofMap x y f) ≫ (originalIso Y (x ≫ f) (y ≫ f)).hom =
      (originalIso X x y).hom ≫ mappingSpaceRight.map X x y f := by
  ext n σ
  apply Subtype.ext
  exact (originalIso_hom_val Y (x ≫ f) (y ≫ f) n _).trans
    (congrArg (fun g => g ≫ f) (originalIso_hom_val X x y n σ)).symm

/-- The genuine whole pointed map is isomorphic as an arrow to the same original unwrapped right mapping-space map. -/
def originalMapArrowIso {X Y : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    Arrow.mk (functor.map (ofMap x y f)) ≅ Arrow.mk (mappingSpaceRight.map X x y f) :=
  Arrow.isoMk (originalIso X x y) (originalIso Y (x ≫ f) (y ≫ f))
    (originalIso_naturality x y f).symm

end SSet.PointedRightMappingSpace
