/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalCylinderExact
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorBoundaryZero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Literal relative interval and double-point product comparisons

The original scalar product has its supplied source projection. Swapping
its coordinates gives the original source-first fixed-base cylinder.
Its preserved double-point coproduct and native zero units retain both
whole original endpoint copies. No base or source fibrancy is required.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The original scalar double point, with its two distinct entire point copies. -/
abbrev relativeIntervalDoublePoint : SSet.{u} := (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})

/-- The original two scalar endpoints form the supplied whole interval boundary. -/
def relativeIntervalWholeBoundary : relativeIntervalDoublePoint.{u} ⟶ (Δ[1] : SSet.{u}) :=
  coprod.desc (stdSimplex.δ (1 : Fin 2)) (stdSimplex.δ (0 : Fin 2))

/-- Swapping the actual two coordinates retains the original fixed-base source projection. -/
def relativeIntervalProductIso (Z : Marked.{u}) (X : Over Z) :
    (overParameterFunctor Z X).obj (Δ[1] : SSet.{u}) ≅ (relativeIntervalCylinder Z).I.obj X :=
  Over.isoMk (prodSwapIso (max (Δ[1] : SSet.{u})) X.left) (by apply Hom.ext; rfl)

/-- The original zero unit has the exact source-functor object used by native coproduct preservation. -/
def relativePointProductIso (Z : Marked.{u}) (X : Over Z) :
    (overParameterFunctor Z X).obj (Δ[0] : SSet.{u}) ≅ X :=
  (overScalarTensorZeroNatIso Z).app X

/-- The entire scalar double-point product is the native coproduct of the same two original slice objects. -/
def relativeDoublePointProductIso (Z : Marked.{u}) (X : Over Z) :
    (overParameterFunctor Z X).obj relativeIntervalDoublePoint.{u} ≅ X ⨿ X := by
  let G := overParameterFunctor Z X
  let _ : PreservesColimitsOfSize.{0, 0} G := (overParameterAdjunction Z X).leftAdjoint_preservesColimits
  exact (PreservesColimitPair.iso G (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})).symm ≪≫
    coprod.mapIso (relativePointProductIso Z X) (relativePointProductIso Z X)

/-- The first preserved endpoint copy retains exactly its native zero unit and original scalar inclusion. -/
theorem relativeDoublePointProductIso_inv_inl (Z : Marked.{u}) (X : Over Z) :
    (coprod.inl : X ⟶ X ⨿ X) ≫ (relativeDoublePointProductIso Z X).inv =
      (relativePointProductIso Z X).inv ≫
        (overParameterFunctor Z X).map (coprod.inl : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}) := by
  let G := overParameterFunctor Z X
  let E : SSet.{u} := Δ[0]
  let _ : PreservesColimitsOfSize.{0, 0} G := (overParameterAdjunction Z X).leftAdjoint_preservesColimits
  change coprod.inl ≫ (coprod.map _ _ ≫ coprodComparison G E E) = _
  rw [← Category.assoc, coprod.inl_map, Category.assoc, inl_coprodComparison]

/-- The second endpoint copy has the same complete original inverse-unit formula. -/
theorem relativeDoublePointProductIso_inv_inr (Z : Marked.{u}) (X : Over Z) :
    (coprod.inr : X ⟶ X ⨿ X) ≫ (relativeDoublePointProductIso Z X).inv =
      (relativePointProductIso Z X).inv ≫
        (overParameterFunctor Z X).map (coprod.inr : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}) := by
  let G := overParameterFunctor Z X
  let E : SSet.{u} := Δ[0]
  let _ : PreservesColimitsOfSize.{0, 0} G := (overParameterAdjunction Z X).leftAdjoint_preservesColimits
  change coprod.inr ≫ (coprod.map _ _ ≫ coprodComparison G E E) = _
  rw [← Category.assoc, coprod.inr_map, Category.assoc, inr_coprodComparison]

/-- The whole original boundary product agrees with the actual relative cylinder boundary, including both
  endpoint maps. -/
theorem relativeDoublePointProductIso_boundary_inv (Z : Marked.{u}) (X : Over Z) :
    (relativeDoublePointProductIso Z X).inv ≫
        (overParameterFunctor Z X).map relativeIntervalWholeBoundary.{u} ≫
        (relativeIntervalProductIso Z X).hom = ((relativeIntervalCylinder Z).app X).i := by
  let G := overParameterFunctor Z X
  let e := (relativeDoublePointProductIso Z X).inv
  let a : G.obj relativeIntervalDoublePoint.{u} ⟶ G.obj (Δ[1] : SSet.{u}) :=
    G.map relativeIntervalWholeBoundary.{u}
  let v := (relativeIntervalProductIso Z X).hom
  change e ≫ a ≫ v = _
  apply coprod.hom_ext
  · calc
      (coprod.inl : X ⟶ X ⨿ X) ≫ (e ≫ a ≫ v) = (coprod.inl ≫ e) ≫ a ≫ v :=
        (Category.assoc _ _ _).symm
      _ = ((relativePointProductIso Z X).inv ≫ G.map coprod.inl) ≫ a ≫ v :=
        congrArg (fun z => z ≫ a ≫ v) (relativeDoublePointProductIso_inv_inl Z X)
      _ = (relativePointProductIso Z X).inv ≫
          G.map (stdSimplex.δ (1 : Fin 2)) ≫ v := by
        change (_ ≫ G.map coprod.inl) ≫ G.map relativeIntervalWholeBoundary.{u} ≫ v = _
        rw [Category.assoc, ← Category.assoc (G.map coprod.inl) (G.map relativeIntervalWholeBoundary.{u}) v,
          ← CategoryTheory.Functor.map_comp, relativeIntervalWholeBoundary, coprod.inl_desc]
      _ = coprod.inl ≫ ((relativeIntervalCylinder Z).app X).i := by
        rw [Precylinder.inl_i]
        apply Over.OverMorphism.ext
        apply Hom.ext
        rfl
  · calc
      (coprod.inr : X ⟶ X ⨿ X) ≫ (e ≫ a ≫ v) = (coprod.inr ≫ e) ≫ a ≫ v :=
        (Category.assoc _ _ _).symm
      _ = ((relativePointProductIso Z X).inv ≫ G.map coprod.inr) ≫ a ≫ v :=
        congrArg (fun z => z ≫ a ≫ v) (relativeDoublePointProductIso_inv_inr Z X)
      _ = (relativePointProductIso Z X).inv ≫
          G.map (stdSimplex.δ (0 : Fin 2)) ≫ v := by
        change (_ ≫ G.map coprod.inr) ≫ G.map relativeIntervalWholeBoundary.{u} ≫ v = _
        rw [Category.assoc, ← Category.assoc (G.map coprod.inr) (G.map relativeIntervalWholeBoundary.{u}) v,
          ← CategoryTheory.Functor.map_comp, relativeIntervalWholeBoundary, coprod.inr_desc]
      _ = coprod.inr ≫ ((relativeIntervalCylinder Z).app X).i := by
        rw [Precylinder.inr_i]
        apply Over.OverMorphism.ext
        apply Hom.ext
        rfl

end SSet.Marked
