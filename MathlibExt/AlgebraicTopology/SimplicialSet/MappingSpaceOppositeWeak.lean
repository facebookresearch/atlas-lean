/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MappingSpaceOpposite
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OppositeBrown
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW
public import MathlibExt.AlgebraicTopology.SimplicialSet.Descent

/-!
# Same-map weak comparison between the two opposite mapping orientations

The whole natural mapping-space Iso and Brown's lemma for the genuine
Kan–Quillen opposite functor transfer right mapping weakness to the
actual left mapping-space map of the opposite original map. Every
original endpoint is retained; no equivalence between object classes
or assumed mapping-space comparison is supplied as an input.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.MappingSpaceOpposite
variable {X Y : SSet.{u}}

/-- The whole same-map opposite comparison is an isomorphism in the actual arrow category. -/
def mapArrowIso (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    Arrow.mk (opFunctor.map (mappingSpaceRight.map X x y f)) ≅
      Arrow.mk (leftMap x y f) :=
  Arrow.isoMk (iso X x y) (iso Y (x ≫ f) (y ≫ f)) (iso_naturality x y f).symm

/-- Weakness of the supplied actual right mapping map gives weakness of the actual opposite-left map, at the
  same original endpoints. -/
theorem left_map_weak [Quasicategory X] [Quasicategory Y]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y)
    (hf : realizationWeakEquivalences (mappingSpaceRight.map X x y f)) :
    realizationWeakEquivalences
      (mappingSpaceLeft.map X.op (vertex y) (vertex x) (opFunctor.map f)) := by
  have hop := modelCategoryQuillen.op_map_weak hf
  have h := (realizationWeakEquivalences.arrow_mk_iso_iff (mapArrowIso x y f)).mp hop
  change realizationWeakEquivalences
    (mappingSpaceLeft.map X.op (vertex y) (vertex x) (opFunctor.map f) ≫
      (leftEndpointIso (vertex_map y f).symm (vertex_map x f).symm).hom) at h
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso _ _).mp h

end SSet.MappingSpaceOpposite

namespace SSet
variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- Original right Dwyer–Kan full faithfulness gives the actual left full-faithfulness condition for the
  opposite original map. -/
theorem dwyerKanFullyFaithful.left_op [Quasicategory X] [Quasicategory Y]
    (hf : dwyerKanFullyFaithful f) : dwyerKanFullyFaithfulLeft (opFunctor.map f) := by
  intro a b
  obtain ⟨y, rfl⟩ := (MappingSpaceOpposite.simplexEquiv X 0).surjective a
  obtain ⟨x, rfl⟩ := (MappingSpaceOpposite.simplexEquiv X 0).surjective b
  exact MappingSpaceOpposite.left_map_weak x y f (hf x y)

end SSet
