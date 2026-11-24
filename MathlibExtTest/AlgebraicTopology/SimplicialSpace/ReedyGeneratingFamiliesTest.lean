/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGeneratingFamilies

/-! # Public use of the literal Reedy families -/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SimplicialSpace.ReedyGeneratingFamilies.Test

/-- Both boundary injections recover the original tensor-factor maps. -/
theorem boundary_legs (m n : ℕ) :
    (boundaryPushout.{u} m n).inl ≫ (boundaryFamily.{u} (m, n)).hom =
        (innerTensorBifunctor.obj
          (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[m] : SSet.{u})))).map
            (SSet.boundary.{u} n).ι ∧
      (boundaryPushout.{u} m n).inr ≫ (boundaryFamily.{u} (m, n)).hom =
        (innerTensorBifunctor.map (outerBoundaryMap.{u} m)).app (Δ[n] : SSet.{u}) :=
  ⟨(boundaryPushout.{u} m n).inl_ι, (boundaryPushout.{u} m n).inr_ι⟩

/-- Both horn injections recover the original maps, for every positive dimension and face. -/
theorem horn_legs (m n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (hornPushout.{u} m ⟨n, hn⟩ i).inl ≫ (hornFamily.{u} (m, ⟨⟨n, hn⟩, i⟩)).hom =
        (innerTensorBifunctor.obj
          (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[m] : SSet.{u})))).map
            (SSet.horn.{u} n i).ι ∧
      (hornPushout.{u} m ⟨n, hn⟩ i).inr ≫ (hornFamily.{u} (m, ⟨⟨n, hn⟩, i⟩)).hom =
        (innerTensorBifunctor.map (outerBoundaryMap.{u} m)).app (Δ[n] : SSet.{u}) :=
  ⟨(hornPushout.{u} m ⟨n, hn⟩ i).inl_ι, (hornPushout.{u} m ⟨n, hn⟩ i).inr_ι⟩

/-- Neither zero boundary dimension is excluded from the literal family. -/
theorem zero_boundaries (n : ℕ) :
    I.{u} (boundaryFamily.{u} (0, n)).hom ∧ I.{u} (boundaryFamily.{u} (n, 0)).hom :=
  ⟨MorphismProperty.ofHoms.mk (f := fun b : BoundaryIndex => (boundaryFamily.{u} b).hom) (0, n), MorphismProperty.ofHoms.mk (f := fun b : BoundaryIndex => (boundaryFamily.{u} b).hom) (n, 0)⟩

/-- Every original positive-dimensional horn, including either endpoint, is in the family. -/
theorem original_horn (m n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    J.{u} (hornFamily.{u} (m, ⟨⟨n, hn⟩, i⟩)).hom :=
  MorphismProperty.ofHoms.mk (f := fun h : HornIndex => (hornFamily.{u} h).hom) (m, ⟨⟨n, hn⟩, i⟩)

/-- The first horn dimension includes both original faces at every outer dimension. -/
theorem both_one_dimensional_horns (m : ℕ) :
    J.{u} (hornFamily.{u} (m, ⟨⟨1, by decide⟩, 0⟩)).hom ∧
      J.{u} (hornFamily.{u} (m, ⟨⟨1, by decide⟩, 1⟩)).hom :=
  ⟨MorphismProperty.ofHoms.mk (f := fun h : HornIndex => (hornFamily.{u} h).hom) (m, ⟨⟨1, by decide⟩, 0⟩),
    MorphismProperty.ofHoms.mk (f := fun h : HornIndex => (hornFamily.{u} h).hom) (m, ⟨⟨1, by decide⟩, 1⟩)⟩

/-- The codomain uses the outer simplex in the outer coordinate and scalar in the inner one. -/
theorem target_bidegree (m n : ℕ) (r s : SimplexCategoryᵒᵖ) :
    (((boundaryFamily.{u} (m, n)).right.diagram.obj r).obj s) =
      ((Δ[m] : SSet.{u}).obj r × (Δ[n] : SSet.{u}).obj s) := rfl

end SimplicialSpace.ReedyGeneratingFamilies.Test
