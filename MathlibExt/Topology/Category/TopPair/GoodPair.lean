/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

module

public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Good topological pairs

A good pair has a nonempty closed subspace that is a strong deformation retract
of a chosen open neighborhood.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopPair

/-- The canonical lift of a pair embedding to a subset containing its range. -/
def neighborhoodInclusion (P : TopPair.{u}) (U : Set P.fst)
    (hU : Set.range P.map ⊆ U) : P.snd ⟶ TopCat.of U :=
  TopCat.ofHom
    { toFun := fun a ↦ ⟨P.map a, hU ⟨a, rfl⟩⟩
      continuous_toFun := P.map.hom.continuous.subtype_mk _ }

@[simp]
theorem neighborhoodInclusion_val (P : TopPair.{u}) (U : Set P.fst)
    (hU : Set.range P.map ⊆ U) (a : P.snd) :
    (neighborhoodInclusion P U hU a).1 = P.map a :=
  rfl

/-- Chosen data exhibiting a topological pair as a good pair. -/
structure GoodPairData (P : TopPair.{u}) where
  /-- The subspace is nonempty. -/
  nonempty_snd : Nonempty P.snd
  /-- The embedded image of the subspace is closed in the ambient space. -/
  isClosed_range : IsClosed (Set.range P.map)
  /-- A chosen open neighborhood of the embedded subspace. -/
  neighborhood : Set P.fst
  /-- The chosen neighborhood is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The embedded subspace lies in the chosen neighborhood. -/
  range_subset_neighborhood : Set.range P.map ⊆ neighborhood
  /-- A retraction from the neighborhood to the original subspace type. -/
  retraction : TopCat.of neighborhood ⟶ P.snd
  /-- The identity deforms to inclusion after retraction, fixing the subspace. -/
  deformation :
    ContinuousMap.HomotopyRel
      ((𝟙 (TopCat.of neighborhood)) :
        TopCat.of neighborhood ⟶ TopCat.of neighborhood).hom
      (retraction ≫
        neighborhoodInclusion P neighborhood range_subset_neighborhood).hom
      (Set.range
        (neighborhoodInclusion P neighborhood range_subset_neighborhood).hom)

namespace GoodPairData

variable {P : TopPair.{u}} (d : GoodPairData P)

/-- The canonical inclusion of the subspace into the chosen neighborhood. -/
abbrev inclusion : P.snd ⟶ TopCat.of d.neighborhood :=
  neighborhoodInclusion P d.neighborhood d.range_subset_neighborhood

/-- The pair embedding together with closedness of its image. -/
theorem isClosedEmbedding_map (d : GoodPairData P) :
    Topology.IsClosedEmbedding P.map :=
  ⟨P.isEmbedding_map, d.isClosed_range⟩

/-- The canonical inclusion into the neighborhood remains an embedding. -/
theorem isEmbedding_inclusion : Topology.IsEmbedding d.inclusion :=
  P.isEmbedding_map.codRestrict d.neighborhood
    (fun a ↦ d.range_subset_neighborhood ⟨a, rfl⟩)

/-- The relative deformation forces the retraction to be the identity on the subspace. -/
theorem inclusion_comp_retraction : d.inclusion ≫ d.retraction = 𝟙 P.snd := by
  apply TopCat.hom_ext
  ext a
  apply d.isEmbedding_inclusion.injective
  simpa using
    (d.deformation.fst_eq_snd
      (x := d.inclusion a) ⟨a, rfl⟩).symm

/-- The subspace is homotopy equivalent to its chosen open neighborhood. -/
noncomputable def neighborhoodHomotopyEquiv :
    ContinuousMap.HomotopyEquiv P.snd d.neighborhood where
  toFun := d.inclusion.hom
  invFun := d.retraction.hom
  left_inv := by
    have h := congrArg TopCat.Hom.hom d.inclusion_comp_retraction
    rw [show d.retraction.hom.comp d.inclusion.hom =
      ContinuousMap.id P.snd from h]
  right_inv := ⟨d.deformation.symm.toHomotopy⟩

@[simp]
theorem neighborhoodHomotopyEquiv_toFun :
    d.neighborhoodHomotopyEquiv.toFun = d.inclusion.hom :=
  rfl

@[simp]
theorem neighborhoodHomotopyEquiv_invFun :
    d.neighborhoodHomotopyEquiv.invFun = d.retraction.hom :=
  rfl

/-- The ambient space paired with the chosen neighborhood. -/
abbrev neighborhoodPair : TopPair.{u} :=
  TopPair.ofSubset d.neighborhood

/-- Enlarge the subspace of a good pair to its chosen neighborhood. -/
def toNeighborhoodPair : P ⟶ d.neighborhoodPair :=
  TopPair.ofHom (𝟙 P.fst) d.inclusion (by
    apply TopCat.hom_ext
    ext a
    rfl)

@[simp] theorem toNeighborhoodPair_fst :
    TopPair.Hom.fst d.toNeighborhoodPair = 𝟙 P.fst := rfl

@[simp] theorem toNeighborhoodPair_snd :
    TopPair.Hom.snd d.toNeighborhoodPair = d.inclusion := rfl

end GoodPairData

/-- The object property of admitting chosen good-pair data. -/
def isGoodPair : ObjectProperty TopPair.{u} :=
  fun P ↦ Nonempty (GoodPairData P)

/-- The full subcategory of good topological pairs. -/
abbrev GoodPair := isGoodPair.FullSubcategory

namespace GoodPair

/-- Choose good-pair data from the proof stored by the full subcategory. -/
noncomputable def data (P : GoodPair.{u}) : GoodPairData P.obj :=
  Classical.choice P.property

/-- Forget that a pair is good. -/
abbrev inclusion : GoodPair.{u} ⥤ TopPair.{u} :=
  ObjectProperty.ι isGoodPair

end GoodPair

end TopPair
