/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootPrism

/-!
# The original marked critical-root prisms preserve the entire horn

The original critical replacement avoids the predecessor and replaces it
by the same original last vertex. All other vertices remain unchanged.
The actual whole union and both genuine interval prisms therefore keep
every original lower face and retain every upper face, using the last
upper face for the original critical predecessor. All entire source
words, original intersections and critical maximum marks are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The same original final degeneracy followed by its exact original critical coface is the actual vertex
replacement. -/
def coneCriticalReplacementVertex (n : ℕ) (i : Vertex.{u} (n + 2)) : Vertex.{u} (n + 2) :=
  coneCriticalReinsert n (coneCriticalMaximumCollapse n i)

/-- The original vertex replacement avoids precisely the same original critical predecessor. -/
theorem coneCriticalReplacementVertex_ne_previous (n : ℕ) (i : Vertex.{u} (n + 2)) :
    coneCriticalReplacementVertex n i ≠ coneCriticalPrevious n := coneCriticalReinsert_ne_previous n _

/-- The original predecessor is sent to its exact same original final-edge target. -/
theorem coneCriticalReplacementVertex_previous (n : ℕ) :
    coneCriticalReplacementVertex.{u} n (coneCriticalPrevious n) = coneCriticalLast n := by
  have h : coneCriticalReinsert.{u} n (ULift.up (Fin.last (n + 1))) = coneCriticalLast n := by
    change ULift.up ((Fin.last (n + 1)).castSucc.succAbove (Fin.last (n + 1))) = ULift.up (Fin.last (n + 2))
    exact congrArg ULift.up (Fin.succAbove_of_le_castSucc _ _ le_rfl)
  exact (congrArg (coneCriticalReinsert n) (coneCriticalMaximumCollapse_previous n)).trans h

/-- Every original vertex outside the predecessor retains its literal original value under the complete critical
replacement. -/
theorem coneCriticalReplacementVertex_of_ne (n : ℕ) (i : Vertex.{u} (n + 2)) (hi : i ≠ coneCriticalPrevious n) :
    coneCriticalReplacementVertex n i = i := by
  have h : i.down ≠ (Fin.last (n + 1)).castSucc := by
    intro h
    exact hi (congrArg ULift.up h)
  change ULift.up ((Fin.last (n + 1)).castSucc.succAbove ((Fin.last (n + 1)).predAbove i.down)) = i
  exact congrArg ULift.up (Fin.succAbove_predAbove h)

/-- The original complete replacement subset retains exactly the whole image under its same native original vertex
operator. -/
theorem coneCriticalRootReplacement_vertices (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    ((coneCriticalRootReplacementFunctor n).obj a).vertices = a.vertices.image (coneCriticalReplacementVertex n) :=
  Finset.image_image

/-- Every original nonfinal coordinate in the complete replacement came from that same original source coordinate. -/
theorem coneCriticalRootReplacement_mem_of_ne_last (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ≠ coneCriticalLast n)
    (h : j ∈ ((coneCriticalRootReplacementFunctor n).obj a).vertices) : j ∈ a.vertices := by
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp
    ((congrArg (fun s => j ∈ s) (coneCriticalRootReplacement_vertices n a)).mp h)
  by_cases hip : i = coneCriticalPrevious n
  · subst i
    exact (hj (hij.symm.trans (coneCriticalReplacementVertex_previous n))).elim
  · exact ((coneCriticalReplacementVertex_of_ne n i hip).symm.trans hij) ▸ hi

/-- Every entire original nonfinal coordinate in the same complete critical union came from its unchanged original
source subset. -/
theorem coneCriticalRootUnion_mem_of_ne_last (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ≠ coneCriticalLast n)
    (h : j ∈ (coneCriticalRootUnionSubset n a).vertices) : j ∈ a.vertices := by
  rcases Finset.mem_union.mp h with h | h
  · exact h
  · exact coneCriticalRootReplacement_mem_of_ne_last n a j hj h

/-- Every original coordinate other than the critical predecessor remains present in the same whole replacement
whenever it was originally present. -/
theorem coneCriticalRootReplacement_mem (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ≠ coneCriticalPrevious n) (h : j ∈ a.vertices) :
    j ∈ ((coneCriticalRootReplacementFunctor n).obj a).vertices := by
  apply (congrArg (fun s => j ∈ s) (coneCriticalRootReplacement_vertices n a)).mpr
  exact Finset.mem_image.mpr ⟨j, h, coneCriticalReplacementVertex_of_ne n j hj⟩

/-- The original last coordinate occurs in every whole replacement of an original subset containing the critical
predecessor. -/
theorem coneCriticalRootReplacement_last_mem (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (h : coneCriticalPrevious n ∈ a.vertices) : coneCriticalLast n ∈ ((coneCriticalRootReplacementFunctor n).obj
      a).vertices := by
  apply (congrArg (fun s => coneCriticalLast n ∈ s) (coneCriticalRootReplacement_vertices n a)).mpr
  exact Finset.mem_image.mpr ⟨coneCriticalPrevious n, h, coneCriticalReplacementVertex_previous n⟩

/-- The SAME original critical predecessor and final vertex remain distinct. -/
theorem coneCriticalPrevious_ne_last (n : ℕ) : coneCriticalPrevious.{u} n ≠ coneCriticalLast n := by
  intro h
  exact Fin.castSucc_ne_last _ (congrArg ULift.down h)

/-- The entire original smaller root coefficient enters the complete critical horn through its same whole marked
critical coface section. -/
def coneCriticalRootHornSection (n : ℕ) :
    coneWeight (⊥ : Vertex.{u} (n + 1)) ⟶ coneCriticalRootHornMarked.{u} n where
  hom := (coneRootCoordinateHorn (Fin.last (n + 2))).lift (coneCriticalRootSection n).hom (by
    intro q a ha
    obtain ⟨a, rfl⟩ := ha
    apply (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) _ _).mpr
    right
    refine ⟨⟨coneCriticalPrevious n, coneCriticalPrevious_pos.{u} n, coneCriticalPrevious_ne_last.{u} n⟩, fun t h => ?_⟩
    change coneCriticalPrevious n ∈ (a.obj t).vertices.image (coneCriticalReinsert n) at h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact coneCriticalReinsert_ne_previous n i hi)
  preserve he := (coneCriticalRootSection n).preserve he

/-- The whole original critical horn section retains its literal entire original target section after its unchanged
full horn inclusion. -/
theorem coneCriticalRootHornSection_inclusion (n : ℕ) :
    coneCriticalRootHornSection.{u} n ≫ coneCriticalRootHornMap n = coneCriticalRootSection n := Hom.ext rfl

/-- The complete original critical horn projects through its same entire original marked inclusion and exact
original final degeneracy. -/
def coneCriticalRootHornProjection (n : ℕ) :
    coneCriticalRootHornMarked.{u} n ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  coneCriticalRootHornMap n ≫ coneCriticalRootProjection n

/-- Both actual whole original marked critical horn maps retain the strict identity of every original smaller root
coefficient. -/
theorem coneCriticalRootHornSection_projection (n : ℕ) :
    coneCriticalRootHornSection.{u} n ≫ coneCriticalRootHornProjection n = 𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ coneCriticalRootProjection n) (coneCriticalRootHornSection_inclusion n)).trans
      (coneCriticalRootSection_projection n))

/-- Each original upper coordinate stays present throughout the entire original identity prism. -/
theorem coneCriticalIdentityCylinder_upper (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ∈ a.vertices) (t : Fin 2) :
    j ∈ (((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj (a, t)).vertices := by
  fin_cases t
  · exact hj
  · exact coneCriticalRootUnion_left n a hj

/-- Every original nonfinal lower coordinate stays absent throughout the whole original identity prism. -/
theorem coneCriticalIdentityCylinder_lower (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ∉ a.vertices) (hjl : j ≠ coneCriticalLast n) (t : Fin 2) :
    j ∉ (((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj (a, t)).vertices := by
  fin_cases t
  · exact hj
  · exact fun h => hj (coneCriticalRootUnion_mem_of_ne_last n a j hjl h)

/-- Every whole original upper coordinate outside the predecessor stays present throughout the entire replacement
prism. -/
theorem coneCriticalReplacementCylinder_upper (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ∈ a.vertices) (hjp : j ≠ coneCriticalPrevious n) (t : Fin 2) :
    j ∈ (((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj (a, t)).vertices := by
  fin_cases t
  · exact coneCriticalRootReplacement_mem n a j hjp hj
  · exact coneCriticalRootUnion_left n a hj

/-- The SAME original upper-predecessor coordinate has the original final upper coordinate throughout its complete
replacement prism. -/
theorem coneCriticalReplacementCylinder_previous (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (hj : coneCriticalPrevious n ∈ a.vertices) (t : Fin 2) :
    coneCriticalLast n ∈ (((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj (a, t)).vertices := by
  fin_cases t
  · exact coneCriticalRootReplacement_last_mem n a hj
  · exact coneCriticalRootUnion_right n a (coneCriticalRootReplacement_last_mem n a hj)

/-- Every whole original nonfinal lower coordinate stays absent throughout the complete original replacement prism. -/
theorem coneCriticalReplacementCylinder_lower (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2)))
    (j : Vertex.{u} (n + 2)) (hj : j ∉ a.vertices) (hjl : j ≠ coneCriticalLast n) (t : Fin 2) :
    j ∉ (((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj (a, t)).vertices := by
  fin_cases t
  · exact fun h => hj (coneCriticalRootReplacement_mem_of_ne_last n a j hjl h)
  · exact fun h => hj (coneCriticalRootUnion_mem_of_ne_last n a j hjl h)

/-- The complete original critical union preserves the same original horn subcomplex on every whole scalar word. -/
theorem coneCriticalRootUnion_horn_mem (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (a : (coneRootCoordinateHorn.{u} (Fin.last (n + 2)) : SSet.{u}).obj q) :
    ((coneCriticalRootHornMap n ≫ coneCriticalRootUnionMap n).hom.app q a) ∈
      (coneRootCoordinateHorn (Fin.last (n + 2))).obj q := by
  apply (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) _ _).mpr
  rcases (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) q a.val).mp a.property with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    exact ⟨j, fun t => coneCriticalRootUnion_left n (a.val.obj t) (hj t)⟩
  · right
    exact ⟨j, fun t h => hj t (coneCriticalRootUnion_mem_of_ne_last n (a.val.obj t) j.val j.property.2 h)⟩

/-- The whole original marked identity prism preserves the SAME original terminal horn at every original scalar and
parameter degree. -/
theorem coneCriticalRootIdentityPrism_horn_mem (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (z : (prod (max (Δ[1] : SSet.{u})) (coneCriticalRootHornMarked n)).toSSet.obj q) :
    ((prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootIdentityPrism n).hom.app q z) ∈
      (coneRootCoordinateHorn (Fin.last (n + 2))).obj q := by
  apply (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) _ _).mpr
  rcases (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) q z.2.val).mp z.2.property with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    exact ⟨j, fun t => coneCriticalIdentityCylinder_upper n (z.2.val.obj t) j.val (hj t)
      (SSet.stdSimplex.asOrderHom z.1 t)⟩
  · right
    exact ⟨j, fun t => coneCriticalIdentityCylinder_lower n (z.2.val.obj t) j.val (hj t) j.property.2
      (SSet.stdSimplex.asOrderHom z.1 t)⟩

/-- The whole original marked replacement prism preserves the complete original terminal horn, retaining each lower
coordinate and the full original upper-predecessor/upper-last relation. -/
theorem coneCriticalRootReplacementPrism_horn_mem (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (z : (prod (max (Δ[1] : SSet.{u})) (coneCriticalRootHornMarked n)).toSSet.obj q) :
    ((prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootReplacementPrism n).hom.app
      q z) ∈
      (coneRootCoordinateHorn (Fin.last (n + 2))).obj q := by
  apply (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) _ _).mpr
  rcases (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) q z.2.val).mp z.2.property with ⟨j, hj⟩ | ⟨j, hj⟩
  · by_cases hjp : j.val = coneCriticalPrevious n
    · left
      have hl : (⊥ : Vertex.{u} (n + 2)) < coneCriticalLast n := by
        change 0 < n + 2
        exact Nat.zero_lt_succ (n + 1)
      exact ⟨⟨coneCriticalLast n, hl⟩, fun t => coneCriticalReplacementCylinder_previous n (z.2.val.obj t)
        (hjp ▸ hj t) (SSet.stdSimplex.asOrderHom z.1 t)⟩
    · left
      exact ⟨j, fun t => coneCriticalReplacementCylinder_upper n (z.2.val.obj t) j.val (hj t) hjp
        (SSet.stdSimplex.asOrderHom z.1 t)⟩
  · right
    exact ⟨j, fun t => coneCriticalReplacementCylinder_lower n (z.2.val.obj t) j.val (hj t) j.property.2
      (SSet.stdSimplex.asOrderHom z.1 t)⟩

/-- The actual entire original critical union map restricts to its SAME whole original marked horn. -/
def coneCriticalRootHornUnionMap (n : ℕ) : coneCriticalRootHornMarked.{u} n ⟶ coneCriticalRootHornMarked.{u} n where
  hom := (coneRootCoordinateHorn (Fin.last (n + 2))).lift
    (coneCriticalRootHornMap n ≫ coneCriticalRootUnionMap n).hom (by
      intro q a ha
      obtain ⟨a, rfl⟩ := ha
      exact coneCriticalRootUnion_horn_mem n q a)
  preserve he := (coneCriticalRootHornMap n ≫ coneCriticalRootUnionMap n).preserve he

/-- The same whole original identity prism restricts to the entire original marked terminal horn with all original
parameters and marks. -/
def coneCriticalRootHornIdentityPrism (n : ℕ) :
    prod (max (Δ[1] : SSet.{u})) (coneCriticalRootHornMarked n) ⟶ coneCriticalRootHornMarked n where
  hom := (coneRootCoordinateHorn (Fin.last (n + 2))).lift
    (prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootIdentityPrism n).hom
    (by
      intro q z hz
      obtain ⟨z, rfl⟩ := hz
      exact coneCriticalRootIdentityPrism_horn_mem n q z)
  preserve he := (prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootIdentityPrism
    n).preserve he

/-- The entire same original replacement prism restricts to the whole original marked terminal horn, retaining its
genuine full lower and upper coordinate relations. -/
def coneCriticalRootHornReplacementPrism (n : ℕ) :
    prod (max (Δ[1] : SSet.{u})) (coneCriticalRootHornMarked n) ⟶ coneCriticalRootHornMarked n where
  hom := (coneRootCoordinateHorn (Fin.last (n + 2))).lift
    (prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootReplacementPrism n).hom
    (by
      intro q z hz
      obtain ⟨z, rfl⟩ := hz
      exact coneCriticalRootReplacementPrism_horn_mem n q z)
  preserve he := (prodMap (𝟙 (max (Δ[1] : SSet.{u}))) (coneCriticalRootHornMap n) ≫ coneCriticalRootReplacementPrism
    n).preserve he

/-- The complete original marked horn identity prism retains its literal whole identity at its original source
endpoint. -/
theorem coneCriticalRootHornIdentityPrism_source (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (coneCriticalRootHornMarked.{u} n)) ≫
      coneCriticalRootHornIdentityPrism n = (zeroParameterUnitIso .maximal (coneCriticalRootHornMarked n)).hom ≫ 𝟙 _
        := by
  apply Hom.ext
  ext q z
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj
    (z.2.val.obj t, (1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = z.2.val.obj t
  rw [hz]
  rfl

/-- The complete original marked horn identity prism retains the SAME entire original horn union at its target
endpoint. -/
theorem coneCriticalRootHornIdentityPrism_target (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 (coneCriticalRootHornMarked.{u} n)) ≫
      coneCriticalRootHornIdentityPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalRootHornMarked n)).hom ≫ coneCriticalRootHornUnionMap n := by
  apply Hom.ext
  ext q z
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj
    (z.2.val.obj t, (0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = coneCriticalRootUnionSubset n
      (z.2.val.obj t)
  rw [hz]
  rfl

/-- The entire original marked horn replacement prism retains its SAME genuine whole collapse-section composite at
the original source endpoint. -/
theorem coneCriticalRootHornReplacementPrism_source (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (coneCriticalRootHornMarked.{u} n)) ≫
      coneCriticalRootHornReplacementPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalRootHornMarked n)).hom ≫
          (coneCriticalRootHornProjection n ≫ coneCriticalRootHornSection n) := by
  apply Hom.ext
  ext q z
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj
    (z.2.val.obj t, (1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = (coneCriticalRootReplacementFunctor
      n).obj (z.2.val.obj t)
  rw [hz]
  rfl

/-- The entire original marked horn replacement prism retains the same full original horn union map at its other
original endpoint. -/
theorem coneCriticalRootHornReplacementPrism_target (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 (coneCriticalRootHornMarked.{u} n)) ≫
      coneCriticalRootHornReplacementPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalRootHornMarked n)).hom ≫ coneCriticalRootHornUnionMap n := by
  apply Hom.ext
  ext q z
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj
    (z.2.val.obj t, (0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = coneCriticalRootUnionSubset n
      (z.2.val.obj t)
  rw [hz]
  rfl

end SSet.Marked.CoherentWeight
