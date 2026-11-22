/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootHorn

/-!
# Original critical-root collapse and its whole coface section

The same final degeneracy and the original coface omitting its critical
predecessor retain their exact simplicial section identity. Their entire
finite subset images give the genuine marked critical-root projection
and section. The original critical maximum collapse is unchanged by
their full composite, with every original subset and scalar word kept.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original coface omitting the critical predecessor is the whole original section of the final degeneracy. -/
def coneCriticalReinsert (n : ℕ) : Vertex.{u} (n + 1) →o Vertex.{u} (n + 2) :=
  (coneCofaceEmbedding (Fin.last (n + 1)).castSucc).toOrderHom

/-- The same complete original coface and final degeneracy retain their exact original simplicial section identity
at every ordinal vertex. -/
theorem coneCriticalCollapse_reinsert (n : ℕ) (i : Vertex.{u} (n + 1)) :
    coneCriticalMaximumCollapse n (coneCriticalReinsert n i) = i := by
  change ULift.up ((Fin.last (n + 1)).predAbove
    ((Fin.last (n + 1)).castSucc.succAbove i.down)) = i
  exact congrArg ULift.up (Fin.predAbove_succAbove (Fin.last (n + 1)) i.down)

/-- The original whole critical coface retains the same original root. -/
theorem coneCriticalReinsert_root (n : ℕ) :
    coneCriticalReinsert.{u} n (⊥ : Vertex.{u} (n + 1)) = ⊥ :=
  coneCofaceEmbedding_root _ (coneCriticalPrevious_pos.{u} n)

/-- Every original critical coface vertex avoids precisely the same original omitted predecessor. -/
theorem coneCriticalReinsert_ne_previous (n : ℕ) (i : Vertex.{u} (n + 1)) :
    coneCriticalReinsert n i ≠ coneCriticalPrevious n :=
  (mem_coneCofaceEmbedding_range (Fin.last (n + 1)).castSucc _).mp ⟨i, rfl⟩

/-- The original complete larger root subset projects by the exact original final-degeneracy image, with the same
original root record. -/
def coneCriticalRootProjectionSubset (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    ConeSubset (⊥ : Vertex.{u} (n + 1)) where
  vertices := a.vertices.image (coneCriticalMaximumCollapse n)
  mem := coneCriticalMaximumCollapse_root n ▸ Finset.mem_image_of_mem (coneCriticalMaximumCollapse n) a.mem
  lower _ _ := bot_le

/-- Every whole original smaller root subset enters by its exact original critical coface image and unchanged root
equality. -/
def coneCriticalRootSectionSubset (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    ConeSubset (⊥ : Vertex.{u} (n + 2)) :=
  coneRootCofaceSubset (Fin.last (n + 1)).castSucc (coneCriticalPrevious_pos.{u} n) a

/-- The original critical-root projection keeps the same whole finite subset image under the native final degeneracy. -/
theorem coneCriticalRootProjectionSubset_vertices (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    (coneCriticalRootProjectionSubset n a).vertices = a.vertices.image (coneCriticalMaximumCollapse n) := rfl

/-- The original critical coface section keeps the same complete finite subset image, with no altered vertex or
maximum. -/
theorem coneCriticalRootSectionSubset_vertices (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    (coneCriticalRootSectionSubset n a).vertices = a.vertices.image (coneCriticalReinsert n) := rfl

/-- The maximum of every whole original projected subset is precisely its actual original collapsed maximum. -/
theorem coneCriticalRootProjectionSubset_maximum (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    (coneCriticalRootProjectionSubset n a).maximum = coneCriticalMaximumCollapse n a.maximum := by
  change (a.vertices.image (coneCriticalMaximumCollapse n)).max' _ = coneCriticalMaximumCollapse n (a.vertices.max' _)
  exact Finset.max'_image (coneCriticalMaximumCollapse n).monotone _ _

/-- The maximum of every complete original section subset is exactly the same original critical coface maximum image. -/
theorem coneCriticalRootSectionSubset_maximum (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    (coneCriticalRootSectionSubset n a).maximum = coneCriticalReinsert n a.maximum := by
  change (a.vertices.image (coneCriticalReinsert n)).max' _ = coneCriticalReinsert n (a.vertices.max' _)
  exact Finset.max'_image (coneCriticalReinsert n).monotone _ _

/-- The complete critical coface subset section retains exactly the original smaller maximum after the same final
degeneracy. -/
theorem coneCriticalRootSectionSubset_collapsedMaximum (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    coneCriticalMaximumCollapse n (coneCriticalRootSectionSubset n a).maximum = a.maximum :=
  (congrArg (coneCriticalMaximumCollapse n) (coneCriticalRootSectionSubset_maximum n a)).trans
    (coneCriticalCollapse_reinsert n a.maximum)

/-- The same whole original critical-root subset projection is a genuine functor on every original inclusion. -/
def coneCriticalRootProjectionFunctor (n : ℕ) :
    ConeSubset (⊥ : Vertex.{u} (n + 2)) ⥤ ConeSubset (⊥ : Vertex.{u} (n + 1)) where
  obj := coneCriticalRootProjectionSubset n
  map f := homOfLE (Finset.image_subset_image (leOfHom f))

/-- The same entire original critical coface subset section is a genuine functor retaining all original inclusion
maps. -/
def coneCriticalRootSectionFunctor (n : ℕ) :
    ConeSubset (⊥ : Vertex.{u} (n + 1)) ⥤ ConeSubset (⊥ : Vertex.{u} (n + 2)) where
  obj := coneCriticalRootSectionSubset n
  map f := homOfLE (Finset.image_subset_image (leOfHom f))

/-- The full original critical-root projection is a genuine marked map preserving precisely its actual
collapsed-maximum marker. -/
def coneCriticalRootProjection (n : ℕ) :
    coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) where
  hom := nerveMap (coneCriticalRootProjectionFunctor n)
  preserve {e} he :=
    (coneCriticalRootProjectionSubset_maximum n (e.obj 0)).trans
      (he.trans (coneCriticalRootProjectionSubset_maximum n (e.obj 1)).symm)

/-- The entire same original critical coface section is marked through its genuine original collapsed-maximum
identity. -/
def coneCriticalRootSection (n : ℕ) :
    coneWeight (⊥ : Vertex.{u} (n + 1)) ⟶ coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) where
  hom := nerveMap (coneCriticalRootSectionFunctor n)
  preserve {e} he :=
    (coneCriticalRootSectionSubset_collapsedMaximum n (e.obj 0)).trans
      (he.trans (coneCriticalRootSectionSubset_collapsedMaximum n (e.obj 1)).symm)

/-- Both whole original marked critical-root maps retain the exact identity of every original smaller root subset
and complete scalar simplex. -/
theorem coneCriticalRootSection_projection (n : ℕ) :
    coneCriticalRootSection.{u} n ≫ coneCriticalRootProjection n = 𝟙 _ := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ConeSubset.ext
  change ((a.obj t).vertices.image (coneCriticalReinsert n)).image (coneCriticalMaximumCollapse n) = (a.obj t).vertices
  rw [Finset.image_image]
  have h : (fun i : Vertex.{u} (n + 1) => coneCriticalMaximumCollapse n (coneCriticalReinsert n i)) = id :=
    funext (coneCriticalCollapse_reinsert n)
  exact (congrArg (fun f : Vertex.{u} (n + 1) → Vertex.{u} (n + 1) => (a.obj t).vertices.image f) h).trans
    Finset.image_id

/-- The same full original critical-root composite retains the actual whole subset replacement functor. -/
def coneCriticalRootReplacementFunctor (n : ℕ) :
    ConeSubset (⊥ : Vertex.{u} (n + 2)) ⥤ ConeSubset (⊥ : Vertex.{u} (n + 2)) :=
  coneCriticalRootProjectionFunctor n ⋙ coneCriticalRootSectionFunctor n

/-- Every entire original replaced subset retains precisely its same actual original collapsed maximum. -/
theorem coneCriticalRootReplacement_collapsedMaximum (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    coneCriticalMaximumCollapse n ((coneCriticalRootReplacementFunctor n).obj a).maximum =
      coneCriticalMaximumCollapse n a.maximum :=
  (coneCriticalRootSectionSubset_collapsedMaximum n (coneCriticalRootProjectionSubset n a)).trans
    (coneCriticalRootProjectionSubset_maximum n a)

end SSet.Marked.CoherentWeight
