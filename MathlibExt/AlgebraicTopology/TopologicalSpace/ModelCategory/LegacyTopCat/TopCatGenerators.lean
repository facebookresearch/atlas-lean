/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Horn

/-!
# Realized simplicial boundary and horn generators

The realized-boundary family consists of `|∂Δ[n]| → |Δ[n]|` in all dimensions.
The realized-horn family consists of `|Λ[n,i]| → |Δ[n]|` in positive dimensions.
Both families consist of closed embeddings for which each codomain point outside
the image is closed: the relative T1 condition.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/--
The morphism family `|∂Δ[n]| → |Δ[n]|`, indexed by all natural dimensions `n`.
-/
noncomputable def realizedBoundaryInclusions : MorphismProperty TopCat.{u} :=
  .ofHoms (fun (n : ℕ) ↦ SSet.toTop.{u}.map (SSet.boundary.{u} n).ι)

/--
The morphism family `|Λ[n + 1,i]| → |Δ[n + 1]|`, including every horn index
in every positive dimension.
-/
noncomputable def realizedHornInclusions : MorphismProperty TopCat.{u} :=
  ⨆ (n : ℕ), .ofHoms (fun (i : Fin (n + 2)) ↦ SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι)

/--
The realized boundary inclusion in every dimension belongs to the
realized-boundary generator family.
-/
theorem boundary_mem_realizedBoundaryInclusions (n : ℕ) :
    realizedBoundaryInclusions (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) := by
  constructor

/--
For a nonzero dimension `n` and any horn index `i`, its realized horn inclusion
belongs to the realized-horn generator family.
-/
theorem horn_mem_realizedHornInclusions (n : ℕ) [NeZero n] (i : Fin (n + 1)) :
    realizedHornInclusions (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι) := by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [realizedHornInclusions, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

/--
Every realized boundary inclusion is a closed embedding whose complementary
points are closed in the codomain.
-/
theorem realizedBoundaryInclusions_le_closedT1Embeddings :
    realizedBoundaryInclusions ≤ TopCat.closedT1Embeddings.{u} :=
  (ofHoms_le_iff _ _).mpr (fun n ↦ SSet.boundary.closedT1Embeddings_toTop_map_ι n)

/--
Every realized horn inclusion is a closed embedding whose complementary
points are closed in the codomain.
-/
theorem realizedHornInclusions_le_closedT1Embeddings :
    realizedHornInclusions ≤ TopCat.closedT1Embeddings.{u} := by
  rintro _ _ _ h
  simp only [realizedHornInclusions, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact SSet.horn.closedT1Embeddings_toTop_map_ι (n + 1) i

end TopCat
