/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Horn

/-!
# Generating realized boundary and horn inclusions in `TopCat`

This file is part of the KQ3 layer. It packages the realized boundary
inclusions `|∂Δ[n]| → |Δ[n]|` and horn inclusions `|Λ[n, i]| → |Δ[n]|` as
`MorphismProperty.ofHoms` families, mirroring `SSet.modelCategoryQuillen.I/J`,
and shows both families lie in `TopCat.closedT1Embeddings` via the accepted
Boundary/Horn providers. This is not a smallness, factorization, cofibration,
weak-equivalence, or model-category claim.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/-- Realized boundary inclusions, indexed by `n : ℕ`. -/
noncomputable def realizedBoundaryInclusions : MorphismProperty TopCat.{u} :=
  .ofHoms (fun (n : ℕ) ↦ SSet.toTop.{u}.map (SSet.boundary.{u} n).ι)

/-- Realized horn inclusions, as the `iSup` over `n` of the `Fin (n + 2)` horns
at dimension `n + 1` (positive-dimensional horns only, mirroring `SSet.J`). -/
noncomputable def realizedHornInclusions : MorphismProperty TopCat.{u} :=
  ⨆ (n : ℕ), .ofHoms (fun (i : Fin (n + 2)) ↦ SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι)

theorem boundary_mem_realizedBoundaryInclusions (n : ℕ) :
    realizedBoundaryInclusions (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) := by
  constructor

theorem horn_mem_realizedHornInclusions (n : ℕ) [NeZero n] (i : Fin (n + 1)) :
    realizedHornInclusions (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι) := by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [realizedHornInclusions, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

/-- Realized boundary inclusions are closed T1-embeddings. -/
theorem realizedBoundaryInclusions_le_closedT1Embeddings :
    realizedBoundaryInclusions ≤ TopCat.closedT1Embeddings.{u} :=
  (ofHoms_le_iff _ _).mpr (fun n ↦ SSet.boundary.closedT1Embeddings_toTop_map_ι n)

/-- Realized horn inclusions are closed T1-embeddings. -/
theorem realizedHornInclusions_le_closedT1Embeddings :
    realizedHornInclusions ≤ TopCat.closedT1Embeddings.{u} := by
  rintro _ _ _ h
  simp only [realizedHornInclusions, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact SSet.horn.closedT1Embeddings_toTop_map_ι (n + 1) i

end TopCat
