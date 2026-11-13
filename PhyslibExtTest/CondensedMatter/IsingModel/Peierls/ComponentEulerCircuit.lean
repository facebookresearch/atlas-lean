/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.ComponentEulerCircuit

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsContourFinal`

* `TightAxisCircuitData 0 ℓ` holds for every `ℓ`: in the box `Λ_0 = {0}` the only connected cluster
  is the singleton `{0}`, whose contour is covered by the component of the axis face `(0, 0)`. Hence
  `contourSubsetCountBound_of_tightData` gives `ContourSubsetCountBound 2 0 ℓ` for every `ℓ`, and
  the derived predicates `AxisContourDualCircuit 2 0 ℓ` (`Peierls.PeierlsAnchorEncode`) and
  `RealisedContourWalkEncoding 2 0 ℓ` (`Peierls.ContourSubsetCount`) hold too;
* the inner condition of `TightAxisCircuitData` (support in a face set `T`, axis face `(j, 0)` in
  `T`, every contour edge in the component of that face) holds for the rectangle
  `boxCluster 1 2 = [0, 1] × [0, 2]` with `T = boxFrame 1 2`, `j = 1`;
* `boxCluster_tight_dualCircuit` and `singletonOrigin_tight_dualCircuit`: a closed trail through all
  contour edges based at an axis face, for the rectangle `[0, 3] × [0, 1]` and the singleton.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsContourFinal

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Ising

/-- The only site of the box `Λ_0` is the origin. -/
lemma eq_origin_of_mem_box_zero {x : Site 2} (hx : x ∈ box 2 0) : x = origin 2 := by
  funext i
  have := hx i
  simp only [nonpos_iff_eq_zero, Int.natAbs_eq_zero] at this
  simp [origin, this]

/-- In the box `Λ_0` the tight axis-circuit data hold for every contour length. -/
lemma tightAxisCircuitData_zero (ℓ : ℕ) : TightAxisCircuitData 0 ℓ := by
  intro F hF
  simp only [realisedContours, Finset.mem_image, Finset.mem_filter] at hF
  obtain ⟨K, ⟨hKconn, hKlen⟩, hKF⟩ := hF
  rw [pcc_mem_connClusterFamily] at hKconn
  have hKbox := clusterFamily_subset_box hKconn.1
  have hK : K = {origin 2} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hKconn.2.1, fun x hx => ?_⟩
    exact eq_origin_of_mem_box_zero (hKbox (Finset.mem_coe.mpr hx))
  subst hK
  refine ⟨{origin 2}, hKbox, hKF, hKlen, singletonBoundarySupport, 0,
    support_singletonOrigin_subset, ?_, axisVertex_zero_mem_singletonBoundarySupport,
    singletonOrigin_componentCovers⟩
  rw [← hKlen]
  exact pcc_one_le_contourLen (by norm_num) hKbox (Finset.mem_singleton_self _)

-- Consequence: the Peierls count holds in `Λ_0` for every contour length.
example (ℓ : ℕ) : ContourSubsetCountBound 2 0 ℓ :=
  contourSubsetCountBound_of_tightData (tightAxisCircuitData_zero ℓ)

-- The axis dual-circuit predicate holds in `Λ_0` for every contour length.
example (ℓ : ℕ) : AxisContourDualCircuit 2 0 ℓ :=
  axisContourDualCircuit_of_tightData (tightAxisCircuitData_zero ℓ)

-- The closed-walk encoding predicate holds in `Λ_0` for every contour length.
example (ℓ : ℕ) : RealisedContourWalkEncoding 2 0 ℓ :=
  realisedContourWalkEncoding_of_tightData (tightAxisCircuitData_zero ℓ)

-- The inner tight condition for the rectangle `[0, 1] × [0, 2]` (perimeter `10`), with `j = 1`.
example : ∃ (T : Finset (Site 2)) (j : ℕ),
    (faceBoundaryGraph (↑(boxCluster 1 2) : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
      j < 10 ∧ axisVertex 2 j ∈ T ∧
      ∀ e ∈ (faceBoundaryGraph (↑(boxCluster 1 2) : Set (Site 2))).edgeSet,
        e ∈ (componentGraph (↑(boxCluster 1 2) : Set (Site 2)) (axisVertex 2 j)).edgeSet :=
  ⟨boxFrame 1 2, 1, support_boxCluster_subset_frame 1 2, by norm_num,
    axisVertex_m_mem_boxFrame 1 2, boxCluster_componentCovers 1 2⟩

-- A covering closed dual trail at the axis face `(3, 0)` for the rectangle `[0, 3] × [0, 1]`.
example : ∃ c : (faceBoundaryGraph (↑(boxCluster 3 1) : Set (Site 2))).Walk
      (axisVertex 2 3) (axisVertex 2 3),
    c.IsTrail ∧
      ∀ e ∈ (faceBoundaryGraph (↑(boxCluster 3 1) : Set (Site 2))).edgeSet, e ∈ c.edges :=
  boxCluster_tight_dualCircuit 3 1

-- A covering closed dual trail at the axis face `(0, 0)` for the singleton cluster.
example : ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
      (axisVertex 2 0) (axisVertex 2 0),
    c.IsTrail ∧
      ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
        e ∈ c.edges :=
  singletonOrigin_tight_dualCircuit

end PhyslibExtTest.CondensedMatter.IsingModel.Peierls.PeierlsContourFinal
