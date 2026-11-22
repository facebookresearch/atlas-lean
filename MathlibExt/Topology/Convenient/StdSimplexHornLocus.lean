/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplex
public import MathlibExt.Topology.Convenient.StdSimplexHornRetract

/-!
# Horn coordinate locus in the standard simplex

For `0 < n` and `k : Fin (n + 1)`, the horn locus is the set of points of
`Convexity.StdSimplex ℝ (Fin (n + 1))` with an off-`k` zero `weights` coordinate.
It is the finite union of the face ranges
`Convexity.StdSimplex.map (Fin.succAbove j)` over `j ≠ k`.
The accepted `affineHornRetract` and `affineHornHomotopy` are packaged here as
continuous maps, with only the endpoint and pointwise-fixed-locus facts needed
for later realized-horn descent. Mathematical source: standard affine horn
description, cf. Goerss--Jardine, *Simplicial Homotopy Theory*, Chapter I, §1.

The hypothesis `0 < n` is load-bearing as in the retract module. No `SSet`,
`TopCat`, colimit, quotient, weak-equivalence, or model-category result is
claimed here; the finite-minimum construction is reused, never duplicated.
-/

@[expose] public section

variable {n : ℕ}

/-- Horn coordinate locus: points with an off-`k` zero `weights` coordinate. -/
def hornLocus (k : Fin (n + 1)) (_hn : 0 < n) :
    Set (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  {t | ∃ j, j ≠ k ∧ t.weights j = 0}

/-- The locus is the union of the off-`k` face ranges. -/
theorem hornLocus_eq_biUnion_faceRanges (k : Fin (n + 1)) (_hn : 0 < n) :
    hornLocus k _hn = ⋃ (j : {j : Fin (n + 1) // j ≠ k}),
      Set.range (Convexity.StdSimplex.map (Fin.succAbove j.val)) := by
  ext t
  simp only [hornLocus, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hjk, hj0⟩
    refine ⟨⟨j, hjk⟩, ?_⟩
    rw [Convexity.StdSimplex.mem_range_map_iff]
    intro y hy
    have hmem : y ∈ ({j} : Set (Fin (n + 1))) := by
      by_contra hcon
      apply hy
      rw [Fin.range_succAbove, Set.mem_compl_iff]
      exact hcon
    rw [Set.mem_singleton_iff.mp hmem, hj0]
  · rintro ⟨⟨j, hjk⟩, hmem⟩
    refine ⟨j, hjk, ?_⟩
    have hjNot : j ∉ Set.range (Fin.succAbove j) := by
      rw [Fin.range_succAbove]
      simp
    exact (Convexity.StdSimplex.mem_range_map_iff _ _).mp hmem j hjNot

/-- The accepted retraction as a continuous map into the locus. -/
noncomputable def hornRetractMap (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap (Convexity.StdSimplex ℝ (Fin (n + 1))) ↥(hornLocus k hn) where
  toFun t :=
    ⟨affineHornRetract k hn t, affineHornRetract_horn k hn t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_affineHornRetract k hn

/-- The accepted straight-line homotopy as a continuous map. -/
noncomputable def hornHomotopyMap (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap
      (Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1))
      (Convexity.StdSimplex ℝ (Fin (n + 1))) where
  toFun p :=
    affineHornHomotopy k hn p.1 ↑p.2 p.2.2
  continuous_toFun :=
    continuous_affineHornHomotopy k hn

/-- The retraction fixes the locus pointwise. -/
theorem hornRetractMap_fix (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (ht : t ∈ hornLocus k hn) :
    ((hornRetractMap k hn t : ↥(hornLocus k hn)) :
      Convexity.StdSimplex ℝ (Fin (n + 1))) = t := by
  obtain ⟨j, hjk, hj0⟩ := ht
  exact affineHornRetract_fix k hn t ⟨j, hjk, hj0⟩

/-- Left homotopy endpoint is the identity. -/
theorem hornHomotopyMap_zero (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    hornHomotopyMap k hn
        (t, ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩) = t :=
  affineHornHomotopy_zero k hn t (Set.left_mem_Icc.mpr zero_le_one)

/-- Right homotopy endpoint is the retraction. -/
theorem hornHomotopyMap_one (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    hornHomotopyMap k hn
        (t, ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩) =
      affineHornRetract k hn t :=
  affineHornHomotopy_one k hn t (Set.right_mem_Icc.mpr zero_le_one)

/-- The horn locus is closed as a finite union of closed face ranges. -/
theorem hornLocus_isClosed (k : Fin (n + 1)) (hn : 0 < n) :
    IsClosed (hornLocus k hn) := by
  revert k hn
  cases n with
  | zero => intro k hn; omega
  | succ m =>
    intro k hn
    rw [hornLocus_eq_biUnion_faceRanges]
    exact isClosed_iUnion_of_finite fun ⟨j, _⟩ =>
      (Convexity.StdSimplex.isClosedEmbedding_map_succAbove j).isClosed_range

/-- The homotopy fixes the locus pointwise at every parameter. -/
theorem hornHomotopyMap_fix (k : Fin (n + 1)) (hn : 0 < n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (ht : t ∈ hornLocus k hn)
    (s : ↥(Set.Icc (0 : ℝ) 1)) :
    hornHomotopyMap k hn (t, s) = t := by
  obtain ⟨j, hjk, hj0⟩ := ht
  exact affineHornHomotopy_fix k hn t ⟨j, hjk, hj0⟩ ↑s s.2
