/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Homotopy.PathOpenCoverGrid

/-!
# Open-cover subordinate path-grid tests

Focused consumers for symbolic universe polymorphism, constant and nonconstant
paths, finite and infinite index types, strict endpoint grids, shared adjacent
vertices, oriented cell endpoints, and exact range containment.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Topology

universe u v

namespace MathlibExtTest.Topology.Homotopy.PathOpenCoverGridTests

private def topCover (ι : Type v) (X : Type u) [TopologicalSpace X] :
    ι → TopologicalSpace.Opens X :=
  fun _ => ⊤

private theorem topCover_isOpenCover (ι : Type v) (X : Type u)
    [TopologicalSpace X] [Nonempty ι] :
    TopologicalSpace.IsOpenCover (topCover ι X) := by
  apply TopologicalSpace.IsOpenCover.mk
  apply le_antisymm le_top
  exact le_iSup_of_le (Classical.choice (inferInstance : Nonempty ι))
    (by simp [topCover])

/-- Symbolic `u`/`v` client for an arbitrary indexed open cover. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {a b : X} (p : Path a b) :
    Nonempty (SubordinatePathGrid U p) :=
  exists_subordinatePathGrid U hU p

/-- The positive saturated grid and its cover labels are available directly. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {a b : X} (p : Path a b) :
    ∃ N, 1 ≤ N ∧ ∀ k, ∃ i,
      Set.range (p.subpath (unitInterval.uniformGrid N k)
        (unitInterval.uniformGrid N (k + 1))) ⊆ U i :=
  exists_uniformGrid_subordinate U hU p

/-- A constant path still receives a nonempty strictly increasing time grid. -/
example {X : Type u} [TopologicalSpace X] (x : X) :
    ∃ G : SubordinatePathGrid (topCover PUnit X) (Path.refl x),
      G.time 0 = 0 ∧
      G.time (Fin.last (G.extraCells + 1)) = 1 ∧
      StrictMono G.time ∧ Nonempty (Fin (G.extraCells + 1)) := by
  obtain ⟨G⟩ := exists_subordinatePathGrid (topCover PUnit X)
    (topCover_isOpenCover PUnit X) (Path.refl x)
  exact ⟨G, G.time_zero, G.time_last, G.time_strictMono, ⟨0⟩⟩

private def intervalPath : Path (0 : unitInterval) 1 :=
  Path.mk (ContinuousMap.id unitInterval) rfl rfl

private def intervalTwoCover : Bool → TopologicalSpace.Opens unitInterval
  | false =>
      ⟨Subtype.val ⁻¹' Set.Iio (2 / 3 : ℝ),
        continuous_subtype_val.isOpen_preimage _ isOpen_Iio⟩
  | true =>
      ⟨Subtype.val ⁻¹' Set.Ioi (1 / 3 : ℝ),
        continuous_subtype_val.isOpen_preimage _ isOpen_Ioi⟩

private theorem intervalTwoCover_isOpenCover :
    TopologicalSpace.IsOpenCover intervalTwoCover := by
  apply TopologicalSpace.IsOpenCover.of_sets
  ext t
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : (t : ℝ) < 2 / 3
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change 1 / 3 < (t : ℝ)
    have ht : 2 / 3 ≤ (t : ℝ) := le_of_not_gt h
    linarith

/-- Concrete nonconstant path and a one-member cover. -/
example : Nonempty
    (SubordinatePathGrid (topCover PUnit unitInterval) intervalPath) :=
  exists_subordinatePathGrid (topCover PUnit unitInterval)
    (topCover_isOpenCover PUnit unitInterval) intervalPath

/-- A genuinely distinct two-member cover subordinates a nonconstant path. -/
example : Nonempty (SubordinatePathGrid intervalTwoCover intervalPath) :=
  exists_subordinatePathGrid intervalTwoCover intervalTwoCover_isOpenCover intervalPath

/-- A many-member finite cover is accepted. -/
example {X : Type u} [TopologicalSpace X] {a b : X} (p : Path a b) :
    Nonempty (SubordinatePathGrid (topCover (Fin 4) X) p) :=
  exists_subordinatePathGrid (topCover (Fin 4) X)
    (topCover_isOpenCover (Fin 4) X) p

/-- The cover index type need not be finite. -/
example {X : Type u} [TopologicalSpace X] {a b : X} (p : Path a b) :
    Nonempty (SubordinatePathGrid (topCover ℕ X) p) :=
  exists_subordinatePathGrid (topCover ℕ X)
    (topCover_isOpenCover ℕ X) p

/-- Every cell has strict left-to-right time orientation. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    {U : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid U p) :
    ∀ k : Fin (G.extraCells + 1), G.time k.castSucc < G.time k.succ :=
  fun _ => G.time_strictMono Fin.castSucc_lt_succ

/-- Consecutive cells use the identical shared path value. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    {U : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid U p) (k : Fin G.extraCells) :
    G.cell k.castSucc 1 = G.cell k.succ 0 :=
  G.cell_target_eq_next_source k

/-- Cell source and target preserve the left-to-right subpath orientation. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    {U : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid U p) (k : Fin (G.extraCells + 1)) :
    G.cell k 0 = p (G.time k.castSucc) ∧
      G.cell k 1 = p (G.time k.succ) :=
  ⟨G.cell_source k, G.cell_target k⟩

/-- The public cell accessor retains the exact labeled range inclusion. -/
example {X : Type u} [TopologicalSpace X] {ι : Type v}
    {U : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid U p) (k : Fin (G.extraCells + 1)) :
    Set.range (G.cell k) ⊆ U (G.label k) :=
  G.cell_range_subset k

end MathlibExtTest.Topology.Homotopy.PathOpenCoverGridTests

end
