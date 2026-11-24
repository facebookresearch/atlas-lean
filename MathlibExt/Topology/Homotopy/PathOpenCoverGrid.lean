/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.UnitInterval

/-!
# Path grids subordinate to indexed open covers

This file provides a uniform grid on the unit interval and packages the
Lebesgue-number subdivision of a path by an arbitrary indexed open cover.
Every returned grid has at least one cell, strictly increasing finite grid
times, literal endpoints `0` and `1`, and one cover label containing the exact
range of each oriented subpath.

The construction generalizes the former private one-dimensional grid in the
fundamental-groupoid van Kampen proof.  The latter delegates to the public
provider below; the two-dimensional van Kampen grid remains private and
unchanged.

Mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval` is the closest
public provider: it gives an eventually constant monotone sequence.  The API
here is distinct in retaining one finite, strictly increasing uniform grid
with literal endpoints and a label for each oriented path cell.

This file makes no simplicial-realization, edge-word, fundamental-groupoid,
fullness, faithfulness, or model-category claim.
-/

@[expose] public section

noncomputable section

open Set Topology

universe u v

namespace unitInterval

/-- Uniform grid points in the unit interval.  The value at `k` is the
projection of `k / N` to `[0, 1]`; consequently the grid saturates at `1` for
`N ≤ k`. -/
def uniformGrid (N k : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ))

/-- Coercion of a uniform grid point to the underlying real number. -/
theorem uniformGrid_coe (N k : ℕ) :
    ((uniformGrid N k : unitInterval) : ℝ) =
      ((Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ)) :
        unitInterval) : ℝ) :=
  rfl

/-- Every uniform grid begins at `0`. -/
@[simp]
theorem uniformGrid_zero (N : ℕ) : uniformGrid N 0 = 0 := by
  unfold uniformGrid
  rw [Nat.cast_zero, zero_div]
  exact Set.projIcc_val zero_le_one
    ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩

/-- A positive uniform grid is equal to `1` at and after its denominator. -/
theorem uniformGrid_top {N k : ℕ} (hN : 1 ≤ N) (hk : N ≤ k) :
    uniformGrid N k = 1 := by
  have hNc : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNc, one_mul]
    exact_mod_cast hk
  calc
    uniformGrid N k = ⟨1, Set.right_mem_Icc.mpr zero_le_one⟩ :=
      Set.projIcc_of_right_le zero_le_one h1
    _ = 1 := by simp

/-- Uniform grid points are monotone in the numerator. -/
theorem uniformGrid_monotone (N : ℕ) : Monotone (uniformGrid N) := by
  intro a b hab
  have hdiv : ((a : ℝ) / (N : ℝ)) ≤ ((b : ℝ) / (N : ℝ)) := by
    by_cases hN : (N : ℝ) = 0
    · rw [hN, div_zero, div_zero]
    · have hNc : (0 : ℝ) < (N : ℝ) :=
        lt_of_le_of_ne' (Nat.cast_nonneg N) hN
      exact (div_le_div_iff_of_pos_right hNc).mpr (Nat.cast_le.mpr hab)
  exact Set.monotone_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one hdiv

/-- Before saturation, a uniform grid point is the literal quotient `k / N`. -/
theorem uniformGrid_val_of_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    ((uniformGrid N k : unitInterval) : ℝ) = (k : ℝ) / (N : ℝ) := by
  have hNc : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hmem : ((k : ℝ) / (N : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg k) (le_of_lt hNc), ?_⟩
    rw [div_le_one hNc]
    exact_mod_cast hk
  have heq : uniformGrid N k = ⟨((k : ℝ) / (N : ℝ)), hmem⟩ :=
    Set.projIcc_of_mem zero_le_one hmem
  rw [heq]

/-- Adjacent uniform grid points are at most `1 / N` apart. -/
theorem uniformGrid_gap (N k : ℕ) :
    ((uniformGrid N (k + 1) : unitInterval) : ℝ) -
        (uniformGrid N k : ℝ) ≤ 1 / (N : ℝ) := by
  have hle : ((k : ℝ) / (N : ℝ)) ≤ (((k + 1 : ℕ) : ℝ) / (N : ℝ)) := by
    by_cases hN : (N : ℝ) = 0
    · rw [hN, div_zero, div_zero]
    · have hNc : (0 : ℝ) < (N : ℝ) :=
        lt_of_le_of_ne' (Nat.cast_nonneg N) hN
      exact (div_le_div_iff_of_pos_right hNc).mpr (by exact_mod_cast Nat.le_succ k)
  have hmono : Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ)) ≤
      Set.projIcc 0 1 zero_le_one (((k + 1 : ℕ) : ℝ) / (N : ℝ)) :=
    Set.monotone_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one hle
  have hrr : ((Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ)) :
      unitInterval) : ℝ) ≤
      ((Set.projIcc 0 1 zero_le_one (((k + 1 : ℕ) : ℝ) / (N : ℝ)) :
        unitInterval) : ℝ) := by
    exact_mod_cast hmono
  have hlip := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1)
    (h := zero_le_one) (c := (((k + 1 : ℕ) : ℝ) / (N : ℝ)))
    (d := ((k : ℝ) / (N : ℝ)))
  rw [abs_of_nonneg (sub_nonneg.mpr hrr)] at hlip
  have hcd : (((k + 1 : ℕ) : ℝ) / (N : ℝ)) - (k : ℝ) / (N : ℝ) =
      1 / (N : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one, add_div]
    ring
  rw [hcd] at hlip
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))] at hlip
  simpa only [uniformGrid_coe] using hlip

/-- A point between two adjacent uniform grid points is within `1 / N` of
the left endpoint. -/
theorem dist_uniformGrid_left_le {N k : ℕ} (t : unitInterval)
    (hlo : uniformGrid N k ≤ t) (hhi : t ≤ uniformGrid N (k + 1)) :
    dist t (uniformGrid N k) ≤ 1 / (N : ℝ) := by
  have hloR : ((uniformGrid N k : unitInterval) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (t : ℝ) ≤ ((uniformGrid N (k + 1) : unitInterval) : ℝ) := by
    exact_mod_cast hhi
  have hgap := uniformGrid_gap N k
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hloR)]
  linarith

/-- Restricting the positive `(n + 1)`-grid to its `n + 2` finite vertices is
strictly increasing. -/
theorem uniformGrid_strictMono (n : ℕ) :
    StrictMono (fun i : Fin (n + 2) => uniformGrid (n + 1) i) := by
  intro i j hij
  have hi : i.val ≤ n + 1 := by omega
  have hj : j.val ≤ n + 1 := by omega
  change ((uniformGrid (n + 1) i : unitInterval) : ℝ) <
    ((uniformGrid (n + 1) j : unitInterval) : ℝ)
  rw [uniformGrid_val_of_le (by omega) hi,
    uniformGrid_val_of_le (by omega) hj]
  have hijR : (i.val : ℝ) < (j.val : ℝ) := by
    exact_mod_cast hij
  exact (div_lt_div_iff_of_pos_right
    (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).mpr hijR

/-- The last vertex of the positive `(n + 1)`-grid is literally `1`. -/
@[simp]
theorem uniformGrid_last (n : ℕ) :
    uniformGrid (n + 1) (Fin.last (n + 1)) = 1 :=
  uniformGrid_top (by omega) le_rfl

end unitInterval

/-- A finite subdivision of a path subordinate to an indexed open cover.
There are `extraCells + 1` cells and `extraCells + 2` vertices, so the grid
always has at least one cell. -/
structure SubordinatePathGrid {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    {a b : X} (p : Path a b) where
  extraCells : ℕ
  time : Fin (extraCells + 2) → unitInterval
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  time_last : time (Fin.last (extraCells + 1)) = 1
  label : Fin (extraCells + 1) → ι
  subordinate : ∀ k,
    Set.range (p.subpath (time k.castSucc) (time k.succ)) ⊆ U (label k)

namespace SubordinatePathGrid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
  {U : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}

/-- The oriented subpath in one cell of a subordinate path grid. -/
def cell (G : SubordinatePathGrid U p) (k : Fin (G.extraCells + 1)) :
    Path (p (G.time k.castSucc)) (p (G.time k.succ)) :=
  p.subpath (G.time k.castSucc) (G.time k.succ)

/-- The source of a grid cell is its left grid vertex. -/
@[simp]
theorem cell_source (G : SubordinatePathGrid U p) (k : Fin (G.extraCells + 1)) :
    G.cell k 0 = p (G.time k.castSucc) :=
  (G.cell k).source

/-- The target of a grid cell is its right grid vertex. -/
@[simp]
theorem cell_target (G : SubordinatePathGrid U p) (k : Fin (G.extraCells + 1)) :
    G.cell k 1 = p (G.time k.succ) :=
  (G.cell k).target

/-- Consecutive cells share their endpoint literally. -/
theorem cell_target_eq_next_source (G : SubordinatePathGrid U p)
    (k : Fin G.extraCells) :
    G.cell k.castSucc 1 = G.cell k.succ 0 := by
  rw [G.cell_target, G.cell_source]
  congr 2

/-- The exact range containment carried by a grid cell. -/
theorem cell_range_subset (G : SubordinatePathGrid U p)
    (k : Fin (G.extraCells + 1)) :
    Set.range (G.cell k) ⊆ U (G.label k) :=
  G.subordinate k

end SubordinatePathGrid

/-- An arbitrary indexed open cover subordinates the saturated uniform grid
of every path at some positive denominator. -/
theorem exists_uniformGrid_subordinate {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {a b : X} (p : Path a b) :
    ∃ N, 1 ≤ N ∧ ∀ k, ∃ i,
      Set.range (p.subpath (unitInterval.uniformGrid N k)
        (unitInterval.uniformGrid N (k + 1))) ⊆ U i := by
  let c : ι → Set unitInterval := fun i => p ⁻¹' (U i : Set X)
  have hcOpen : ∀ i, IsOpen (c i) := by
    intro i
    exact p.continuous.isOpen_preimage _ (U i).isOpen
  have hcCover : Set.univ ⊆ ⋃ i, c i := by
    intro t _
    obtain ⟨i, hi⟩ := hU.exists_mem (p t)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hcOpen hcCover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  have hN : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < δ := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    exact hn
  refine ⟨n + 1, by omega, fun k => ?_⟩
  have hmono : unitInterval.uniformGrid (n + 1) k ≤
      unitInterval.uniformGrid (n + 1) (k + 1) :=
    unitInterval.uniformGrid_monotone _ (Nat.le_succ k)
  have hball : ∀ t : unitInterval,
      t ∈ Set.uIcc (unitInterval.uniformGrid (n + 1) k)
          (unitInterval.uniformGrid (n + 1) (k + 1)) →
        dist t (unitInterval.uniformGrid (n + 1) k) < δ := by
    intro t ht
    rw [Set.uIcc_of_le hmono] at ht
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp ht
    exact lt_of_le_of_lt
      (unitInterval.dist_uniformGrid_left_le t hlo hhi) hN
  obtain ⟨i, hi⟩ := hδ (unitInterval.uniformGrid (n + 1) k) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  intro y hy
  simp only [Path.range_subpath] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact hi (Metric.mem_ball.mpr (hball t ht))

/-- Every path admits a finite, strictly increasing grid subordinate to an
arbitrary indexed open cover. -/
theorem exists_subordinatePathGrid {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {a b : X} (p : Path a b) :
    Nonempty (SubordinatePathGrid U p) := by
  obtain ⟨N, hN, hsub⟩ := exists_uniformGrid_subordinate U hU p
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    exact ⟨N - 1, by omega⟩
  choose label hlabel using fun k : Fin (n + 1) => hsub k
  exact ⟨
    { extraCells := n
      time := fun i => unitInterval.uniformGrid (n + 1) i
      time_strictMono := unitInterval.uniformGrid_strictMono n
      time_zero := unitInterval.uniformGrid_zero _
      time_last := unitInterval.uniformGrid_last n
      label := label
      subordinate := hlabel }⟩

end
