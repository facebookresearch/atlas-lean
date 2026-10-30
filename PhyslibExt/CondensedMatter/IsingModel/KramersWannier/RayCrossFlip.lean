/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingWitness
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.EventToCut

/-!
# Ray-count parity flips across lattice edges

How the ray-count parity of a site with respect to a closed lattice walk changes when the site
moves to a neighbour, and the resulting description of the boundary edges of the inside region.

## i. Overview

For a closed walk `Vc` of `ℤ²` and a site `u`, `jec_rayCount u Vc` counts the edges of `Vc`
crossing the leftward ray from `u`. Moving `u` one step to the right changes this count by the
number of traversals of one specific edge `rpc_hCrossEdge u` (the vertical edge just below-left of
`u`). Moving it one step up changes the analogous wall count by the traversals of
`rpc_vCrossEdge u`. Hence a lattice edge `uv` is a boundary edge of the inside region
`jec_leftRegion Vc` exactly when `Vc` traverses the crossing edge `rpc_crossEdge u v` an odd number
of times (`rpc_crossFlip`). Note that `rpc_crossEdge u v` is a primal edge next to `uv`, not `uv`
itself.

Headline fidelity:
- `rpc_crossFlip`, `rpc_horizontalFlip_iff`, `rpc_verticalFlip_iff` and the unit-square example
  are unconditional.
- `rpc_leftRegion_bdEdge_iff` is conditional on `rpc_CrossEdgeOddIffOnWalk Vc`.
- `rpc_primalWalkLeftRegionMatch_of_bridge` is vacuous: its conclusion
  `kwc_PrimalWalkLeftRegionMatch` is refuted by
  `StatMech.Walls.ceo_primalWalkLeftRegionMatch_false`, so its hypothesis
  (`rpc_CrossEdgeOddIffOnWalk` for every closed walk) is false.

## ii. Key results

- `StatMech.Walls.rpc_crossEdge` : the crossing edge of a lattice edge
- `StatMech.Walls.rpc_crossFlip` : boundary edges of the inside region via crossing-edge parity
- `StatMech.Walls.rpc_CrossEdgeOddIffOnWalk` : crossing-edge parity matches membership in `Vc`
- `StatMech.Walls.rpc_unitSquare_flip` : the top edge of the unit cell is a boundary edge of the
  inside of the unit-square loop

## iii. Table of contents

- A. Horizontal steps and the ray count
- B. Vertical steps and the wall count
- C. Boundary edges of the inside region

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.Lattice

/-! ## A. Horizontal steps and the ray count -/

/-- The vertical edge from `(u₀, u₁ - 1)` to `(u₀, u₁)`, crossed by the leftward ray of the right
neighbour of `u` but not by that of `u`. -/
def rpc_hCrossEdge (u : Site 2) : Sym2 (Site 2) :=
  s(![u 0, u 1 - 1], ![u 0, u 1])

/-- The leftward ray from `u` does not cross `rpc_hCrossEdge u`. -/
@[simp] lemma rpc_hCrossEdge_isRayEdge_left (u : Site 2) :
    ¬ jec_rayEdge u (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega

/-- The leftward ray from the right neighbour of `u` crosses `rpc_hCrossEdge u`. -/
lemma rpc_hCrossEdge_isRayEdge_right (u v : Site 2) (h0 : v 0 = u 0 + 1)
    (h1 : v 1 = u 1) : jec_rayEdge v (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨⟨trivial, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩

/-- For lattice edges, the ray of the right neighbour crosses exactly the edges crossed by the ray
of `u` and `rpc_hCrossEdge u`. -/
lemma rpc_rayEdge_horizontalStep (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_rayEdge v s(p, q) ↔ (jec_rayEdge u s(p, q) ∨ s(p, q) = rpc_hCrossEdge u) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk, rpc_hCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq0, hp0⟩, hstr⟩
    rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
    · by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inl ⟨by omega, by omega⟩⟩
      · have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 - 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq0, hp0⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq0, by omega⟩, ?_⟩
      rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega

open Classical in
/-- Ray counts of `v = u + (1, 0)` and `u` on a list of lattice edges differ by the count of
`rpc_hCrossEdge u`. -/
lemma rpc_rayCount_edges_split (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_rayEdge v e)) =
      l.countP (fun e => decide (jec_rayEdge u e)) + l.count (rpc_hCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_rayEdge_horizontalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_rayEdge u s(p, q) ∧ s(p, q) = rpc_hCrossEdge u) := by
      rintro ⟨hru, heq⟩
      exact rpc_hCrossEdge_isRayEdge_left u (heq ▸ hru)
    by_cases hru : jec_rayEdge u s(p, q)
    · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inl hru)
      have hne : s(p, q) ≠ rpc_hCrossEdge u := fun h => hexcl ⟨hru, h⟩
      rw [ite_eq_left (by simp [hrv]), ite_eq_left (by simp [hru])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_hCrossEdge u
      · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [ite_eq_left (by simp [hrv]), ite_eq_right (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_eq_left]; omega
      · have hrv : ¬ jec_rayEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hru h'
          · exact hcross h'
        rw [ite_eq_right (by simp [hrv]), ite_eq_right (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega

/-- The ray count of `u + (1, 0)` exceeds that of `u` by the number of traversals of
`rpc_hCrossEdge u`. -/
lemma rpc_rayCount_horizontalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    jec_rayCount v Vc = jec_rayCount u Vc + Vc.edges.count (rpc_hCrossEdge u) := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact rpc_rayCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)

/-- The ray-count parities of `u` and `u + (1, 0)` differ iff `rpc_hCrossEdge u` is traversed an odd
number of times. -/
lemma rpc_horizontalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_hCrossEdge u)) := by
  rw [rpc_rayCount_horizontalStep_diff Vc u v h0 h1, Nat.even_add,
    ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_rayCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_hCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]

/-! ## B. Vertical steps and the wall count -/

/-- The horizontal edge from `(u₀ - 1, u₁)` to `(u₀, u₁)`. -/
def rpc_vCrossEdge (u : Site 2) : Sym2 (Site 2) :=
  s(![u 0 - 1, u 1], ![u 0, u 1])

/-- The wall of `u` does not contain `rpc_vCrossEdge u`. -/
lemma rpc_vCrossEdge_isWallEdge_left (u : Site 2) : ¬ jec_wallEdge u (rpc_vCrossEdge u) := by
  rw [rpc_vCrossEdge, jec_wallEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega

/-- For lattice edges, the wall of the upper neighbour contains exactly the edges in the wall of `u`
and `rpc_vCrossEdge u`. -/
lemma rpc_wallEdge_verticalStep (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_wallEdge v s(p, q) ↔ (jec_wallEdge u s(p, q) ∨ s(p, q) = rpc_vCrossEdge u) := by
  rw [jec_wallEdge_mk, jec_wallEdge_mk, rpc_vCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq1, hp1⟩, hstr⟩
    rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inl ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 - 1 := by omega
        have hq0e : q 0 = u 0 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq1, hp1⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq1, by omega⟩, ?_⟩
      rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega

open Classical in
/-- Wall counts of `v = u + (0, 1)` and `u` on a list of lattice edges differ by the count of
`rpc_vCrossEdge u`. -/
lemma rpc_wallCount_edges_split (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_wallEdge v e)) =
      l.countP (fun e => decide (jec_wallEdge u e)) + l.count (rpc_vCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_wallEdge_verticalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_wallEdge u s(p, q) ∧ s(p, q) = rpc_vCrossEdge u) := by
      rintro ⟨hwu, heq⟩
      exact rpc_vCrossEdge_isWallEdge_left u (heq ▸ hwu)
    by_cases hwu : jec_wallEdge u s(p, q)
    · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inl hwu)
      have hne : s(p, q) ≠ rpc_vCrossEdge u := fun h => hexcl ⟨hwu, h⟩
      rw [ite_eq_left (by simp [hwv]), ite_eq_left (by simp [hwu])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_vCrossEdge u
      · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [ite_eq_left (by simp [hwv]), ite_eq_right (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_true]; omega
      · have hwv : ¬ jec_wallEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hwu h'
          · exact hcross h'
        rw [ite_eq_right (by simp [hwv]), ite_eq_right (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega

/-- The wall count of `u + (0, 1)` exceeds that of `u` by the number of traversals of
`rpc_vCrossEdge u`. -/
lemma rpc_wallCount_verticalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    jec_wallCount v Vc = jec_wallCount u Vc + Vc.edges.count (rpc_vCrossEdge u) := by
  classical
  rw [jec_wallCount, jec_wallCount]
  exact rpc_wallCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)

/-- The ray-count parities of `u` and `u + (0, 1)` differ iff `rpc_vCrossEdge u` is traversed an odd
number of times. -/
lemma rpc_verticalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_vCrossEdge u)) := by
  rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc,
    rpc_wallCount_verticalStep_diff Vc u v h0 h1, Nat.even_add, ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_wallCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_vCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]

/-! ## C. Boundary edges of the inside region -/

/-- The crossing edge of the lattice edge `uv`: `rpc_hCrossEdge` of the left endpoint for a
horizontal edge, `rpc_vCrossEdge` of the lower endpoint for a vertical edge. -/
noncomputable def rpc_crossEdge (u v : Site 2) : Sym2 (Site 2) := by
  classical
  exact
    if v 0 = u 0 + 1 then rpc_hCrossEdge u
    else if u 0 = v 0 + 1 then rpc_hCrossEdge v
    else if v 1 = u 1 + 1 then rpc_vCrossEdge u
    else rpc_vCrossEdge v

/-- A lattice edge `uv` is a boundary edge of the inside region of `Vc` iff `Vc` traverses
`rpc_crossEdge u v` an odd number of times. -/
theorem rpc_crossFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ Odd (Vc.edges.count (rpc_crossEdge u v)) := by
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  have hrestate : ((¬ Even (jec_rayCount u Vc)) ↔ ¬ ¬ Even (jec_rayCount v Vc)) ↔
      (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) := by
    constructor <;> intro h <;>
      · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
          simp_all
  rw [hrestate, rpc_crossEdge]
  by_cases hc0 : v 0 = u 0 + 1
  · rw [ite_eq_left hc0]; exact rpc_horizontalFlip_iff Vc u v hc0 (by omega)
  · rw [ite_eq_right hc0]
    by_cases hc0' : u 0 = v 0 + 1
    · rw [ite_eq_left hc0']
      have hfl := rpc_horizontalFlip_iff Vc v u hc0' (by omega)
      rw [← hfl]
      constructor <;> intro h <;>
        · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
            simp_all
    · rw [ite_eq_right hc0']
      have hv0 : v 0 = u 0 := by omega
      by_cases hc1 : v 1 = u 1 + 1
      · rw [ite_eq_left hc1]; exact rpc_verticalFlip_iff Vc u v hv0 hc1
      · rw [ite_eq_right hc1]
        have hc1' : u 1 = v 1 + 1 := by omega
        have hfl := rpc_verticalFlip_iff Vc v u (by omega) hc1'
        rw [← hfl]
        constructor <;> intro h <;>
          · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
              simp_all

/-- For every lattice edge `uv`, `Vc` traverses `rpc_crossEdge u v` an odd number of times iff `uv`
is an edge of `Vc`. -/
def rpc_CrossEdgeOddIffOnWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    (Odd (Vc.edges.count (rpc_crossEdge u v)) ↔ s(u, v) ∈ Vc.edges)

/-- Under `rpc_CrossEdgeOddIffOnWalk Vc`, the boundary edges of the inside of `Vc` are the edges of
`Vc`. -/
lemma rpc_leftRegion_bdEdge_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges := by
  rw [rpc_crossFlip Vc hadj]
  exact hbridge hadj

/-- `rpc_CrossEdgeOddIffOnWalk` for every closed walk implies `kwc_PrimalWalkLeftRegionMatch`.
Vacuous: the conclusion is refuted by `ceo_primalWalkLeftRegionMatch_false`, so the hypothesis is
false. -/
lemma rpc_primalWalkLeftRegionMatch_of_bridge
    (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
      rpc_CrossEdgeOddIffOnWalk Vc) :
    kwc_PrimalWalkLeftRegionMatch := by
  intro a Vc u v hadj
  rw [List.mem_toFinset]
  exact ((rpc_leftRegion_bdEdge_iff Vc (hbridge Vc) hadj).symm)

/-- The edge from `(0, 1)` to `(1, 1)` is a boundary edge of the inside of the unit-square loop. -/
theorem rpc_unitSquare_flip :
    bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  have hodd : ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
    wwit_unitSquareLoop_inside_odd
  have heven : Even (jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop) := by
    have hcount : jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
      unfold wwit_unitSquareLoop
      simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
        jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      norm_num
    rw [hcount]; exact ⟨0, rfl⟩
  simp only [heven, not_true, hodd, not_false_iff]

/-- The unit-square loop traverses the crossing edge of `(0, 1)`–`(1, 1)` an odd number of times. -/
lemma rpc_unitSquare_crossEdge_odd :
    Odd (wwit_unitSquareLoop.edges.count
      (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact (rpc_crossFlip wwit_unitSquareLoop hadj).mp rpc_unitSquare_flip

end Walls

end StatMech
