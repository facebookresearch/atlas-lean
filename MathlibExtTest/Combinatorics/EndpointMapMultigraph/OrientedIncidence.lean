/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.OrientedIncidence

@[expose] public section

namespace EndpointMapMultigraphOrientedIncidenceTest

open EndpointMapMultigraph Matrix

/-! ### Two parallel edges `0 → 1` -/

/-- Both parallel edges keep their own column, `+1` at `0` and `-1` at `1`. -/
example :
    orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 0 0 = 1 ∧
      orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 0 1 = 1 ∧
      orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 1 0 = -1 ∧
      orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [orientedIncidence_apply]

theorem parallel_mk_eq (c : (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2))
    (fun _ => 1)).ConnectedComponent) :
    c = (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).connectedComponentMk 0 := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    fin_cases v
    · rfl
    · exact SimpleGraph.ConnectedComponent.sound
        (underlyingGraph_adj_of_ne (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)
          (e := 0) (by decide)).reachable.symm

theorem parallel_card :
    Nat.card (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).ConnectedComponent =
      1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨_, parallel_mk_eq⟩

/-- Parallel edges do not raise the rank: two parallel edges on two vertices have rank one. -/
example : (orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).rank = 1 := by
  rw [rank_orientedIncidence _ _ (by decide), parallel_card]
  rfl

/-- A zero-sum vector is attained; a vector with nonzero total is not. -/
example :
    (![1, -1] : Fin 2 → ℝ) ∈
        LinearMap.range (orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).mulVecLin ∧
      (![1, 0] : Fin 2 → ℝ) ∉
        LinearMap.range
          (orientedIncidence (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).mulVecLin := by
  constructor
  · rw [mem_range_orientedIncidence_iff _ _ (by decide)]
    intro c
    have hall : ∀ v,
        (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).connectedComponentMk v = c :=
      fun v => (parallel_mk_eq _).trans (parallel_mk_eq c).symm
    simp [hall]
  · rw [mem_range_orientedIncidence_iff _ _ (by decide)]
    intro h
    have h0 := h ((underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).connectedComponentMk
      0)
    have hall : ∀ v,
        (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).connectedComponentMk v =
          (underlyingGraph (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1)).connectedComponentMk 0 :=
      fun v => parallel_mk_eq _
    simp [hall] at h0

/-! ### Two antiparallel edges `0 → 1` and `1 → 0` -/

/-- Reversing an edge negates its column: the columns are `(1, -1)` and `(-1, 1)`. -/
example :
    orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0] 0 0 = 1 ∧
      orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0] 1 0 = -1 ∧
      orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0] 0 1 = -1 ∧
      orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0] 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [orientedIncidence_apply]

theorem antiparallel_mk_eq (c : (underlyingGraph (![0, 1] : Fin 2 → Fin 2)
    ![1, 0]).ConnectedComponent) :
    c = (underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).connectedComponentMk 0 := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    fin_cases v
    · rfl
    · exact SimpleGraph.ConnectedComponent.sound
        (underlyingGraph_adj_of_ne (![0, 1] : Fin 2 → Fin 2) ![1, 0]
          (e := 0) (by decide)).reachable.symm

/-- Antiparallel edges, like parallel ones, give rank one on two vertices. -/
example : (orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0]).rank = 1 := by
  have hcard :
      Nat.card (underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).ConnectedComponent = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨_, antiparallel_mk_eq⟩
  rw [rank_orientedIncidence _ _ (by decide), hcard]
  rfl

/-- The range is the same as for two parallel edges: `(1, -1)` is attained, `(1, 0)` is not. -/
example :
    (![1, -1] : Fin 2 → ℝ) ∈
        LinearMap.range (orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0]).mulVecLin ∧
      (![1, 0] : Fin 2 → ℝ) ∉
        LinearMap.range (orientedIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0]).mulVecLin := by
  constructor
  · rw [mem_range_orientedIncidence_iff _ _ (by decide)]
    intro c
    have hall : ∀ v,
        (underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).connectedComponentMk v = c :=
      fun v => (antiparallel_mk_eq _).trans (antiparallel_mk_eq c).symm
    simp [hall]
  · rw [mem_range_orientedIncidence_iff _ _ (by decide)]
    intro h
    have h0 := h ((underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).connectedComponentMk 0)
    have hall : ∀ v,
        (underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).connectedComponentMk v =
          (underlyingGraph (![0, 1] : Fin 2 → Fin 2) ![1, 0]).connectedComponentMk 0 :=
      fun v => antiparallel_mk_eq _
    simp [hall] at h0

/-! ### A disconnected graph: edge `0 → 1` and an isolated vertex `2` -/

theorem disconnected_reachable_two {u v : Fin 3}
    (h : (underlyingGraph (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).Reachable u v) :
    (u = 2 ↔ v = 2) := by
  rw [underlyingGraph_reachable_iff] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    simp only [AdjacentUsing, Finset.mem_univ, true_and, exists_const] at hbc
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa using ih

theorem disconnected_mk_ne :
    (underlyingGraph (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).connectedComponentMk 0 ≠
      (underlyingGraph (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).connectedComponentMk 2 := by
  intro h
  simpa using disconnected_reachable_two (SimpleGraph.ConnectedComponent.exact h)

/-- A vector constant on each component, with different values on the two components, lies in
the left kernel. -/
example :
    (![5, 5, 7] : Fin 3 → ℝ) ᵥ* orientedIncidence (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1) =
      0 := by
  rw [vecMul_orientedIncidence_eq_zero_iff _ _ (by decide)]
  intro u v huv
  have := disconnected_reachable_two huv
  fin_cases u <;> fin_cases v <;> simp_all

/-- A vector that is not constant along the edge is not in the left kernel. -/
example :
    (![5, 6, 7] : Fin 3 → ℝ) ᵥ* orientedIncidence (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1) ≠
      0 := by
  rw [Ne, vecMul_orientedIncidence_eq_zero_iff _ _ (by decide)]
  intro h
  have := h 0 1 (underlyingGraph_adj_of_ne (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)
    (e := 0) (by decide)).reachable
  norm_num at this

/-- An anchor at vertex `0` only leaves the isolated vertex `2` unanchored: not surjective. -/
example :
    ¬Function.Surjective
      ((orientedIncidence (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).fromCols
        (boundaryColumns (fun _ : Fin 1 => (0 : Fin 3)) fun _ => 1)).mulVec := by
  rw [surjective_mulVec_fromCols_boundaryColumns_iff _ _ (by decide) _ _ (by simp)]
  intro h
  obtain ⟨j, hj⟩ := h
    ((underlyingGraph (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).connectedComponentMk 2)
  exact disconnected_mk_ne hj

/-- Anchors at `0` (sign `+1`) and at the isolated vertex `2` (sign `-1`): surjective. -/
example :
    Function.Surjective
      ((orientedIncidence (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)).fromCols
        (boundaryColumns (![0, 2] : Fin 2 → Fin 3) ![1, -1])).mulVec := by
  rw [surjective_mulVec_fromCols_boundaryColumns_iff _ _ (by decide) _ _
    (by intro j; fin_cases j <;> simp)]
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    fin_cases v
    · exact ⟨0, rfl⟩
    · exact ⟨0, SimpleGraph.ConnectedComponent.sound
        (underlyingGraph_adj_of_ne (fun _ : Fin 1 => (0 : Fin 3)) (fun _ => 1)
          (e := 0) (by decide)).reachable⟩
    · exact ⟨1, rfl⟩

/-! ### Empty situations -/

/-- With no edges, the rank formula counts every vertex as its own component. -/
example :
    Nat.card (underlyingGraph (Empty.elim : Empty → Fin 2) Empty.elim).ConnectedComponent =
      2 := by
  have h := rank_orientedIncidence_add_card_connectedComponent
    (Empty.elim : Empty → Fin 2) Empty.elim (fun e => e.elim)
  have h0 : orientedIncidence (Empty.elim : Empty → Fin 2) Empty.elim = 0 := by
    ext _ e
    exact e.elim
  rw [h0, Matrix.rank_zero, Fintype.card_fin] at h
  omega

/-- An isolated vertex with no boundary column is unanchored: not surjective. -/
example :
    ¬Function.Surjective
      ((orientedIncidence (Empty.elim : Empty → Fin 1) Empty.elim).fromCols
        (boundaryColumns (Empty.elim : Empty → Fin 1) Empty.elim)).mulVec := by
  rw [surjective_mulVec_fromCols_boundaryColumns_iff _ _ (fun e => e.elim) _ _
    (fun j => j.elim)]
  intro h
  obtain ⟨j, -⟩ :=
    h ((underlyingGraph (Empty.elim : Empty → Fin 1) Empty.elim).connectedComponentMk 0)
  exact j.elim

/-- An isolated vertex with one boundary column of sign `-1` is anchored: surjective. -/
example :
    Function.Surjective
      ((orientedIncidence (Empty.elim : Empty → Fin 1) Empty.elim).fromCols
        (boundaryColumns (fun _ : Unit => (0 : Fin 1)) fun _ => -1)).mulVec := by
  rw [surjective_mulVec_fromCols_boundaryColumns_iff _ _ (fun e => e.elim) _ _ (by simp)]
  intro c
  exact ⟨(), Subsingleton.elim _ _⟩

/-- With no vertices the condition is vacuous and the map is surjective. -/
example :
    Function.Surjective
      ((orientedIncidence (Empty.elim : Empty → Empty) Empty.elim).fromCols
        (boundaryColumns (Empty.elim : Empty → Empty) Empty.elim)).mulVec := by
  rw [surjective_mulVec_fromCols_boundaryColumns_iff _ _ (fun e => e.elim) _ _
    (fun j => j.elim)]
  intro c
  exact c.ind fun v => v.elim

end EndpointMapMultigraphOrientedIncidenceTest
