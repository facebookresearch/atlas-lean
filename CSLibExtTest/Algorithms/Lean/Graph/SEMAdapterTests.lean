/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.SEMAdapter

/-!
# SEM adapter tests

Chain and disconnected graphs admit the finite inverse; a loop graph and
the transposed support convention fail the hypotheses.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

open TopologicalSort MathlibExt.Probability.Statistics.Measurement

namespace SEMAdapterTest

open TopologicalSort SEMAdapter

/-- Helper: a graph on `Fin n` whose edges all go forward in `Fin.val`
is acyclic. Any directed cycle would have nondecreasing `val` along the
chain but a strictly decreasing closing edge. -/
private theorem acyclic_of_val_lt {n : ℕ} (g : DirectedAdjacency (Fin n))
    (hedge : ∀ u v, g.Edge u v → u.val < v.val) :
    IsAcyclic g := by
  rintro ⟨cycle, hne, hnodup, hchain, hclose, hmem⟩
  cases cycle with
  | nil => exact hne rfl
  | cons first rest =>
    dsimp at hclose
    have hle : ∀ (a : Fin n) (l : List (Fin n)),
        List.IsChain g.Edge (a :: l) → ∀ b ∈ a :: l, a.val ≤ b.val := by
      intro a l h
      induction l generalizing a with
      | nil =>
        intro b hb
        simp at hb
        subst hb
        exact le_rfl
      | cons bmid l ih =>
        intro b hb
        have h1 : g.Edge a bmid := List.IsChain.rel h
        have h2 : List.IsChain g.Edge (bmid :: l) := List.IsChain.tail h
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb | hb
        · exact le_rfl
        · rw [hb]
          exact le_of_lt (hedge a bmid h1)
        · have hmid := hedge a bmid h1
          have htail := ih bmid h2 b (List.mem_cons.mpr (Or.inr hb))
          omega
    have hmem0 := List.getLast_mem (l := first :: rest) (by simp)
    have hle1 := hle first rest hchain _ hmem0
    have hlt2 := hedge _ _ hclose
    omega

/-- Chain graph `0 → 1 → 2` on `Fin 3`. -/
def chainGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by
    intro v
    fin_cases v <;> simp
  adjacency := fun v => if v = 0 then [1] else if v = 1 then [2] else []

/-- Chain coefficients: `B 1 0 = 3` (edge `0 → 1`), `B 2 1 = 5` (edge `1 → 2`). -/
def chainB : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 3 else if i = 2 ∧ j = 1 then 5 else 0

/-- Nonvacuous chain: the main theorem applies; the inverse is the finite
sum `1 + B + B ^ 2` over `Finset.range (Fintype.card (Fin 3))`. -/
theorem chain_inverse :
    (1 - chainB)⁻¹ = ∑ k ∈ Finset.range (Fintype.card (Fin 3)), chainB ^ k := by
  have hedge : ∀ u v, chainGraph.Edge u v → u.val < v.val := by
    show ∀ u v, v ∈ chainGraph.adjacency u → u.val < v.val
    decide
  have hacyclic : IsAcyclic chainGraph := acyclic_of_val_lt chainGraph hedge
  have hB : ∀ i j, chainB i j ≠ 0 → chainGraph.Edge j i := by
    intro i j hij
    simp only [chainB] at hij
    by_cases h1 : (i = 1 ∧ j = 0)
    · obtain ⟨rfl, rfl⟩ := h1
      show (1 : Fin 3) ∈ chainGraph.adjacency 0
      decide
    · by_cases h2 : (i = 2 ∧ j = 1)
      · obtain ⟨rfl, rfl⟩ := h2
        show (2 : Fin 3) ∈ chainGraph.adjacency 1
        decide
      · simp [h1, h2] at hij
  exact inverse_of_acyclic chainGraph chainB hacyclic hB

/-- Chain nilpotence at the stated bound: `chainB ^ 3 = 0`. -/
theorem chain_pow_card_eq_zero :
    chainB ^ Fintype.card (Fin 3) = 0 := by
  have hedge : ∀ u v, chainGraph.Edge u v → u.val < v.val := by
    show ∀ u v, v ∈ chainGraph.adjacency u → u.val < v.val
    decide
  have hacyclic : IsAcyclic chainGraph := acyclic_of_val_lt chainGraph hedge
  have hB : ∀ i j, chainB i j ≠ 0 → chainGraph.Edge j i := by
    intro i j hij
    simp only [chainB] at hij
    by_cases h1 : (i = 1 ∧ j = 0)
    · obtain ⟨rfl, rfl⟩ := h1
      show (1 : Fin 3) ∈ chainGraph.adjacency 0
      decide
    · by_cases h2 : (i = 2 ∧ j = 1)
      · obtain ⟨rfl, rfl⟩ := h2
        show (2 : Fin 3) ∈ chainGraph.adjacency 1
        decide
      · simp [h1, h2] at hij
  exact pow_card_eq_zero_of_acyclic chainGraph chainB hacyclic hB

/-- Disconnected graph: chain `0 → 1 → 2` plus isolated vertex `3`. -/
def disconnectedGraph : DirectedAdjacency (Fin 4) where
  vertices := [0, 1, 2, 3]
  vertices_nodup := by decide
  vertices_complete := by
    intro v
    fin_cases v <;> simp
  adjacency := fun v => if v = 0 then [1] else if v = 1 then [2] else []

/-- Disconnected coefficients: as `chainB` on `Fin 4`, zero row/column at `3`. -/
def disconnectedB : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 3 else if i = 2 ∧ j = 1 then 5 else 0

/-- An isolated vertex does not block the finite inverse identity. -/
theorem disconnected_inverse :
    (1 - disconnectedB)⁻¹ =
      ∑ k ∈ Finset.range (Fintype.card (Fin 4)), disconnectedB ^ k := by
  have hedge : ∀ u v, disconnectedGraph.Edge u v → u.val < v.val := by
    show ∀ u v, v ∈ disconnectedGraph.adjacency u → u.val < v.val
    decide
  have hacyclic : IsAcyclic disconnectedGraph :=
    acyclic_of_val_lt disconnectedGraph hedge
  have hB : ∀ i j, disconnectedB i j ≠ 0 → disconnectedGraph.Edge j i := by
    intro i j hij
    simp only [disconnectedB] at hij
    by_cases h1 : (i = 1 ∧ j = 0)
    · obtain ⟨rfl, rfl⟩ := h1
      show (1 : Fin 4) ∈ disconnectedGraph.adjacency 0
      decide
    · by_cases h2 : (i = 2 ∧ j = 1)
      · obtain ⟨rfl, rfl⟩ := h2
        show (2 : Fin 4) ∈ disconnectedGraph.adjacency 1
        decide
      · simp [h1, h2] at hij
  exact inverse_of_acyclic disconnectedGraph disconnectedB hacyclic hB

/-- Self-loop graph `0 → 0`: acyclicity itself fails, so the main
theorem's hypothesis is unavailable (no inverse identity is claimed). -/
def loopGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by
    intro v
    fin_cases v <;> simp
  adjacency := fun v => if v = 0 then [0] else []

theorem loop_not_acyclic : ¬ IsAcyclic loopGraph := by
  intro h
  apply h
  refine ⟨[0], by decide, by decide, List.IsChain.singleton 0, ?_, by decide⟩
  show (0 : Fin 3) ∈ loopGraph.adjacency 0
  decide

theorem loop_no_topologicalOrder :
    ¬ ∃ order : List (Fin 3), IsTopologicalOrder loopGraph order := by
  rintro ⟨order, _, _, hfwd⟩
  have hedge : loopGraph.Edge 0 0 := by
    show (0 : Fin 3) ∈ loopGraph.adjacency 0
    decide
  exact absurd (hfwd 0 0 hedge) (lt_irrefl _)

/-- Two-cycle `0 → 1 → 0`: acyclicity and topological order both fail. -/
def cycleGraph : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by
    intro v
    fin_cases v <;> simp
  adjacency := fun v => if v = 0 then [1] else if v = 1 then [0] else []

theorem cycle_not_acyclic : ¬ IsAcyclic cycleGraph := by
  intro h
  apply h
  have e01 : cycleGraph.Edge 0 1 := by
    show (1 : Fin 3) ∈ cycleGraph.adjacency 0
    decide
  refine ⟨[0, 1], by decide, by decide,
    List.IsChain.cons_cons e01 (List.IsChain.singleton 1), ?_, by decide⟩
  show (0 : Fin 3) ∈ cycleGraph.adjacency 1
  decide

theorem cycle_no_topologicalOrder :
    ¬ ∃ order : List (Fin 3), IsTopologicalOrder cycleGraph order := by
  rintro ⟨order, _, _, hfwd⟩
  have e01 : cycleGraph.Edge 0 1 := by
    show (1 : Fin 3) ∈ cycleGraph.adjacency 0
    decide
  have e10 : cycleGraph.Edge 1 0 := by
    show (0 : Fin 3) ∈ cycleGraph.adjacency 1
    decide
  have g1 := hfwd 0 1 e01
  have g2 := hfwd 1 0 e10
  omega

/-- Transposed coefficients: `B 0 1 = 3` would need edge `1 → 0`, which
`chainGraph` does not have; `B 1 2 = 5` would need edge `2 → 1`. -/
def transposedB : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 3 else if i = 1 ∧ j = 2 then 5 else 0

/-- Orientation failure, support form: the `hB` hypothesis of
`inverse_of_acyclic` is false for the transposed matrix. -/
theorem transposed_support_fails :
    ¬ (∀ i j, transposedB i j ≠ 0 → chainGraph.Edge j i) := by
  intro h
  have hne : transposedB 0 1 ≠ 0 := by norm_num [transposedB]
  have hcon := h 0 1 hne
  revert hcon
  show ¬ (0 : Fin 3) ∈ chainGraph.adjacency 1
  decide

/-- Orientation failure, rank form: at the canonical order `[0, 1, 2]`,
the `ord j < ord i` hypothesis of the MathlibExt identities is false
(it would require `idxOf 1 < idxOf 0`). -/
theorem transposed_rank_fails :
    ¬ (∀ i j, transposedB i j ≠ 0 →
        ([0, 1, 2] : List (Fin 3)).idxOf j < ([0, 1, 2] : List (Fin 3)).idxOf i) := by
  intro h
  have hne : transposedB 0 1 ≠ 0 := by norm_num [transposedB]
  have hcon := h 0 1 hne
  revert hcon
  decide

end SEMAdapterTest

end Cslib.Algorithms.Lean
