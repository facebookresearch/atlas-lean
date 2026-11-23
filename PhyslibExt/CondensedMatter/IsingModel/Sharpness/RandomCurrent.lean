/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Random currents on finite graphs

Currents `n : E → ℕ`, their sources, weights `∏ (βJ_e)^{n_e}/n_e!`, the connectivity they induce,
backbones, and the graph with a ghost vertex.

## i. Overview

A current on a finite graph `G` assigns a multiplicity `n_e ∈ ℕ` to every edge. Its sources `∂n` are
the vertices of odd total incident multiplicity, and its weight is `w(n) = ∏_{e ∈ E}
(βJ_e)^{n_e}/n_e!`. Two vertices are connected in `n` if a path of edges with `n_e ≥ 1` joins them.
Backbones are paths using only edges of odd multiplicity. The graph `withGhost G` adds a vertex
joined to every site, used to encode an external field.

## ii. Key results

- `Current` : currents on the edges of `G`
- `sources` : the source set `∂n`
- `weight` : the current weight
- `CurrentConnected` : connectivity in a current
- `IsBackbonePath` : backbone paths
- `withGhost` : the graph with a ghost vertex

## iii. Table of contents

- A. Currents, sources and weights
- B. Connectivity
- C. Backbones
- D. The trace of a current
- E. The ghost vertex

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
  arXiv:1607.06933

-/

@[expose] public section

open SimpleGraph Finset


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Currents, sources and weights -/

/-- A current on the edges of `V`: a multiplicity `n_e ∈ ℕ` for every unordered pair `e`. -/
abbrev Current (V : Type*) : Type _ := Sym2 V → ℕ

/-- The total multiplicity `∑_{e ∋ x} n_e` of the edges of `G` incident to `x`. -/
noncomputable def incidentFlux (n : Current V) (x : V) : ℕ :=
  ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e), n e

/-- The sources `∂n`: the vertices with odd incident flux. -/
noncomputable def sources (n : Current V) : Finset V :=
  Finset.univ.filter (fun x => Odd (incidentFlux G n x))

@[simp]
lemma mem_sources {n : Current V} {x : V} :
    x ∈ sources G n ↔ Odd (incidentFlux G n x) := by
  simp [sources]

/-- The current weight `w(n) = ∏_{e ∈ E(G)} (βJ_e)^{n_e}/n_e!`. -/
noncomputable def weight (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) : ℝ :=
  ∏ e ∈ G.edgeFinset, (β * J e) ^ (n e) / (Nat.factorial (n e))

omit [DecidableEq V] in
/-- Current weights are nonnegative for `β ≥ 0` and nonnegative couplings. -/
lemma weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ weight G β J n := by
  unfold weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (Nat.cast_nonneg _)

omit [DecidableEq V] in
@[simp]
lemma weight_zero (β : ℝ) (J : Sym2 V → ℝ) :
    weight G β J (fun _ => 0) = 1 := by
  simp [weight]

/-! ## B. Connectivity -/

/-- The subgraph of `G` of edges with `n_e ≥ 1`. -/
def currentSubgraph (n : Current V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ 1 ≤ n s(x, y)
  symm := by
    constructor
    intro x y ⟨hadj, hpos⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => hadj.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma currentSubgraph_adj (n : Current V) (x y : V) :
    (currentSubgraph G n).Adj x y ↔ G.Adj x y ∧ 1 ≤ n s(x, y) := Iff.rfl

/-- Decidability of adjacency in `currentSubgraph`. -/
instance decidableRel_currentSubgraph (n : Current V) :
    DecidableRel (currentSubgraph G n).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ 1 ≤ n s(x, y)))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma currentSubgraph_le (n : Current V) : currentSubgraph G n ≤ G :=
  fun _ _ h => h.1

/-- `x` and `y` are joined by a path of edges carrying positive current. -/
def CurrentConnected (n : Current V) (x y : V) : Prop :=
  (currentSubgraph G n).Reachable x y

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[refl]
lemma CurrentConnected.refl (n : Current V) (x : V) : CurrentConnected G n x x :=
  SimpleGraph.Reachable.refl x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma CurrentConnected.symm {n : Current V} {x y : V}
    (h : CurrentConnected G n x y) : CurrentConnected G n y x :=
  SimpleGraph.Reachable.symm h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma CurrentConnected.trans {n : Current V} {x y z : V}
    (hxy : CurrentConnected G n x y) (hyz : CurrentConnected G n y z) :
    CurrentConnected G n x z :=
  SimpleGraph.Reachable.trans hxy hyz

/-! ## C. Backbones -/

/-- The subgraph of `G` of edges with odd multiplicity. -/
def oddSubgraph (n : Current V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ Odd (n s(x, y))
  symm := by
    constructor
    intro x y ⟨hadj, hodd⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => hadj.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma oddSubgraph_adj (n : Current V) (x y : V) :
    (oddSubgraph G n).Adj x y ↔ G.Adj x y ∧ Odd (n s(x, y)) := Iff.rfl

/-- Decidability of adjacency in `oddSubgraph`. -/
instance decidableRel_oddSubgraph (n : Current V) :
    DecidableRel (oddSubgraph G n).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ Odd (n s(x, y))))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma oddSubgraph_le (n : Current V) : oddSubgraph G n ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma oddSubgraph_le_currentSubgraph (n : Current V) :
    oddSubgraph G n ≤ currentSubgraph G n := by
  intro x y ⟨hadj, hodd⟩
  exact ⟨hadj, hodd.pos⟩

/-- Backbone paths from `x` to `y`: paths in the subgraph of odd edges. -/
abbrev IsBackbonePath (n : Current V) (x y : V) : Type _ :=
  (oddSubgraph G n).Path x y

/-- A canonical backbone path: the least one for a given linear order on backbone paths. -/
noncomputable def backbone (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) : IsBackbonePath G n x y :=
  (Finset.univ : Finset (IsBackbonePath G n x y)).min'
    (Finset.univ_nonempty_iff.mpr h)

lemma backbone_le (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) (p : IsBackbonePath G n x y) :
    backbone G n x y h ≤ p :=
  Finset.min'_le _ _ (Finset.mem_univ p)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma IsBackbonePath.currentConnected {n : Current V} {x y : V}
    (p : IsBackbonePath G n x y) : CurrentConnected G n x y :=
  (p.1.mapLe (oddSubgraph_le_currentSubgraph G n)).reachable

/-! ## D. The trace of a current -/

/-- The trace of a current: the bond configuration with `e` open iff `n_e ≥ 1`. -/
def percolationField (n : Current V) : Sym2 V → Bool :=
  fun e => decide (1 ≤ n e)

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma percolationField_apply (n : Current V) (e : Sym2 V) :
    percolationField n e = true ↔ 1 ≤ n e := by
  simp [percolationField]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma currentSubgraph_eq_percolationField (n : Current V) :
    currentSubgraph G n =
      G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true} := by
  ext x y
  simp only [currentSubgraph_adj, inf_adj, fromEdgeSet_adj, Set.mem_ofPred_eq,
    percolationField_apply]
  constructor
  · rintro ⟨hadj, hpos⟩
    exact ⟨hadj, hpos, hadj.ne⟩
  · rintro ⟨hadj, hpos, _⟩
    exact ⟨hadj, hpos⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma currentConnected_iff_percolationField (n : Current V) (x y : V) :
    CurrentConnected G n x y ↔
      (G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true}).Reachable x y := by
  rw [CurrentConnected, currentSubgraph_eq_percolationField]

/-! ## E. The ghost vertex -/

/-- The ghost vertex `none` of `Option V`. -/
def ghost : Option V := none

/-- The graph on `V ⊔ {ghost}` with the edges of `G` and an edge from every site to the ghost. -/
def withGhost : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some x, some y => G.Adj x y
    | some _, none => True
    | none, some _ => True
    | none, none => False
  symm := by
    constructor
    rintro (_ | x) (_ | y) h
    · exact h
    · exact h
    · exact h
    · exact G.symm.symm _ _ h
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl x h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma withGhost_adj_some_some (x y : V) :
    (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma withGhost_adj_some_ghost (x : V) :
    (withGhost G).Adj (some x) ghost := trivial

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma withGhost_adj_ghost_some (x : V) :
    (withGhost G).Adj ghost (some x) := trivial

end Sharpness

end StatMech
