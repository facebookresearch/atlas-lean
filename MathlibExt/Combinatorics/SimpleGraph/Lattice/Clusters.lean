/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Probability.Configuration.ConfigSpace

/-!
# Open clusters of a bond configuration on `ℤ^d`

Given a bond configuration `ω : ConfigSpace (Sym2 (Site d))`, an edge of the hypercubic lattice is
open when `ω` assigns it `true`. This file defines the open subgraph, the connectivity relation it
induces, and the open cluster of a site.

## Main definitions

* `StatMech.Lattice.openSubgraph d ω`: the spanning subgraph of open lattice edges.
* `StatMech.Lattice.Connected d ω x y`: `x` and `y` are joined by an open path.
* `StatMech.Lattice.cluster d ω x`: the open cluster of `x`.
* `StatMech.Lattice.ConnectedWithin d ω S x y`: `x` and `y` are joined by an open path inside `S`.

## Main results

* `StatMech.Lattice.connected_equivalence`: open connectivity is an equivalence relation.
* `StatMech.Lattice.cluster_eq_of_connected`: connected sites have the same cluster.
-/

@[expose] public section

open Set

namespace StatMech

namespace Lattice

variable {d : ℕ}

/-- The lattice edge `{x, y}` is open in the configuration `ω`: `x` and `y` are nearest neighbours
and `ω s(x, y) = true`. -/
def IsOpenEdge (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) : Prop :=
  (hypercubicLattice d).Adj x y ∧ ω s(x, y) = true

theorem isOpenEdge_symm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : IsOpenEdge d ω y x := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj.symm, ?_⟩
  rwa [Sym2.eq_swap]

theorem isOpenEdge_irrefl {ω : ConfigSpace (Sym2 (Site d))} (x : Site d) :
    ¬ IsOpenEdge d ω x x := fun h => h.1.ne rfl

theorem isOpenEdge_imp_adj {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : (hypercubicLattice d).Adj x y := h.1

/-- The open subgraph of `ω`: the spanning subgraph of `ℤ^d` consisting of the open edges. -/
def openSubgraph (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : SimpleGraph (Site d) where
  Adj x y := IsOpenEdge d ω x y
  symm := ⟨fun _ _ h => isOpenEdge_symm h⟩
  loopless := ⟨fun x h => isOpenEdge_irrefl x h⟩

@[simp]
theorem openSubgraph_adj (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSubgraph d ω).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl

theorem openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d ω ≤ hypercubicLattice d := fun _ _ h => h.1

/-- `x` and `y` are connected by an open path, that is, reachable in `openSubgraph d ω`. -/
def Connected (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) : Prop :=
  (openSubgraph d ω).Reachable x y

theorem connected_refl (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    Connected d ω x x := SimpleGraph.Reachable.refl x

@[refl]
theorem connected_rfl {ω : ConfigSpace (Sym2 (Site d))} {x : Site d} :
    Connected d ω x x := SimpleGraph.Reachable.refl x

theorem Connected.symm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : Connected d ω x y) : Connected d ω y x := SimpleGraph.Reachable.symm h

theorem Connected.trans {ω : ConfigSpace (Sym2 (Site d))} {x y z : Site d}
    (hxy : Connected d ω x y) (hyz : Connected d ω y z) : Connected d ω x z :=
  SimpleGraph.Reachable.trans hxy hyz

theorem connected_comm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    Connected d ω x y ↔ Connected d ω y x := SimpleGraph.reachable_comm

theorem connected_equivalence (ω : ConfigSpace (Sym2 (Site d))) :
    Equivalence (Connected d ω) := (openSubgraph d ω).reachable_is_equivalence

theorem IsOpenEdge.connected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : Connected d ω x y :=
  SimpleGraph.Adj.reachable (G := openSubgraph d ω) h

/-- The open cluster of `x`: the set of sites connected to `x` by an open path. -/
def cluster (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Set (Site d) :=
  {y | Connected d ω x y}

@[simp]
theorem mem_cluster {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    y ∈ cluster d ω x ↔ Connected d ω x y := Iff.rfl

theorem self_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    x ∈ cluster d ω x := connected_refl ω x

theorem cluster_eq_of_connected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : Connected d ω x y) : cluster d ω x = cluster d ω y := by
  ext z
  simp only [mem_cluster]
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- The open subgraph of `ω` induced on a set `S` of sites. -/
def openSubgraphInduce (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d)) :
    SimpleGraph S :=
  (openSubgraph d ω).induce S

@[simp]
theorem openSubgraphInduce_adj (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x y : S) :
    (openSubgraphInduce d ω S).Adj x y ↔ (openSubgraph d ω).Adj x y := Iff.rfl

/-- `x` and `y` in `S` are connected by an open path that stays inside `S`. -/
def ConnectedWithin (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x y : S) : Prop :=
  (openSubgraphInduce d ω S).Reachable x y

theorem connectedWithin_refl (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x : S) : ConnectedWithin d ω S x x := SimpleGraph.Reachable.refl x

theorem ConnectedWithin.symm {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y : S} (h : ConnectedWithin d ω S x y) : ConnectedWithin d ω S y x :=
  SimpleGraph.Reachable.symm h

theorem ConnectedWithin.trans {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y z : S} (hxy : ConnectedWithin d ω S x y) (hyz : ConnectedWithin d ω S y z) :
    ConnectedWithin d ω S x z := SimpleGraph.Reachable.trans hxy hyz

theorem ConnectedWithin.connected {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y : S} (h : ConnectedWithin d ω S x y) : Connected d ω x y := by
  have hmap : (openSubgraphInduce d ω S).Reachable x y →
      (openSubgraph d ω).Reachable (x : Site d) (y : Site d) :=
    fun hr => hr.map (SimpleGraph.Embedding.induce S).toHom
  exact hmap h

/-- Connection inside `S` implies connection inside any `T ⊇ S`. -/
theorem connectedWithin_mono_set (ω : ConfigSpace (Sym2 (Site d)))
    {S T : Set (Site d)} (hST : S ⊆ T) {x y : S}
    (h : ConnectedWithin d ω S x y) :
    ConnectedWithin d ω T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
  let f : (openSubgraph d ω).induce S →g (openSubgraph d ω).induce T :=
    { toFun := fun z => ⟨(z : Site d), hST z.2⟩
      map_rel' := fun {a b} hab => hab }
  exact h.map f

/-- A closed walk in the open subgraph that repeats no edge (an open circuit). -/
def IsOpenCircuit (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (w : (openSubgraph d ω).Walk x x) : Prop := w.IsCircuit

end Lattice

end StatMech
