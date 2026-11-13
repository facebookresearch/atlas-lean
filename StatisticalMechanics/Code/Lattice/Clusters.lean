/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice

open Set

namespace StatMech

namespace Lattice

variable {d : ℕ}




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




def openSubgraph (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : SimpleGraph (Site d) where
  Adj x y := IsOpenEdge d ω x y
  symm _ _ h := isOpenEdge_symm h
  loopless := ⟨fun x h => isOpenEdge_irrefl x h⟩

@[simp]
theorem openSubgraph_adj (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSubgraph d ω).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl



theorem openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d ω ≤ hypercubicLattice d := fun _ _ h => h.1



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




def openSubgraphInduce (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d)) :
    SimpleGraph S :=
  (openSubgraph d ω).induce S

@[simp]
theorem openSubgraphInduce_adj (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x y : S) :
    (openSubgraphInduce d ω S).Adj x y ↔ (openSubgraph d ω).Adj x y := Iff.rfl



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



def IsOpenCircuit (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (w : (openSubgraph d ω).Walk x x) : Prop := w.IsCircuit

end Lattice

end StatMech
