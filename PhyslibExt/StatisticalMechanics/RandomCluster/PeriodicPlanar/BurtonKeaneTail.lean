/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTrifurcation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour
public import Mathlib.Combinatorics.SimpleGraph.Ends.Properties

/-!
# Infinite tails of an infinite cluster outside a finite set

An infinite open cluster meeting a finite set `K` leaves `K` through an open edge into an infinite
part of the cluster that stays connected outside `K`.

## i. Overview

The open cluster of `x`, viewed as a locally finite connected graph, is infinite and so has an end.
That end picks an infinite component of the cluster with the vertices of `K` removed. A boundary
edge of this component gives an open edge from a vertex inside `K` to a vertex outside, and the
component is an infinite tail connected by open paths avoiding `K`. These tails are the input to
the trifurcation construction of the Burton–Keane argument. `infiniteCluster_has_open_exit` is
proved unconditionally.

## ii. Key results

- `PeriodicGraph.infiniteCluster_component_after_finset` : removing a finite set from an infinite
  cluster leaves an infinite component.
- `PeriodicGraph.infiniteCluster_has_open_exit` : an infinite cluster meeting `K` has an open exit
  edge from `K` into an infinite tail connected outside `K`.

## iii. Table of contents

- A. The cluster as a locally finite graph
- B. Infinite components outside a finite set
- C. Exit edges and tail data

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Set SimpleGraph

set_option linter.unusedSectionVars false

namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

/-! ## A. The cluster as a locally finite graph -/

/-- The vertices of the open cluster of `x`, as a subtype. -/
abbrev PeriodicGraph.TailClusterVertex (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) :=
  {y : V // y ∈ P.cluster omega x}

/-- The open subgraph induced on the open cluster of `x`. -/
abbrev PeriodicGraph.tailClusterGraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    SimpleGraph (P.TailClusterVertex omega x) :=
  (P.openSubgraph omega).induce (P.cluster omega x)

/-- The vertices of `K` that lie in the open cluster of `x`, as a finite set of cluster vertices. -/
noncomputable def PeriodicGraph.tailClusterCut (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) (K : Finset V) :
    Finset (P.TailClusterVertex omega x) :=
  K.preimage Subtype.val Subtype.val_injective.injOn

/-- The cluster graph is locally finite, since the periodic graph is. -/
noncomputable instance PeriodicGraph.tailClusterGraphLocallyFinite
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    SimpleGraph.LocallyFinite (P.tailClusterGraph omega x) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  intro v
  let f : (P.tailClusterGraph omega x).neighborSet v ->
      P.graph.neighborSet v.1 := fun w =>
    ⟨w.1.1, w.2.1⟩
  exact Fintype.ofInjective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P.graph.neighborSet v.1 => (z : V)) h)

/-- The cluster graph is preconnected: any two cluster vertices are joined by an open path inside
the cluster. -/
instance PeriodicGraph.tailClusterGraphPreconnected
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    Fact (P.tailClusterGraph omega x).Preconnected := ⟨by
  intro u v
  have huv : (P.openSubgraph omega).Reachable u.1 v.1 := u.2.symm.trans v.2
  obtain ⟨w⟩ := huv
  exact StatMech.Lattice.walk_induce_reachable (P.openSubgraph omega)
    (P.cluster omega x) w (fun z hz => by
      exact u.2.trans (w.takeUntil z hz).reachable)
    u.2 v.2⟩

/-! ## B. Infinite components outside a finite set -/

/-- Removing the finite set `K` from an infinite cluster leaves an infinite connected component. -/
lemma PeriodicGraph.infiniteCluster_component_after_finset
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) :
    ∃ D : (P.tailClusterGraph omega x).ComponentCompl
        (P.tailClusterCut omega x K), D.supp.Infinite := by
  have : Infinite (P.TailClusterVertex omega x) := hinf.to_subtype
  let e : (P.tailClusterGraph omega x).end :=
    ⟨(SimpleGraph.nonempty_ends_of_infinite
      (P.tailClusterGraph omega x)).choose,
      (SimpleGraph.nonempty_ends_of_infinite
      (P.tailClusterGraph omega x)).choose_spec⟩
  let D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K) :=
    (e : (j : (Finset (P.TailClusterVertex omega x))ᵒᵖ) ->
      (P.tailClusterGraph omega x).componentComplFunctor.obj j)
      (Opposite.op (P.tailClusterCut omega x K))
  exact ⟨D, SimpleGraph.end_componentCompl_infinite
    (P.tailClusterGraph omega x) e (Opposite.op (P.tailClusterCut omega x K))⟩

/-- The vertices of `V` underlying a component of the cluster with `K` removed. -/
def PeriodicGraph.tailComponentVertices
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) : Set V :=
  Subtype.val '' (D : Set (P.TailClusterVertex omega x))

lemma PeriodicGraph.tailComponentVertices_infinite
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) (hD : D.supp.Infinite) :
    (P.tailComponentVertices omega x K D).Infinite :=
  hD.image Subtype.val_injective.injOn

lemma PeriodicGraph.tailComponentVertices_subset_cluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) :
    P.tailComponentVertices omega x K D ⊆ P.cluster omega x := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

lemma PeriodicGraph.tailComponentVertices_connected_outside
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) :
    ∀ u ∈ P.tailComponentVertices omega x K D,
      ∀ v ∈ P.tailComponentVertices omega x K D,
        ∃ (hu : u ∉ (K : Set V)) (hv : v ∉ (K : Set V)),
          ((P.openSubgraph omega).induce (K : Set V)ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩ := by
  rintro u ⟨uC, huD, rfl⟩ v ⟨vC, hvD, rfl⟩
  rcases huD with ⟨huCut, huComp⟩
  rcases hvD with ⟨hvCut, hvComp⟩
  have huK : uC.1 ∉ (K : Set V) := by
    intro hmem
    exact huCut (by simp [PeriodicGraph.tailClusterCut, hmem])
  have hvK : vC.1 ∉ (K : Set V) := by
    intro hmem
    exact hvCut (by simp [PeriodicGraph.tailClusterCut, hmem])
  refine ⟨huK, hvK, ?_⟩
  have hreach :
      ((P.tailClusterGraph omega x).induce
        ((P.tailClusterCut omega x K : Set (P.TailClusterVertex omega x)))ᶜ).Reachable
          ⟨uC, huCut⟩ ⟨vC, hvCut⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact huComp.trans hvComp.symm
  let f : ((P.tailClusterGraph omega x).induce
      ((P.tailClusterCut omega x K : Set (P.TailClusterVertex omega x)))ᶜ) →g
      ((P.openSubgraph omega).induce (K : Set V)ᶜ) := {
    toFun := fun z => ⟨z.1.1, by
      intro hzK
      exact z.2 (by simp [PeriodicGraph.tailClusterCut, hzK])⟩
    map_rel' := by intro a b hab; exact hab }
  exact hreach.map f

/-! ## C. Exit edges and tail data -/

/-- An open exit edge from `inside ∈ K` to `outside ∉ K` together with an infinite tail of the
cluster of `x` that contains `outside` and is connected by open paths avoiding `K`. -/
structure PeriodicGraph.InfiniteTailData (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (K : Finset V) (x : V) where
  inside : V
  outside : V
  tail : Set V
  inside_mem : inside ∈ K
  outside_not_mem : outside ∉ K
  exit_open : (P.openSubgraph omega).Adj inside outside
  outside_mem_tail : outside ∈ tail
  tail_infinite : tail.Infinite
  tail_subset_cluster : tail ⊆ P.cluster omega x
  tail_connected_outside :
    ∀ a ∈ tail, ∀ b ∈ tail,
      ∃ (ha : a ∉ (K : Set V)) (hb : b ∉ (K : Set V)),
        ((P.openSubgraph omega).induce (K : Set V)ᶜ).Reachable
          ⟨a, ha⟩ ⟨b, hb⟩

/-- An infinite cluster containing a vertex of the finite set `K` has an open exit edge from `K`
into an infinite tail connected outside `K`. -/
theorem PeriodicGraph.infiniteCluster_has_open_exit
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) (hxK : x ∈ K) :
    Nonempty (P.InfiniteTailData omega K x) := by
  obtain ⟨D, hD⟩ := P.infiniteCluster_component_after_finset omega x hinf K
  have hcut : (P.tailClusterCut omega x K).Nonempty := by
    refine ⟨⟨x, P.self_mem_cluster omega x⟩, ?_⟩
    simp [PeriodicGraph.tailClusterCut, hxK]
  obtain ⟨⟨v, u⟩, hvD, huCut, hadj⟩ :=
    D.exists_adj_boundary_pair (P.tailClusterGraphPreconnected omega x).out hcut
  have huK : u.1 ∈ K := by simpa [PeriodicGraph.tailClusterCut] using huCut
  have hvK : v.1 ∉ K := by
    intro hv
    exact D.notMem_of_mem hvD (by simp [PeriodicGraph.tailClusterCut, hv])
  exact ⟨{
    inside := u.1
    outside := v.1
    tail := P.tailComponentVertices omega x K D
    inside_mem := huK
    outside_not_mem := hvK
    exit_open := hadj.symm
    outside_mem_tail := ⟨v, hvD, rfl⟩
    tail_infinite := P.tailComponentVertices_infinite omega x K D hD
    tail_subset_cluster := P.tailComponentVertices_subset_cluster omega x K D
    tail_connected_outside :=
      P.tailComponentVertices_connected_outside omega x K D }⟩

/-- A chosen exit edge and infinite tail for an infinite cluster meeting `K`. -/
noncomputable def PeriodicGraph.infiniteTailData
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) (hxK : x ∈ K) :
    P.InfiniteTailData omega K x :=
  (P.infiniteCluster_has_open_exit omega x hinf K hxK).some

end StatMech.FK.PeriodicPlanar
