/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Latent projection and c-components

An *acyclic directed mixed graph* (ADMG) has directed and bidirected edges.
The *latent projection* of a Bayesian network onto its observed nodes keeps
a directed edge for every directed path whose internal vertices are latent,
and a bidirected edge for every pair with a latent common cause (Evans,
APTS Causal Inference notes, Def. 15.1). The *c-components* of an ADMG are
the connected components of its bidirected part (Tian and Pearl, 2002).

## Main definitions

* `ADMG`: a directed relation with no directed cycle, and a bidirected
  simple graph.
* `ADMG.cComponent`: the bidirected connected component of a vertex.
* `BayesNet.LatentPath`: a directed path whose internal vertices are latent.
* `BayesNet.latentProjection`: the ADMG on the observed nodes.

## Main results

* `ADMG.mem_cComponent_iff`: c-component membership is bidirected
  reachability.
* `BayesNet.isDescendant_iff_reflTransGen_latentProjection`: ancestral
  relations agree between a network and its latent projection.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*} {n : ℕ}

namespace BayesNet

variable (b : BayesNet α n)

end BayesNet

/-- An acyclic directed mixed graph: a directed relation with no directed
cycle, and a bidirected simple graph. -/
structure ADMG (V : Type*) where
  /-- The directed edges. -/
  dir : V → V → Prop
  /-- The bidirected edges. -/
  bidir : SimpleGraph V
  /-- No directed cycle. -/
  acyclic : ∀ v, ¬ Relation.TransGen dir v v

namespace ADMG

variable {V : Type*} (G : ADMG V)

/-- The c-component of `v`: its bidirected connected component. -/
def cComponent (v : V) : Set V :=
  (G.bidir.connectedComponentMk v).supp

/-- Membership in a c-component is bidirected reachability. -/
theorem mem_cComponent_iff {v w : V} :
    w ∈ G.cComponent v ↔ G.bidir.Reachable v w := by
  unfold cComponent
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, eq_comm,
    SimpleGraph.ConnectedComponent.eq]

end ADMG

namespace BayesNet

variable (b : BayesNet α n) (L : Finset (Fin n))

/-- A directed path of length ≥ 1 from `u` to `w` whose internal vertices
are latent (Evans APTS Def 15.1). -/
def LatentPath (u w : Fin n) : Prop :=
  ∃ m, Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) u m ∧ b.Edge m w

theorem edge_lt {i j : Fin n} (h : b.Edge i j) : i < j := h.1

theorem reflTransGen_edge_le {a c : Fin n}
    (h : Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) a c) : a ≤ c := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (le_of_lt (b.edge_lt hstep.1))

/-- A latent path strictly increases the topological index. -/
theorem LatentPath.lt {u w : Fin n} (h : b.LatentPath L u w) : u < w := by
  obtain ⟨m, hpath, hedge⟩ := h
  exact lt_of_le_of_lt (b.reflTransGen_edge_le L hpath) (b.edge_lt hedge)

theorem transGen_latentPath_lt {a c : {v : Fin n // v ∉ L}}
    (h : Relation.TransGen (fun (v w : {v : Fin n // v ∉ L}) => b.LatentPath L v w) a c) :
    (a : Fin n) < c := by
  induction h with
  | single h => exact LatentPath.lt b L h
  | tail _ h ih => exact lt_trans ih (LatentPath.lt b L h)

/-- The latent projection onto the observed nodes `{v // v ∉ L}`:
directed edges for latent paths, bidirected edges for latent common
causes (Evans APTS Def 15.1). -/
def latentProjection : ADMG {v : Fin n // v ∉ L} where
  dir v w := b.LatentPath L v w
  bidir :=
    { Adj := fun v w => v ≠ w ∧ ∃ t ∈ L, b.LatentPath L t v ∧ b.LatentPath L t w
      symm := by
        refine ⟨?_⟩
        intro a b h
        exact ⟨h.1.symm, h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.2,
          h.2.choose_spec.2.1⟩
      loopless := by
        refine ⟨?_⟩
        intro a h
        exact h.1 rfl }
  acyclic v hv := by
    exact lt_irrefl _ (transGen_latentPath_lt b L hv)

/-- The directed part of the projection is irreflexive. -/
theorem latentProjection_dir_irrefl (v : {v : Fin n // v ∉ L}) :
    ¬ (b.latentProjection L).dir v v := by
  intro h
  exact lt_irrefl _ (LatentPath.lt b L h)

theorem reflTransGen_r_edges {x m : Fin n}
    (hseg : Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) x m) :
    Relation.ReflTransGen b.Edge x m := by
  induction hseg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih hstep.1

theorem latentPath_edges {x y : Fin n} (h : b.LatentPath L x y) :
    Relation.ReflTransGen b.Edge x y := by
  obtain ⟨m, hseg, hedge⟩ := h
  exact Relation.ReflTransGen.tail (b.reflTransGen_r_edges L hseg) hedge

theorem reflTransGen_edge_decomp {x y : Fin n}
    (h : Relation.ReflTransGen b.Edge x y) :
    ∀ (o p : {v : Fin n // v ∉ L}),
    Relation.ReflTransGen (b.latentProjection L).dir o p →
    Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) (p : Fin n) x →
    (∀ hx : x ∉ L, p = ⟨x, hx⟩) →
    ∃ q : {v : Fin n // v ∉ L},
      Relation.ReflTransGen (b.latentProjection L).dir o q ∧
      Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) (q : Fin n) y ∧
      ∀ hy : y ∉ L, q = ⟨y, hy⟩ := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · intro o p hdir hseg hcon
    exact ⟨p, hdir, hseg, hcon⟩
  · intro a c hstep hrest ih o p hdir hseg hcon
    by_cases hc : c ∈ L
    · exact ih o p hdir (Relation.ReflTransGen.tail hseg ⟨hstep, hc⟩)
        (fun hx => False.elim (hx hc))
    · exact ih o ⟨c, hc⟩ (Relation.ReflTransGen.tail hdir ⟨a, hseg, hstep⟩)
        Relation.ReflTransGen.refl (fun _ => rfl)

/-- Ancestral relations agree between the network and its projection. -/
theorem isDescendant_iff_reflTransGen_latentProjection
    (v w : {v : Fin n // v ∉ L}) :
    b.IsDescendant v w ↔
      Relation.ReflTransGen (b.latentProjection L).dir v w := by
  constructor
  · intro h
    obtain ⟨q, hdir, _, hcon⟩ := b.reflTransGen_edge_decomp L h v v
      Relation.ReflTransGen.refl Relation.ReflTransGen.refl (fun _ => rfl)
    have hqw : q = w := hcon w.2
    rw [hqw] at hdir
    exact hdir
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h2 ih =>
      exact Relation.ReflTransGen.trans ih (b.latentPath_edges L h2)

end BayesNet

end Cslib.MachineLearning.GraphicalModels
