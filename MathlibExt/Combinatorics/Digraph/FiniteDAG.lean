/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Extension.Linear

/-!
# Finite directed graphs and finite DAGs

Acyclicity of a `Digraph` as irreflexivity of the transitive closure of adjacency (no
directed cycle), its equivalence with well-foundedness on a finite vertex type,
topological orders as bijections onto positions in which every edge points forward,
roots and leaves, and directed paths.

## Main results

* `Digraph.isAcyclic_iff_wellFounded`: on a finite vertex type, acyclicity is
  well-foundedness of adjacency.
* `Digraph.IsAcyclic.exists_isTopologicalOrder`: every finite DAG admits a topological
  order.
* `Digraph.isAcyclic_iff_exists_isTopologicalOrder`: a digraph is acyclic iff it has a
  topological order; the directed 3-cycle has none.
* `Digraph.IsAcyclic.roots_nonempty`, `Digraph.IsAcyclic.leaves_nonempty`: a nonempty
  finite DAG has a root and a leaf.
* `Digraph.finite_paths`: a finite digraph has finitely many directed paths, and in a
  DAG every directed walk is a path.

For undirected forests use `SimpleGraph.IsAcyclic`.
-/

@[expose] public section

namespace Digraph

variable {V : Type*} (G : Digraph V)

/-- A digraph is acyclic when no vertex reaches itself by a directed walk of positive length. -/
def IsAcyclic : Prop :=
  ∀ v, ¬ Relation.TransGen G.Adj v v

/-- A topological order of a finite digraph: a bijection onto positions in which every edge
points forward. -/
def IsTopologicalOrder [Fintype V] (σ : V ≃ Fin (Fintype.card V)) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → σ u < σ v

/-- Roots (sources): vertices with no incoming edge. -/
def roots [Fintype V] [DecidableRel G.Adj] : Finset V :=
  {v | ∀ u, ¬ G.Adj u v}

/-- Leaves (sinks): vertices with no outgoing edge. -/
def leaves [Fintype V] [DecidableRel G.Adj] : Finset V :=
  {v | ∀ w, ¬ G.Adj v w}

/-- Directed paths: duplicate-free vertex lists in which consecutive vertices are joined by an
edge (the empty list and single vertices included). -/
def paths : Set (List V) :=
  {p | p.IsChain G.Adj ∧ p.Nodup}

variable {G}

theorem mem_roots [Fintype V] [DecidableRel G.Adj] {v : V} :
    v ∈ G.roots ↔ ∀ u, ¬ G.Adj u v := by
  simp [roots]

theorem mem_leaves [Fintype V] [DecidableRel G.Adj] {v : V} :
    v ∈ G.leaves ↔ ∀ w, ¬ G.Adj v w := by
  simp [leaves]

/-- An acyclic digraph has no loops. -/
theorem IsAcyclic.irrefl (h : G.IsAcyclic) (v : V) : ¬ G.Adj v v :=
  fun hv => h v (Relation.TransGen.single hv)

/-- On a finite vertex type, acyclicity is well-foundedness of adjacency (the form used by
parent relations, where `G.Adj Y X` means `Y` is a parent of `X`). -/
theorem isAcyclic_iff_wellFounded [Finite V] : G.IsAcyclic ↔ WellFounded G.Adj := by
  constructor
  · intro h
    have : IsTrans V (Relation.TransGen G.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    have : Std.Irrefl (Relation.TransGen G.Adj) := ⟨h⟩
    exact Subrelation.wf (fun hab => Relation.TransGen.single hab)
      (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen G.Adj))
  · intro hwf v hv
    exact hwf.transGen.induction (C := fun y => ¬ Relation.TransGen G.Adj y y) v
      (fun y ih hy => ih y hy hy) hv

/-- A digraph with a topological order is acyclic. -/
theorem IsTopologicalOrder.isAcyclic [Fintype V] {σ : V ≃ Fin (Fintype.card V)}
    (hσ : G.IsTopologicalOrder σ) : G.IsAcyclic := by
  have key : ∀ {u v : V}, Relation.TransGen G.Adj u v → σ u < σ v := by
    intro u v huv
    induction huv with
    | single h => exact hσ h
    | tail _ h ih => exact ih.trans (hσ h)
  exact fun v hv => lt_irrefl _ (key hv)

/-- Every finite DAG admits a topological order (a linear extension of its reachability
order). -/
theorem IsAcyclic.exists_isTopologicalOrder [Fintype V] (h : G.IsAcyclic) :
    ∃ σ : V ≃ Fin (Fintype.card V), G.IsTopologicalOrder σ := by
  classical
  let : PartialOrder V :=
    { le := Relation.ReflTransGen G.Adj
      le_refl := fun _ => Relation.ReflTransGen.refl
      le_trans := fun _ _ _ => Relation.ReflTransGen.trans
      le_antisymm := fun a b hab hba => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with hba' | hab'
        · exact hba'.symm
        · exact absurd (Relation.TransGen.trans_left hab' hba) (h a) }
  let : Fintype (LinearExtension V) := inferInstanceAs (Fintype V)
  let e : LinearExtension V ≃o Fin (Fintype.card V) :=
    (Fintype.orderIsoFinOfCardEq (LinearExtension V) rfl).symm
  refine ⟨(Equiv.refl V).trans e.toEquiv, ?_⟩
  intro u v huv
  have hle : toLinearExtension u ≤ toLinearExtension v :=
    toLinearExtension.monotone (Relation.ReflTransGen.single huv)
  have hne : toLinearExtension u ≠ toLinearExtension v := by
    intro huv'
    exact h.irrefl u (by
      have : u = v := huv'
      exact this ▸ huv)
  exact e.strictMono (lt_of_le_of_ne hle hne)

/-- Acyclicity is exactly the existence of a topological order. -/
theorem isAcyclic_iff_exists_isTopologicalOrder [Fintype V] :
    G.IsAcyclic ↔ ∃ σ : V ≃ Fin (Fintype.card V), G.IsTopologicalOrder σ :=
  ⟨IsAcyclic.exists_isTopologicalOrder, fun ⟨_, hσ⟩ => hσ.isAcyclic⟩

/-- A nonempty finite DAG has a root. -/
theorem IsAcyclic.roots_nonempty [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (h : G.IsAcyclic) : G.roots.Nonempty := by
  obtain ⟨σ, hσ⟩ := h.exists_isTopologicalOrder
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  refine ⟨σ.symm ⟨0, hpos⟩, mem_roots.mpr fun u hu => ?_⟩
  have := hσ hu
  rw [Equiv.apply_symm_apply, Fin.lt_def] at this
  simp only at this
  omega

/-- A nonempty finite DAG has a leaf. -/
theorem IsAcyclic.leaves_nonempty [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (h : G.IsAcyclic) : G.leaves.Nonempty := by
  obtain ⟨σ, hσ⟩ := h.exists_isTopologicalOrder
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  refine ⟨σ.symm ⟨Fintype.card V - 1, by omega⟩, mem_leaves.mpr fun w hw => ?_⟩
  have := hσ hw
  rw [Equiv.apply_symm_apply] at this
  have h2 := (σ w).isLt
  rw [Fin.lt_def] at this
  simp only at this
  omega

/-- In a DAG every directed walk (a list whose consecutive vertices are joined by edges) is
duplicate-free, hence a directed path. -/
theorem IsAcyclic.nodup_of_isChain [Finite V] (h : G.IsAcyclic) {p : List V}
    (hp : p.IsChain G.Adj) : p.Nodup := by
  have := Fintype.ofFinite V
  obtain ⟨σ, hσ⟩ := h.exists_isTopologicalOrder
  have hmap : (p.map σ).IsChain (· < ·) :=
    List.isChain_map σ |>.mpr (hp.imp fun _ _ hab => hσ hab)
  have hpw : (p.map σ).Pairwise (· < ·) := List.isChain_iff_pairwise.mp hmap
  exact List.Nodup.of_map σ (hpw.imp ne_of_lt)

/-- A finite digraph has finitely many directed paths. -/
theorem finite_paths [Finite V] : G.paths.Finite := by
  classical
  have := Fintype.ofFinite V
  refine (List.finite_length_le V (Fintype.card V)).subset ?_
  intro p hp
  exact hp.2.length_le_card

/-- In a finite DAG directed walks and directed paths coincide, so there are finitely many
directed walks. -/
theorem IsAcyclic.finite_isChain [Finite V] (h : G.IsAcyclic) :
    {p : List V | p.IsChain G.Adj}.Finite := by
  classical
  have := Fintype.ofFinite V
  refine (finite_paths (G := G)).subset ?_
  intro p hp
  exact ⟨hp, h.nodup_of_isChain hp⟩

/-- The directed 3-cycle `0 → 1 → 2 → 0`. -/
def cycle3 : Digraph (Fin 3) where
  Adj i j := j = i + 1

/-- The directed 3-cycle is not acyclic. -/
theorem not_isAcyclic_cycle3 : ¬ cycle3.IsAcyclic := by
  intro h
  apply h 0
  have h01 : cycle3.Adj 0 1 := show (1 : Fin 3) = 0 + 1 from rfl
  have h12 : cycle3.Adj 1 2 := show (2 : Fin 3) = 1 + 1 from rfl
  have h20 : cycle3.Adj 2 0 := show (0 : Fin 3) = 2 + 1 from rfl
  exact ((Relation.TransGen.single h01).tail h12).tail h20

/-- The directed 3-cycle has no topological order. -/
theorem cycle3_not_isTopologicalOrder (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    ¬ cycle3.IsTopologicalOrder σ :=
  fun hσ => not_isAcyclic_cycle3 hσ.isAcyclic

end Digraph
