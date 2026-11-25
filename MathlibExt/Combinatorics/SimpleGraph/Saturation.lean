/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- MathlibExt/Combinatorics/SimpleGraph/Saturation.lean
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Minimal

@[expose] public section

/-!
# Graph saturation and the saturation number

Source: Huanying Bian, Qing Cui, Shengjin Ji, and Fuhong Ma,
*On the saturation number of the kite graph*, arXiv:2608.16069v1.

For a fixed graph `H`, a graph `G` is `H`-saturated if `G` does not contain a
copy of `H`, but for any edge `e` not in `E(G)`, the graph `G + e` contains a
copy of `H`. The saturation number `sat(n, H)` is the minimum size of an
`H`-saturated graph on `n` vertices.

Representation: `H`-saturation is maximal `H`-freeness (`Maximal H.Free G`) in
the graph-inclusion order, with the equivalence to the source's missing-edge
formulation proved below. `sat` is the infimum of edge counts over saturated
graphs on `Fin n`; it equals `0` when no saturated graph exists.
-/

namespace SimpleGraph

variable {V W : Type*} (H : SimpleGraph V)

/-- **$H$-saturated graphs.** Let $H$ be a simple graph. A simple graph $G$ is $H$-saturated if $G$
is $H$-free (it contains no copy of $H$ as a subgraph) and is maximal with this property: every
$H$-free simple graph $G'$ on the same vertex set as $G$ with $G \subseteq G'$ equals $G$. -/
def IsSaturated (G : SimpleGraph W) : Prop :=
  Maximal H.Free G

theorem isSaturated_def (G : SimpleGraph W) :
    H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, H.Free G' → G ≤ G' → G' ≤ G :=
  Iff.rfl

/-- **Saturation via strict supergraphs.** Let $H$ be a simple graph. A simple graph $G$ is
$H$-saturated if and only if $G$ is $H$-free and every simple graph $G'$ on the same vertex set
with $G \subsetneq G'$ contains a copy of $H$. -/
theorem isSaturated_iff_forall_gt (G : SimpleGraph W) :
    H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, G < G' → ¬ H.Free G' :=
  maximal_iff_forall_gt

/-- **Saturation via missing edges.** Let $H$ be a simple graph. A simple graph $G$ is
$H$-saturated if and only if $G$ is $H$-free and, for all distinct vertices $s$ and $t$ of $G$
that are not adjacent in $G$, the graph $G + st$ obtained from $G$ by adding the edge $st$
contains a copy of $H$.

This is the usual missing-edge definition of $H$-saturation. -/
theorem isSaturated_iff_missing_edge (G : SimpleGraph W) :
    H.IsSaturated G ↔
      H.Free G ∧ ∀ s t : W, s ≠ t → ¬ G.Adj s t → ¬ H.Free (G ⊔ edge s t) := by
  rw [isSaturated_iff_forall_gt]
  constructor
  · rintro ⟨hfree, hall⟩
    exact ⟨hfree, fun s t hne hmiss => hall (G.lt_sup_edge s t hne hmiss)⟩
  · rintro ⟨hfree, hall⟩
    refine ⟨hfree, fun G' hlt hfree' => ?_⟩
    obtain ⟨hle, hne⟩ := lt_iff_le_not_ge.mp hlt
    rw [le_iff_adj] at hle hne
    push Not at hne
    obtain ⟨s, t, hadj', hadj⟩ := hne
    have hst : s ≠ t := G'.ne_of_adj hadj'
    have hle2 : G ⊔ edge s t ≤ G' := sup_le hle ((edge_le_iff (G := G')).mpr (Or.inr hadj'))
    exact hfree' ((not_free.mp (hall s t hst hadj)).mono_right hle2)

/-- **Saturation of complete graphs.** Let $H$ be a simple graph. The complete graph on any vertex
set is $H$-saturated if and only if it is $H$-free.

A complete graph has no missing edge, so only $H$-freeness matters. The vertex set of the complete
graph is independent of that of $H$, so this condition is not vacuous: $H$ need not embed in a
complete graph with fewer vertices. -/
theorem isSaturated_top : H.IsSaturated (⊤ : SimpleGraph W) ↔ H.Free (⊤ : SimpleGraph W) := by
  constructor
  · exact fun h => h.1
  · intro h
    exact maximal_iff_forall_gt.mpr ⟨h, fun _ hlt => absurd hlt not_top_lt⟩

/-- **Edge counts of saturated graphs.** Let $H$ be a simple graph and $n$ a natural number.
The set of saturated edge counts of $H$ on $n$ vertices is the set of natural numbers $m$ such
that some $H$-saturated simple graph on the vertex set $\{0, 1, \dots, n - 1\}$ has exactly $m$
edges. -/
def satCounts (n : ℕ) : Set ℕ :=
  { m | ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
    G.edgeFinset.card = m }

/-- **Saturation number.** Let $H$ be a simple graph and $n$ a natural number. The saturation
number $\operatorname{sat}(n, H)$ is the minimum number of edges of an $H$-saturated simple graph
on the vertex set $\{0, 1, \dots, n - 1\}$, and is $0$ when no such graph exists. -/
noncomputable def sat (n : ℕ) : ℕ :=
  sInf (H.satCounts n)

/-- **The saturation number is zero when no saturated graph exists.** Let $H$ be a simple graph,
$n$ a natural number, and $\operatorname{sat}(n, H)$ the saturation number of $H$ on $n$
vertices. If the set of saturated edge counts of $H$ on $n$ vertices is empty, that is, no
$H$-saturated simple graph on the vertex set $\{0, 1, \dots, n - 1\}$ exists, then
$\operatorname{sat}(n, H) = 0$. -/
theorem sat_eq_zero_of_counts_empty (n : ℕ) (h : H.satCounts n = ∅) : H.sat n = 0 := by
  change sInf (H.satCounts n) = 0
  rw [h, Nat.sInf_empty]

/-- **Saturated graphs bound the saturation number.** Let $H$ be a simple graph, $n$ a natural
number, and $\operatorname{sat}(n, H)$ the saturation number of $H$ on $n$ vertices. Every
$H$-saturated simple graph on the vertex set $\{0, 1, \dots, n - 1\}$ has at least
$\operatorname{sat}(n, H)$ edges. -/
theorem sat_le_card_of_isSaturated (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : H.IsSaturated G) :
    H.sat n ≤ G.edgeFinset.card := by
  change sInf (H.satCounts n) ≤ _
  refine csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ?_
  change ∃ G' : SimpleGraph (Fin n), ∃ _ : DecidableRel G'.Adj,
    H.IsSaturated G' ∧ G'.edgeFinset.card = G.edgeFinset.card
  exact ⟨G, inferInstance, h, rfl⟩

/-- Attainment: when a saturated graph exists, some saturated graph has exactly
`sat(n, H)` edges. -/
theorem exists_isSaturated_card_eq_sat (n : ℕ) (h : (H.satCounts n).Nonempty) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
      G.edgeFinset.card = H.sat n := by
  obtain ⟨G, hdec, hsat, hcard⟩ := Nat.sInf_mem h
  exact ⟨G, hdec, hsat, hcard⟩

end SimpleGraph
