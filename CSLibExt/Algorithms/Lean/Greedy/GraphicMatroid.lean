/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The graphic matroid, and Kruskal's algorithm as matroid greedy

CLRS, third edition, Section 16.4: for an undirected graph `G`, the forests of `G` (edge sets
without cycles) are the independent sets of a matroid, the graphic matroid `M_G` (Theorem 16.5),
and the greedy algorithm on `M_G` is Kruskal's algorithm.

* `ncard_edgeSet_add_card_connectedComponent`: a forest on `V` with `e` edges has
  `|V| - e` connected components. The proof deletes edges one at a time: in a forest every edge is
  a bridge, and deleting a bridge adds exactly one component
  (`card_connectedComponent_deleteEdges_of_not_reachable`).
* `exists_insert_isAcyclic`: the augmentation property. If two forests have `|I| < |J|`, some
  edge of `J` extends `I` to a forest: otherwise every edge of `J` joins vertices already
  connected by `I`, so `J` has at least as many components as `I`, hence at most as many edges.
* `graphicMatroid G`: Mathlib's `Matroid` on `Sym2 V` with ground set `G.edgeSet` and the forests
  of `G` as independent sets.
* `forestOracle G`: an executable independence test (every chosen edge is a bridge of the chosen
  set), with `forestOracle_iff`.
* `kruskal_optimal`, `kruskal_isBase`: `matroidGreedy (forestOracle G)` on the edges in
  nonincreasing weight order returns a maximum-weight forest, and a maximal one (a spanning forest)
  when the order lists every edge of `G`.

## Cost model

As in `MatroidGreedy`: one unit per edge scanned (one oracle query). The oracle's own cost is not
modeled; `forestOracle` decides reachability with Mathlib's instance, which is exponential, so it
is a specification-level oracle for small tests, not union-find.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.GraphicMatroid

open SimpleGraph

variable {V : Type*}

/-! ## Deleting a bridge adds one component -/

section Bridge

variable {H : SimpleGraph V} {a b : V}

/-- A walk in `H` either avoids the edge `a – b` or can be rerouted through its endpoints. -/
private theorem reachable_split (x : V) {y : V} (h : H.Reachable x y) :
    (H.deleteEdges {s(a, b)}).Reachable x y ∨
      ((H.deleteEdges {s(a, b)}).Reachable x a ∧ (H.deleteEdges {s(a, b)}).Reachable b y) ∨
      ((H.deleteEdges {s(a, b)}).Reachable x b ∧ (H.deleteEdges {s(a, b)}).Reachable a y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl SimpleGraph.Reachable.rfl
  | @tail y z _ hyz ih =>
      by_cases he : s(y, z) = s(a, b)
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h | ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inr (Or.inl ⟨h, SimpleGraph.Reachable.rfl⟩)
          · exact Or.inr (Or.inl ⟨h, SimpleGraph.Reachable.rfl⟩)
          · exact Or.inl h
        · rcases ih with h | ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inr (Or.inr ⟨h, SimpleGraph.Reachable.rfl⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h, SimpleGraph.Reachable.rfl⟩)
      · have hstep : (H.deleteEdges {s(a, b)}).Reachable y z :=
          SimpleGraph.Adj.reachable (by
            rw [SimpleGraph.deleteEdges_adj]; exact ⟨hyz, by simpa using he⟩)
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans hstep)
        · exact Or.inr (Or.inl ⟨h1, h2.trans hstep⟩)
        · exact Or.inr (Or.inr ⟨h1, h2.trans hstep⟩)

/-- Deleting an edge `a – b` whose endpoints become disconnected adds exactly one component. -/
theorem card_connectedComponent_deleteEdges_of_not_reachable [Finite V] (hab : H.Adj a b)
    (hbr : ¬ (H.deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card (H.deleteEdges {s(a, b)}).ConnectedComponent =
      Nat.card H.ConnectedComponent + 1 := by
  classical
  have := Fintype.ofFinite V
  set H' := H.deleteEdges {s(a, b)} with hH'
  have hle : H' ≤ H := SimpleGraph.deleteEdges_le _
  -- the component of `b` maps to `none`, every other component to its image in `H`
  let f : H'.ConnectedComponent → Option H.ConnectedComponent := fun c =>
    if c = H'.connectedComponentMk b then none else some (c.map (SimpleGraph.Hom.ofLE hle))
  have hf : Function.Bijective f := by
    constructor
    · intro c₁ c₂ h
      induction c₁ using SimpleGraph.ConnectedComponent.ind with
      | h x₁ =>
      induction c₂ using SimpleGraph.ConnectedComponent.ind with
      | h x₂ =>
      by_cases h₁ : H'.connectedComponentMk x₁ = H'.connectedComponentMk b <;>
        by_cases h₂ : H'.connectedComponentMk x₂ = H'.connectedComponentMk b
      · rw [h₁, h₂]
      · simp [f, h₁, h₂] at h
      · simp [f, h₁, h₂] at h
      · simp only [f, h₁, h₂, ite_false, Option.some.injEq,
          SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.eq] at h
        rw [SimpleGraph.ConnectedComponent.eq] at h₁ h₂ ⊢
        rcases reachable_split x₁ h with h | ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h.symm h₂
        · exact absurd h h₁
    · intro o
      cases o with
      | none => exact ⟨H'.connectedComponentMk b, by simp [f]⟩
      | some c =>
          induction c using SimpleGraph.ConnectedComponent.ind with
          | h x =>
          by_cases hx : H'.connectedComponentMk x = H'.connectedComponentMk b
          · refine ⟨H'.connectedComponentMk a, ?_⟩
            have ha : H'.connectedComponentMk a ≠ H'.connectedComponentMk b := by
              rw [Ne, SimpleGraph.ConnectedComponent.eq]; exact hbr
            simp only [f, ha, ite_false, SimpleGraph.ConnectedComponent.map_mk, Option.some.injEq,
              SimpleGraph.ConnectedComponent.eq]
            rw [SimpleGraph.ConnectedComponent.eq] at hx
            exact hab.reachable.trans ((hx.mono hle).symm)
          · exact ⟨H'.connectedComponentMk x, by simp [f, hx]⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_option,
    Nat.card_eq_fintype_card]

end Bridge

/-! ## Forests: edges plus components equal vertices -/

/-- A forest on `V` with `e` edges has `|V| - e` connected components. -/
theorem ncard_edgeSet_add_card_connectedComponent [Finite V] :
    ∀ (n : ℕ) (F : SimpleGraph V), F.IsAcyclic → F.edgeSet.ncard = n →
      F.edgeSet.ncard + Nat.card F.ConnectedComponent = Nat.card V
  | 0, F, _, hn => by
      have hF : F = ⊥ := SimpleGraph.edgeSet_eq_empty.1
        ((Set.ncard_eq_zero (Set.toFinite _)).1 hn)
      subst hF
      rw [hn, zero_add]
      refine (Nat.card_eq_of_bijective (⊥ : SimpleGraph V).connectedComponentMk
        ⟨fun u v h => ?_, fun c => ?_⟩).symm
      · rwa [SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_bot] at h
      · induction c using SimpleGraph.ConnectedComponent.ind with
        | h v => exact ⟨v, rfl⟩
  | n + 1, F, hF, hn => by
      obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega : F.edgeSet.ncard ≠ 0)
      induction e using Sym2.ind with
      | h a b =>
      have hab : F.Adj a b := he
      have hbr : ¬ (F.deleteEdges {s(a, b)}).Reachable a b :=
        SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_isBridge.1 hF he)
      have hF' : (F.deleteEdges {s(a, b)}).IsAcyclic := hF.anti (SimpleGraph.deleteEdges_le _)
      have hcard : (F.deleteEdges {s(a, b)}).edgeSet.ncard = n := by
        rw [SimpleGraph.edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem he]; omega
      have ih := ncard_edgeSet_add_card_connectedComponent n _ hF' hcard
      rw [card_connectedComponent_deleteEdges_of_not_reachable hab hbr, hcard] at ih
      omega

/-! ## Augmentation -/

/-- Edge sets of `G` are loop-free, so `fromEdgeSet` keeps all of them. -/
private theorem edgeSet_fromEdgeSet_of_subset {G : SimpleGraph V} {I : Set (Sym2 V)}
    (hI : I ⊆ G.edgeSet) : (fromEdgeSet I).edgeSet = I := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, and_iff_left_iff_imp]
  intro he hdiag
  exact G.not_isDiag_of_mem_edgeSet (hI he) (Sym2.mem_diagSet.1 hdiag)

/-- The augmentation property of forests: if `|I| < |J|`, some edge of `J` extends `I` to a
forest. -/
theorem exists_insert_isAcyclic [Finite V] {G : SimpleGraph V} {I J : Set (Sym2 V)}
    (hIG : I ⊆ G.edgeSet) (hJG : J ⊆ G.edgeSet) (hI : (fromEdgeSet I).IsAcyclic)
    (hJ : (fromEdgeSet J).IsAcyclic) (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ (fromEdgeSet (insert e I)).IsAcyclic := by
  by_contra hno
  push Not at hno
  set A := fromEdgeSet I
  set B := fromEdgeSet J
  -- every edge of `J` joins vertices that `I` already connects
  have hadj : ∀ u v, B.Adj u v → A.Reachable u v := by
    intro u v huv
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    by_cases hI' : s(u, v) ∈ I
    · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hI', huv.2⟩)
    · by_contra hnr
      apply hno _ huv.1 hI'
      have heq : fromEdgeSet (insert s(u, v) I) = A ⊔ SimpleGraph.edge u v := by
        ext x y
        simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, A]
        constructor
        · rintro ⟨h | h, hne⟩
          · right; refine ⟨?_, hne⟩; rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · left; exact ⟨rfl, rfl⟩
            · right; exact ⟨rfl, rfl⟩
          · left; exact ⟨h, hne⟩
        · rintro (⟨h, hne⟩ | ⟨h, hne⟩)
          · exact ⟨Or.inr h, hne⟩
          · refine ⟨Or.inl ?_, hne⟩
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Sym2.eq_swap
      rw [heq]
      exact hI.sup_edge_of_not_reachable hnr
  have hBA : ∀ x y, B.Reachable x y → A.Reachable x y := by
    intro x y h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact SimpleGraph.Reachable.rfl
    | tail _ hyz ih => exact ih.trans (hadj _ _ hyz)
  -- `I` and `I ∪ J` have the same components
  have hK : Nat.card (A ⊔ B).ConnectedComponent = Nat.card A.ConnectedComponent := by
    refine (Nat.card_eq_of_bijective
      (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left))
      ⟨fun c₁ c₂ h => ?_, SimpleGraph.ConnectedComponent.surjective_map_ofLE _⟩).symm
    induction c₁ using SimpleGraph.ConnectedComponent.ind with
    | h x =>
    induction c₂ using SimpleGraph.ConnectedComponent.ind with
    | h y =>
    simp only [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.eq] at h
    change (A ⊔ B).Reachable x y at h
    rw [SimpleGraph.ConnectedComponent.eq]
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact SimpleGraph.Reachable.rfl
    | tail _ hyz ih =>
        rcases (SimpleGraph.sup_adj _ _ _ _).1 hyz with h | h
        · exact ih.trans h.reachable
        · exact ih.trans (hadj _ _ h)
  have hKB := SimpleGraph.ConnectedComponent.card_le_card_of_le (le_sup_right : B ≤ A ⊔ B)
  have hA := ncard_edgeSet_add_card_connectedComponent _ A hI rfl
  have hB := ncard_edgeSet_add_card_connectedComponent _ B hJ rfl
  rw [edgeSet_fromEdgeSet_of_subset hIG] at hA
  rw [edgeSet_fromEdgeSet_of_subset hJG] at hB
  omega

/-! ## The graphic matroid -/

/-- `I` is a forest of `G`: a set of edges of `G` without cycles. -/
def IsForestSet (G : SimpleGraph V) (I : Set (Sym2 V)) : Prop :=
  I ⊆ G.edgeSet ∧ (fromEdgeSet I).IsAcyclic

/-- The graphic matroid of `G` (CLRS Theorem 16.5): ground set `G.edgeSet`, independent sets the
forests of `G`. -/
noncomputable def graphicMatroid [Finite V] (G : SimpleGraph V) : Matroid (Sym2 V) :=
  (IndepMatroid.ofFinite (Set.toFinite G.edgeSet) (IsForestSet G)
    ⟨Set.empty_subset _, by simp⟩
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, hJ.2.anti (SimpleGraph.fromEdgeSet_mono hIJ)⟩)
    (fun _ _ hI hJ hlt => by
      obtain ⟨e, heJ, heI, h⟩ := exists_insert_isAcyclic hI.1 hJ.1 hI.2 hJ.2 hlt
      exact ⟨e, heJ, heI, Set.insert_subset (hJ.1 heJ) hI.1, h⟩)
    (fun _ hI => hI.1)).matroid

@[simp] theorem graphicMatroid_indep [Finite V] {G : SimpleGraph V} {I : Set (Sym2 V)} :
    (graphicMatroid G).Indep I ↔ IsForestSet G I := Iff.rfl

@[simp] theorem graphicMatroid_E [Finite V] (G : SimpleGraph V) :
    (graphicMatroid G).E = G.edgeSet := rfl

/-! ## An executable independence oracle -/

variable [Fintype V] [DecidableEq V]

/-- The graph of a finite edge set, with decidable adjacency. -/
def chosen (T : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet ↑T

omit [Fintype V] [DecidableEq V] in
@[simp] theorem chosen_adj (T : Finset (Sym2 V)) (u v : V) :
    (chosen T).Adj u v ↔ s(u, v) ∈ T ∧ u ≠ v := by
  simp [chosen]

instance (T : Finset (Sym2 V)) : DecidableRel (chosen T).Adj := fun u v =>
  decidable_of_iff (s(u, v) ∈ T ∧ u ≠ v) (by simp [chosen])

/-- `e` is a bridge of the edge set `S`: deleting it disconnects its endpoints. -/
def bridgeIn (S : Finset (Sym2 V)) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u v => !decide ((chosen (S.erase e)).Reachable u v), fun u v => by
    simp only [SimpleGraph.reachable_comm]⟩ e

/-- What `bridgeIn` tests. -/
theorem bridgeIn_iff (S : Finset (Sym2 V)) (u v : V) :
    bridgeIn S s(u, v) = true ↔ ¬ (fromEdgeSet ↑(S.erase s(u, v))).Reachable u v := by
  simp [bridgeIn, chosen]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The independence oracle of the graphic matroid: every chosen element is an edge of `G` and a
bridge of the chosen set (a graph is a forest iff every edge is a bridge). -/
def forestOracle (S : Finset (Sym2 V)) : Bool :=
  decide (∀ e ∈ S, e ∈ G.edgeFinset ∧ bridgeIn S e = true)

variable {G}

/-- The oracle decides independence in the graphic matroid. -/
theorem forestOracle_iff (S : Finset (Sym2 V)) :
    forestOracle G S = true ↔ (graphicMatroid G).Indep ↑S := by
  rw [graphicMatroid_indep, IsForestSet]
  simp only [forestOracle, decide_eq_true_eq, SimpleGraph.mem_edgeFinset]
  constructor
  · intro h
    have hsub : (↑S : Set (Sym2 V)) ⊆ G.edgeSet := fun e he => (h e he).1
    refine ⟨hsub, SimpleGraph.isAcyclic_iff_forall_isBridge.2 fun e he => ?_⟩
    rw [edgeSet_fromEdgeSet_of_subset hsub] at he
    have hb := (h e he).2
    induction e using Sym2.ind with
    | h u v =>
    rw [SimpleGraph.isBridge_iff, SimpleGraph.deleteEdges_fromEdgeSet]
    simpa [bridgeIn, chosen, Finset.coe_erase] using hb
  · rintro ⟨hsub, hacyc⟩ e he
    refine ⟨hsub he, ?_⟩
    have hbr := SimpleGraph.isAcyclic_iff_forall_isBridge.1 hacyc
      (by rw [edgeSet_fromEdgeSet_of_subset hsub]; exact he)
    induction e using Sym2.ind with
    | h u v =>
    rw [SimpleGraph.isBridge_iff, SimpleGraph.deleteEdges_fromEdgeSet] at hbr
    simpa [bridgeIn, chosen, Finset.coe_erase] using hbr

/-! ## Kruskal's algorithm as matroid greedy -/

open Cslib.Algorithms.Lean.TimeM

/-- Kruskal's algorithm in the form of CLRS Section 16.4: the matroid greedy algorithm on the
graphic matroid returns a forest of `G`. -/
theorem kruskal_isForest (es : List (Sym2 V)) :
    IsForestSet G ↑(matroidGreedy (forestOracle G) es).ret :=
  graphicMatroid_indep.1 (matroidGreedy_indep (M := graphicMatroid G) forestOracle_iff es).1

/-- With the edges in nonincreasing weight order, no forest of `G` drawn from them weighs more
than the result (CLRS Theorem 16.11 on the graphic matroid). -/
theorem kruskal_optimal (w : Sym2 V → ℕ) {es : List (Sym2 V)}
    (hsorted : es.Pairwise fun a b => w b ≤ w a) {I : Finset (Sym2 V)}
    (hI : IsForestSet G ↑I) (hIes : ∀ x ∈ I, x ∈ es) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedy (forestOracle G) es).ret, w x :=
  matroidGreedy_optimal (M := graphicMatroid G) forestOracle_iff w hsorted
    (graphicMatroid_indep.2 hI) hIes

/-- If the order lists exactly the edges of `G`, the result is a maximal forest of `G` (a base of
the graphic matroid). -/
theorem kruskal_isBase {es : List (Sym2 V)} (hground : ∀ x, x ∈ G.edgeSet ↔ x ∈ es) :
    (graphicMatroid G).IsBase ↑(matroidGreedy (forestOracle G) es).ret :=
  matroidGreedy_isBase (M := graphicMatroid G) forestOracle_iff es
    (fun x => by rw [graphicMatroid_E]; exact hground x)

end Cslib.Algorithms.Lean.GraphicMatroid
