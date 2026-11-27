/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.BergeLemma
public import Mathlib.Data.Finset.SymmDiff
import MathlibExt.Combinatorics.Matching.ShortAugmentingPath
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain

/-!
# Augmenting after a shortest augmentation

An augmenting walk after augmentation along a shortest augmenting walk has length at least
the original length plus the number of shared edges.

J. E. Hopcroft and R. M. Karp, *An n^{5/2} algorithm for maximum matchings in bipartite graphs*,
SIAM Journal on Computing 2(4) (1973), 225–231, §2, Theorem 2.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.IsAugmentingWalk

open SimpleGraph
open scoped symmDiff

private lemma card_symmDiff_add_twice_card_inter {α : Type*} [DecidableEq α]
    (s t : Finset α) : (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at ht
  have hdis : Disjoint (s \ t) (t \ s) := Finset.disjoint_left.mpr (by
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1)
  have hcard : (s ∆ t).card = (s \ t).card + (t \ s).card :=
    Finset.card_union_of_disjoint hdis
  omega

private lemma short_walk_in_difference {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (M N : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hN : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hcard : N.card = M.card + 2) :
    ∃ (u v : V) (r : G.Walk u v), IsAugmentingWalk M r ∧
      r.length ≤ (M \ N).card + 1 := by
  classical
  let := Fintype.ofFinite V
  let A := M \ N
  let B := N \ M
  let K := fromEdgeSet ((A ∪ B : Finset _) : Set (Sym2 V))
  have hG : ∀ e ∈ A ∪ B, e ∈ G.edgeSet := by
    intro e he
    exact (Finset.mem_union.mp he).elim
      (fun h => hMG e (Finset.mem_sdiff.mp h).1)
      (fun h => hNG e (Finset.mem_sdiff.mp h).1)
  have hK : K.edgeSet = ↑(A ∪ B) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (hG e he)⟩⟩
  have hle : K ≤ G := edgeSet_subset_edgeSet.mp (by
    rw [hK]
    exact fun e he => hG e he)
  have hlocal : ∀ e ∈ M, ∀ f ∈ A ∪ B, ∀ x : V, x ∈ e → x ∈ f → e ∈ A := by
    intro e he f hf x hxe hxf
    refine Finset.mem_sdiff.mpr ⟨he, ?_⟩
    intro heN
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨hfM, hfN⟩ := Finset.mem_sdiff.mp hf
      have hef : e = f := by
        by_contra hne
        exact hM e he f hfM hne x hxe hxf
      exact hfN (hef ▸ heN)
    · obtain ⟨hfN, hfM⟩ := Finset.mem_sdiff.mp hf
      have hef : e = f := by
        by_contra hne
        exact hN e heN f hfN hne x hxe hxf
      exact hfM (hef ▸ he)
  have hAcard := Finset.card_sdiff_add_card_inter M N
  have hBcard := Finset.card_sdiff_add_card_inter N M
  rw [Finset.inter_comm N M] at hBcard
  have hgap : B.card - A.card = 2 := by dsimp [A, B]; omega
  obtain ⟨u, v, r, hr, hlen⟩ := exists_isAugmentingWalk_length_le K A B
    (fun e he => hK ▸ Finset.mem_union_left B he)
    (fun e he f hf => hM e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1)
    (fun e he => hK ▸ Finset.mem_union_right A he)
    (fun e he f hf => hN e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1)
    (by dsimp [A, B]; omega)
  have hedges {e : Sym2 V} (he : e ∈ r.edges) : e ∈ A ∪ B := by
    have := r.edges_subset_edgeSet he
    rwa [hK] at this
  have exposed (x : V) (hx : x ∈ r.support) (h : ∀ e ∈ A, x ∉ e) : ∀ e ∈ M, x ∉ e := by
    obtain ⟨f, hf, hxf⟩ :=
      (Walk.mem_support_iff_exists_mem_edges_of_not_nil (Walk.not_nil_of_ne hr.1)).mp hx
    exact fun e he hxe => h e (hlocal e he f (hedges hf) x hxe hxf) hxe
  have mem_iff (e : Sym2 V) (he : e ∈ r.edges) : e ∈ A ↔ e ∈ M :=
    ⟨fun h => (Finset.mem_sdiff.mp h).1,
      fun h => hlocal e h e (hedges he) _ e.out_fst_mem e.out_fst_mem⟩
  refine ⟨u, v, r.mapLe hle, ?_, ?_⟩
  · simp only [IsAugmentingWalk, Walk.support_mapLe_eq_support, Walk.edges_mapLe_eq_edges,
      Walk.length_mapLe]
    refine ⟨hr.1, hr.2.1, exposed u r.start_mem_support hr.2.2.1,
      exposed v r.end_mem_support hr.2.2.2.1, ?_, hr.2.2.2.2.2⟩
    exact hr.2.2.2.2.1.imp_of_mem_imp fun a b ha hb hab => by
      simpa only [mem_iff a ha, mem_iff b hb] using hab
  · rw [Walk.length_mapLe]
    rw [hgap] at hlen
    dsimp [A] at hlen
    omega

/-- **Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2).** Let `M` be a matching
of a finite simple graph `G`, `p` a shortest `M`-augmenting walk, and `q` a walk augmenting for
the matching `M ⊕ E(p)` obtained by augmenting along `p`. Then
`|q| ≥ |p| + |E(p) ∩ E(q)|` (Hopcroft and Karp, SIAM J. Comput. 2 (1973), §2, Theorem 2). -/
theorem length_add_card_inter_le {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {u v : V} (p : G.Walk u v) (hp : IsAugmentingWalk M p)
    (hshort : ∀ (u' v' : V) (p' : G.Walk u' v'), IsAugmentingWalk M p' → p.length ≤ p'.length)
    {u' v' : V} (q : G.Walk u' v') (hq : IsAugmentingWalk (M ∆ p.edges.toFinset) q) :
    p.length + (p.edges.toFinset ∩ q.edges.toFinset).card ≤ q.length := by
  classical
  obtain ⟨h₁G, h₁M, h₁card⟩ := hp.symmDiff_isMatching hMG hM
  obtain ⟨hNG, hN, hNcard⟩ := hq.symmDiff_isMatching h₁G h₁M
  let N := (M ∆ p.edges.toFinset) ∆ q.edges.toFinset
  have hcard : N.card = M.card + 2 := by dsimp [N]; omega
  obtain ⟨a, b, r, hr, hlen⟩ := short_walk_in_difference G M N hMG hM hNG hN hcard
  have hmin := hshort a b r hr
  have hAcard := Finset.card_sdiff_add_card_inter M N
  have hDcard := card_symmDiff_add_twice_card_inter M N
  have hD : M ∆ N = p.edges.toFinset ∆ q.edges.toFinset := by
    simp only [N, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
  rw [hD] at hDcard
  have hPcard : p.edges.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup (Walk.edges_nodup_of_support_nodup hp.2.1),
      Walk.length_edges]
  have hQcard : q.edges.toFinset.card = q.length := by
    rw [List.toFinset_card_of_nodup (Walk.edges_nodup_of_support_nodup hq.2.1),
      Walk.length_edges]
  have hPQcard := card_symmDiff_add_twice_card_inter p.edges.toFinset q.edges.toFinset
  omega

end MetaMathlibExt.IsAugmentingWalk
