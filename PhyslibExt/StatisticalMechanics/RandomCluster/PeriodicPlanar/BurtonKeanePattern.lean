/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTail
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreePendantTree
public import MathlibExt.Combinatorics.SimpleGraph.TreeExteriorAmalgam

/-!
# Building a trifurcation from three infinite clusters

Three distinct infinite clusters can be turned into a trifurcation by resetting the edges near a
finite connected set.

## i. Overview

Given three vertices in distinct infinite clusters, join them by a finite connected vertex set `K`.
Each cluster leaves `K` along an infinite tail outside `K`. Inside the finite graph formed by `K`
and the three exit points, a tree with three pendant leaves has a hub of degree three. Opening
exactly the tree edges among the edges touching `K` and keeping the configuration outside `K`
makes the hub a trifurcation: deleting it leaves three disjoint infinite open clusters. This is the
local modification step of the Burton–Keane argument. Both key results are proved unconditionally.

## ii. Key results

- `PeriodicGraph.three_clusters_core_pattern_trifurcation` : for a connected finite set `K`
  meeting three distinct infinite clusters, some pattern on the edges touching `K` creates a
  trifurcation.
- `PeriodicGraph.three_clusters_pattern_trifurcation` : on a connected periodic graph, three
  distinct infinite clusters yield a finite edge set and a pattern on it creating a trifurcation.

## iii. Table of contents

- A. Edges touching a finite set and programmed patterns
- B. The trifurcation pattern

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open MeasureTheory Set SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type} [Countable V] [DecidableEq V]

/-! ## A. Edges touching a finite set and programmed patterns -/

/-- The finite set of graph edges with at least one endpoint in `K`. -/
noncomputable def PeriodicGraph.incidentEdgeFinset
    (P : PeriodicGraph V) (K : Finset V) : Finset (Sym2 V) := by
  letI : P.graph.LocallyFinite := P.locallyFinite
  exact K.biUnion fun x => (P.graph.neighborFinset x).image fun y => s(x, y)

lemma PeriodicGraph.mem_incidentEdgeFinset_mk
    (P : PeriodicGraph V) (K : Finset V) (x y : V) :
    s(x, y) ∈ P.incidentEdgeFinset K ↔
      P.graph.Adj x y ∧ (x ∈ K ∨ y ∈ K) := by
  classical
  let : P.graph.LocallyFinite := P.locallyFinite
  simp only [PeriodicGraph.incidentEdgeFinset, Finset.mem_biUnion,
    Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hzK, w, hzw, heq⟩
    simp only [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hzw, Or.inl hzK⟩
    · exact ⟨hzw.symm, Or.inr hzK⟩
  · rintro ⟨hxy, hxK | hyK⟩
    · exact ⟨x, hxK, y, hxy, rfl⟩
    · exact ⟨y, hyK, x, hxy.symm, by simp⟩

/-- The image in `V` of the edges of a finite graph `T` under the vertex map `f`. -/
noncomputable def programmedPeriodicTreeEdges {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (f : W → V) :
    Finset (Sym2 V) := T.edgeFinset.image (Sym2.map f)

/-- The pattern on the edge set `I` that opens exactly the edges lying in `O`. -/
noncomputable def programmedPeriodicTreePattern (I O : Finset (Sym2 V)) :
    ConfigSpace ↥I := fun e => decide (e.1 ∈ O)

/-- The open edges of `omega` with both endpoints outside `K`. -/
def PeriodicGraph.exteriorOpenGraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (K : Finset V) : SimpleGraph V where
  Adj x y := (P.openSubgraph omega).Adj x y ∧ x ∉ K ∧ y ∉ K
  symm := ⟨by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => (P.openSubgraph omega).irrefl h.1⟩

lemma PeriodicGraph.exteriorOpenGraph_le (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (K : Finset V) :
    P.exteriorOpenGraph omega K ≤ P.openSubgraph omega := fun _ _ h => h.1

/-! ## B. The trifurcation pattern -/

/-- If a connected finite set `K` meets three distinct infinite clusters, some pattern on the
edges touching `K` makes a vertex of `K` a trifurcation. -/
theorem PeriodicGraph.three_clusters_core_pattern_trifurcation
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (K : Finset V) (hKconn : (P.graph.induce (K : Set V)).Connected)
    (x : Fin 3 → V) (hxK : ∀ i, x i ∈ K)
    (hinf : ∀ i, (P.cluster omega (x i)).Infinite)
    (hclusters : ∀ i j, i ≠ j →
      P.cluster omega (x i) ≠ P.cluster omega (x j)) :
    ∃ (eta : ConfigSpace ↥(P.incidentEdgeFinset K)) (hub : V),
      P.IsTrifurcation (setPattern (P.incidentEdgeFinset K) eta omega) hub := by
  classical
  let D : (i : Fin 3) → P.InfiniteTailData omega K (x i) := fun i =>
    P.infiniteTailData omega (x i) (hinf i) K (hxK i)
  let inside : Fin 3 → V := fun i => (D i).inside
  let outside : Fin 3 → V := fun i => (D i).outside
  have hinside : ∀ i, inside i ∈ K := fun i => (D i).inside_mem
  have hout : ∀ i, outside i ∉ K := fun i => (D i).outside_not_mem
  have houtinj : Function.Injective outside := by
    intro i j hij
    by_contra hne
    have hi : outside i ∈ P.cluster omega (x i) :=
      (D i).tail_subset_cluster (D i).outside_mem_tail
    have hj : outside j ∈ P.cluster omega (x j) :=
      (D j).tail_subset_cluster (D j).outside_mem_tail
    rw [hij] at hi
    exact hclusters i j hne
      ((P.cluster_eq_of_reachable omega hi).trans
        (P.cluster_eq_of_reachable omega hj).symm)
  let W := Sum (↥K) (Fin 3)
  let core : ↥K → W := Sum.inl
  let terminal : Fin 3 → W := Sum.inr
  let H : SimpleGraph W := {
    Adj := fun a b => match a, b with
      | Sum.inl q, Sum.inl r => P.graph.Adj q.1 r.1
      | Sum.inl q, Sum.inr i => q.1 = inside i
      | Sum.inr i, Sum.inl q => q.1 = inside i
      | Sum.inr _, Sum.inr _ => False
    symm := by
      constructor
      rintro (a | i) (b | j) h
      · exact h.symm
      · exact h
      · exact h
      · exact h
    loopless := by
      constructor
      intro a
      rcases a with a | i
      · exact P.graph.irrefl
      · simp
  }
  let embedW : W → V := fun q => match q with
    | Sum.inl z => z.1
    | Sum.inr i => outside i
  have hembedW : Function.Injective embedW := by
    intro a b hab
    rcases a with a | i <;> rcases b with b | j
    · exact congrArg Sum.inl (Subtype.ext hab)
    · change a.1 = outside j at hab
      exact False.elim ((hout j) (hab ▸ a.2))
    · change outside i = b.1 at hab
      exact False.elim ((hout i) (hab ▸ b.2))
    · exact congrArg Sum.inr (houtinj hab)
  have hHle : ∀ {a b}, H.Adj a b → P.graph.Adj (embedW a) (embedW b) := by
    intro a b hab
    rcases a with a | i <;> rcases b with b | j
    · exact hab
    · change a.1 = inside j at hab
      simpa [embedW, hab] using (D j).exit_open.1
    · change b.1 = inside i at hab
      simpa [embedW, hab] using (D i).exit_open.1.symm
    · exact False.elim hab
  have hHconn : H.Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨core ⟨x 0, hxK 0⟩⟩⟩
    intro a b
    have hcoreReach : ∀ q r : ↥K, H.Reachable (core q) (core r) := by
      intro q r
      let f : P.graph.induce (K : Set V) →g H := {
        toFun := core
        map_rel' := by intro u v huv; exact huv }
      exact (hKconn.preconnected q r).map f
    have hroot : ∀ q : W, H.Reachable (core ⟨x 0, hxK 0⟩) q := by
      intro q
      rcases q with q | i
      · exact hcoreReach _ q
      · exact (hcoreReach _ ⟨inside i, hinside i⟩).trans
          (show H.Adj (core ⟨inside i, hinside i⟩) (terminal i) from rfl).reachable
    exact (hroot a).symm.trans (hroot b)
  have htermdeg : ∀ i, H.degree (terminal i) = 1 := by
    intro i
    rw [degree_eq_one_iff_existsUnique_adj]
    refine ⟨core ⟨inside i, hinside i⟩, rfl, ?_⟩
    intro q hq
    rcases q with q | j
    · exact congrArg core (Subtype.ext hq)
    · exact False.elim hq
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hTH, hstemInj,
      hstemAdj, hleafInj, hleafTerminal, hstemLeaf, _hTreach, hTcut⟩ :=
    StatMech.Percolation.three_pendant_vertices_have_tripod H hHconn terminal
      (by intro i j h; exact Sum.inr.inj h) htermdeg
  let : DecidableRel T.Adj := hTdec
  let embed : C → V := fun z => embedW z.1
  have hembed : Function.Injective embed := hembedW.comp Subtype.val_injective
  choose sigma hsigma using hleafTerminal
  have hsigmaInj : Function.Injective sigma := by
    intro i j hij
    apply hleafInj
    apply Subtype.ext
    rw [hsigma i, hsigma j, hij]
  have hsigmaSurj : Function.Surjective sigma :=
    Finite.injective_iff_surjective.mp hsigmaInj
  let I := P.incidentEdgeFinset K
  let O := programmedPeriodicTreeEdges T embed
  let eta := programmedPeriodicTreePattern I O
  let omega' := setPattern I eta omega
  let E := P.exteriorOpenGraph omega K
  let U := P.openSubgraph omega'
  have htreeTouch : ∀ {a b : C}, T.Adj a b → s(embed a, embed b) ∈ I := by
    intro a b hab
    rw [P.mem_incidentEdgeFinset_mk]
    refine ⟨hHle (hTH a b hab), ?_⟩
    rcases ha : a.1 with qa | ia
    · exact Or.inl (by simp [embed, embedW, ha])
    · rcases hb : b.1 with qb | ib
      · exact Or.inr (by simp [embed, embedW, hb])
      · have hfalse := hTH a b hab
        exact False.elim (by simp [H, ha, hb] at hfalse)
  have htreeOpen : ∀ {a b : C}, T.Adj a b → U.Adj (embed a) (embed b) := by
    intro a b hab
    rw [P.openSubgraph_adj]
    refine ⟨hHle (hTH a b hab), ?_⟩
    change (setPattern I eta omega) s(embed a, embed b) = true
    rw [setPattern_of_mem eta (htreeTouch hab)]
    simp only [eta, programmedPeriodicTreePattern, decide_eq_true_eq]
    unfold O programmedPeriodicTreeEdges
    rw [Finset.mem_image]
    exact ⟨s(a, b), by simpa using hab, by simp⟩
  have hE_le_U : E ≤ U := by
    intro a b hab
    rw [P.openSubgraph_adj]
    refine ⟨hab.1.1, ?_⟩
    have hnotI : s(a, b) ∉ I := by
      rw [P.mem_incidentEdgeFinset_mk]
      simp only [not_and, not_or]
      intro _
      exact ⟨hab.2.1, hab.2.2⟩
    change (setPattern I eta omega) s(a, b) = true
    rw [setPattern_of_not_mem eta hnotI]
    exact hab.1.2
  have hEsep : ∀ i j, i ≠ j →
      ¬ E.Reachable (embed (leaf i)) (embed (leaf j)) := by
    intro i j hij hr
    have hr' := hr.mono (P.exteriorOpenGraph_le omega K)
    have hleaf (k : Fin 3) : embed (leaf k) = outside (sigma k) := by
      unfold embed
      rw [hsigma k]
    rw [hleaf i, hleaf j] at hr'
    have hi := (D (sigma i)).tail_subset_cluster (D (sigma i)).outside_mem_tail
    have hj := (D (sigma j)).tail_subset_cluster (D (sigma j)).outside_mem_tail
    exact hclusters (sigma i) (sigma j) (fun h => hij (hsigmaInj h))
      ((P.cluster_eq_of_reachable omega (hi.trans (hr'.trans hj.symm))))
  have hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i := by
    intro z y hzy
    rcases hz : z.1 with q | k
    · have hzembed : embed z = q.1 := by
        unfold embed
        rw [hz]
      exact False.elim (hzy.2.1 (hzembed.symm ▸ q.2))
    · obtain ⟨i, hi⟩ := hsigmaSurj k
      refine ⟨i, Subtype.ext ?_⟩
      rw [hsigma i, hi, hz]
  have hhubCore : ∃ q : ↥K, hub.1 = core q := by
    rcases hh : hub.1 with q | j
    · exact ⟨q, rfl⟩
    · exfalso
      have h0 := hTH hub (stem 0) (hstemAdj 0)
      have h1 := hTH hub (stem 1) (hstemAdj 1)
      rcases hs0 : (stem 0).1 with q0 | j0 <;>
        rcases hs1 : (stem 1).1 with q1 | j1
      · have h0' : q0.1 = inside j := by simpa [H, hh, hs0] using h0
        have h1' : q1.1 = inside j := by simpa [H, hh, hs1] using h1
        exact (by decide : (0 : Fin 3) ≠ 1)
          (hstemInj (Subtype.ext (by
            calc
              (stem 0).1 = Sum.inl q0 := hs0
              _ = Sum.inl q1 := congrArg Sum.inl (Subtype.ext (h0'.trans h1'.symm))
              _ = (stem 1).1 := hs1.symm)))
      · exact False.elim (by simp [H, hh, hs1] at h1)
      · exact False.elim (by simp [H, hh, hs0] at h0)
      · exact False.elim (by simp [H, hh, hs0] at h0)
  obtain ⟨hubCore, hhubCore⟩ := hhubCore
  have hhubK : embed hub ∈ K := by
    unfold embed
    rw [hhubCore]
    exact hubCore.2
  have hUdecomp : ∀ {a b}, U.Adj a b →
      E.Adj a b ∨ ∃ u v, T.Adj u v ∧ embed u = a ∧ embed v = b := by
    intro a b hab
    rw [P.openSubgraph_adj] at hab
    by_cases htouch : a ∈ K ∨ b ∈ K
    · right
      have hI : s(a, b) ∈ I := (P.mem_incidentEdgeFinset_mk K a b).2 ⟨hab.1, htouch⟩
      have hopen := hab.2
      change (setPattern I eta omega) s(a, b) = true at hopen
      rw [setPattern_of_mem eta hI] at hopen
      have hO : s(a, b) ∈ O := by
        simpa only [eta, programmedPeriodicTreePattern, decide_eq_true_eq] using hopen
      unfold O programmedPeriodicTreeEdges at hO
      rw [Finset.mem_image] at hO
      obtain ⟨e, he, heq⟩ := hO
      induction e using Sym2.inductionOn with
      | _ u v =>
          rw [SimpleGraph.mem_edgeFinset] at he
          simp only [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · exact ⟨u, v, he, hu, hv⟩
          · exact ⟨v, u, he.symm, hv, hu⟩
    · left
      push Not at htouch
      have hnotI : s(a, b) ∉ I := by
        rw [P.mem_incidentEdgeFinset_mk]
        exact fun h => h.2.elim htouch.1 htouch.2
      refine ⟨⟨hab.1, ?_⟩, htouch.1, htouch.2⟩
      have hopen := hab.2
      change (setPattern I eta omega) s(a, b) = true at hopen
      rwa [setPattern_of_not_mem eta hnotI] at hopen
  have hUsep := StatMech.Percolation.tree_exterior_amalgam_separated
    T E U embed hembed hub leaf hTcut hEsep hEonly hUdecomp
  have hE_le_Ucut : E ≤ U.deleteIncidenceSet (embed hub) := by
    intro a b hab
    rw [deleteIncidenceSet_adj]
    exact ⟨hE_le_U hab, fun h => hab.2.1 (h ▸ hhubK),
      fun h => hab.2.2 (h ▸ hhubK)⟩
  let treeCutHom : T.deleteIncidenceSet hub →g
      U.deleteIncidenceSet (embed hub) := {
    toFun := embed
    map_rel' := by
      intro a b hab
      rw [deleteIncidenceSet_adj] at hab ⊢
      exact ⟨htreeOpen hab.1, fun h => hab.2.1 (hembed h),
        fun h => hab.2.2 (hembed h)⟩ }
  have hstemLeafCut : ∀ i,
      (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (stem i)) (embed (leaf i)) := fun i =>
    (hstemLeaf i).map treeCutHom
  have htailE : ∀ i, ∀ z ∈ (D (sigma i)).tail,
      E.Reachable (embed (leaf i)) z := by
    intro i z hz
    obtain ⟨ha, hb, hr⟩ := (D (sigma i)).tail_connected_outside
      (outside (sigma i)) (D (sigma i)).outside_mem_tail z hz
    let f : ((P.openSubgraph omega).induce (K : Set V)ᶜ) →g E := {
      toFun := fun q => q.1
      map_rel' := by intro a b hab; exact ⟨hab, a.2, b.2⟩ }
    have hleaf : embed (leaf i) = outside (sigma i) := by
      unfold embed
      rw [hsigma i]
    rw [hleaf]
    exact hr.map f
  have hremove : P.openSubgraph (removeVertex (embed hub) omega') =
      U.deleteIncidenceSet (embed hub) := by
    ext a b
    simp only [deleteIncidenceSet_adj, PeriodicGraph.openSubgraph_adj,
      removeVertex, U]
    by_cases ha : embed hub = a
    · subst a; simp
    by_cases hb : embed hub = b
    · subst b; simp
    have hmem : embed hub ∉ s(a, b) := by
      simpa only [Sym2.mem_iff, not_or] using ⟨ha, hb⟩
    simp [Ne.symm ha, Ne.symm hb, hmem]
  have hstemInf : ∀ i,
      (P.cluster (removeVertex (embed hub) omega') (embed (stem i))).Infinite := by
    intro i
    apply (D (sigma i)).tail_infinite.mono
    intro z hz
    rw [show P.cluster (removeVertex (embed hub) omega') (embed (stem i)) =
      {z | (P.openSubgraph (removeVertex (embed hub) omega')).Reachable
        (embed (stem i)) z} from rfl, Set.mem_ofPred_eq, hremove]
    exact (hstemLeafCut i).trans ((htailE i z hz).mono hE_le_Ucut)
  refine ⟨eta, embed hub, embed (stem 0), embed (stem 1), embed (stem 2),
    htreeOpen (hstemAdj 0), htreeOpen (hstemAdj 1), htreeOpen (hstemAdj 2),
    hstemInf 0, hstemInf 1, hstemInf 2, ?_, ?_, ?_⟩
  · rw [hremove]
    intro hr
    exact hUsep 0 1 (by decide)
      ((hstemLeafCut 0).symm.trans (hr.trans (hstemLeafCut 1)))
  · rw [hremove]
    intro hr
    exact hUsep 0 2 (by decide)
      ((hstemLeafCut 0).symm.trans (hr.trans (hstemLeafCut 2)))
  · rw [hremove]
    intro hr
    exact hUsep 1 2 (by decide)
      ((hstemLeafCut 1).symm.trans (hr.trans (hstemLeafCut 2)))

/-- On a connected periodic graph, three distinct infinite clusters yield a finite edge set and a
pattern on it whose insertion creates a trifurcation. -/
theorem PeriodicGraph.three_clusters_pattern_trifurcation
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (omega : ConfigSpace (Sym2 V)) (x : Fin 3 → V)
    (hinf : ∀ i, (P.cluster omega (x i)).Infinite)
    (hclusters : ∀ i j, i ≠ j →
      P.cluster omega (x i) ≠ P.cluster omega (x j)) :
    ∃ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (hub : V),
      P.IsTrifurcation (setPattern I eta omega) hub := by
  classical
  obtain ⟨w1⟩ := hconn.preconnected (x 0) (x 1)
  obtain ⟨w2⟩ := hconn.preconnected (x 0) (x 2)
  let K : Finset V := w1.support.toFinset ∪ w2.support.toFinset
  have hxK : ∀ i, x i ∈ K := by
    intro i
    fin_cases i
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr w1.start_mem_support)
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr w1.end_mem_support)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr w2.end_mem_support)
  have hKconn : (P.graph.induce (K : Set V)).Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨x 0, hxK 0⟩⟩
    have hroot : ∀ q : ↥K,
        (P.graph.induce (K : Set V)).Reachable ⟨x 0, hxK 0⟩ q := by
      intro q
      have hqK := q.2
      change q.1 ∈ w1.support.toFinset ∪ w2.support.toFinset at hqK
      rw [Finset.mem_union] at hqK
      rcases hqK with hq | hq
      · have hqs : q.1 ∈ w1.support := List.mem_toFinset.mp hq
        let r := w1.takeUntil q.1 hqs
        have hrK : ∀ z ∈ r.support, z ∈ (K : Set V) := by
          intro z hz
          apply Finset.mem_union_left
          exact List.mem_toFinset.mpr (w1.support_takeUntil_subset_support hqs hz)
        exact ⟨r.induce (K : Set V) hrK⟩
      · have hqs : q.1 ∈ w2.support := List.mem_toFinset.mp hq
        let r := w2.takeUntil q.1 hqs
        have hrK : ∀ z ∈ r.support, z ∈ (K : Set V) := by
          intro z hz
          apply Finset.mem_union_right
          exact List.mem_toFinset.mpr (w2.support_takeUntil_subset_support hqs hz)
        exact ⟨r.induce (K : Set V) hrK⟩
    intro a b
    exact (hroot a).symm.trans (hroot b)
  obtain ⟨eta, hub, htrif⟩ :=
    P.three_clusters_core_pattern_trifurcation omega K hKconn x hxK hinf hclusters
  exact ⟨P.incidentEdgeFinset K, eta, hub, htrif⟩

end StatMech.FK.PeriodicPlanar
