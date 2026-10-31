/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

/-!
# Tree forest data

A finite tree mapped into the open subgraph, separating the branches of each trifurcation, gives the
spanning-tree leaf count and the trifurcation count.

## i. Overview

`slh_TreeForestData ω n` is a finite tree with an injective map `π` into the open subgraph, a vertex
`ιT x` over each trifurcation, and sections `sec x a` of its branches such that the tree reflects
connectivity after removing `x`. Separated branches then give degree three at `ιT x`, which yields
`flc2_SpanningTreeLeafCount` and `Tcount ≤ |∂B_n|`.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `slh_deg_ge_three_of_cut` : separated branches give degree three
- `slh_spanningTreeLeafCount_of_treeForest` : tree forest data give the spanning-tree certificate
- `slh_Tcount_le_boundary_of_treeForest` : the counting bound

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

-- The instance binder is kept so that existing callers and the statement are unchanged.
set_option linter.unusedDecidableInType false in
lemma slh_cut_neighbor {W : Type*} [DecidableEq W] {G : SimpleGraph W} {x a : W} (hxa : x ≠ a)
    (h : G.Reachable x a) :
    ∃ (c : W) (hc : c ≠ x) (ha : a ≠ x), G.Adj x c ∧
      (G.induce ({x}ᶜ : Set W)).Reachable ⟨c, by simpa using hc⟩ ⟨a, by simpa using ha⟩ := by
  classical
  obtain ⟨p⟩ := h
  set q : G.Walk x a := (p.toPath : G.Walk x a) with hq
  have hqp : q.IsPath := (p.toPath).2
  have hnnil : ¬ q.Nil := Walk.not_nil_of_ne hxa
  set c := q.snd with hc
  have hadj : G.Adj x c := q.adj_snd hnnil
  have hcx : c ≠ x := (G.ne_of_adj hadj).symm
  have hax : a ≠ x := fun h => hxa h.symm
  have hsupp : ∀ y ∈ q.tail.support, y ∈ ({x}ᶜ : Set W) := by
    intro y hy
    have hcons : q.support = x :: q.tail.support := by
      rw [Walk.support_tail_of_not_nil q hnnil, Walk.cons_tail_support]
    have hnd := hqp.support_nodup
    rw [hcons, List.nodup_cons] at hnd
    intro hyx
    simp only [Set.mem_singleton_iff] at hyx
    subst hyx
    exact hnd.1 hy
  have hind := q.tail.induce ({x}ᶜ : Set W) hsupp
  exact ⟨c, hcx, hax, hadj, ⟨hind.copy (by simp [hc]) rfl⟩⟩

-- The instance binder is kept so that existing callers and the statement are unchanged.
set_option linter.unusedDecidableInType false in
lemma slh_deg_ge_three_of_cut {W : Type*} [DecidableEq W] [Fintype W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {x a₁ a₂ a₃ : W}
    (hr₁ : G.Reachable x a₁) (hr₂ : G.Reachable x a₂) (hr₃ : G.Reachable x a₃)
    (hx₁ : x ≠ a₁) (hx₂ : x ≠ a₂) (hx₃ : x ≠ a₃)
    (hcut₁₂ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₂, by simpa using hx₂.symm⟩)
    (hcut₁₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩)
    (hcut₂₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₂, by simpa using hx₂.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩) :
    3 ≤ G.degree x := by
  classical
  obtain ⟨c₁, _, _, hadj₁, hreach₁⟩ := slh_cut_neighbor hx₁ hr₁
  obtain ⟨c₂, _, _, hadj₂, hreach₂⟩ := slh_cut_neighbor hx₂ hr₂
  obtain ⟨c₃, _, _, hadj₃, hreach₃⟩ := slh_cut_neighbor hx₃ hr₃
  have h12 : c₁ ≠ c₂ := by rintro rfl; exact hcut₁₂ (hreach₁.symm.trans hreach₂)
  have h13 : c₁ ≠ c₃ := by rintro rfl; exact hcut₁₃ (hreach₁.symm.trans hreach₃)
  have h23 : c₂ ≠ c₃ := by rintro rfl; exact hcut₂₃ (hreach₂.symm.trans hreach₃)
  have hsub : ({c₁, c₂, c₃} : Finset W) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [G.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hadj₁
    · exact hadj₂
    · exact hadj₃
  have hcard : ({c₁, c₂, c₃} : Finset W).card = 3 :=
    Finset.card_eq_three.mpr ⟨c₁, c₂, c₃, h12, h13, h23, rfl⟩
  calc 3 = ({c₁, c₂, c₃} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
    _ = G.degree x := G.card_neighborFinset_eq_degree x

lemma slh_edge_transfer (x u v : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    (hadj : (openSubgraph d ω).Adj u v) (hux : u ≠ x) (hvx : v ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj u v := by
  obtain ⟨hl, ho⟩ := hadj
  refine ⟨hl, ?_⟩
  rw [removeSite_apply_of_notMem]
  · exact ho
  · intro hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hux rfl
    · exact hvx rfl

lemma slh_walk_avoid_transfer {x u v : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d ω).Walk u v) (hw : x ∉ w.support) :
    (openSubgraph d (removeSite x ω)).Reachable u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    obtain ⟨hax, hw'⟩ := hw
    have hbx : x ≠ b := fun h => by subst h; exact hw' (w.start_mem_support)
    exact (Adj.reachable
      (slh_edge_transfer x a b ω hab (Ne.symm hax) (Ne.symm hbx))).trans (ih hw')

lemma slh_connected_removeSite_of_G_induce {W : Type*} {ω : ConfigSpace (Sym2 (Site d))}
    {G : SimpleGraph W} (π : W → Site d)
    (hπ : ∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v))
    (hπinj : Function.Injective π)
    {p wi wj : W} (hwi : wi ≠ p) (hwj : wj ≠ p)
    (h : (G.induce ({p}ᶜ : Set W)).Reachable ⟨wi, by simpa using hwi⟩ ⟨wj, by simpa using hwj⟩) :
    Connected d (removeSite (π p) ω) (π wi) (π wj) := by
  obtain ⟨w⟩ := h
  set f : (G.induce ({p}ᶜ : Set W)) →g (openSubgraph d ω) :=
    { toFun := fun u => π u.1
      map_rel' := fun {a b} hab => hπ a.1 b.1 hab } with hf
  set w' := w.map f with hw'
  have hsupp : (π p) ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨c, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (hπinj (by simpa [hf] using hcx))
  exact slh_walk_avoid_transfer w' hsupp

open Classical in
/-- Tree forest data for `B_n`: a finite tree mapped injectively into the open subgraph, with a
vertex over each trifurcation, branch sections that reflect connectivity after removing the
trifurcation, and leaves mapped injectively to the boundary. -/
def slh_TreeForestData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
    (π : W → Site d) (ιT : Site d → W) (sec : Site d → Site d → W) (lamL : W → Site d),
    G.IsTree ∧ 2 ≤ Fintype.card W ∧
    (∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v)) ∧
    Function.Injective π ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → π (ιT x) = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ιT x = ιT y → x = y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, Connected d ω x a →
      π (sec x a) = a ∧ sec x a ≠ ιT x ∧ G.Reachable (ιT x) (sec x a)) ∧
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d n) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))

lemma slh_spanningTreeLeafCount_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, sec, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hsec, hlammap, hlaminj⟩ := h
  refine ⟨W, inferInstance, inferInstance, G, inferInstance, ιT, lamL, hTree, hWcard,
    ?_, hιinj, hlammap, hlaminj⟩
  intro x hxbox htri
  have htri' := htri
  obtain ⟨a₁, a₂, a₃, ⟨hne12, hne13, hne23⟩, ⟨hc1, hc2, hc3⟩, _, ⟨hcut12, hcut13, hcut23⟩⟩ := htri'
  set p := ιT x with hp
  have hpx : π p = x := hπιT x hxbox htri
  obtain ⟨hπw1, hw1p, hr1⟩ := hsec x hxbox htri a₁ hc1
  obtain ⟨hπw2, hw2p, hr2⟩ := hsec x hxbox htri a₂ hc2
  obtain ⟨hπw3, hw3p, hr3⟩ := hsec x hxbox htri a₃ hc3
  have hcutG : ∀ (u v : W) (b c : Site d), π u = b → π v = c →
      (hup : u ≠ p) → (hvp : v ≠ p) →
      ¬ Connected d (removeSite x ω) b c →
      ¬ (G.induce ({p}ᶜ : Set W)).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v b c hub hvc hup hvp hcut hreach
    apply hcut
    have := slh_connected_removeSite_of_G_induce π hπ hπinj hup hvp hreach
    rwa [hpx, hub, hvc] at this
  refine slh_deg_ge_three_of_cut hr1 hr2 hr3 hw1p.symm hw2p.symm hw3p.symm
    (hcutG _ _ _ _ hπw1 hπw2 hw1p hw2p hcut12)
    (hcutG _ _ _ _ hπw1 hπw3 hw1p hw3p hcut13)
    (hcutG _ _ _ _ hπw2 hπw3 hw2p hw3p hcut23)

lemma slh_Tcount_le_boundary_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n (slh_spanningTreeLeafCount_of_treeForest ω n h)

open Classical in
lemma slh_treeForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    slh_TreeForestData ω n := by
  classical
  have hzne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun v => if v = 0 then z₀ else z₁), (fun _ => (0 : Fin 2)), (fun _ _ => (0 : Fin 2)),
    (fun v => if v = 0 then z₀ else z₁), Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro u v huv
    have h01 : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
      revert huv; fin_cases u <;> fin_cases v <;> simp_all
    rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hopen
    · simpa using hopen.symm
  · intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · intro u hu v hv huv
    fin_cases u <;> fin_cases v <;> simp_all

end Percolation

end StatMech
