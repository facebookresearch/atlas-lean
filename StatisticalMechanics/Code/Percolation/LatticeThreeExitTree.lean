/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Percolation.GridBoxConnected
import Code.Percolation.ThreePendantTree

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d n : ℕ}


abbrev ThreeExitVertex (d n : ℕ) :=
  Sum (↑(boxFinsetBK d n) : Type) (Fin 3)



def threeExitGraph (inside : Fin 3 → Site d) :
    SimpleGraph (ThreeExitVertex d n) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inl y => (hypercubicLattice d).Adj x.1 y.1
    | Sum.inl x, Sum.inr i => x.1 = inside i
    | Sum.inr i, Sum.inl x => x.1 = inside i
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro a b
    cases a <;> cases b <;> simp_all [adj_comm]
  loopless := ⟨by
    rintro (x | i)
    · exact (hypercubicLattice d).irrefl
    · simp⟩

instance (inside : Fin 3 → Site d) : DecidableRel (threeExitGraph (n := n) inside).Adj :=
  fun a b => by cases a <;> cases b <;> simp [threeExitGraph] <;> infer_instance


def threeExitTip (i : Fin 3) : ThreeExitVertex d n := Sum.inr i

theorem threeExitTip_injective :
    Function.Injective (threeExitTip (d := d) (n := n)) := Sum.inr_injective


theorem threeExitTip_degree_one (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) (i : Fin 3) :
    (threeExitGraph (n := n) inside).degree (threeExitTip i) = 1 := by
  classical
  rw [degree_eq_one_iff_existsUnique_adj]
  let q : ↑(boxFinsetBK d n) := ⟨inside i, by simpa [boxFinsetBK] using hinside i⟩
  refine ⟨Sum.inl q, by simp [threeExitGraph, threeExitTip, q], ?_⟩
  intro z hz
  rcases z with z | j
  · simp only [threeExitGraph] at hz
    exact congrArg Sum.inl (Subtype.ext hz)
  · simp [threeExitGraph, threeExitTip] at hz

private theorem boxEdgeWalk_support_mem {x y : Site d}
    (w : (openSubgraph d (forceOpenFinset (boxEdges d n) (fun _ => false))).Walk x y)
    (hx : x ∈ box d n) : ∀ z ∈ w.support, z ∈ box d n := by
  induction w with
  | nil =>
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hx
  | @cons a b c hab w ih =>
      intro z hz
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx
      · have hedge : s(a, b) ∈ boxEdges d n := by
          rw [openSubgraph_adj] at hab
          rcases hab with ⟨_, hopen⟩
          simpa [forceOpenFinset] using hopen
        have hb : b ∈ box d n := (mem_boxEdges_iff.mp hedge).2.1
        exact ih hb z hz


theorem threeExitGraph_core_reachable (inside : Fin 3 → Site d)
    {x y : ↑(boxFinsetBK d n)} :
    (threeExitGraph inside).Reachable (Sum.inl x) (Sum.inl y) := by
  classical
  have hx : x.1 ∈ box d n := by
    simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using x.2
  have hy : y.1 ∈ box d n := by
    simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using y.2
  obtain ⟨w⟩ := box_allOpen_reachable (fun _ => false) hx hy
  have hwbox : ∀ z ∈ w.support, z ∈ box d n :=
    boxEdgeWalk_support_mem w hx
  let wi := w.induce (box d n) hwbox
  let f : (openSubgraph d
      (forceOpenFinset (boxEdges d n) (fun _ => false))).induce (box d n) →g
      threeExitGraph inside := {
    toFun := fun z => Sum.inl ⟨z.1, by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using z.2⟩
    map_rel' := by
      intro a b hab
      exact (openSubgraph_le _ hab)
  }
  exact ⟨wi.map f⟩


theorem threeExitGraph_connected (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) :
    (threeExitGraph (n := n) inside).Connected := by
  classical
  rw [connected_iff]
  refine ⟨?_, ⟨Sum.inr 0⟩⟩
  intro a b
  let core : Fin 3 → ↑(boxFinsetBK d n) := fun i =>
    ⟨inside i, by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using hinside i⟩
  have tip_core : ∀ i, (threeExitGraph inside).Adj (Sum.inr i) (Sum.inl (core i)) := by
    intro i
    simp [threeExitGraph, core]
  have toCore : ∀ z : ThreeExitVertex d n,
      ∃ q : ↑(boxFinsetBK d n), (threeExitGraph inside).Reachable z (Sum.inl q) := by
    rintro (q | i)
    · exact ⟨q, Reachable.refl _⟩
    · exact ⟨core i, (tip_core i).reachable⟩
  obtain ⟨qa, ha⟩ := toCore a
  obtain ⟨qb, hb⟩ := toCore b
  exact ha.trans ((threeExitGraph_core_reachable inside).trans hb.symm)



def threeExitSite (outside : Fin 3 → Site d) : ThreeExitVertex d n → Site d
  | Sum.inl x => x.1
  | Sum.inr i => outside i

theorem threeExitSite_injective (outside : Fin 3 → Site d)
    (hout : ∀ i, outside i ∉ box d n) (houtinj : Function.Injective outside) :
    Function.Injective (threeExitSite (d := d) (n := n) outside) := by
  intro a b h
  rcases a with a | i <;> rcases b with b | j
  · exact congrArg Sum.inl (Subtype.ext h)
  · exfalso
    change a.1 = outside j at h
    exact hout j (h ▸ (by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using a.2))
  · exfalso
    change outside i = b.1 at h
    exact hout i (h.symm ▸ (by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using b.2))
  · exact congrArg Sum.inr (houtinj h)

theorem threeExitGraph_maps_to_lattice (inside outside : Fin 3 → Site d)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i))
    {a b : ThreeExitVertex d n} (hab : (threeExitGraph inside).Adj a b) :
    (hypercubicLattice d).Adj (threeExitSite outside a) (threeExitSite outside b) := by
  rcases a with a | i <;> rcases b with b | j
  · exact hab
  · simpa [threeExitGraph, threeExitSite] using hab ▸ hexit j
  · simpa [threeExitGraph, threeExitSite] using hab ▸ (hexit i).symm
  · simp [threeExitGraph] at hab


theorem lattice_three_exit_tree (inside outside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n)
    (hout : ∀ i, outside i ∉ box d n)
    (houtinj : Function.Injective outside)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i)) :
    ∃ (C : Set (ThreeExitVertex d n)) (T : SimpleGraph C)
      (_ : DecidableRel T.Adj) (hub : C) (stem leaf : Fin 3 → C),
      T.IsTree ∧
      Function.Injective (fun z : C => threeExitSite outside z.1) ∧
      (∀ a b, T.Adj a b → (threeExitGraph inside).Adj a.1 b.1) ∧
      (∀ a b, T.Adj a b →
        (hypercubicLattice d).Adj
          (threeExitSite outside a.1) (threeExitSite outside b.1)) ∧
      Function.Injective stem ∧
      (∀ i, T.Adj hub (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, ∃ j, threeExitSite outside (leaf i).1 = outside j) ∧
      (∀ j, ∃ i, (leaf i).1 = threeExitTip j) ∧
      (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧
      (∀ i, T.Reachable hub (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  classical
  let G := threeExitGraph (n := n) inside
  have hconn : G.Connected := threeExitGraph_connected inside hinside
  have hpdeg : ∀ i, G.degree (threeExitTip i) = 1 :=
    threeExitTip_degree_one inside hinside
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hTG, hsteminj,
      hstemadj, hleafinj, hleafTip, hstemleaf, hreach, hcut⟩ :=
    three_pendant_vertices_have_tripod G hconn threeExitTip
      threeExitTip_injective hpdeg
  choose sigma hsigma using hleafTip
  have hsigma_inj : Function.Injective sigma := by
    intro i j hij
    apply hleafinj
    apply Subtype.ext
    rw [hsigma i, hsigma j, hij]
  have hsigma_surj : Function.Surjective sigma :=
    Finite.injective_iff_surjective.mp hsigma_inj
  have htip_surj : ∀ j, ∃ i, (leaf i).1 = threeExitTip j := by
    intro j
    obtain ⟨i, hi⟩ := hsigma_surj j
    exact ⟨i, by rw [hsigma i, hi]⟩
  refine ⟨C, T, hTdec, hub, stem, leaf, hTree, ?_, hTG, ?_, hsteminj,
    hstemadj, hleafinj, ?_, htip_surj, hstemleaf, hreach, hcut⟩
  · exact (threeExitSite_injective outside hout houtinj).comp Subtype.val_injective
  · intro a b hab
    exact threeExitGraph_maps_to_lattice inside outside hexit (hTG a b hab)
  · intro i
    exact ⟨sigma i, by rw [hsigma i]; rfl⟩

end StatMech.Percolation
