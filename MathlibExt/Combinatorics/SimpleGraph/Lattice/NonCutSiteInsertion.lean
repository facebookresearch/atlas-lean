/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected

/-!
# Inserting a non-cut site keeps the complement connected

Removing a vertex `c` from a graph `G` preserves reachability between the other vertices as long
as the neighbours of `c` stay mutually reachable without `c`: a walk through `c` can be rerouted
between the neighbours it uses on either side. Applied to the square lattice with a set `B`
removed, this gives a local criterion, `tnbp_RingConnected c B`, under which the complement of
`insert c B` stays connected. Building a finite set one site at a time, each site satisfying the
criterion with respect to the sites added before it (`tnbp_RingChain`), keeps every remaining
site connected to the exterior of a box containing the set.

This is the local replacement for the global leaf-insertion property `arcns_LeafRemovable`,
which is false (`lrc_leafRemovable_false`).

## Main definitions

* `StatMech.Lattice.tnbp_RingConnected c B`: any two lattice neighbours of `c` that are off `B`
  are connected in the lattice with `insert c B` removed.
* `StatMech.Lattice.tnbp_RingClear c B`: none of the eight sites around `c` (its four
  neighbours and four diagonal neighbours) lies in `insert c B`.
* `StatMech.Lattice.tnbp_RingChain L`: every site of the list `L` satisfies
  `tnbp_RingConnected` with respect to the set of sites after it.

## Main results

* `StatMech.Lattice.tnbp_reachable_of_avoid`: removing a vertex whose neighbours stay mutually
  reachable preserves reachability between the other vertices (any graph).
* `StatMech.Lattice.tnbp_neighbours_connected_of_ringClear`: a clear ring of eight sites around
  `c` makes `c` a non-cut site.
* `StatMech.Lattice.tnbp_reachesExterior_insert_of_ringConnected`: inserting a non-cut site into
  a set satisfying `arcxc_ReachesExterior` preserves the criterion.
* `StatMech.Lattice.tnbp_reachesExterior_ringChain`: a finite set in a box built by a ring chain
  satisfies `arcxc_ReachesExterior`, so its complement is connected.

## Implementation notes

`tnbp_RingClear` never holds when `B` contains a site within king distance one of `c`, so it does
not apply to arcs of two or more sites; for those, `tnbp_RingConnected` has to be checked
directly. In this file `tnbp_RingChain` is established only for single sites
(`tnbp_ringChain_singleton`).
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {V : Type*}

/-- Rerouting a walk around a removed vertex. Let `G'` be `G` with the vertex `c` removed, and
suppose any two neighbours of `c` are connected in `G'`. Then for a walk in `G` from `x` to
`y ≠ c`, any vertex `a ≠ c` that is connected in `G'` to `x` (or adjacent to `c` when `x = c`)
is connected in `G'` to `y`. -/
theorem tnbp_reroute_avoiding (G G' : SimpleGraph V) (c : V)
    (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
    (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q) :
    ∀ {x y : V} (_w : G.Walk x y) (a : V), a ≠ c →
      (x = c → G.Adj a c) → (x ≠ c → G'.Reachable a x) →
      y ≠ c → G'.Reachable a y := by
  classical
  intro x y w
  induction w with
  | nil =>
    intro a _ _ hxn hy
    exact hxn hy
  | @cons x z y' h p ih =>
    intro a ha hxc hxn hy'
    by_cases hxc' : x = c
    · have hcz : G.Adj c z := hxc' ▸ h
      by_cases hzc : z = c
      · exact ih a ha (fun _ => hxc hxc') (fun hzn => absurd hzc hzn) hy'
      · have hreach : G'.Reachable a z := hneigh a z (hxc hxc').symm hcz
        exact ih a ha (fun hh => absurd hh hzc) (fun _ => hreach) hy'
    · have hax : G'.Reachable a x := hxn hxc'
      by_cases hzc : z = c
      · have hxcadj : G.Adj x c := hzc ▸ h
        exact hax.trans (ih x hxc' (fun _ => hxcadj) (fun hh => absurd hzc hh) hy')
      · have hxz : G'.Adj x z := (hG' x z).mpr ⟨h, hxc', hzc⟩
        have haz : G'.Reachable a z := hax.trans hxz.reachable
        exact ih a ha (fun hh => absurd hh hzc) (fun _ => haz) hy'

/-- Removing a non-cut vertex. If `G'` is `G` with the vertex `c` removed and the neighbours of
`c` are pairwise connected in `G'`, then any two vertices other than `c` that are connected in
`G` are connected in `G'`. This is the vertex analogue of Mathlib's
`SimpleGraph.Reachable.reachable_deleteEdges_of_not_isBridge` for edges. -/
theorem tnbp_reachable_of_avoid (G G' : SimpleGraph V) (c : V)
    (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
    (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q)
    {x y : V} (hx : x ≠ c) (hy : y ≠ c) (hr : G.Reachable x y) : G'.Reachable x y := by
  obtain ⟨w⟩ := hr
  exact tnbp_reroute_avoiding G G' c hG' hneigh w x hx (fun hh => absurd hh hx)
    (fun _ => Reachable.refl _) hy

/-- Removing `insert c B` from the lattice is removing `B`, then the site `c`. -/
theorem tnbp_insert_adj_iff (c : Site 2) (B : Set (Site 2)) (a b : Site 2) :
    (ffc_offSupportLattice (insert c B)).Adj a b ↔
      (ffc_offSupportLattice B).Adj a b ∧ a ≠ c ∧ b ≠ c := by
  simp only [ffc_offSupportLattice_adj, Set.mem_insert_iff, not_or]
  tauto

/-- The site `c` is a non-cut site of the lattice with `B` removed: any two neighbours of `c`
off `B` remain connected once `c` is removed too. -/
def tnbp_RingConnected (c : Site 2) (B : Set (Site 2)) : Prop :=
  ∀ p q : Site 2, (ffc_offSupportLattice B).Adj c p → (ffc_offSupportLattice B).Adj c q →
    (ffc_offSupportLattice (insert c B)).Reachable p q

/-- If `c` is a non-cut site for `B`, sites other than `c` connected off `B` stay connected off
`insert c B`. -/
theorem tnbp_reachable_insert_of_ringConnected {c : Site 2} {B : Set (Site 2)}
    (hring : tnbp_RingConnected c B) {x y : Site 2} (hx : x ≠ c) (hy : y ≠ c)
    (hr : (ffc_offSupportLattice B).Reachable x y) :
    (ffc_offSupportLattice (insert c B)).Reachable x y :=
  tnbp_reachable_of_avoid (ffc_offSupportLattice B) (ffc_offSupportLattice (insert c B)) c
    (tnbp_insert_adj_iff c B) hring hx hy hr

theorem tnbp_step_reachable (B' : Set (Site 2)) {a b : Site 2}
    (hadj : (hypercubicLattice 2).Adj a b) (ha : a ∉ B') (hb : b ∉ B') :
    (ffc_offSupportLattice B').Reachable a b :=
  SimpleGraph.Adj.reachable ⟨hadj, ha, hb⟩

/-- The four lattice neighbours of a site `c`. -/
theorem tnbp_neighbour_cases {c p : Site 2} (h : (hypercubicLattice 2).Adj c p) :
    p = ![c 0 + 1, c 1] ∨ p = ![c 0 - 1, c 1] ∨ p = ![c 0, c 1 + 1] ∨ p = ![c 0, c 1 - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  have hp : p = ![p 0, p 1] := by funext i; fin_cases i <;> rfl
  have key : (p 0 = c 0 + 1 ∧ p 1 = c 1) ∨ (p 0 = c 0 - 1 ∧ p 1 = c 1) ∨
             (p 0 = c 0 ∧ p 1 = c 1 + 1) ∨ (p 0 = c 0 ∧ p 1 = c 1 - 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl (by rw [hp, h0, h1])
  · exact Or.inr (Or.inl (by rw [hp, h0, h1]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hp, h0, h1])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hp, h0, h1])))

/-- None of the eight sites around `c` (four neighbours, four diagonal neighbours) lies in
`insert c B`. -/
def tnbp_RingClear (c : Site 2) (B : Set (Site 2)) : Prop :=
  (![c 0 + 1, c 1] : Site 2) ∉ insert c B ∧ (![c 0 - 1, c 1] : Site 2) ∉ insert c B ∧
    (![c 0, c 1 + 1] : Site 2) ∉ insert c B ∧ (![c 0, c 1 - 1] : Site 2) ∉ insert c B ∧
    (![c 0 + 1, c 1 + 1] : Site 2) ∉ insert c B ∧ (![c 0 - 1, c 1 + 1] : Site 2) ∉ insert c B ∧
    (![c 0 + 1, c 1 - 1] : Site 2) ∉ insert c B ∧ (![c 0 - 1, c 1 - 1] : Site 2) ∉ insert c B

/-- With a clear ring around `c`, each neighbour of `c` reaches the east neighbour `(c 0 + 1, c 1)`
along the ring, avoiding `insert c B`. -/
theorem tnbp_neighbours_to_ref {c : Site 2} {B : Set (Site 2)} (h : tnbp_RingClear c B) :
    (ffc_offSupportLattice (insert c B)).Reachable ![c 0 - 1, c 1] ![c 0 + 1, c 1] ∧
      (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 + 1] ![c 0 + 1, c 1] ∧
      (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 - 1] ![c 0 + 1, c 1] := by
  obtain ⟨hE, hW, hN, hS, hNE, hNW, hSE, hSW⟩ := h
  set B' := insert c B
  set cx := c 0; set cy := c 1
  have rE_NE : (ffc_offSupportLattice B').Reachable ![cx + 1, cy] ![cx + 1, cy + 1] :=
    tnbp_step_reachable B' (vadj_step (cx + 1) cy) hE hNE
  have rNE_N : (ffc_offSupportLattice B').Reachable ![cx + 1, cy + 1] ![cx, cy + 1] :=
    tnbp_step_reachable B' (hadj_step cx (cy + 1)).symm hNE hN
  have rN_NW : (ffc_offSupportLattice B').Reachable ![cx, cy + 1] ![cx - 1, cy + 1] := by
    have := hadj_step (cx - 1) (cy + 1); simp only [show cx - 1 + 1 = cx by ring] at this
    exact tnbp_step_reachable B' this.symm hN hNW
  have rNW_W : (ffc_offSupportLattice B').Reachable ![cx - 1, cy + 1] ![cx - 1, cy] :=
    tnbp_step_reachable B' (vadj_step (cx - 1) cy).symm hNW hW
  have rS_SE : (ffc_offSupportLattice B').Reachable ![cx, cy - 1] ![cx + 1, cy - 1] :=
    tnbp_step_reachable B' (hadj_step cx (cy - 1)) hS hSE
  have rSE_E : (ffc_offSupportLattice B').Reachable ![cx + 1, cy - 1] ![cx + 1, cy] := by
    have := vadj_step (cx + 1) (cy - 1); simp only [show cy - 1 + 1 = cy by ring] at this
    exact tnbp_step_reachable B' this hSE hE
  refine ⟨?_, ?_, ?_⟩
  · exact (rNW_W.symm.trans rN_NW.symm).trans (rNE_N.symm.trans rE_NE.symm)
  · exact rNE_N.symm.trans rE_NE.symm
  · exact rS_SE.trans rSE_E

/-- A clear ring around `c` makes `c` a non-cut site for `B`. -/
theorem tnbp_neighbours_connected_of_ringClear {c : Site 2} {B : Set (Site 2)}
    (h : tnbp_RingClear c B) : tnbp_RingConnected c B := by
  obtain ⟨rW, rN, rS⟩ := tnbp_neighbours_to_ref h
  have toRef : ∀ p : Site 2, (hypercubicLattice 2).Adj c p →
      (ffc_offSupportLattice (insert c B)).Reachable p ![c 0 + 1, c 1] := by
    intro p hp
    rcases tnbp_neighbour_cases hp with rfl | rfl | rfl | rfl
    · exact Reachable.refl _
    · exact rW
    · exact rN
    · exact rS
  intro p q hcp hcq
  exact (toRef p hcp.1).trans (toRef q hcq.1).symm

/-- Inserting a non-cut site `c` of the box into a set satisfying the exterior-reachability
criterion preserves the criterion. -/
theorem tnbp_reachesExterior_insert_of_ringConnected {B : Set (Site 2)} {R : ℕ} {c : Site 2}
    (hbase : arcxc_ReachesExterior B R) (hc : c ∈ box 2 R) (hring : tnbp_RingConnected c B) :
    arcxc_ReachesExterior (insert c B) R := by
  obtain ⟨hBsub, hreach⟩ := hbase
  have hsub : insert c B ⊆ box 2 R := Set.insert_subset hc hBsub
  refine ⟨hsub, ?_⟩
  intro x hx
  have hxB : x ∉ B := fun h => hx (Set.mem_insert_of_mem c h)
  have hxc : x ≠ c := fun h => hx (h ▸ Set.mem_insert c B)
  obtain ⟨e, p, hp, heExt⟩ := hreach x hxB
  have heBox : e ∉ box 2 R := by rw [exterior_eq_compl_box] at heExt; exact heExt
  have hec : e ≠ c := fun h => heBox (h.symm ▸ hc)
  have hxe_B : (ffc_offSupportLattice B).Reachable x e :=
    (ffc_reachable_iff_offSupportWalk hxB).mpr ⟨p, hp⟩
  have hxe_ins : (ffc_offSupportLattice (insert c B)).Reachable x e :=
    tnbp_reachable_insert_of_ringConnected hring hxc hec hxe_B
  obtain ⟨p', hp'⟩ := (ffc_reachable_iff_offSupportWalk hx).mp hxe_ins
  exact ⟨e, p', hp', heExt⟩

/-- The empty set satisfies the exterior-reachability criterion. -/
theorem tnbp_empty_reachesExterior (R : ℕ) : arcxc_ReachesExterior (∅ : Set (Site 2)) R := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro x _
  exact arcxc_reachesExterior_of_rowClear (fun t _ => Set.notMem_empty _)

/-- A ring chain: each site of the list is a non-cut site with respect to the set of the sites
after it. Read from the end, the list builds a set one non-cut site at a time. -/
def tnbp_RingChain : List (Site 2) → Prop
  | [] => True
  | c :: L' => tnbp_RingConnected c {x : Site 2 | x ∈ L'} ∧ tnbp_RingChain L'

@[simp] theorem tnbp_ringChain_nil : tnbp_RingChain [] := trivial

theorem tnbp_ringChain_cons {c : Site 2} {L' : List (Site 2)}
    (hhead : tnbp_RingConnected c {x : Site 2 | x ∈ L'}) (htail : tnbp_RingChain L') :
    tnbp_RingChain (c :: L') := ⟨hhead, htail⟩

/-- A finite set of sites of the box `box 2 R` listed as a ring chain satisfies the
exterior-reachability criterion; in particular its complement is connected
(`arcxc_connected_of_reachesExterior`). Ring chains are shown to exist here only for single
sites (`tnbp_ringChain_singleton`). -/
theorem tnbp_reachesExterior_ringChain {R : ℕ} :
    ∀ {L : List (Site 2)}, (∀ c ∈ L, c ∈ box 2 R) → tnbp_RingChain L →
      arcxc_ReachesExterior {x : Site 2 | x ∈ L} R := by
  intro L
  induction L with
  | nil =>
    intro _ _
    have hset : {x : Site 2 | x ∈ ([] : List (Site 2))} = (∅ : Set (Site 2)) := by
      ext z; simp
    rw [hset]; exact tnbp_empty_reachesExterior R
  | cons c L' ih =>
    intro hbox hchain
    obtain ⟨hringHead, htail⟩ := hchain
    have hboxL' : ∀ d ∈ L', d ∈ box 2 R := fun d hd => hbox d (List.mem_cons_of_mem _ hd)
    have hbaseL' : arcxc_ReachesExterior {x : Site 2 | x ∈ L'} R := ih hboxL' htail
    have hset : {x : Site 2 | x ∈ c :: L'} = insert c {x : Site 2 | x ∈ L'} := by
      ext z; simp [List.mem_cons]
    rw [hset]
    exact tnbp_reachesExterior_insert_of_ringConnected hbaseL'
      (hbox c List.mem_cons_self) hringHead

/-- The ring around any site is clear of the empty set. -/
theorem tnbp_ringClear_singleton (c : Site 2) : tnbp_RingClear c (∅ : Set (Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [Set.mem_insert_iff]
      refine fun hmem => ?_
      rcases hmem with h | h
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
        omega
      · exact Set.notMem_empty _ h

/-- A single site is a ring chain. -/
theorem tnbp_ringChain_singleton (c : Site 2) : tnbp_RingChain [c] :=
  tnbp_ringChain_cons
    (by
      have := tnbp_neighbours_connected_of_ringClear (tnbp_ringClear_singleton c)
      simpa using this)
    tnbp_ringChain_nil

/-- Inserting a site with a clear ring preserves the exterior-reachability criterion. -/
theorem tnbp_reachesExterior_insert_of_ringClear {B : Set (Site 2)} {R : ℕ} {c : Site 2}
    (hbase : arcxc_ReachesExterior B R) (hc : c ∈ box 2 R) (hclear : tnbp_RingClear c B) :
    arcxc_ReachesExterior (insert c B) R :=
  tnbp_reachesExterior_insert_of_ringConnected hbase hc
    (tnbp_neighbours_connected_of_ringClear hclear)

end Lattice

end StatMech
