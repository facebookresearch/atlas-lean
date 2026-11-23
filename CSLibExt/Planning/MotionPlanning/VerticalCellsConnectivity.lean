/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.VerticalCells
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

open scoped Topology

/-!
# Incidence graph connectivity for trapezoidal decompositions

The bipartite trap/wall incidence graph of a supplied trapezoidal decomposition
and the pointwise equivalence between graph reachability and path-connectedness
in free space (LaValle, Planning Algorithms, Sec. 6.2.2).
-/

namespace Cslib.Planning.MotionPlanning

namespace VerticalCells


/-!
Incidence graph of a trapezoidal decomposition (LaValle, Planning Algorithms,
Sec. 6.2.2) and the graph-to-path direction: points in reachable cells are
joined by a path in `F`.
-/

/-- Adjacency of the incidence graph: a trapezoid cell is adjacent to a wall cell
exactly when the wall lies on one of the trapezoid's sides; same-kind cells are
never adjacent. LaValle, Planning Algorithms, Sec. 6.2.2. -/
def TrapDecomp.incidenceAdj {F : Set plane} (D : TrapDecomp F) : D.Cell → D.Cell → Prop
  | .inl i, .inr j => (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)
  | .inr j, .inl i => (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)
  | _, _ => False

/-- The bipartite incidence graph on `D.Cell`: trapezoids adjacent to incident
walls. LaValle, Planning Algorithms, Sec. 6.2.2. -/
def TrapDecomp.incidenceGraph {F : Set plane} (D : TrapDecomp F) : SimpleGraph D.Cell where
  Adj := D.incidenceAdj
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> exact h⟩
  loopless := ⟨by
    intro a h
    cases a <;> exact h⟩

theorem TrapDecomp.incidenceGraph_adj_inl_inr {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (j : Fin D.k) :
    D.incidenceGraph.Adj (.inl i) (.inr j) ↔
      (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j) :=
  Iff.rfl

theorem TrapDecomp.incidenceGraph_not_adj_inl_inl {F : Set plane} (D : TrapDecomp F)
    (i i' : Fin D.m) : ¬ D.incidenceGraph.Adj (.inl i) (.inl i') :=
  fun h => h

theorem TrapDecomp.incidenceGraph_not_adj_inr_inr {F : Set plane} (D : TrapDecomp F)
    (j j' : Fin D.k) : ¬ D.incidenceGraph.Adj (.inr j) (.inr j') :=
  fun h => h

/-- Points of a convex set are joined in any larger set, via the segment. -/
private theorem joinedIn_of_convex_subset {s t : Set plane} (hconv : Convex ℝ s)
    (hsub : s ⊆ t) {p q : plane} (hp : p ∈ s) (hq : q ∈ s) : JoinedIn t p q := by
  have hseg : segment ℝ p q ⊆ s := hconv.segment_subset hp hq
  have hconn : IsPathConnected (segment ℝ p q) :=
    (convex_segment p q).isPathConnected ⟨p, left_mem_segment ℝ p q⟩
  exact (hconn.joinedIn p (left_mem_segment ℝ p q) q
    (right_mem_segment ℝ p q)).mono (hseg.trans hsub)

/-- The segment from a point of an open convex set to a point of its closure lies
in the set except possibly at the far endpoint. -/
private theorem segment_subset_union_of_mem_closure {s : Set plane} (hconv : Convex ℝ s)
    (ho : IsOpen s) {x y : plane} (hx : x ∈ s) (hy : y ∈ closure s) :
    segment ℝ x y ⊆ s ∪ {y} := by
  have hinter : interior s = s := ho.interior_eq
  have hx' : x ∈ interior s := by rwa [hinter]
  rw [segment_subset_iff]
  intro a b ha hb hab
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    exact Or.inr (by simp)
  · have ha' : 0 < a := lt_of_le_of_ne ha (fun h => ha0 h.symm)
    have hmem := hconv.combo_interior_closure_mem_interior hx' hy ha' hb hab
    rw [hinter] at hmem
    exact Or.inl hmem

/-- A trapezoid point and a wall point of incident cells are joined in `F`: the
segment to a wall point stays in the trap carrier (open convex, wall in its
closure) except at its endpoint, which lies in the wall carrier. -/
theorem joinedIn_of_trap_wall {F : Set plane} (D : TrapDecomp F)
    {i : Fin D.m} {j : Fin D.k}
    (hadj : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j))
    {p q : plane} (hp : p ∈ (D.trap i).carrier) (hq : q ∈ (D.wall j).carrier) :
    JoinedIn F p q := by
  obtain ⟨r, hr⟩ := (D.wall j).carrier_nonempty
  have hsub_trap : (D.trap i).carrier ⊆ F := D.trap_carrier_subset i
  have hsub_wall : (D.wall j).carrier ⊆ F := D.wall_carrier_subset j
  have hclo : (D.wall j).carrier ⊆ closure (D.trap i).carrier := by
    cases hadj with
    | inl hR => exact D.wall_subset_closure_of_hasOnRight hR
    | inr hL => exact D.wall_subset_closure_of_hasOnLeft hL
  have hseg : segment ℝ p r ⊆ F :=
    (segment_subset_union_of_mem_closure (D.trap i).convex_carrier
      (D.trap i).isOpen_carrier hp (hclo hr)).trans
      (Set.union_subset hsub_trap (Set.singleton_subset_iff.mpr (hsub_wall hr)))
  have hconn : IsPathConnected (segment ℝ p r) :=
    (convex_segment p r).isPathConnected ⟨p, left_mem_segment ℝ p r⟩
  have hpr : JoinedIn F p r :=
    (hconn.joinedIn p (left_mem_segment ℝ p r) r
      (right_mem_segment ℝ p r)).mono hseg
  have hrq : JoinedIn F r q :=
    joinedIn_of_convex_subset (D.wall j).convex_carrier hsub_wall hr hq
  exact hpr.trans hrq

/-- Points in adjacent cells are joined in `F`. Only the openness of the trap
carrier is used; openness of `F` is not needed for this direction. -/
theorem TrapDecomp.joinedIn_of_adj_mem {F : Set plane} (D : TrapDecomp F)
    {c1 c2 : D.Cell} (h : D.incidenceGraph.Adj c1 c2)
    {p q : plane} (hp : p ∈ D.carrier c1) (hq : q ∈ D.carrier c2) : JoinedIn F p q := by
  cases c1 with
  | inl i =>
    cases c2 with
    | inl i' => exact absurd h (D.incidenceGraph_not_adj_inl_inl i i')
    | inr j =>
      exact joinedIn_of_trap_wall D ((D.incidenceGraph_adj_inl_inr i j).mp h) hp hq
  | inr j =>
    cases c2 with
    | inl i =>
      exact (joinedIn_of_trap_wall D
        ((D.incidenceGraph_adj_inl_inr i j).mp h) hq hp).symm
    | inr j' => exact absurd h (D.incidenceGraph_not_adj_inr_inr j j')

/-- Every cell carrier is contained in `F`. -/
theorem TrapDecomp.carrier_subset {F : Set plane} (D : TrapDecomp F) (c : D.Cell) :
    D.carrier c ⊆ F := by
  cases c with
  | inl i => exact D.trap_carrier_subset i
  | inr j => exact D.wall_carrier_subset j

/-- Points in the same cell are joined in `F`, by convexity of the carrier. -/
theorem joinedIn_of_same_cell {F : Set plane} (D : TrapDecomp F)
    {c : D.Cell} {p q : plane} (hp : p ∈ D.carrier c) (hq : q ∈ D.carrier c) :
    JoinedIn F p q := by
  cases c with
  | inl i =>
    exact joinedIn_of_convex_subset (D.trap i).convex_carrier
      (D.trap_carrier_subset i) hp hq
  | inr j =>
    exact joinedIn_of_convex_subset (D.wall j).convex_carrier
      (D.wall_carrier_subset j) hp hq

/-- Points in reachable cells are joined in `F`, by induction on the walk.
Openness of `F` is not needed for this direction. -/
theorem TrapDecomp.joinedIn_of_reachable {F : Set plane} (D : TrapDecomp F)
    {qI qG : plane} {cI cG : D.Cell}
    (hcI : qI ∈ D.carrier cI) (hcG : qG ∈ D.carrier cG)
    (h : D.incidenceGraph.Reachable cI cG) : JoinedIn F qI qG := by
  obtain ⟨w⟩ := h
  induction w generalizing qI qG with
  | nil =>
    exact joinedIn_of_same_cell D hcI hcG
  | cons hadj _ ih =>
    obtain ⟨r, hr⟩ := D.cell_nonempty _
    exact (D.joinedIn_of_adj_mem hadj hcI hr).trans (ih hr hcG)

/-- Union of carriers of cells reachable from `cI` in the incidence graph.
LaValle, Planning Algorithms, Sec. 6.2.2: reachability classes group 2-cells
with their bordering 1-cells. -/
def TrapDecomp.reachUnion {F : Set plane} (D : TrapDecomp F) (cI : D.Cell) : Set plane :=
  {p | ∃ c, D.incidenceGraph.Reachable cI c ∧ p ∈ D.carrier c}

/-- Membership in the reachability union from a reachable cell. -/
theorem TrapDecomp.mem_reachUnion {F : Set plane} (D : TrapDecomp F)
    (cI c : D.Cell) (h : D.incidenceGraph.Reachable cI c)
    {p : plane} (hp : p ∈ D.carrier c) : p ∈ D.reachUnion cI :=
  ⟨c, h, hp⟩

/-- The reachability union is contained in `F`. -/
theorem TrapDecomp.reachUnion_subset {F : Set plane} (D : TrapDecomp F) (cI : D.Cell) :
    D.reachUnion cI ⊆ F := by
  intro p hp
  obtain ⟨c, _, hpc⟩ := hp
  exact D.carrier_subset c hpc

/-- Carrier of a reachable cell lies in the union. -/
theorem TrapDecomp.carrier_subset_reachUnion {F : Set plane} (D : TrapDecomp F)
    (cI c : D.Cell) (h : D.incidenceGraph.Reachable cI c) :
    D.carrier c ⊆ D.reachUnion cI := by
  intro p hp
  exact ⟨c, h, hp⟩

/-- Cells sharing a point of `F` agree, by uniqueness of the cell per point. -/
theorem TrapDecomp.eq_of_mem_carrier {F : Set plane} (D : TrapDecomp F)
    {p : plane} (hpF : p ∈ F) {c₁ c₂ : D.Cell}
    (h₁ : p ∈ D.carrier c₁) (h₂ : p ∈ D.carrier c₂) : c₁ = c₂ :=
  (D.existsUnique_cell p hpF).unique h₁ h₂

/-- Incidence adjacency from a trapezoid to an incident wall.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.adj_inl_inr_of_has {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (j : Fin D.k)
    (hadj : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) :
    D.incidenceGraph.Adj (.inl i) (.inr j) :=
  hadj

/-- Incidence adjacency from a wall to an incident trapezoid.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.adj_inr_inl_of_has {F : Set plane} (D : TrapDecomp F)
    (i : Fin D.m) (j : Fin D.k)
    (hadj : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) :
    D.incidenceGraph.Adj (.inr j) (.inl i) :=
  hadj

/-- An incident trapezoid of a reachable wall is reachable. -/
theorem TrapDecomp.reachable_inl_of_inr {F : Set plane} (D : TrapDecomp F)
    (cI : D.Cell) (i : Fin D.m) (j : Fin D.k)
    (hreach : D.incidenceGraph.Reachable cI (.inr j))
    (hadj : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j)) :
    D.incidenceGraph.Reachable cI (.inl i) :=
  hreach.trans (D.adj_inr_inl_of_has i j hadj).reachable

/-- An incident trapezoid of an unreachable wall is unreachable. -/
theorem TrapDecomp.not_reachable_inl_of_not_reachable_inr {F : Set plane}
    (D : TrapDecomp F) (cI : D.Cell) (i : Fin D.m) (j : Fin D.k)
    (hadj : (D.trap i).HasOnRight (D.wall j) ∨ (D.trap i).HasOnLeft (D.wall j))
    (hnot : ¬ D.incidenceGraph.Reachable cI (.inr j)) :
    ¬ D.incidenceGraph.Reachable cI (.inl i) := by
  intro h
  exact hnot (h.trans (D.adj_inl_inr_of_has i j hadj).reachable)

/-- Carrier of an unreachable cell is disjoint from the union. -/
theorem TrapDecomp.disjoint_carrier_reachUnion_of_not_reachable {F : Set plane}
    (D : TrapDecomp F) (cI c' : D.Cell)
    (hnot : ¬ D.incidenceGraph.Reachable cI c') :
    Disjoint (D.carrier c') (D.reachUnion cI) := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  obtain ⟨c, hreach, hpc⟩ := hp2
  have hpF : p ∈ F := D.carrier_subset c' hp1
  have heq : c = c' := D.eq_of_mem_carrier hpF hpc hp1
  subst heq
  exact hnot hreach

/-- The reachability union is open: trap points use the open carrier, wall points
use the wall neighborhood, whose incident trapezoids are also reachable.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.isOpen_reachUnion {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (cI : D.Cell) : IsOpen (D.reachUnion cI) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨c, hreach, hmem⟩ := hp
  cases c with
  | inl i =>
    have ho : IsOpen (D.trap i).carrier := (D.trap i).isOpen_carrier
    have hmem' : (D.trap i).carrier ∈ 𝓝 p := ho.mem_nhds hmem
    have hsub : (D.trap i).carrier ⊆ D.reachUnion cI :=
      D.carrier_subset_reachUnion cI (.inl i) hreach
    exact Filter.mem_of_superset hmem' hsub
  | inr j =>
    obtain ⟨U, hUmem, hUsub⟩ := D.wall_neighborhood hF j p hmem
    have hsub : U ⊆ D.reachUnion cI := by
      intro q hq
      have hq' := hUsub hq
      simp only [Set.mem_union, Set.mem_iUnion] at hq'
      cases hq' with
      | inl hwall =>
        exact D.mem_reachUnion cI (.inr j) hreach hwall
      | inr hex =>
        obtain ⟨i, hadj, hqi⟩ := hex
        have hreach_i : D.incidenceGraph.Reachable cI (.inl i) :=
          D.reachable_inl_of_inr cI i j hreach hadj
        exact D.mem_reachUnion cI (.inl i) hreach_i hqi
    exact Filter.mem_of_superset hUmem hsub

/-- Points of `F` outside the union have a neighborhood whose trace on `F` stays
outside: trap points use the open carrier, wall points use the wall neighborhood,
whose incident trapezoids are also unreachable.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.exists_nhds_inter_subset_diff {F : Set plane} (D : TrapDecomp F)
    (hF : IsOpen F) (cI : D.Cell) (p : plane) (hp : p ∈ F \ D.reachUnion cI) :
    ∃ U ∈ 𝓝 p, U ∩ F ⊆ F \ D.reachUnion cI := by
  obtain ⟨hpF, hpnS⟩ := hp
  obtain ⟨c', hpc'⟩ := (D.existsUnique_cell p hpF).exists
  have hnot : ¬ D.incidenceGraph.Reachable cI c' := by
    intro hreach
    exact hpnS (D.mem_reachUnion cI c' hreach hpc')
  cases c' with
  | inl i =>
    have ho : IsOpen (D.trap i).carrier := (D.trap i).isOpen_carrier
    have hmem : (D.trap i).carrier ∈ 𝓝 p := ho.mem_nhds hpc'
    refine ⟨(D.trap i).carrier, hmem, ?_⟩
    intro q hq
    obtain ⟨hqcar, hqF⟩ := hq
    refine ⟨hqF, ?_⟩
    intro hqS
    have hdisj := D.disjoint_carrier_reachUnion_of_not_reachable cI (.inl i) hnot
    exact (Set.disjoint_left.mp hdisj hqcar hqS).elim
  | inr j =>
    obtain ⟨U, hUmem, hUsub⟩ := D.wall_neighborhood hF j p hpc'
    refine ⟨U, hUmem, ?_⟩
    intro q hq
    obtain ⟨hqU, hqF⟩ := hq
    refine ⟨hqF, ?_⟩
    intro hqS
    have hq' := hUsub hqU
    simp only [Set.mem_union, Set.mem_iUnion] at hq'
    cases hq' with
    | inl hwall =>
      have hdisj := D.disjoint_carrier_reachUnion_of_not_reachable cI (.inr j) hnot
      exact (Set.disjoint_left.mp hdisj hwall hqS).elim
    | inr hex =>
      obtain ⟨i, hadj, hqi⟩ := hex
      have hnot_i : ¬ D.incidenceGraph.Reachable cI (.inl i) :=
        D.not_reachable_inl_of_not_reachable_inr cI i j hadj hnot
      have hdisj := D.disjoint_carrier_reachUnion_of_not_reachable cI (.inl i) hnot_i
      exact (Set.disjoint_left.mp hdisj hqi hqS).elim

/-- Path-to-graph direction: points joined in `F` lie in reachable cells. The
union of carriers of reachable cells is relatively clopen in `F`, so a path in
`F` cannot leave it.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.reachable_of_joinedIn {F : Set plane} (D : TrapDecomp F) (hF : IsOpen F)
    {qI qG : plane} {cI cG : D.Cell}
    (hcI : qI ∈ D.carrier cI) (hcG : qG ∈ D.carrier cG)
    (h : JoinedIn F qI qG) : D.incidenceGraph.Reachable cI cG := by
  have hG : qG ∈ F := D.carrier_subset _ hcG
  have hS_open : IsOpen (D.reachUnion cI) := D.isOpen_reachUnion hF cI
  have hqI_mem : qI ∈ D.reachUnion cI :=
    D.mem_reachUnion cI cI (SimpleGraph.Reachable.refl _) hcI
  have hqG_mem : qG ∈ D.reachUnion cI := by
    by_contra hcon
    obtain ⟨γ, hγF⟩ := h
    have hA_open : IsOpen (⇑γ ⁻¹' D.reachUnion cI) := hS_open.preimage γ.continuous
    have hB_open : IsOpen (⇑γ ⁻¹' (F \ D.reachUnion cI)) := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      simp only [Set.mem_preimage] at ht
      obtain ⟨U, hUmem, hUsub⟩ := D.exists_nhds_inter_subset_diff hF cI (γ t) ht
      have hcont : ContinuousAt ⇑γ t := γ.continuous.continuousAt
      have hpremem : ⇑γ ⁻¹' U ∈ 𝓝 t := hcont.preimage_mem_nhds hUmem
      have hsub : ⇑γ ⁻¹' U ⊆ ⇑γ ⁻¹' (F \ D.reachUnion cI) := by
        intro s hs
        simp only [Set.mem_preimage] at hs ⊢
        exact hUsub ⟨hs, hγF s⟩
      exact Filter.mem_of_superset hpremem hsub
    have hdisjS : Disjoint (D.reachUnion cI) (F \ D.reachUnion cI) := by
      rw [Set.disjoint_left]
      intro a ha1 ha2
      exact ha2.2 ha1
    have hdisj : Disjoint (⇑γ ⁻¹' D.reachUnion cI) (⇑γ ⁻¹' (F \ D.reachUnion cI)) :=
      Disjoint.preimage _ hdisjS
    have hcover : Set.univ ⊆ (⇑γ ⁻¹' D.reachUnion cI) ∪ (⇑γ ⁻¹' (F \ D.reachUnion cI)) := by
      intro t _
      simp only [Set.mem_union, Set.mem_preimage]
      by_cases hmem : γ t ∈ D.reachUnion cI
      · exact Or.inl hmem
      · exact Or.inr ⟨hγF t, hmem⟩
    have hpre : IsPreconnected (Set.univ : Set unitInterval) := isPreconnected_univ
    have hsub :=
      IsPreconnected.subset_or_subset hA_open hB_open hdisj hcover hpre
    have h0A : (0 : unitInterval) ∈ ⇑γ ⁻¹' D.reachUnion cI := by
      simp only [Set.mem_preimage]
      rw [γ.source]
      exact hqI_mem
    have h1B : (1 : unitInterval) ∈ ⇑γ ⁻¹' (F \ D.reachUnion cI) := by
      simp only [Set.mem_preimage]
      rw [γ.target]
      exact ⟨hG, hcon⟩
    cases hsub with
    | inl hsubA =>
      have h1A : (1 : unitInterval) ∈ ⇑γ ⁻¹' D.reachUnion cI :=
        hsubA (Set.mem_univ _)
      exact (Set.disjoint_left.mp hdisj h1A h1B).elim
    | inr hsubB =>
      have h0B : (0 : unitInterval) ∈ ⇑γ ⁻¹' (F \ D.reachUnion cI) :=
        hsubB (Set.mem_univ _)
      exact (Set.disjoint_left.mp hdisj h0A h0B).elim
  obtain ⟨c, hreach, hqc⟩ := hqG_mem
  have heq : c = cG := D.eq_of_mem_carrier hG hqc hcG
  subst heq
  exact hreach

/-- Pointwise equivalence between graph reachability and path connectivity.
LaValle, Planning Algorithms, Sec. 6.2.2. -/
theorem TrapDecomp.reachable_iff_joinedIn {F : Set plane} (D : TrapDecomp F) (hF : IsOpen F)
    {qI qG : plane} {cI cG : D.Cell}
    (hcI : qI ∈ D.carrier cI) (hcG : qG ∈ D.carrier cG) :
    D.incidenceGraph.Reachable cI cG ↔ JoinedIn F qI qG := by
  constructor
  · intro h
    exact D.joinedIn_of_reachable hcI hcG h
  · intro h
    exact D.reachable_of_joinedIn hF hcI hcG h

end VerticalCells

end Cslib.Planning.MotionPlanning
