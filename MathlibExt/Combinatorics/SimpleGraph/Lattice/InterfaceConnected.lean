/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceOrbit

/-!
# Reductions of `InterfaceConnected` to local conditions

`InterfaceConnected K` asks that boundary darts with heads in one component of `Kᶜ` share an orbit.
The file shows that being in the same orbit implies that the heads are connected, and reduces the
converse to three local conditions: orbits can be transported along king moves (steps to any of the
eight surrounding sites) outside `K`, connectivity in `Kᶜ` implies king connectivity, and every dart
at a reached vertex lies in the orbit.

## Main definitions

* `StatMech.Lattice.IsInnerCorner K e`: the site diagonally ahead of `e` lies in `K`, so the
  successor of `e` rotates about its head.
* `StatMech.Lattice.SameOrbit K e f`: `f` is an iterate of `e` under `dartNext K`.
* `StatMech.Lattice.KingAdj u v`: `u` and `v` are distinct and differ by at most one in each
  coordinate.
* `StatMech.Lattice.boundaryKingGraph K`: the king-move graph on `Kᶜ`.
* `StatMech.Lattice.OrbitKingTransport K`, `StatMech.Lattice.BoundaryKingConnected K`,
  `StatMech.Lattice.OrbitVertexSaturate K`: the three local conditions.

## Main results

* `StatMech.Lattice.SameOrbit.symm_of_finite`: for finite `K`, sharing an orbit is symmetric.
* `StatMech.Lattice.sameComponent_of_sameOrbit`: darts in one orbit have heads in one component of
  `Kᶜ`.
* `StatMech.Lattice.interfaceConnected_of_kingResidues`: the three local conditions imply
  `InterfaceConnected K`.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

theorem dartNext_head_eq_iff_front_mem (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).head = e.head ↔ e.head + (-rot90Fun e.dir) ∈ K := by
  classical
  constructor
  · intro hhd
    by_contra hA
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · have h := dartNext_straight_head K e hA hB
      rw [hhd] at h
      apply neg_rot90Fun_dartDir_ne_zero e
      have h' : e.head + (-rot90Fun e.dir) = e.head + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h'
    · have h := dartNext_left_head K e hA hB
      rw [hhd] at h
      have hd : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
      rw [hd] at h
      have hdir : e.dir = -rot90Fun e.dir := add_left_cancel h
      exact neg_rot90Fun_dartDir_ne_dartDir e hdir.symm
  · intro hA
    exact (dartNext_front_head K e hA).1

theorem dartNext_rotates_head (K : Set (Site 2)) (e : Dart)
    (hA : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir :=
  dartNext_front_head K e hA

theorem dartNext_dir_eq_rot90_of_front (K : Set (Site 2)) (e : Dart)
    (hA : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).dir = rot90Fun e.dir :=
  (dartNext_front_head K e hA).2

/-- The site `e.head + r`, with `r` the clockwise rotation of `e.dir`, lies in `K`; then the
successor of `e` has the same head. -/
def IsInnerCorner (K : Set (Site 2)) (e : Dart) : Prop :=
  e.head + (-rot90Fun e.dir) ∈ K

theorem dartNext_iterate_head_fixed (K : Set (Site 2)) (e : Dart) :
    ∀ (k : ℕ), (∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) →
      ((dartNext K)^[k] e).head = e.head ∧
      ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro hcorner
    have hm : ∀ j < m, IsInnerCorner K ((dartNext K)^[j] e) := fun j hj =>
      hcorner j (Nat.lt_succ_of_lt hj)
    obtain ⟨hh, hd⟩ := ih hm
    have hcm : IsInnerCorner K ((dartNext K)^[m] e) := hcorner m (Nat.lt_succ_self m)
    have hstep := dartNext_front_head K ((dartNext K)^[m] e) hcm
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · rw [hstep.1, hh]
    · rw [hstep.2, hd, ← Function.iterate_succ_apply' rot90Fun m e.dir]

theorem dartNext_iterate_isBoundary_head_fixed (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ)
    (hcorner : ∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) :
    IsBoundaryDart K ((dartNext K)^[k] e) ∧
      ((dartNext K)^[k] e).head = e.head ∧
      ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
  refine ⟨iterate_isBoundaryDart K e he k, dartNext_iterate_head_fixed K e k hcorner⟩

/-- The dart `f` is obtained from `e` by iterating the boundary successor map of `K`. -/
def SameOrbit (K : Set (Site 2)) (e f : Dart) : Prop := ∃ n : ℕ, (dartNext K)^[n] e = f

theorem SameOrbit.refl (K : Set (Site 2)) (e : Dart) : SameOrbit K e e := ⟨0, rfl⟩

theorem SameOrbit.trans {K : Set (Site 2)} {e f g : Dart}
    (h1 : SameOrbit K e f) (h2 : SameOrbit K f g) : SameOrbit K e g := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply, hm, hn]

theorem SameOrbit.symm_of_finite {K : Set (Site 2)} (hK : K.Finite) {e f : Dart}
    (he : IsBoundaryDart K e) (h : SameOrbit K e f) : SameOrbit K f e := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨p, hp, hper⟩ := dartNext_periodic K hK e he
  refine ⟨(n / p + 1) * p - n, ?_⟩
  have hle : n ≤ (n / p + 1) * p := by
    have h1 : n / p * p ≤ n := Nat.div_mul_le_self n p
    have h2 : n < n / p * p + p := Nat.lt_div_mul_add hp
    rw [Nat.add_one_mul]
    omega
  rw [← hn, ← Function.iterate_add_apply]
  rw [Nat.sub_add_cancel hle]
  have hmul : ∀ k : ℕ, (dartNext K)^[k * p] e = e := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [Nat.succ_mul, Function.iterate_add_apply, hper, ih]
  exact hmul (n / p + 1)

theorem sameComponent_of_sameOrbit (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  obtain ⟨n, hn⟩ := h
  exact dartNext_orbit_head_sameComponent K e f he hf hn

theorem interfaceConnected_iff_sameOrbit (K : Set (Site 2)) :
    InterfaceConnected K ↔
      ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
        ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ →
          SameOrbit K e f :=
  Iff.rfl

/-- Boundary darts whose heads are connected in `Kᶜ` lie in the same orbit; a reformulation of
`StatMech.Lattice.InterfaceConnected`. -/
def OrbitHeadsSaturate (K : Set (Site 2)) : Prop :=
  ∀ (e f : Dart), IsBoundaryDart K e → IsBoundaryDart K f →
    (∀ (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
      ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩) →
    SameOrbit K e f

theorem interfaceConnected_of_orbitHeadsSaturate (K : Set (Site 2))
    (h : OrbitHeadsSaturate K) : InterfaceConnected K := by
  intro e f he hf hreach
  exact h e f he hf (fun _he' _hf' => hreach)

theorem orbitHeadsSaturate_of_interfaceConnected (K : Set (Site 2))
    (h : InterfaceConnected K) : OrbitHeadsSaturate K := by
  intro e f he hf hreach
  exact h e f he hf (hreach he hf)

/-- King adjacency on `ℤ²`: distinct sites that differ by at most one in each coordinate. -/
def KingAdj (u v : Site 2) : Prop := u ≠ v ∧ ∀ i, (u i - v i).natAbs ≤ 1

theorem KingAdj.symm {u v : Site 2} (h : KingAdj u v) : KingAdj v u := by
  refine ⟨h.1.symm, fun i => ?_⟩
  rw [← Int.natAbs_neg, neg_sub]; exact h.2 i

/-- The graph of king moves on the complement of `K`. -/
def boundaryKingGraph (K : Set (Site 2)) : SimpleGraph (↥(Kᶜ : Set (Site 2))) where
  Adj a b := KingAdj (a : Site 2) (b : Site 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem boundaryKingGraph_adj (K : Set (Site 2)) (a b : ↥(Kᶜ : Set (Site 2))) :
    (boundaryKingGraph K).Adj a b ↔ KingAdj (a : Site 2) (b : Site 2) := Iff.rfl

/-- Some boundary dart in the orbit of `e` has head `v`. -/
def OrbitReached (K : Set (Site 2)) (e : Dart) (v : Site 2) : Prop :=
  ∃ d : Dart, IsBoundaryDart K d ∧ d.head = v ∧ SameOrbit K e d

theorem orbitReached_self (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    OrbitReached K e e.head :=
  ⟨e, he, rfl, SameOrbit.refl K e⟩

/-- If the orbit of `e` reaches a site outside `K`, it reaches every king neighbour of that site
outside `K`. -/
def OrbitKingTransport (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e →
    ∀ {u v : Site 2}, u ∉ K → v ∉ K → KingAdj u v →
      OrbitReached K e u → OrbitReached K e v

/-- Every boundary dart whose head is reached by the orbit of `e` lies in that orbit. -/
def OrbitVertexSaturate (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e → ∀ {v : Site 2}, OrbitReached K e v →
    ∀ d : Dart, IsBoundaryDart K d → d.head = v → SameOrbit K e d

/-- Sites connected by a lattice path in `Kᶜ` are connected by king moves in `Kᶜ`. -/
def BoundaryKingConnected (K : Set (Site 2)) : Prop :=
  ∀ {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K),
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩ →
    (boundaryKingGraph K).Reachable ⟨u, hu⟩ ⟨w, hw⟩

theorem orbitReached_of_kingReachable (K : Set (Site 2)) (htr : OrbitKingTransport K)
    (e : Dart) (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (hreach : (boundaryKingGraph K).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
    (hou : OrbitReached K e u) : OrbitReached K e w := by
  obtain ⟨p⟩ := hreach
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), (boundaryKingGraph K).Walk a b →
      OrbitReached K e (a : Site 2) → OrbitReached K e (b : Site 2) from
    H ⟨u, hu⟩ ⟨w, hw⟩ p hou
  intro a b q
  induction q with
  | nil => intro h; exact h
  | @cons a b c hadj q' ih =>
    intro hoa
    have hking : KingAdj (a : Site 2) (b : Site 2) := (boundaryKingGraph_adj K a b).mp hadj
    have ho_b : OrbitReached K e (b : Site 2) := htr e he a.2 b.2 hking hoa
    exact ih ho_b

theorem interfaceConnected_of_kingResidues (K : Set (Site 2))
    (htr : OrbitKingTransport K) (hcon : BoundaryKingConnected K)
    (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K := by
  intro e f he hf hreach
  have hking : (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ :=
    hcon he.2 hf.2 hreach
  have hbase : OrbitReached K e e.head := orbitReached_self K e he
  have hfhead : OrbitReached K e f.head :=
    orbitReached_of_kingReachable K htr e he he.2 hf.2 hking hbase
  exact hsat e he hfhead f hf rfl

end Lattice

end StatMech
