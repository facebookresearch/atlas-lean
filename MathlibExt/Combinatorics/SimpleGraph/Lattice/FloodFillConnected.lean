/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeometricFaces
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanLeftRegionInterior

/-!
# Flood fills avoiding a set of sites

The flood fill of a seed avoiding a set `B` is the set of sites reachable from the seed by lattice
paths that avoid `B`. A flood fill avoiding `B` lies off `B` and is connected in the lattice with
`B` removed. Neither the inside nor the outside of a closed walk is ever the flood fill, avoiding
the walk, of a site off the walk: the outside, and the inside when nonempty, meet the walk.

## Main definitions

* `StatMech.Lattice.ffc_offSupportLattice B`: the square lattice with the sites of `B` removed.
* `StatMech.Lattice.ffc_lift_walk`: a lattice path avoiding `B` as a walk in that graph.
* `StatMech.Lattice.ffc_floodFill B seed`: the sites reachable from `seed` avoiding `B`.

## Main results

* `StatMech.Lattice.ffc_reachable_iff_offSupportWalk`: reachability avoiding `B` is the existence of
  a lattice path avoiding `B`.
* `StatMech.Lattice.ffc_floodFill_step`: flood fills are closed under lattice steps avoiding `B`.
* `StatMech.Lattice.ffc_side_reachable_of_eq_floodFill`: a set equal to a flood fill avoiding the
  walk is connected in the cut lattice.
* `StatMech.Lattice.ffc_leftRegion_ne_floodFill`,
  `StatMech.Lattice.ffc_compl_leftRegion_ne_floodFill`: the inside and the outside of a closed walk
  are never such flood fills.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The square lattice with every vertex of `B` removed (edges with an endpoint in `B` deleted). -/
def ffc_offSupportLattice (B : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B
  symm := by
    refine ⟨?_⟩
    rintro x y ⟨hadj, hx, hy⟩
    exact ⟨hadj.symm, hy, hx⟩
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem ffc_offSupportLattice_adj (B : Set (Site 2)) (x y : Site 2) :
    (ffc_offSupportLattice B).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B := Iff.rfl

theorem ffc_offSupportLattice_le (B : Set (Site 2)) :
    ffc_offSupportLattice B ≤ hypercubicLattice 2 := fun _ _ h => h.1

theorem ffc_offSupportWalk_support {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∀ z ∈ w.support, z ∉ B := by
  induction w with
  | nil => intro z hz; rw [SimpleGraph.Walk.support_nil] at hz; rw [List.mem_singleton] at hz;
           exact hz ▸ hx
  | @cons a b c hab p ih =>
    intro z hz
    have hb : b ∉ B := hab.2.2
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact ih hb z h

theorem ffc_project_walk {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, (∀ z ∈ p.support, z ∉ B) ∧ p.support = w.support := by
  classical
  refine ⟨w.mapLe (ffc_offSupportLattice_le B), ?_, ?_⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
    exact ffc_offSupportWalk_support w hx z hz
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]

/-- A lattice walk avoiding `B`, viewed as a walk in `ffc_offSupportLattice B`. -/
def ffc_lift_walk {B : Set (Site 2)} :
    ∀ {x y : Site 2} (p : (hypercubicLattice 2).Walk x y),
      (∀ z ∈ p.support, z ∉ B) → (ffc_offSupportLattice B).Walk x y
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons hab p, hp =>
      SimpleGraph.Walk.cons
        ⟨hab, hp _ (by simp), hp _ (by
          rw [SimpleGraph.Walk.support_cons]; right; exact p.start_mem_support)⟩
        (ffc_lift_walk p (fun z hz => hp z (by
          rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)))

theorem ffc_reachable_iff_offSupportWalk {B : Set (Site 2)} {x y : Site 2} (hx : x ∉ B) :
    (ffc_offSupportLattice B).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨p, hp, _⟩ := ffc_project_walk w hx
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨ffc_lift_walk p hp⟩

/-- The flood fill of `seed` avoiding `B`: the sites reachable from `seed` in the lattice with
`B` removed. -/
def ffc_floodFill (B : Set (Site 2)) (seed : Site 2) : Set (Site 2) :=
  {z | (ffc_offSupportLattice B).Reachable seed z}

@[simp] theorem ffc_mem_floodFill {B : Set (Site 2)} {seed z : Site 2} :
    z ∈ ffc_floodFill B seed ↔ (ffc_offSupportLattice B).Reachable seed z := Iff.rfl

theorem ffc_seed_mem_floodFill (B : Set (Site 2)) (seed : Site 2) :
    seed ∈ ffc_floodFill B seed :=
  SimpleGraph.Reachable.refl _

theorem ffc_floodFill_offSupport {B : Set (Site 2)} {seed : Site 2} (hseed : seed ∉ B)
    {z : Site 2} (hz : z ∈ ffc_floodFill B seed) : z ∉ B := by
  rw [ffc_mem_floodFill] at hz
  obtain ⟨w⟩ := hz
  exact ffc_offSupportWalk_support w hseed z w.end_mem_support

/-- A removed site is isolated in the lattice with the sites of `B` removed. -/
theorem oc_ffc_reachable_eq_of_mem {B : Set (Site 2)} {x y : Site 2} (hx : x ∈ B)
    (h : (ffc_offSupportLattice B).Reachable x y) : x = y := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hx hadj.2.1

theorem ffc_floodFill_reachable_offSupportLattice {B : Set (Site 2)} {seed : Site 2}
    {x y : Site 2} (hx : x ∈ ffc_floodFill B seed) (hy : y ∈ ffc_floodFill B seed) :
    (ffc_offSupportLattice B).Reachable x y := by
  rw [ffc_mem_floodFill] at hx hy
  exact hx.symm.trans hy

theorem ffc_floodFill_path_connected_offSupport {B : Set (Site 2)} {seed : Site 2}
    (hseed : seed ∉ B) {x y : Site 2}
    (hx : x ∈ ffc_floodFill B seed) (hy : y ∈ ffc_floodFill B seed) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
  have hxB : x ∉ B := ffc_floodFill_offSupport hseed hx
  exact (ffc_reachable_iff_offSupportWalk hxB).mp
    (ffc_floodFill_reachable_offSupportLattice hx hy)

theorem ffc_floodFill_self_offSupport_walk {B : Set (Site 2)} {seed : Site 2} (hseed : seed ∉ B)
    {z : Site 2} (hz : z ∈ ffc_floodFill B seed) :
    ∃ p : (hypercubicLattice 2).Walk seed z, ∀ w ∈ p.support, w ∉ B :=
  ffc_floodFill_path_connected_offSupport hseed (ffc_seed_mem_floodFill B seed) hz

theorem ffc_floodFill_step {B : Set (Site 2)} {seed z w : Site 2}
    (hz : z ∈ ffc_floodFill B seed) (hadj : (hypercubicLattice 2).Adj z w)
    (hzB : z ∉ B) (hwB : w ∉ B) :
    w ∈ ffc_floodFill B seed := by
  rw [ffc_mem_floodFill] at hz ⊢
  exact hz.trans ((ffc_offSupportLattice_adj B z w).mpr ⟨hadj, hzB, hwB⟩).reachable

theorem ffc_engine_nonvacuous :
    ∃ p : (hypercubicLattice 2).Walk (![0, 0] : Site 2) ![1, 0],
      ∀ z ∈ p.support, z ∉ ({z | z = (![5, 5] : Site 2)} : Set (Site 2)) := by
  set B : Set (Site 2) := {z | z = (![5, 5] : Site 2)} with hB
  have hseed : (![0, 0] : Site 2) ∉ B := by
    simp only [hB, Set.mem_ofPred_eq]; intro h; have := congrFun h 0; simp at this
  have hadj : (hypercubicLattice 2).Adj (![0, 0] : Site 2) ![1, 0] := by
    rw [hypercubicLattice_adj]; decide
  have htgt : (![1, 0] : Site 2) ∉ B := by
    simp only [hB, Set.mem_ofPred_eq]; intro h; have := congrFun h 0; simp at this
  have hmem : (![1, 0] : Site 2) ∈ ffc_floodFill B (![0, 0] : Site 2) :=
    ffc_floodFill_step (ffc_seed_mem_floodFill B _) hadj hseed htgt
  exact ffc_floodFill_path_connected_offSupport hseed (ffc_seed_mem_floodFill B _) hmem

theorem ffc_floodFill_reachable_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) {x y : Site 2}
    (hx : x ∈ ffc_floodFill {z | z ∈ Vc.support} seed)
    (hy : y ∈ ffc_floodFill {z | z ∈ Vc.support} seed) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
  obtain ⟨p, hp⟩ := ffc_floodFill_path_connected_offSupport hseed hx hy
  exact jlri_offSupport_walk_in_barrier Vc p hp

theorem ffc_side_reachable_of_eq_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) {T : Set (Site 2)}
    (hT : T = ffc_floodFill {z | z ∈ Vc.support} seed) {x y : Site 2} (hx : x ∈ T) (hy : y ∈ T) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  ffc_floodFill_reachable_in_barrier Vc hseed (hT ▸ hx) (hT ▸ hy)

/-- The inside of a closed walk is never the flood fill, avoiding the walk, of a site off the walk.
The flood fill contains its seed, so the inside would be nonempty and lie entirely off the walk,
contradicting `StatMech.Lattice.oc_leftRegion_meets_support`. -/
theorem ffc_leftRegion_ne_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) :
    jec_leftRegion Vc ≠ ffc_floodFill {z | z ∈ Vc.support} seed := by
  intro h
  have hmem : seed ∈ jec_leftRegion Vc := h ▸ ffc_seed_mem_floodFill _ seed
  obtain ⟨s, hs, hsupp⟩ := oc_leftRegion_meets_support Vc hmem
  rw [h] at hs
  exact ffc_floodFill_offSupport (B := {z | z ∈ Vc.support}) hseed hs hsupp

/-- The outside of a closed walk is never the flood fill, avoiding the walk, of a site off the walk:
the flood fill lies off the walk, but some vertex of the walk is outside
(`StatMech.Lattice.oc_not_forall_outside_offSupport`). -/
theorem ffc_compl_leftRegion_ne_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) :
    (jec_leftRegion Vc)ᶜ ≠ ffc_floodFill {z | z ∈ Vc.support} seed := by
  intro h
  refine oc_not_forall_outside_offSupport Vc fun s hs => ?_
  have hs' : s ∈ ffc_floodFill {z | z ∈ Vc.support} seed := h ▸ hs
  exact ffc_floodFill_offSupport (B := {z | z ∈ Vc.support}) hseed hs'

end Lattice

end StatMech
