/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FloodFillConnected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InsideConnected

/-!
# The off-support interior of a closed lattice walk

For a closed walk `Vc` in the square lattice on `Site 2 = Fin 2 → ℤ`, the inside
`jec_leftRegion Vc` consists of the sites with odd ray count (the even–odd rule). This file
studies the *off-support interior* `jil_offSupportInterior Vc`: the inside sites that `Vc` does
not visit. Ray-count parity is constant along lattice paths avoiding `Vc`, so a flood fill from an
off-support seed stays on one side of `Vc`, and so does every horizontal run of sites off `Vc`.

`jil_RowLinked Vc seed` says that every off-support interior site is joined to `seed` by a lattice
path avoiding `Vc`. For a seed in the off-support interior this means that the off-support
interior is a single connected component of the lattice with the support of `Vc` removed, namely
the flood fill of the seed. This is not automatic: for some simple closed walks the off-support
interior is disconnected (`iwc_interior_disconnected`).

## Main definitions

* `StatMech.Lattice.jil_offSupportInterior Vc`: inside sites of `Vc` not on `Vc`.
* `StatMech.Lattice.jil_RowLinked Vc seed`: every off-support interior site reaches `seed` by a
  lattice path avoiding `Vc`.
* `StatMech.Lattice.jil_interiorStepGraph Vc`: the square lattice induced on the off-support
  interior.

## Main results

* `StatMech.Lattice.jil_floodFill_subset_leftRegion`,
  `StatMech.Lattice.jil_floodFill_subset_exterior`: a flood fill avoiding `Vc` stays inside
  (outside) `Vc` when its seed is inside (outside).
* `StatMech.Lattice.jil_hsegment_subset_leftRegion`: a horizontal segment avoiding `Vc` lies on
  one side of `Vc`.
* `StatMech.Lattice.jil_offSupportInterior_eq_floodFill`: for a row-linked seed, the off-support
  interior is the flood fill of the seed.
* `StatMech.Lattice.jil_floodFill_eq_offSupportComponent`: the flood fill avoiding `Vc` is the
  component `offSupportComponent Vc seed`.
* `StatMech.Lattice.jil_rowLinked_of_stepReachable`: connectivity of the induced square lattice
  gives a row-linked seed.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- One step to the right between two sites off `B` stays in the flood fill. -/
theorem jil_floodFill_stepRight (B : Set (Site 2)) {seed : Site 2} {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ ffc_floodFill B seed)
    (hzB : (![x, y] : Site 2) ∉ B) (hwB : (![x + 1, y] : Site 2) ∉ B) :
    (![x + 1, y] : Site 2) ∈ ffc_floodFill B seed := by
  refine ffc_floodFill_step hz ?_ hzB hwB
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp

/-- A horizontal run of sites off `B` that starts in the flood fill of `seed` lies in it. -/
theorem jil_floodFill_run_right (B : Set (Site 2)) {seed : Site 2} {x₀ y : ℤ} (k : ℕ)
    (h0 : (![x₀, y] : Site 2) ∈ ffc_floodFill B seed)
    (hoff : ∀ t : ℕ, t ≤ k → (![x₀ + (t : ℤ), y] : Site 2) ∉ B) :
    (![x₀ + (k : ℤ), y] : Site 2) ∈ ffc_floodFill B seed := by
  induction k with
  | zero => simpa using h0
  | succ m ih =>
    have hm : (![x₀ + (m : ℤ), y] : Site 2) ∈ ffc_floodFill B seed :=
      ih (fun t ht => hoff t (ht.trans (Nat.le_succ m)))
    have hmB : (![x₀ + (m : ℤ), y] : Site 2) ∉ B := hoff m (Nat.le_succ m)
    have hsB : (![x₀ + ((m : ℤ) + 1), y] : Site 2) ∉ B := by
      have := hoff (m + 1) le_rfl
      simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc] using this
    have hstep := jil_floodFill_stepRight B hm hmB (by
      simpa [add_assoc] using hsB)
    simpa [Nat.cast_succ, add_assoc] using hstep

/-- Every site of the flood fill of `seed` avoiding `Vc` has the ray-count parity of `seed`. -/
theorem jil_floodFill_sameParity {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    {z : Site 2} (hz : z ∈ ffc_floodFill {p | p ∈ Vc.support} seed) :
    (Even (jec_rayCount seed Vc) ↔ Even (jec_rayCount z Vc)) := by
  obtain ⟨p, hp⟩ := ffc_floodFill_self_offSupport_walk hseed hz
  exact oee_rayParity_const_along_walk Vc p (by
    intro w hw; exact hp w hw)

/-- The flood fill avoiding the support of `Vc` is the component `offSupportComponent Vc seed` of
the lattice with the vertices of `Vc` removed. -/
theorem jil_floodFill_eq_offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) :
    ffc_floodFill {p | p ∈ Vc.support} seed = offSupportComponent Vc seed :=
  rfl

/-- The flood fill avoiding `Vc` of an off-support seed inside `Vc` stays inside `Vc`. See also
`offSupportComponent_subset_interior`, the same statement for `offSupportComponent`
(`jil_floodFill_eq_offSupportComponent`). -/
theorem jil_floodFill_subset_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jec_leftRegion Vc := by
  intro z hz
  rw [jec_mem_leftRegion] at hseedIn ⊢
  have hpar := jil_floodFill_sameParity Vc hseed hz
  exact fun h => hseedIn (hpar.mpr h)

/-- The flood fill avoiding `Vc` of an off-support seed outside `Vc` stays outside `Vc`. See also
`offSupportComponent_subset_exterior`. -/
theorem jil_floodFill_subset_exterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedOut : seed ∉ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ (jec_leftRegion Vc)ᶜ := by
  intro z hz
  rw [jec_mem_leftRegion, not_not] at hseedOut
  rw [Set.mem_compl_iff, jec_mem_leftRegion, not_not]
  have hpar := jil_floodFill_sameParity Vc hseed hz
  exact hpar.mp hseedOut

/-- A horizontal segment avoiding `B` lies in the flood fill of its left end. -/
theorem jil_hsegment_mem_floodFill (B : Set (Site 2)) {lo hi y x : ℤ}
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
    (![x, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) := by
  set k : ℕ := (x - lo).toNat with hk
  have hxk : x = lo + (k : ℤ) := by rw [hk]; omega
  rw [hxk]
  refine jil_floodFill_run_right B k ?_ ?_
  · exact ffc_seed_mem_floodFill B (![lo, y] : Site 2)
  · intro t ht
    refine hoff (lo + (t : ℤ)) (by omega) ?_
    have : (t : ℤ) ≤ (k : ℤ) := by exact_mod_cast ht
    omega

/-- Two sites of a horizontal segment avoiding `B` are joined by a lattice path avoiding `B`. -/
theorem jil_hsegment_reachable_offSupport (B : Set (Site 2)) {lo hi y x₁ x₂ : ℤ}
    (hloB : (![lo, y] : Site 2) ∉ B)
    (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi) (hx₂lo : lo ≤ x₂) (hx₂hi : x₂ ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk (![x₁, y] : Site 2) ![x₂, y],
      ∀ z ∈ p.support, z ∉ B := by
  have h1 : (![x₁, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill B hx₁lo hx₁hi hoff
  have h2 : (![x₂, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill B hx₂lo hx₂hi hoff
  exact ffc_floodFill_path_connected_offSupport hloB h1 h2

/-- All sites of a horizontal segment avoiding `Vc` have the same ray-count parity. -/
theorem jil_hsegment_sameParity {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {lo hi y x : ℤ} (hloB : (![lo, y] : Site 2) ∉ Vc.support)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
    (Even (jec_rayCount (![lo, y] : Site 2) Vc) ↔ Even (jec_rayCount (![x, y] : Site 2) Vc)) := by
  have hmem : (![x, y] : Site 2) ∈ ffc_floodFill {p | p ∈ Vc.support} (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill {p | p ∈ Vc.support} hxlo hxhi
      (by intro t ht ht'; exact hoff t ht ht')
  exact jil_floodFill_sameParity Vc hloB hmem

/-- A horizontal segment avoiding `Vc` lies on one side of `Vc`: if one of its sites is inside `Vc`,
all are. -/
theorem jil_hsegment_subset_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {lo hi y x₀ x : ℤ}
    (hx₀lo : lo ≤ x₀) (hx₀hi : x₀ ≤ hi) (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support)
    (hin : (![x₀, y] : Site 2) ∈ jec_leftRegion Vc) :
    (![x, y] : Site 2) ∈ jec_leftRegion Vc := by
  have hloB : (![lo, y] : Site 2) ∉ Vc.support := hoff lo le_rfl (le_trans hx₀lo hx₀hi)
  rw [jec_mem_leftRegion] at hin ⊢
  have hpx₀ := jil_hsegment_sameParity Vc hloB hx₀lo hx₀hi hoff
  have hpx := jil_hsegment_sameParity Vc hloB hxlo hxhi hoff
  intro h
  exact hin (hpx₀.mp (hpx.mpr h))

/-- The off-support interior of a closed walk `Vc`: the sites inside `Vc` (odd ray count) that `Vc`
does not visit. -/
def jil_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc}

@[simp] theorem jil_mem_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∈ jil_offSupportInterior Vc ↔ z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc := Iff.rfl

/-- The flood fill avoiding `Vc` of an off-support seed inside `Vc` lies in the off-support
interior. -/
theorem jil_floodFill_subset_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jil_offSupportInterior Vc := by
  intro z hz
  rw [jil_mem_offSupportInterior]
  refine ⟨?_, jil_floodFill_subset_leftRegion Vc hseed hseedIn hz⟩
  have := ffc_floodFill_offSupport (B := {p | p ∈ Vc.support}) (by
    simpa using hseed) hz
  simpa using this

/-- Every off-support interior site of `Vc` is joined to `seed` by a lattice path avoiding `Vc`. For
`seed` in the off-support interior, this says the off-support interior is connected in the lattice
with the support of `Vc` removed. See also `inside_offSupport_connected_iff_covers`, the same
connectivity for the whole inside of `Vc`. -/
def jil_RowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc,
    ∃ p : (hypercubicLattice 2).Walk z seed, ∀ w ∈ p.support, w ∉ Vc.support

theorem jil_offSupportInterior_subset_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc ⊆ ffc_floodFill {p | p ∈ Vc.support} seed := by
  intro z hz
  obtain ⟨p, hp⟩ := hlink z hz
  have hzB : z ∉ ({p | p ∈ Vc.support} : Set (Site 2)) := by
    simpa using (jil_mem_offSupportInterior Vc z |>.mp hz).1
  have hreach : (ffc_offSupportLattice {p | p ∈ Vc.support}).Reachable z seed :=
    (ffc_reachable_iff_offSupportWalk hzB).mpr ⟨p, by intro w hw; simpa using hp w hw⟩
  exact hreach.symm

/-- For an off-support interior seed with `jil_RowLinked Vc seed`, the off-support interior is the
flood fill of the seed in the lattice with the support of `Vc` removed. See also
`interior_eq_offSupportComponent_iff`. -/
theorem jil_offSupportInterior_eq_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc)
    (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc = ffc_floodFill {p | p ∈ Vc.support} seed :=
  Set.Subset.antisymm (jil_offSupportInterior_subset_floodFill Vc hlink)
    (jil_floodFill_subset_offSupportInterior Vc hseed hseedIn)

/-- The square lattice induced on the off-support interior of `Vc`. -/
def jil_interiorStepGraph {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (jil_offSupportInterior Vc) :=
  (hypercubicLattice 2).induce (jil_offSupportInterior Vc)

/-- A walk in `jil_interiorStepGraph Vc` is a lattice walk avoiding `Vc`. -/
theorem jil_stepGraph_walk_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : jil_offSupportInterior Vc}
    (w : (jil_interiorStepGraph Vc).Walk x y) :
    ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2),
      ∀ z ∈ p.support, z ∉ Vc.support := by
  classical
  induction w with
  | @nil u => exact ⟨SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1⟩
  | @cons u v t hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2) := by
      rw [jil_interiorStepGraph] at hadj
      exact SimpleGraph.induce_adj.mp hadj
    have huoff : (u : Site 2) ∉ Vc.support :=
      (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · subst h; exact huoff
    · exact hp z h

/-- If every site of the induced square lattice on the off-support interior reaches `seed`, then
`jil_RowLinked Vc seed` holds. -/
theorem jil_rowLinked_of_stepReachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (jil_interiorStepGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    jil_RowLinked Vc seed := by
  intro z hz
  obtain ⟨w⟩ := hstep ⟨z, hz⟩
  exact jil_stepGraph_walk_offSupport Vc w

theorem jil_stepGraph_horizontal_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x + 1, y], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jil_stepGraph_vertical_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x, y + 1], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

end Lattice

end StatMech
