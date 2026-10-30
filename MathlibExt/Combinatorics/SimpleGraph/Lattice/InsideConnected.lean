/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanLeftRegionInterior

/-!
# Connectivity off a closed walk

Remove the vertices of a closed lattice walk `Vc` from `ℤ²`. Components of what remains lie entirely
inside or entirely outside `jec_leftRegion Vc`. The inside is connected off `Vc` iff one such
component covers it.

Hypotheses saying that every site of a side lies off `Vc` hold only in degenerate cases: some vertex
of `Vc` is always outside (`StatMech.Lattice.oc_not_forall_outside_offSupport`), and a nonempty
inside always contains a vertex of `Vc` (`StatMech.Lattice.oc_leftRegion_meets_support`). The
results below that assume every inside site is off `Vc` therefore apply only when the inside is
empty.

## Main definitions

* `StatMech.Lattice.offSupport Vc`: the square lattice with the vertices of `Vc` removed; the same
  graph as `StatMech.Lattice.ffc_offSupportLattice` of the support of `Vc`.
* `StatMech.Lattice.offSupportComponent Vc seed`: the component of `seed` off `Vc`.

## Main results

* `StatMech.Lattice.offSupport_reachable_iff_offSupportWalk`: reachability off `Vc` is the existence
  of a lattice path avoiding `Vc`.
* `StatMech.Lattice.offSupport_component_monochromatic`: components off `Vc` stay on one side.
* `StatMech.Lattice.inside_offSupport_connected_iff_covers`: the inside is connected off `Vc` iff
  one component covers it.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The square lattice with the vertices of the closed walk `Vc` removed. It is the same graph as
`StatMech.Lattice.ffc_offSupportLattice {z | z ∈ Vc.support}`. -/
noncomputable def offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ x ∉ Vc.support ∧ y ∉ Vc.support
  symm := by
    refine ⟨?_⟩
    intro x y ⟨hadj, hx, hy⟩
    exact ⟨hadj.symm, hy, hx⟩
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem offSupport_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : Site 2) :
    (offSupport Vc).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ x ∉ Vc.support ∧ y ∉ Vc.support := Iff.rfl

theorem offSupport_le {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    offSupport Vc ≤ hypercubicLattice 2 := fun _ _ h => h.1

theorem offSupport_walk_support_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (offSupport Vc).Walk x y) (hx : x ∉ Vc.support) :
    ∀ z ∈ p.support, z ∉ Vc.support := by
  induction p with
  | nil => intro z hz; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
           exact hz ▸ hx
  | @cons u w c hadj q ih =>
    have hw : w ∉ Vc.support := hadj.2.2
    intro z hz
    rw [SimpleGraph.Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h ▸ hx
    · exact ih hw z h

theorem offSupport_to_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (offSupport Vc).Walk x y) (hx : x ∉ Vc.support) :
    ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  refine ⟨p.mapLe (offSupport_le Vc), ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
  exact offSupport_walk_support_offSupport Vc p hx z hz

theorem offSupport_reachable_to_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (offSupport Vc).Reachable x y) (hx : x ∉ Vc.support) :
    ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  obtain ⟨p⟩ := h
  exact offSupport_to_offSupportWalk Vc p hx

theorem offSupportWalk_to_offSupport_reachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (offSupport Vc).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w c hadj q ih =>
    have hu : u ∉ Vc.support := hp u (by simp)
    have hw : w ∉ Vc.support := hp w (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hadj' : (offSupport Vc).Adj u w := ⟨hadj, hu, hw⟩
    exact hadj'.reachable.trans (ih htail)

theorem offSupport_reachable_iff_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support) :
    (offSupport Vc).Reachable x y ↔
      ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  constructor
  · intro h; exact offSupport_reachable_to_offSupportWalk Vc h hx
  · rintro ⟨pw, hpw⟩; exact offSupportWalk_to_offSupport_reachable Vc pw hpw

theorem inside_sameRegion_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (offSupport Vc).Reachable x y) (hx : x ∉ Vc.support) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc h hx
  exact jlri_sameRegion_along_offSupport_walk Vc pw hpw

theorem offSupport_component_monochromatic {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∈ jec_leftRegion Vc) (hst : (offSupport Vc).Reachable s t)
    (hsoff : s ∉ Vc.support) :
    t ∈ jec_leftRegion Vc :=
  (inside_sameRegion_offSupport Vc hst hsoff).mp hs

theorem offSupport_component_monochromatic_out {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∉ jec_leftRegion Vc) (hst : (offSupport Vc).Reachable s t)
    (hsoff : s ∉ Vc.support) :
    t ∉ jec_leftRegion Vc :=
  fun ht => hs ((inside_sameRegion_offSupport Vc hst hsoff).mpr ht)

/-- If every inside site is off `Vc` and the inside is connected in the lattice with `Vc`
removed, any two inside sites are joined by a lattice path avoiding `Vc`. The hypothesis `hoff`
(every inside site is off `Vc`) holds only when the inside is empty: a nonempty inside contains
a vertex of `Vc` (`StatMech.Lattice.oc_leftRegion_meets_support`), so for a nonempty inside this
statement is vacuous. -/
theorem hInOff_of_offSupport_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hconn : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (offSupport Vc).Reachable s t) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
  intro s t hs ht
  exact offSupport_reachable_to_offSupportWalk Vc (hconn s t hs ht) (hoff s hs)

theorem inside_offSupport_connected_of_hub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (offSupport Vc).Reachable s t := by
  intro s t hs ht
  exact ((hhub s hs).symm).trans (hhub t ht)

/-- If every inside site is off `Vc` and is reachable off `Vc` from one hub `c₀`, any two inside
sites are joined by a lattice path avoiding `Vc`. The hypothesis `hoff` (every inside site is
off `Vc`) holds only when the inside is empty: a nonempty inside contains a vertex of `Vc`
(`StatMech.Lattice.oc_leftRegion_meets_support`), so for a nonempty inside this statement is
vacuous. -/
theorem hInOff_of_interiorHub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  hInOff_of_offSupport_connected Vc hoff (inside_offSupport_connected_of_hub Vc hhub)

theorem minimalLoop_inside_sameRegion_offSupport (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {x y : Site 2}
    (h : (offSupport (mpl_orbitLoop K a)).Reachable x y) (hx : x ∉ (mpl_orbitLoop K a).support) :
    (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) :=
  inside_sameRegion_offSupport (mpl_orbitLoop K a) h hx

/-- `StatMech.Lattice.hInOff_of_interiorHub` for the face loop of a boundary orbit. The
hypothesis `hoff` (every inside site is off `Vc`) holds only when the inside is empty: a
nonempty inside contains a vertex of `Vc` (`StatMech.Lattice.oc_leftRegion_meets_support`), so
for a nonempty inside this statement is vacuous. -/
theorem minimalLoop_hInOff_of_interiorHub (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
        (offSupport (mpl_orbitLoop K a)).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
      t ∈ jec_leftRegion (mpl_orbitLoop K a) →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support :=
  hInOff_of_interiorHub (mpl_orbitLoop K a) hoff hhub

/-- The sites reachable from `seed` in the lattice with the vertices of `Vc` removed. -/
def offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Set (Site 2) :=
  {z | (offSupport Vc).Reachable seed z}

@[simp] theorem mem_offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed z : Site 2} :
    z ∈ offSupportComponent Vc seed ↔ (offSupport Vc).Reachable seed z := Iff.rfl

theorem seed_mem_offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) : seed ∈ offSupportComponent Vc seed :=
  SimpleGraph.Reachable.refl _

theorem offSupportComponent_subset_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    offSupportComponent Vc seed ⊆ jec_leftRegion Vc := by
  intro z hz
  rw [mem_offSupportComponent] at hz
  exact offSupport_component_monochromatic Vc hseed hz hsoff

theorem offSupportComponent_subset_exterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    offSupportComponent Vc seed ⊆ (jec_leftRegion Vc)ᶜ := by
  intro z hz
  rw [mem_offSupportComponent] at hz
  exact offSupport_component_monochromatic_out Vc hseed hz hsoff

theorem offSupportComponent_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsoff : seed ∉ Vc.support) {z : Site 2}
    (hz : z ∈ offSupportComponent Vc seed) : z ∉ Vc.support := by
  rw [mem_offSupportComponent] at hz
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc hz hsoff
  exact hpw z pw.end_mem_support

theorem offSupportComponent_hub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) :
    ∀ z : Site 2, z ∈ offSupportComponent Vc seed → (offSupport Vc).Reachable seed z :=
  fun _ hz => (mem_offSupportComponent Vc).mp hz

theorem interior_eq_offSupportComponent_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    jec_leftRegion Vc = offSupportComponent Vc seed ↔
      jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
  constructor
  · intro h; rw [h]
  · intro h
    exact le_antisymm h (offSupportComponent_subset_interior Vc hseed hsoff)

theorem interiorHub_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable seed s :=
  fun _ hs => (mem_offSupportComponent Vc).mp (hcov hs)

/-- If every inside site is off `Vc` and one component off `Vc` covers the inside, any two
inside sites are joined by a lattice path avoiding `Vc`. The hypothesis `hoff` (every inside
site is off `Vc`) holds only when the inside is empty: a nonempty inside contains a vertex of
`Vc` (`StatMech.Lattice.oc_leftRegion_meets_support`), so for a nonempty inside this statement
is vacuous. -/
theorem hInOff_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  hInOff_of_interiorHub Vc hoff (interiorHub_of_covers Vc hcov)

theorem inside_offSupport_connected_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (offSupport Vc).Reachable s t := by
  intro s t hs ht
  exact ((interiorHub_of_covers Vc hcov s hs).symm).trans (interiorHub_of_covers Vc hcov t ht)

theorem minimalLoop_offSupportComponent_subset_interior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {seed : Site 2}
    (hseed : seed ∈ jec_leftRegion (mpl_orbitLoop K a))
    (hsoff : seed ∉ (mpl_orbitLoop K a).support) :
    offSupportComponent (mpl_orbitLoop K a) seed ⊆ jec_leftRegion (mpl_orbitLoop K a) :=
  offSupportComponent_subset_interior (mpl_orbitLoop K a) hseed hsoff

/-- `StatMech.Lattice.hInOff_of_covers` for the face loop of a boundary orbit. The hypothesis
`hoff` (every inside site is off `Vc`) holds only when the inside is empty: a nonempty inside
contains a vertex of `Vc` (`StatMech.Lattice.oc_leftRegion_meets_support`), so for a nonempty
inside this statement is vacuous. -/
theorem minimalLoop_hInOff_of_covers (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {seed : Site 2}
    (hcov : jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
      t ∈ jec_leftRegion (mpl_orbitLoop K a) →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support :=
  hInOff_of_covers (mpl_orbitLoop K a) hoff hcov

theorem inside_offSupport_connected_iff_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) :
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (offSupport Vc).Reachable s t)
      ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
  constructor
  · intro hconn z hz
    exact (mem_offSupportComponent Vc).mpr (hconn seed z hseed hz)
  · intro hcov
    exact inside_offSupport_connected_of_covers Vc hcov

end Lattice

end StatMech
