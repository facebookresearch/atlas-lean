/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FaceComponentBijection

/-!
# The off-walk lattice as a graph on the off-walk sites

For a closed walk `Vc` in the square lattice `ℤ²`, `StatMech.Lattice.fcb_offComplGraph Vc` is the
lattice induced on the sites off `Vc`. Its reachability is the reachability of
`StatMech.Lattice.offSupport Vc` between off-walk sites, so its connected components are the
off-walk components. An inside site and an outside site (in the even–odd sense of
`jec_leftRegion Vc`) lie in different components.

A covering argument "if there are exactly two off-walk components, one of them is the inside" cannot
be used here: a nonempty inside always contains a vertex of `Vc`
(`StatMech.Lattice.oc_leftRegion_meets_support`), so the inside is never a set of off-walk sites.

## Main results

* `StatMech.Lattice.icc_induce_reachable_iff`: reachability in `fcb_offComplGraph Vc` is
  reachability off `Vc`.
* `StatMech.Lattice.icc_mem_offSupportComponent_iff`: equal components are membership in the same
  off-walk component.
* `StatMech.Lattice.icc_card_two_dichotomy`: in a type with two elements, every element is one of
  two given distinct elements.
* `StatMech.Lattice.icc_components_distinct`: inside and outside off-walk sites lie in different
  components.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}

/-- Two off-walk sites are reachable in `fcb_offComplGraph Vc` iff they are reachable in
`StatMech.Lattice.offSupport Vc`. -/
theorem icc_induce_reachable_iff (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} :
    (fcb_offComplGraph Vc).Reachable x y ↔ (offSupport Vc).Reachable (x : Site 2) (y : Site 2) :=
  ⟨fun h => fcb_induce_reachable_to_ambient Vc h, fun h => fcb_ambient_reachable_to_induce Vc h⟩

theorem icc_mem_offSupportComponent_iff (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} :
    (fcb_offComplGraph Vc).connectedComponentMk x = (fcb_offComplGraph Vc).connectedComponentMk y ↔
      (y : Site 2) ∈ offSupportComponent Vc (x : Site 2) := by
  rw [ConnectedComponent.eq, icc_induce_reachable_iff, mem_offSupportComponent]

/-- If `α` has exactly two elements and `a ≠ b`, every element of `α` is `a` or `b`. See also
`Nat.card_eq_two_iff` and `Nat.card_eq_two_iff'`. -/
theorem icc_card_two_dichotomy {α : Type*} (h : Nat.card α = 2) {a b : α} (hab : a ≠ b) (c : α) :
    c = a ∨ c = b := by
  classical
  have hfin : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype α := Fintype.ofFinite α
  by_contra hc
  push Not at hc
  obtain ⟨hca, hcb⟩ := hc
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hcb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hab, hca.symm⟩
  have hle : ({a, b, c} : Finset α).card ≤ Fintype.card α := Finset.card_le_univ _
  rw [Nat.card_eq_fintype_card] at h
  omega

/-- An inside and an outside off-walk site lie in different components of `fcb_offComplGraph Vc`:
off-walk paths keep the parity of the ray count. -/
theorem icc_components_distinct (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : {z : Site 2 // z ∉ Vc.support}}
    (hInMem : (sIn : Site 2) ∈ jec_leftRegion Vc) (hOutMem : (sOut : Site 2) ∉ jec_leftRegion Vc) :
    (fcb_offComplGraph Vc).connectedComponentMk sIn ≠
      (fcb_offComplGraph Vc).connectedComponentMk sOut := by
  rw [Ne, ConnectedComponent.eq, icc_induce_reachable_iff]
  intro hreach
  exact hOutMem (offSupport_component_monochromatic Vc hInMem hreach sIn.2)

end Lattice

end StatMech
