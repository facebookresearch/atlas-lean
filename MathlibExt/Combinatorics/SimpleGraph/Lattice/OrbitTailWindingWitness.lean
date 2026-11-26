/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness

/-!
# Winding witnesses from a tail joined to an odd site

Let `olb_orbitLoop K hK e he` be the face loop of the boundary orbit of a dart `e` of a finite set
`K` of sites. The parity of the ray count is constant along lattice paths avoiding the loop. Hence
if the tail of some dart of the orbit is joined, avoiding the loop, to a site of odd ray count
(`jsp_OrbitWinds`), that tail has odd ray count; since tails of boundary darts lie in `K`, this is
a winding witness: a site of `K` inside the loop.

Faces are labelled by their lower left corners, so "avoiding the loop" means that the path never
visits a site whose upper right face is on the loop. For the unit cell the only tail is the origin,
whose upper right face is on the loop, so `jsp_OrbitWinds` fails there.

The two-component form of the discrete Jordan curve theorem for closed walks is
`StatMech.Lattice.ccs_closedLoop_two_components`.

## Main definitions

* `StatMech.Lattice.jsp_OrbitWinds K hK a`: some orbit tail is joined off the loop to a site of odd
  ray count.

## Main results

* `StatMech.Lattice.jsp_tailOdd_of_orbitWinds`: `jsp_OrbitWinds` gives an orbit tail with odd ray
  count.
* `StatMech.Lattice.jsp_winding_witness_of_orbitWinds`: `jsp_OrbitWinds` gives a site of `K` with
  odd ray count.
-/

@[expose] public section

open SimpleGraph Function Set

namespace StatMech

namespace Lattice

/-- If the tail of the `i`-th dart of the orbit is joined, by a path avoiding the face loop, to a
site of odd ray count, then that tail has odd ray count. -/
theorem jsp_tailOdd_of_oddCell_reaches_tail (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2} (i : ℕ)
    (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
    (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
    wwit_TailOdd K hK a :=
  ⟨i, ooi_odd_of_connected_to_odd (olb_orbitLoop K hK a.1 a.2) p hp hodd⟩

/-- The tail of some dart of the orbit of `a` is joined, by a lattice path avoiding the face loop,
to a site of odd ray count. This fails for the unit cell, whose only tail lies on its loop. -/
def jsp_OrbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ (i : ℕ) (z₀ : Site 2) (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀),
    (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support) ∧
    ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))

/-- `jsp_OrbitWinds` gives a dart of the orbit whose tail has odd ray count. -/
theorem jsp_tailOdd_of_orbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hwind : jsp_OrbitWinds K hK a) :
    wwit_TailOdd K hK a := by
  obtain ⟨i, z₀, p, hp, hodd⟩ := hwind
  exact jsp_tailOdd_of_oddCell_reaches_tail K hK a i p hp hodd

/-- `jsp_OrbitWinds` gives a winding witness: a site of `K` with odd ray count with respect to the
face loop. -/
theorem jsp_winding_witness_of_orbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hwind : jsp_OrbitWinds K hK a) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) :=
  wwit_winding_witness_of_tailOdd K hK a (jsp_tailOdd_of_orbitWinds K hK a hwind)

end Lattice

end StatMech
