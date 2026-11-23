/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ClosedContourSeparation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitExteriorEven

/-!
# Sites inside a boundary orbit loop have odd ray count

If some site has odd ray count with respect to the face loop of a boundary orbit, every site joined
to it by a path avoiding the loop also has odd ray count. Combined with `OrbitExteriorEven`, if the
sites of `K` are joined to an odd site and the sites outside `K` to a far site avoiding the loop,
then `K` is exactly the inside of the loop (`ccs_OrbitIsLoop K`).

## Main results

* `StatMech.Lattice.ooi_odd_of_connected_to_odd`: odd ray parity spreads along paths avoiding the
  loop.
* `StatMech.Lattice.ooi_insideHalf_of_oddWitness`: under that connectivity, all sites of `K` have
  odd ray count.
* `StatMech.Lattice.ooi_orbitIsLoop_of_witness`: both halves together give `ccs_OrbitIsLoop K`.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

theorem ooi_odd_of_connected_to_odd {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support)
    (hodd : ¬ Even (jec_rayCount z0 Vc)) :
    ¬ Even (jec_rayCount z Vc) :=
  fun hez => hodd ((oee_rayParity_const_along_walk Vc p hp).mp hez)

theorem ooi_insideHalf_of_oddWitness (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {z0 : Site 2}
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  intro z hz
  obtain ⟨p, hp⟩ := hInt z hz
  exact ooi_odd_of_connected_to_odd (olb_orbitLoop K hK e he) p hp hodd0

theorem ooi_orbitIsLoop_of_witness (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (_hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
    ccs_OrbitIsLoop K :=
  ⟨_, olb_orbitLoop K hK e he,
    ooi_insideHalf_of_oddWitness K hK e he hodd0 hInt,
    oee_outsideHalf_of_exteriorEq K hK e he hExt⟩

end Lattice

end StatMech
