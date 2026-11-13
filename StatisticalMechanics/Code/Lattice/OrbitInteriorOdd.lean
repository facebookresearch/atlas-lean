/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.ClosedContourSeparation

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
