/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitTailWindingWitness

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitTailWindingWitness`

* Not covered: `jsp_OrbitWinds` fails for the unit cell (Stage B) and no instance is proved for a
  larger set. The definition is checked to unfold as stated.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitTailWindingWitness

example (K : Set (Site 2)) (hK : K.Finite) (a : {e : Dart // IsBoundaryDart K e}) :
    jsp_OrbitWinds K hK a ↔ ∃ (i : ℕ) (z₀ : Site 2)
      (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀),
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support) ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := Iff.rfl

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitTailWindingWitness
