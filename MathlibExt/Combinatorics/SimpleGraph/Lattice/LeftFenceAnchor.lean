/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary

/-!
# The left fence orbit has a winding witness

Let `z₀` be a site in the leftmost column of a finite nonempty set `K` whose left neighbour is not
in `K`, and let `a` be the leftward dart at `z₀` (the *left fence*). The boundary orbit of `a`
contains `a` itself, so it has a vertical step left of the leftmost column; when its face loop is a
cycle, it therefore has a winding witness. For star hulls of finite sets face loops are cycles, so
every finite nonempty star hull has a boundary orbit with a winding witness, with no further
hypothesis.

## Main results

* `StatMech.Lattice.lfa_leftFence_anchor`: every finite nonempty set has a left fence dart.
* `StatMech.Lattice.lfa_leftFence_windingWitness`: the orbit of a left fence dart whose face loop
  is a cycle has a winding witness.
* `StatMech.Lattice.lfa_starHull_exists_windingWitness`: the star hull of a finite nonempty set
  has a boundary orbit with a winding witness.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Every finite nonempty set `K` has a site `z₀` in its leftmost column whose leftward dart is a
boundary dart. -/
theorem lfa_leftFence_anchor (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, IsBoundaryDart K (leftDart z₀) ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  obtain ⟨z₀, hz₀, hbd, _hdir, _htail, hmin⟩ := ocb_leftFence_data K hK hne
  exact ⟨z₀, hz₀, hbd, hmin⟩

/-- A dart lies on its own orbit. -/
theorem lfa_leftFence_on_own_orbit (K : Set (Site 2)) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (leftDart z₀)) :
    ∃ n : ℕ, (dartNext K)^[n] (⟨leftDart z₀, hbd⟩ : {e : Dart // IsBoundaryDart K e}).1
      = leftDart z₀ :=
  ⟨0, by simp⟩

/-- The orbit of the leftward dart at `z₀` has a vertical step in column `z₀ 0 - 1`. -/
theorem lfa_leftFence_reachesLeftmost (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (leftDart z₀)) (m : ℤ) (hm : z₀ 0 = m) :
    lmo_OrbitReachesLeftmost K ⟨leftDart z₀, hbd⟩ m :=
  ocb_reachesLeftmost_of_leftFence_on_orbit K hK ⟨leftDart z₀, hbd⟩ z₀ m hm
    (lfa_leftFence_on_own_orbit K z₀ hbd)

/-- The orbit of a left fence dart whose face loop is a cycle has a winding witness. -/
theorem lfa_leftFence_windingWitness (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (leftDart z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K ⟨leftDart z₀, hbd⟩).IsCycle) :
    wei_WindingWitness K ⟨leftDart z₀, hbd⟩ :=
  lmo_windingWitness_of_reachesLeftmost K ⟨leftDart z₀, hbd⟩ m hmin hcyc
    (lfa_leftFence_reachesLeftmost K hK z₀ hbd m hm)

/-- If the face loops of all left fence orbits of a finite nonempty set are cycles, some boundary
orbit has a winding witness. -/
theorem lfa_exists_anchor_windingWitness (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (hcyc : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart K (leftDart z₀),
      (mpl_orbitLoop K ⟨leftDart z₀, hbd⟩).IsCycle) :
    ∃ a : {e : Dart // IsBoundaryDart K e}, wei_WindingWitness K a := by
  obtain ⟨z₀, _hz₀, hbd, hmin⟩ := lfa_leftFence_anchor K hK hne
  exact ⟨⟨leftDart z₀, hbd⟩,
    lfa_leftFence_windingWitness K hK z₀ hbd (z₀ 0) rfl hmin (hcyc z₀ hbd)⟩

/-- The orbit of a left fence dart of a finite star hull, of length at least three, has a winding
witness. -/
theorem lfa_starHull_leftFence_windingWitness (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart (ndt_StarHull K) (leftDart z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ ndt_StarHull K, m ≤ w 0)
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨leftDart z₀, hbd⟩) :
    wei_WindingWitness (ndt_StarHull K) ⟨leftDart z₀, hbd⟩ :=
  lfa_leftFence_windingWitness (ndt_StarHull K) (starHull_finite K hK) z₀ hbd m hm hmin
    (shw_starHull_mpl_isCycle K ⟨leftDart z₀, hbd⟩ hp)

/-- If all left fence orbits of the star hull of a finite nonempty set have length at least three,
some boundary orbit has a winding witness. The length hypothesis always holds, see
`lfa_starHull_exists_windingWitness`. -/
theorem lfa_starHull_exists_anchor_windingWitness (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (hp : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart (ndt_StarHull K) (leftDart z₀),
      3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨leftDart z₀, hbd⟩) :
    ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e},
      wei_WindingWitness (ndt_StarHull K) a := by
  obtain ⟨z₀, _hz₀, hbd, hmin⟩ :=
    lfa_leftFence_anchor (ndt_StarHull K) (starHull_finite K hK) (sht_starHull_nonempty K hne)
  exact ⟨⟨leftDart z₀, hbd⟩,
    lfa_starHull_leftFence_windingWitness K hK z₀ hbd (z₀ 0) rfl hmin (hp z₀ hbd)⟩

/-- The star hull of a finite nonempty set has a boundary orbit with a winding witness: a site of
the star hull enclosed by the face loop of the orbit. -/
theorem lfa_starHull_exists_windingWitness (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) :
    ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e},
      wei_WindingWitness (ndt_StarHull K) a :=
  lfa_starHull_exists_anchor_windingWitness K hK hne
    (fun _ _ => shp_starHull_period_ge_three K hK _)

/-- If the face loop of the orbit encloses some site and encloses only sites of `K`, the orbit has a
winding witness. -/
theorem lfa_windingWitness_of_interiorSubset_and_enclosed (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hint : eaw_InteriorSubset K a)
    (henc : ∃ z : Site 2, ¬ Even (jec_rayCount z (mpl_orbitLoop K a))) :
    wei_WindingWitness K a := by
  obtain ⟨z, hz⟩ := henc
  exact ⟨z, hint z hz, hz⟩

/-- The leftward dart at the origin is a boundary dart of the unit cell. -/
theorem lfa_unitCell_leftFence_isBoundaryDart :
    IsBoundaryDart unitCell (leftDart (![0, 0] : Site 2)) := by
  apply lmo_leftDartAt_isBoundaryDart
  · rw [unitCell, Set.mem_singleton_iff]
  · rw [unitCell, Set.mem_singleton_iff]
    intro h
    have := congrFun h 0
    simp at this

/-- The left fence orbit of the unit cell has a vertical step in column `-1`. -/
theorem lfa_unitCell_leftFence_reachesLeftmost :
    lmo_OrbitReachesLeftmost unitCell ⟨leftDart (![0, 0] : Site 2),
      lfa_unitCell_leftFence_isBoundaryDart⟩ 0 :=
  lfa_leftFence_reachesLeftmost unitCell (Set.finite_singleton _) (![0, 0] : Site 2)
    lfa_unitCell_leftFence_isBoundaryDart 0 (by simp)

end Lattice

end StatMech
