/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.LexMinOrientation

/-!
# Orbits that pass the left fence have winding witnesses

Take a site `z₀` of a finite set `K` in the leftmost column of `K` with no site of `K` directly to
its left; the leftward dart `leftDart z₀` is then a boundary dart (the *left fence*). If the
boundary orbit of `a` passes through the left fence and its face loop is a cycle, the orbit has a
leftmost vertical step coming from a leftward dart, hence a winding witness.

The orbit of `a` passes through the left fence iff the heads of `a` and of the left fence lie in
the same component of the complement of `K`, provided `K` is `InterfaceConnected`. For star
hulls this gives a winding witness for every orbit whose heads reach the left fence in the
complement, under `InterfaceConnected`. That hypothesis fails for disconnected sets (two
separated sites share the outer complement component but have different boundary orbits), so the
star hull result applies to connected configurations; it is satisfied by a single site.

## Main results

* `StatMech.Lattice.ocb_leftFence_data`: every finite nonempty set has a left fence dart in its
  leftmost column.
* `StatMech.Lattice.ocb_windingWitness_of_leftFence_on_orbit`: an orbit through the left fence
  whose face loop is a cycle has a winding witness.
* `StatMech.Lattice.ocb_leftFence_on_orbit_iff_headSameComponent`: for interface-connected sets,
  the orbit passes the left fence iff its heads reach the fence head in the complement.
* `StatMech.Lattice.ocb_starHull_windingWitness_of_interfaceConnected`: the star hull version.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Every finite nonempty set `K` has a site `z₀` in its leftmost column whose leftward dart is a
boundary dart. -/
theorem ocb_leftFence_data (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, IsBoundaryDart K (leftDart z₀) ∧ (leftDart z₀).dir = ![-1, 0] ∧
      (leftDart z₀).tail 0 = z₀ 0 ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  obtain ⟨z₀, hz₀, hwest, _hsouth, hmin⟩ := lmo_lexMinCell K hK hne
  refine ⟨z₀, hz₀, lmo_leftDartAt_isBoundaryDart hz₀ hwest, leftDart_dir z₀, ?_, hmin⟩
  rw [leftDart_tail]

/-- A dart on the orbit of `a` is reached within one period. -/
theorem ocb_on_orbit_index_lt_period (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {e : Dart} {n : ℕ}
    (hn : (dartNext K)^[n] a.1 = e) :
    ∃ k < dartOrbitPeriod K a, (dartNext K)^[k] a.1 = e := by
  have hpos : 0 < dartOrbitPeriod K a := dartOrbitPeriod_pos K hK a
  refine ⟨n % dartOrbitPeriod K a, Nat.mod_lt _ hpos, ?_⟩
  have hsub : (dartNextSub K)^[n % dartOrbitPeriod K a] a = (dartNextSub K)^[n] a := by
    have := Function.iterate_mod_minimalPeriod_eq (f := dartNextSub K) (x := a)
      (n := n)
    simp only [dartOrbitPeriod]; exact this
  have hval := congrArg Subtype.val hsub
  rw [dartNextSub_iterate_val, dartNextSub_iterate_val] at hval
  rw [hval, hn]

/-- If the orbit of `a` passes through the leftward dart at `z₀`, it has a vertical step in column
`z₀ 0 - 1`. -/
theorem ocb_reachesLeftmost_of_leftFence_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z₀ : Site 2) (m : ℤ) (hm : z₀ 0 = m)
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = leftDart z₀) :
    lmo_OrbitReachesLeftmost K a m := by
  obtain ⟨n, hn⟩ := hon
  obtain ⟨k, hk, hke⟩ := ocb_on_orbit_index_lt_period K hK a hn
  refine lmo_reachesLeftmost_of_left_tail K a m hk ?_ ?_
  · rw [hke, leftDart_tail, hm]
  · rw [hke, leftDart_dir]

/-- An orbit whose face loop is a cycle and which passes through the leftward dart at a site of the
leftmost column has a winding witness. -/
theorem ocb_windingWitness_of_leftFence_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z₀ : Site 2) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K a).IsCycle)
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = leftDart z₀) :
    wei_WindingWitness K a :=
  lmo_windingWitness_of_reachesLeftmost K a m hmin hcyc
    (ocb_reachesLeftmost_of_leftFence_on_orbit K hK a z₀ m hm hon)

/-- If the orbit of `a` passes through the left fence, the heads of `a` and of the fence lie in the
same component of the complement. -/
theorem ocb_leftFence_head_sameComponent_of_on_orbit {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (leftDart z₀))
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = leftDart z₀) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨a.1.head, a.2.2⟩ ⟨(leftDart z₀).head, hbd.2⟩ := by
  obtain ⟨n, hn⟩ := hon
  exact dartNext_orbit_head_sameComponent K a.1 (leftDart z₀) a.2 hbd hn

/-- For an interface-connected set, if the heads of `a` and of the left fence lie in the same
component of the complement, the orbit of `a` passes through the fence. -/
theorem ocb_leftFence_on_orbit_of_sameComponent {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (leftDart z₀))
    (hInt : InterfaceConnected K)
    (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨a.1.head, a.2.2⟩ ⟨(leftDart z₀).head, hbd.2⟩) :
    ∃ n : ℕ, (dartNext K)^[n] a.1 = leftDart z₀ :=
  hInt a.1 (leftDart z₀) a.2 hbd hcomp

/-- For an interface-connected set, the orbit of `a` passes through the left fence iff the heads of
`a` and of the fence lie in the same component of the complement. -/
theorem ocb_leftFence_on_orbit_iff_headSameComponent {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (leftDart z₀))
    (hInt : InterfaceConnected K) :
    (∃ n : ℕ, (dartNext K)^[n] a.1 = leftDart z₀)
      ↔ ((hypercubicLattice 2).induce Kᶜ).Reachable
          ⟨a.1.head, a.2.2⟩ ⟨(leftDart z₀).head, hbd.2⟩ :=
  ⟨ocb_leftFence_head_sameComponent_of_on_orbit a hbd,
    ocb_leftFence_on_orbit_of_sameComponent a hbd hInt⟩

/-- A boundary orbit of length at least three of the star hull of a finite nonempty set has a
winding witness, provided the star hull is `InterfaceConnected` and the heads of the orbit reach
the head of every left fence dart in the complement. `InterfaceConnected` fails when the star
hull is disconnected; the reachability hypothesis fails for orbits around holes. -/
theorem ocb_starHull_windingWitness_of_interfaceConnected (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (hInt : InterfaceConnected (ndt_StarHull K)) :
    (∀ (z₀ : Site 2) (hbd : IsBoundaryDart (ndt_StarHull K) (leftDart z₀)),
        z₀ ∈ ndt_StarHull K → (∀ w ∈ ndt_StarHull K, z₀ 0 ≤ w 0) →
        ((hypercubicLattice 2).induce (ndt_StarHull K)ᶜ).Reachable
          ⟨a.1.head, a.2.2⟩ ⟨(leftDart z₀).head, hbd.2⟩) →
      wei_WindingWitness (ndt_StarHull K) a := by
  intro hreach
  have hSK : (ndt_StarHull K).Finite := starHull_finite K hK
  obtain ⟨z₀, hz₀, hbd, _hdir, _htail, hmin⟩ := ocb_leftFence_data (ndt_StarHull K) hSK
    (sht_starHull_nonempty K hne)
  have hcyc : (mpl_orbitLoop (ndt_StarHull K) a).IsCycle := shw_starHull_mpl_isCycle K a hp
  have hcomp := hreach z₀ hbd hz₀ hmin
  have hon : ∃ n : ℕ, (dartNext (ndt_StarHull K))^[n] a.1 = leftDart z₀ :=
    ocb_leftFence_on_orbit_of_sameComponent a hbd hInt hcomp
  exact ocb_windingWitness_of_leftFence_on_orbit (ndt_StarHull K) hSK a z₀ (z₀ 0) rfl hmin hcyc hon

end Lattice

end StatMech
