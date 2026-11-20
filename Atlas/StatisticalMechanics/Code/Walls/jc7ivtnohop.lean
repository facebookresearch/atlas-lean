/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Walls.jc6_ivt

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice


















theorem jc7_subStretch_visits_row (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (r : ℤ) (hr1 : min (u 1) (v 1) ≤ r) (hr2 : r ≤ max (u 1) (v 1)) :
    ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = r :=
  jc6_orbit_subStretch_visits_row K hK e he hu hv r hr1 hr2








theorem jc7_cannot_hop_over_cell (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (f : Site 2) (hf1 : min (u 1) (v 1) ≤ f 1) (hf2 : f 1 ≤ max (u 1) (v 1)) :
    ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = f 1 :=
  jc6_orbit_cannot_hop_over_cell K hK e he hu hv f hf1 hf2

















theorem jc7_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ :=
  jc6_orbit_subStretch_cannot_hop K hK e he hu hv ρ hmiss








theorem jc7_missedRow_sameSide (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    (ρ < u 1 ∧ ρ < v 1) ∨ (u 1 < ρ ∧ v 1 < ρ) := by
  rcases jc7_subStretch_cannot_hop K hK e he hu hv ρ hmiss with h | h
  · exact Or.inl (lt_min_iff.mp h)
  · exact Or.inr (max_lt_iff.mp h)










theorem jc7_orbit_step_coord_le_one (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {i : ℕ} (hi : i < (olb_orbitLoop K hK e he).length) (k : Fin 2) :
    (((olb_orbitLoop K hK e he).getVert i) k - ((olb_orbitLoop K hK e he).getVert (i + 1)) k).natAbs
      ≤ 1 :=
  jc6_orbit_step_coord_le_one K hK e he hi k











theorem jc7_walk_visits_row {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (r : ℤ) (hr1 : min (a 1) (b 1) ≤ r) (hr2 : r ≤ max (a 1) (b 1)) :
    ∃ p ∈ w.support, p 1 = r :=
  jc6_walk_visits_row w r hr1 hr2





theorem jc7_walk_cannot_hop {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (ρ : ℤ) (hmiss : ∀ p ∈ w.support, p 1 ≠ ρ) :
    ρ < min (a 1) (b 1) ∨ max (a 1) (b 1) < ρ :=
  jc6_walk_cannot_hop w ρ hmiss











theorem jc7_nonvacuous_middleRow : ∃ p ∈ jc6_vArc.support, p 1 = 1 :=
  jc6_ivt_nonvacuous_middleRow




theorem jc7_nonvacuous_cannotHop :
    (5 : ℤ) < min ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) ∨
      max ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) < (5 : ℤ) :=
  jc6_ivt_nonvacuous_cannotHop

























end Walls

end StatMech
