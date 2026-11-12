/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice









theorem jc8_one_le_of_not_even {n : ℕ} (h : ¬ Even n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · exact absurd (Nat.even_iff.mpr rfl) h
  · exact hp


















theorem jc8_crossCount_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) :=
  crossCount_parity S w





theorem jc8_crossCount_parity_eq_of_sameEndpoints (S : Set (Site 2)) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 :=
  crossCount_parity_eq_of_sameEndpoints S w₁ w₂




theorem jc8_crossCount_even_of_closed (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (crossCount S w) :=
  crossCount_even_of_loop S w












theorem jc8_crossCount_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) :=
  crossCount_odd_of_separated S hx hy w





theorem jc8_crossCount_ge_one_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    1 ≤ crossCount S w :=
  jc8_one_le_of_not_even (jc8_crossCount_odd_of_separated S hx hy w)














theorem jc8_orbitLoop_crossCount_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (S : Set (Site 2)) :
    Even (crossCount S (olb_orbitLoop K hK e he)) :=
  olb_orbitLoop_crossCount_even K hK e he S








theorem jc8_crossCount_odd_of_opposite_leftRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
    (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    ¬ Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w) :=
  jc8_crossCount_odd_of_separated (jec_leftRegion (olb_orbitLoop K hK e he)) hx hy w







theorem jc8_crossCount_ge_one_of_opposite_leftRegion (K : Set (Site 2)) (hK : K.Finite)
    (e : Dart) (he : IsBoundaryDart K e) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
    (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w :=
  jc8_one_le_of_not_even
    (jc8_crossCount_odd_of_opposite_leftRegion K hK e he w hx hy)






theorem jc8_leftRegion_sameSide_of_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (heven : Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w)) :
    (x ∈ jec_leftRegion (olb_orbitLoop K hK e he) ↔
      y ∈ jec_leftRegion (olb_orbitLoop K hK e he)) :=
  (jc8_crossCount_parity (jec_leftRegion (olb_orbitLoop K hK e he)) w).mp heven


















def jc8_CrossParityLeftRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  (∀ (S : Set (Site 2)) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y),
      Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S)) ∧
  (∀ {x y : Site 2} (w : (hypercubicLattice 2).Walk x y),
      x ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
      y ∉ jec_leftRegion (olb_orbitLoop K hK e he) →
      1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w)




theorem jc8_crossParityLeftRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc8_CrossParityLeftRegion K hK e he :=
  ⟨fun S {_x _y} w => jc8_crossCount_parity S w,
   fun {_x _y} w hx hy => jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w hx hy⟩










theorem jc8_crossCount_parity_self (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (crossCount S w) :=
  jc8_crossCount_even_of_closed S w





theorem jc8_leftRegion_loop_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he))
      (olb_orbitLoop K hK e he)) :=
  jc8_orbitLoop_crossCount_even K hK e he (jec_leftRegion (olb_orbitLoop K hK e he))






























end Walls

end StatMech
