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

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls














theorem kc2_crossCount_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) :=
  crossCount_parity S w




theorem kc2_crossCount_even_of_loop (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (crossCount S w) :=
  crossCount_even_of_loop S w





theorem kc2_crossCount_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) :=
  crossCount_odd_of_separated S hx hy w





theorem kc2_crossCount_parity_eq_of_sameEndpoints (S : Set (Site 2)) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 :=
  crossCount_parity_eq_of_sameEndpoints S w₁ w₂














theorem kc2_rayCount_eq_zero_farLeft (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hfar : ∀ p ∈ w.support, z 0 ≤ p 0) :
    jec_rayCount z w = 0 :=
  jec_rayCount_eq_zero_of_right z w hfar



theorem kc2_ray_even_farLeft (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hfar : ∀ p ∈ w.support, z 0 ≤ p 0) :
    Even (jec_rayCount z w) := by
  rw [kc2_rayCount_eq_zero_farLeft z w hfar]; exact ⟨0, rfl⟩







theorem kc2_not_mem_leftRegion_farLeft {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact kc2_ray_even_farLeft z Vc hfar





theorem kc2_ray_even_farRight {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2)
    (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
    Even (jec_rayCount z Vc) :=
  jec_ray_even_far Vc z hfar















theorem kc2_crossCountParity_node :
    (∀ (S : Set (Site 2)) (x y : Site 2) (w : (hypercubicLattice 2).Walk x y),
        Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2),
        (∀ p ∈ Vc.support, z 0 ≤ p 0) → z ∉ jec_leftRegion Vc) :=
  ⟨fun S _ _ w => kc2_crossCount_parity S w,
   fun _ Vc z hfar => kc2_not_mem_leftRegion_farLeft Vc z hfar⟩

end StatMech.Walls
