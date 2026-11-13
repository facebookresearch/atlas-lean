/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {d : ℕ}










theorem kc6_beacon_mem_compl (hd : 1 ≤ d) (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R) :
    beacon d R ∈ Fᶜ :=
  exterior_subset_compl F R hF (beacon_mem_exterior R hd)





theorem kc6_beacon_component_infinite (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R) :
    (((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩).supp.Infinite := by
  classical
  set G := (hypercubicLattice d).induce Fᶜ with hG
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hF
  have hbext : beacon d R ∈ exterior d R := beacon_mem_exterior R (by omega)
  have : Infinite ↥(exterior d R) := (exterior_infinite R hd).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior d R) => (⟨(w : Site d), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
  · intro p q hpq; exact Subtype.ext (by simpa using congrArg Subtype.val hpq)
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R hd hsub (w : Site d) (beacon d R) w.2 hbext)
















theorem kc6_unique_infinite_component (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R) :
    ∃! C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent,
      C.supp.Infinite ∧ C = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
  classical
  have hCbinf :
      (((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩).supp.Infinite :=
    kc6_beacon_component_infinite hd F R hF
  refine ⟨((hypercubicLattice d).induce Fᶜ).connectedComponentMk
      ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩, ⟨hCbinf, rfl⟩, ?_⟩
  rintro C ⟨_, rfl⟩
  rfl





theorem kc6_infinite_iff_eq_beacon_component (hd : 2 ≤ d) (F : Set (Site d)) (hFfin : F.Finite)
    (R : ℕ) (hF : F ⊆ box d R)
    (C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent) :
    C.supp.Infinite ↔ C = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
      ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
  classical
  obtain ⟨C0, ⟨hC0inf, hC0uniq⟩⟩ := unique_infinite_component hd F hFfin
  have hCbinf :
      (((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩).supp.Infinite :=
    kc6_beacon_component_infinite hd F R hF
  have hCbC0 :
      ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ = C0 := hC0uniq _ hCbinf
  constructor
  · intro hCinf
    have hCC0 : C = C0 := hC0uniq _ hCinf
    rw [hCC0, ← hCbC0]
  · rintro rfl
    exact hCbinf












theorem kc6_infinite_iff_reachable_beacon (hd : 2 ≤ d) (F : Set (Site d)) (hFfin : F.Finite)
    (R : ℕ) (hF : F ⊆ box d R) {z : Site d} (hzmem : z ∈ Fᶜ) :
    (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite ↔
      ((hypercubicLattice d).induce Fᶜ).Reachable
        ⟨z, hzmem⟩ ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
  rw [kc6_infinite_iff_eq_beacon_component hd F hFfin R hF]
  exact ConnectedComponent.eq






theorem kc6_exterior_eq_beacon_component (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R)
    {z : Site d} (hz : z ∈ exterior d R) :
    ∃ hzmem : z ∈ Fᶜ,
      ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩ =
        ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
          ⟨beacon d R, kc6_beacon_mem_compl (by omega) F R hF⟩ := by
  classical
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hF
  have hbext : beacon d R ∈ exterior d R := beacon_mem_exterior R (by omega)
  refine ⟨hsub hz, ?_⟩
  exact ConnectedComponent.sound
    (exterior_reachable_compl F R hd hsub z (beacon d R) hz hbext)





theorem kc6_exterior_component_infinite (hd : 2 ≤ d) (F : Set (Site d)) (hFfin : F.Finite) (R : ℕ)
    (hF : F ⊆ box d R) {z : Site d} (hz : z ∈ exterior d R) :
    ∃ hzmem : z ∈ Fᶜ,
      (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
  obtain ⟨hzmem, heq⟩ := kc6_exterior_eq_beacon_component hd F R hF hz
  refine ⟨hzmem, ?_⟩
  rw [kc6_infinite_iff_eq_beacon_component hd F hFfin R hF]
  exact heq

end Walls

end StatMech
