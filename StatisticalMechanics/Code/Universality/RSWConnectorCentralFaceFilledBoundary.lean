/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceJordan
import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Lattice.PeierlsContourFinal
import Code.Ising.KWGeometricDual
import Code.Walls.fwrfaceregion












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box
open StatMech.Walls

noncomputable section



theorem rlc_centralFaceReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (w : (openSubgraphInduce 2
      (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈
        rlc_connectorCentralFaceReachSet gamma gamma' rho,
      ((hypercubicLattice 2).induce
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_connectorCentralFaceReachSet gamma gamma' rho :=
        rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩


theorem rlc_connectorCentralFaceReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨huBox, huSource⟩ := hu
  obtain ⟨hvBox, hvSource⟩ := hv
  have hsource : (rlc_connectorRightAnchor gamma : Site 2) ∈
      rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    ⟨(rlc_connectorRightAnchor gamma).2, Reachable.refl _⟩
  obtain ⟨hu', huLift⟩ := rlc_centralFaceReachSet_openWalk_lift
    gamma gamma' rho hu0 huSource.some.reverse
  obtain ⟨hv', hvLift⟩ := rlc_centralFaceReachSet_openWalk_lift
    gamma gamma' rho hsource hvSource.some
  have huEq :
      (⟨(rlc_connectorRightAnchor gamma : Site 2), hu'⟩ :
        rlc_connectorCentralFaceReachSet gamma gamma' rho) =
      ⟨(rlc_connectorRightAnchor gamma : Site 2), hsource⟩ := rfl
  have hvEq :
      (⟨v, hv'⟩ : rlc_connectorCentralFaceReachSet gamma gamma' rho) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at huLift
  rw [hvEq] at hvLift
  exact huLift.trans hvLift

theorem rlc_connectorCentralFaceReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorCentralFaceReachSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h



noncomputable def rlc_connectorCentralFaceExteriorComponent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).ConnectedComponent :=
  Classical.choose (unique_infinite_component (by norm_num)
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho))

theorem rlc_connectorCentralFaceExteriorComponent_infinite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorCentralFaceExteriorComponent gamma gamma' rho).supp.Infinite :=
  (Classical.choose_spec (unique_infinite_component (by norm_num)
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho))).1


def rlc_connectorCentralFaceExteriorSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Set (Site 2) :=
  {z | ∃ hz : z ∈
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ,
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).connectedComponentMk
        ⟨z, hz⟩ =
      rlc_connectorCentralFaceExteriorComponent gamma gamma' rho}


def rlc_connectorCentralFaceFilledReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Set (Site 2) :=
  (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)ᶜ

theorem rlc_connectorCentralFaceReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceReachSet gamma gamma' rho ⊆
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  intro z hz hExt
  exact hExt.1 hz

theorem rlc_connectorCentralFaceExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    hpExt⟩

theorem rlc_connectorCentralFaceFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho).Finite := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  apply (box_finite 2 R).subset
  intro z hzFill
  by_contra hzBox
  have hzExt : z ∈ exterior 2 R := by
    rw [exterior_eq_compl_box]
    exact hzBox
  have hzNotK : z ∈ Kᶜ := exterior_subset_compl K R hR hzExt
  have hzInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hzExt
  have hzComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
        hzInf
        (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
  exact hzFill ⟨hzNotK, hzComp⟩




theorem rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  have hKRect : K ⊆ rect (-2 * n) (2 * n) (-n) n := by
    rintro z ⟨hz, _⟩
    exact hz
  have promote {z q : Site 2}
      (hzNot : z ∈ Kᶜ) (hqExt : q ∈ exterior 2 R)
      (hzq : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, exterior_subset_compl K R hR hqExt⟩) :
      z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    let hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩).supp.Infinite :=
      exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
    have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩ =
          rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
      (unique_infinite_component (by norm_num) K
        (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
          hqInf
          (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
    exact ⟨hzNot, (ConnectedComponent.sound hzq).trans hqComp⟩
  intro z hzFill
  rw [mem_rect]
  by_contra hzRect
  have hzCases : z 0 < -2 * n ∨ 2 * n < z 0 ∨
      z 1 < -n ∨ n < z 1 := by
    omega
  have hzNot : z ∈ Kᶜ := by
    intro hzK
    exact hzRect (by simpa [mem_rect] using hKRect hzK)
  rcases hzCases with hzLeft | hzRight | hzBottom | hzTop
  · let c : Int := z 0 - R - 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht
      intro htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 0 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 0 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 0 + R + 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht
      intro htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 0 ≤ c := by dsimp only [c]; omega
      have htBounds : z 0 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 - R - 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht
      intro htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 1 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 1 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 + R + 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht
      intro htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 1 ≤ c := by dsimp only [c]; omega
      have htBounds : z 1 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))


theorem rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_connectorCentralFaceFilledReachSet,
            Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_connectorCentralFaceFilledReachSet,
            Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_connectorCentralFaceExteriorSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h

private theorem rlc_centralFace_walk_first_exit_set
    (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (a b : Site 2) (p : (hypercubicLattice 2).Walk x a),
      (hypercubicLattice 2).Adj a b ∧
        (∀ z ∈ p.support, z ∈ A) ∧ b ∉ A := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · obtain ⟨u, v, q, huv, hq, hv⟩ := ih hb hy
        refine ⟨u, v, Walk.cons hab q, huv, ?_, hv⟩
        simp only [SimpleGraph.Walk.support_cons, List.forall_mem_cons]
        exact ⟨hx, hq⟩
      · exact ⟨a, b, Walk.nil, hab, by simpa, hb⟩


theorem rlc_connectorCentralFaceFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    ∃ z : Site 2,
      ∃ hz : z ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho,
      ((hypercubicLattice 2).induce
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_connectorCentralFaceReachSet_subset_filled
            gamma gamma' rho hz⟩ := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_centralFace_walk_first_exit_set A w huA hkNotA
  have haA : a ∈ A := hqA a q.end_mem_support
  obtain ⟨haNotK, hua⟩ := haA
  have hbK : b ∈ K := by
    by_contra hbNotK
    have habK : ((hypercubicLattice 2).induce Kᶜ).Adj
        ⟨a, haNotK⟩ ⟨b, hbNotK⟩ := hab
    exact hbNotA ⟨hbNotK, hua.trans habK.reachable⟩
  have hAinH : A ⊆ H := by
    intro z hzA hzExt
    obtain ⟨hzNotK, huz⟩ := hzA
    obtain ⟨_hzNotK', hzComp⟩ := hzExt
    have huComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨u, huK⟩ =
          rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩

theorem rlc_connectorCentralFaceFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_connectorCentralFaceFilledReachSet_reaches_reachSet
      gamma gamma' rho hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_connectorCentralFaceFilledReachSet_reaches_reachSet
      gamma gamma' rho hv
  have hmiddle := (rlc_connectorCentralFaceReachSet_reachable
    gamma gamma' rho hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_connectorCentralFaceReachSet_subset_filled
          gamma gamma' rho)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorCentralFaceFilledReachSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h


theorem rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FaceBoundaryConnected
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
      (phb_boundarySupport
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
        (rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho)) := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
      gamma gamma' rho ha hb
  · intro a b ha hb
    apply rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
      gamma gamma' rho
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using ha
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using hb




theorem rlc_connectorCentralFaceFilledBoundary_degree_eq_two
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).degree f = 2 := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryGraph_degree_eq_two_of_connected_complement
    H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
      gamma gamma' rho ha hb
  · intro a b ha hb
    apply rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using ha
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using hb
  · exact hf




theorem rlc_connectorCentralFaceFilledBoundary_isCycles
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).IsCycles := by
  intro f hf
  have hfSupport : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support := by
    obtain ⟨g, hfg⟩ := hf
    exact hfg.mem_support_left
  rw [Set.ncard_eq_toFinset_card']
  exact rlc_connectorCentralFaceFilledBoundary_degree_eq_two
    gamma gamma' rho hfSupport





theorem rlc_isCycle_of_isCycles_isTrail
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {v : V} (c : G.Walk v v) (hcycles : G.IsCycles)
    (hcne : c ≠ .nil) (hcTrail : c.IsTrail) : c.IsCycle := by
  let p := c.cycleBypass
  have hpCycle : p.IsCycle := hcTrail.isCycle_cycleBypass hcne
  have hpStep {a b : V} (ha : a ∈ p.support) (hab : G.Adj a b) :
      s(a, b) ∈ p.edges := by
    have haVerts : a ∈ p.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using ha
    have habSub : p.toSubgraph.Adj a b :=
      (hpCycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
    exact p.adj_toSubgraph_iff_mem_edges.mp habSub
  have walk_subset {a b : V} (w : G.Walk a b)
      (ha : a ∈ p.support) :
      w.edges ⊆ p.edges ∧ b ∈ p.support := by
    induction w with
    | nil => exact ⟨by simp, ha⟩
    | @cons a b d hab w ih =>
        have habP : s(a, b) ∈ p.edges := hpStep ha hab
        have hb : b ∈ p.support :=
          p.snd_mem_support_of_mem_edges habP
        have hi := ih hb
        constructor
        · intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          exact he.elim (fun h => h ▸ habP) (fun h => hi.1 h)
        · exact hi.2
  have hcSubset : c.edges ⊆ p.edges :=
    (walk_subset c p.start_mem_support).1
  have hpSubset : p.edges ⊆ c.edges := by
    exact SimpleGraph.Walk.edges_cycleBypass_subset
  have hcp : c.edges.length ≤ p.edges.length := by
    rw [← List.toFinset_card_of_nodup hcTrail.edges_nodup,
      ← List.toFinset_card_of_nodup hpCycle.edges_nodup]
    exact Finset.card_le_card (by
      intro e he
      exact List.mem_toFinset.mpr (hcSubset (List.mem_toFinset.mp he)))
  have hpc : p.edges.length ≤ c.edges.length := by
    rw [← List.toFinset_card_of_nodup hpCycle.edges_nodup,
      ← List.toFinset_card_of_nodup hcTrail.edges_nodup]
    exact Finset.card_le_card (by
      intro e he
      exact List.mem_toFinset.mpr (hpSubset (List.mem_toFinset.mp he)))
  have hlength : p.length = c.length := by
    rw [← SimpleGraph.Walk.length_edges, ← SimpleGraph.Walk.length_edges]
    omega
  cases c with
  | nil => exact False.elim (hcne rfl)
  | @cons a b h hab w =>
      have hbypassLength : w.length ≤ w.bypass.length := by
        dsimp only [p, SimpleGraph.Walk.cycleBypass] at hlength
        simpa using hlength.ge
      have hbypass : w.bypass = w :=
        w.bypass_eq_self_of_length_le hbypassLength
      rw [SimpleGraph.Walk.isCycle_def]
      refine ⟨hcTrail, by simp, ?_⟩
      simpa [hbypass] using w.bypass_isPath.support_nodup



theorem rlc_connectorCentralFaceFilledBoundary_other_neighbor
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
    ∃ b : Site 2,
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧
      u ≠ b := by
  let G := faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  have hvSupport : v ∈ G.support := huv.mem_support_right
  have hdegree : G.degree v = 2 :=
    rlc_connectorCentralFaceFilledBoundary_degree_eq_two
      gamma gamma' rho hvSupport
  by_contra hnone
  push Not at hnone
  have hsub : G.neighborFinset v ⊆ {u} := by
    intro b hb
    simp only [Finset.mem_singleton]
    exact (hnone b (SimpleGraph.mem_neighborFinset G v b |>.mp hb)).symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree,
    hdegree] at hcard
  omega



theorem rlc_connectorCentralFaceFilledBoundary_existsUnique_other_neighbor
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
    ∃! b : Site 2,
      u ≠ b ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b := by
  exact (rlc_connectorCentralFaceFilledBoundary_isCycles
    gamma gamma' rho).existsUnique_ne_adj huv.symm


theorem rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hp : p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hq : q ∉ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  by_contra hpK
  have hqExt : q ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩

theorem rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · have hq : q ∉
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := hpq.2.mp hp
    have hpK := rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
      gamma gamma' rho hp hq hpq.1
    have hqK : q ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      intro hqK
      exact hq (rlc_connectorCentralFaceReachSet_subset_filled
        gamma gamma' rho hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
      gamma gamma' rho hq hp hpq.1.symm
    have hpK : p ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      intro hpK
      exact hp (rlc_connectorCentralFaceReachSet_subset_filled
        gamma gamma' rho hpK)
    simp [hpK, hqK]



theorem rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ≤
      faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach :=
    rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet
      gamma gamma' rho hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2




theorem rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  have hfgReach : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g :=
    rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' rho hfg
  intro htrace
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfgReach.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfgReach.2
  rcases Finset.mem_union.mp htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 (hpq ▸ hright)
    have hpReach := rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hends.1
    have hqReach := rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hends.2
    exact (hpqBoundary.2.mp hpReach) hqReach
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 (hpq ▸ hleft)
    have hpNot := rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hends.1
    have hqNot := rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hends.2
    exact hpNot (hpqBoundary.2.mpr hqNot)



theorem rlc_connectorCentralFaceFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        f g := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  have hconn :=
    rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
      gamma gamma' rho
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom







structure RlcCentralFaceLowestFilledAxisGap {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  height : Int
  height_lower : (gamma.1.1 : Site 2) 1 ≤ height
  height_upper : height < (gamma'.1.2.1 : Site 2) 1
  axis_inside : ![0, height] ∈
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  axis_outside : ![0, height + 1] ∉
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  axis_below_inside : ∀ s : Int,
    (gamma.1.1 : Site 2) 1 ≤ s → s ≤ height →
      ![0, s] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  boundary : ((![0, height], ![0, height + 1]) ∈ edgeBoundary 2
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))




theorem rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 →
        ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)) := by
  classical
  let lower := (gamma.1.1 : Site 2) 1
  let upper := (gamma'.1.2.1 : Site 2) 1
  let S := rlc_connectorCentralFaceReachSet gamma gamma' rho
  have hlowerLt : lower < upper := by
    have hright := hposition.right_axis_strict
    have hleft := hposition.left_axis_strict
    dsimp [lower, upper]
    omega
  have hlowerPath : (![0, lower] : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    have haxis : (gamma.1.1 : Site 2) = ![0, lower] := by
      ext i
      fin_cases i <;> simp [lower, gamma.1.1.2.2]
    rw [← haxis]
    exact rlc_path_start_mem_vertices gamma.1
  have hupperPath : (![0, upper] : Site 2) ∈
      rlc_pathVertices gamma'.1 := by
    have haxis : (gamma'.1.2.1 : Site 2) = ![0, upper] := by
      ext i
      fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
    rw [← haxis]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hlower : (![0, lower] : Site 2) ∈ S :=
    rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hlowerPath
  have hupper : (![0, upper] : Site 2) ∉ S :=
    rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hupperPath
  let A : Finset Int := (Finset.Icc lower upper).filter
    (fun t => ![0, t] ∈ S)
  have hlowerA : lower ∈ A := by
    simp [A, hlower, le_of_lt hlowerLt]
  have hA : A.Nonempty := ⟨lower, hlowerA⟩
  let t := A.max' hA
  have htA : t ∈ A := A.max'_mem hA
  have htBounds : lower ≤ t ∧ t ≤ upper := by
    simpa [A] using (Finset.mem_filter.mp htA).1
  have htS : ![0, t] ∈ S := (Finset.mem_filter.mp htA).2
  have htlt : t < upper := by
    apply lt_of_le_of_ne htBounds.2
    intro h
    exact hupper (h ▸ htS)
  have habove : ∀ s : Int, t < s → s ≤ upper → ![0, s] ∉ S := by
    intro s hts hsu hsS
    have hsA : s ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hsu⟩, hsS⟩
    have hmax := A.le_max' s hsA
    change s ≤ t at hmax
    omega
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htBounds.1, htlt, htS, habove,
    ⟨hadj, iff_of_true htS (habove (t + 1) (by omega) (by omega))⟩⟩





theorem rlc_centralFace_verticalGap_outside_mem_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 →
        ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      ![0, t + 1] ∈
        rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
  classical
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨t, htLower, htUpper, htIn, habove, _htBoundary⟩ :=
    rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure
      gamma gamma' hposition rho hno
  let upper := (gamma'.1.2.1 : Site 2) 1
  let leftStart := (gamma'.1.1 : Site 2)
  have hupperCoord : (![0, upper] : Site 2) = gamma'.1.2.1 := by
    ext i
    fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
  have hleftStartCoord : leftStart = ![-2 * n, leftStart 1] := by
    have hs := gamma'.1.1.2
    rw [mem_leftSide] at hs
    ext i
    fin_cases i <;> simp [leftStart, hs.2]
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  have hrightEndK : (gamma.1.2.1 : Site 2) ∈ K :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_connector_path_end_mem_vertices gamma.1)
  have hrightEndBox := hR hrightEndK
  have hrightEndX : (gamma.1.2.1 : Site 2) 0 = 2 * n := by
    exact gamma.1.2.1.2.2
  have hnR : 2 * n ≤ (R : Int) := by
    rw [mem_box] at hrightEndBox
    have h0 := hrightEndBox 0
    rw [hrightEndX] at h0
    have h0' : ((2 * n).natAbs : Int) ≤ (R : Int) := by
      exact_mod_cast h0
    exact le_trans Int.le_natAbs h0'
  let far : Site 2 := ![-((R : Int) + 1), 0]
  have hfarExt : far ∈ exterior 2 R := by
    simpa [far] using axisFarLeft_mem_exterior R
  have hfarNotK : far ∈ Kᶜ := exterior_subset_compl K R hR hfarExt
  let wAxis : (hypercubicLattice 2).Walk ![0, t + 1]
      (gamma'.1.2.1 : Site 2) :=
    (sw_vertSeg 0 (t + 1) upper).copy rfl hupperCoord
  let wLeft : (hypercubicLattice 2).Walk
      (gamma'.1.2.1 : Site 2) leftStart :=
    (rlc_ambientCrossingWalk gamma'.1).reverse
  let wHoriz : (hypercubicLattice 2).Walk leftStart
      ![-((R : Int) + 1), leftStart 1] :=
    (sw_horizSeg (leftStart 1) (-2 * n) (-((R : Int) + 1))).copy
      hleftStartCoord.symm rfl
  let wVert : (hypercubicLattice 2).Walk
      ![-((R : Int) + 1), leftStart 1] far :=
    (sw_vertSeg (-((R : Int) + 1)) (leftStart 1) 0).copy rfl rfl
  let w := ((wAxis.append wLeft).append wHoriz).append wVert
  have hwNot : ∀ z ∈ w.support, z ∈ Kᶜ := by
    intro z hz
    dsimp only [w] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with ((hzAxis | hzLeft) | hzHoriz) | hzVert
    · change z ∈ ((sw_vertSeg 0 (t + 1) upper).copy _ _).support at hzAxis
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzAxis
      obtain ⟨s, hs, rfl⟩ := hzAxis
      rw [Set.mem_uIcc, Or.comm] at hs
      rcases hs with hs | hs
      · exact habove s (by omega) (by omega)
      · exact habove s (by omega) (by omega)
    · have hzPath : z ∈ rlc_pathVertices gamma'.1 :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 z).1 (by
            simpa [wLeft, SimpleGraph.Walk.support_reverse] using hzLeft)
      exact rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno hzPath
    · change z ∈ ((sw_horizSeg (leftStart 1) (-2 * n)
          (-((R : Int) + 1))).copy _ _).support at hzHoriz
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzHoriz
      obtain ⟨s, hs, rfl⟩ := hzHoriz
      rw [Set.mem_uIcc] at hs
      have hsle : s ≤ -2 * n := by
        rcases hs with hs | hs <;> omega
      intro hzK
      have hzRect := hzK.1
      rw [mem_rect] at hzRect
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzRect
      have hseq : s = -2 * n := by omega
      have hzEq : (![s, leftStart 1] : Site 2) = leftStart := by
        calc
          (![s, leftStart 1] : Site 2) = ![-2 * n, leftStart 1] := by
            rw [hseq]
          _ = leftStart := hleftStartCoord.symm
      rw [hzEq] at hzK
      exact (rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno (rlc_path_start_mem_vertices gamma'.1)) hzK
    · change z ∈ ((sw_vertSeg (-((R : Int) + 1))
          (leftStart 1) 0).copy _ _).support at hzVert
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzVert
      obtain ⟨s, _hs, rfl⟩ := hzVert
      intro hzK
      have hzRect := hzK.1
      rw [mem_rect] at hzRect
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzRect
      have hx := hzRect.1
      omega
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ ⟨far, hfarNotK⟩ := by
    exact ⟨w.induce Kᶜ hwNot⟩
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩).supp.Infinite := by
    have hfarInf := exterior_mem_infiniteComponent
      (by norm_num) K R hR hfarExt
    have hcomp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ =
      ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨far, hfarNotK⟩ := ConnectedComponent.sound hreach
    rwa [hcomp]
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
        hqInf
        (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
  exact ⟨t, htLower, htUpper, htIn, habove,
    ⟨hwNot _ w.start_mem_support, hqComp⟩⟩



theorem rlc_centralFaceFilled_verticalGap_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧
      ![0, t + 1] ∉
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧
      ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  obtain ⟨t, htLower, htUpper, htIn, _habove, htOut⟩ :=
    rlc_centralFace_verticalGap_outside_mem_exterior
      gamma gamma' hposition rho hno
  have htFill := rlc_connectorCentralFaceReachSet_subset_filled
    gamma gamma' rho htIn
  have hsuccNotFill : ![0, t + 1] ∉
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using htOut
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htLower, htUpper, htFill, hsuccNotFill,
    ⟨hadj, iff_of_true htFill hsuccNotFill⟩⟩




structure RlcCentralFaceRetainedAnchoredBoundary {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  height : Int
  firstFace : Site 2
  secondFace : Site 2
  contour : (faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
      firstFace firstFace
  height_lower : (gamma.1.1 : Site 2) 1 ≤ height
  height_upper : height < (gamma'.1.2.1 : Site 2) 1
  axis_inside : ![0, height] ∈
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  axis_outside : ![0, height + 1] ∉
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  anchor_adj : (faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
      firstFace secondFace
  anchor_shared : sharedPrimalEdge firstFace secondFace =
    s((![0, height] : Site 2), ![0, height + 1])
  contour_isTrail : contour.IsTrail
  contour_covers : ∀ e ∈ (faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).edgeSet,
      e ∈ contour.edges
  anchor_mem : s(firstFace, secondFace) ∈ contour.edges



theorem RlcCentralFaceRetainedAnchoredBoundary.contour_isCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    B.contour.IsCycle := by
  apply rlc_isCycle_of_isCycles_isTrail B.contour
    (rlc_connectorCentralFaceFilledBoundary_isCycles gamma gamma' rho)
  · intro hnil
    have hanchor := B.anchor_mem
    rw [hnil] at hanchor
    simpa using hanchor
  · exact B.contour_isTrail



theorem RlcCentralFaceRetainedAnchoredBoundary.exists_orientedAnchorCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ c : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace B.firstFace,
      c.IsCycle ∧ c.snd = B.secondFace ∧
        c.toSubgraph.verts = B.contour.toSubgraph.verts := by
  have hanchorSub : B.contour.toSubgraph.Adj
      B.firstFace B.secondFace :=
    B.contour.adj_toSubgraph_iff_mem_edges.mpr B.anchor_mem
  exact B.contour_isCycle.exists_isCycle_snd_verts_eq hanchorSub




theorem RlcCentralFaceRetainedAnchoredBoundary.exactComplementaryAnchorPath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.secondFace B.firstFace,
      a.IsPath ∧
        s(B.firstFace, B.secondFace) ∉ a.edges ∧
        ∀ e : Sym2 (Site 2),
          e ∈ B.contour.edges ↔
            e = s(B.firstFace, B.secondFace) ∨ e ∈ a.edges := by
  let G := faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  obtain ⟨c, hc, hsnd, hverts⟩ := B.exists_orientedAnchorCycle
  let a : G.Walk B.secondFace B.firstFace := c.tail.copy hsnd rfl
  have haPath : a.IsPath := by
    simpa [a] using hc.isPath_tail
  have hdecomp : c.edges =
      s(B.firstFace, B.secondFace) :: a.edges := by
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons u v w huv p =>
        have hv : v = B.secondFace :=
          (SimpleGraph.Walk.snd_cons p huv).symm.trans hsnd
        simp only [SimpleGraph.Walk.edges_cons, a,
          SimpleGraph.Walk.tail_cons]
        rw [SimpleGraph.Walk.edges_copy]
        congr 1
        · exact congrArg (Sym2.mk B.firstFace) hv
        · exact (SimpleGraph.Walk.edges_copy p _ _).symm
  have hcycles : G.IsCycles :=
    rlc_connectorCentralFaceFilledBoundary_isCycles gamma gamma' rho
  have hsameEdges (e : Sym2 (Site 2)) :
      e ∈ c.edges ↔ e ∈ B.contour.edges := by
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [← c.adj_toSubgraph_iff_mem_edges,
          ← B.contour.adj_toSubgraph_iff_mem_edges]
        constructor
        · intro hxy
          have hxC : x ∈ c.toSubgraph.verts :=
            c.toSubgraph.edge_vert hxy
          have hxB : x ∈ B.contour.toSubgraph.verts := by
            rwa [← hverts]
          exact (B.contour_isCycle.adj_toSubgraph_iff_of_isCycles
            hcycles hxB y).2 hxy.adj_sub
        · intro hxy
          have hxB : x ∈ B.contour.toSubgraph.verts :=
            B.contour.toSubgraph.edge_vert hxy
          have hxC : x ∈ c.toSubgraph.verts := by
            rwa [hverts]
          exact (hc.adj_toSubgraph_iff_of_isCycles
            hcycles hxC y).2 hxy.adj_sub
  have haAvoid : s(B.firstFace, B.secondFace) ∉ a.edges := by
    have hnodup := hc.edges_nodup
    rw [hdecomp, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨a, haPath, haAvoid, ?_⟩
  intro e
  rw [← hsameEdges, hdecomp, List.mem_cons]



theorem rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices gamma'.1) :
    z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
  classical
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨t, _htLower, _htUpper, _htIn, habove, hqExt⟩ :=
    rlc_centralFace_verticalGap_outside_mem_exterior
      gamma gamma' hposition rho hno
  let upper := (gamma'.1.2.1 : Site 2) 1
  have hupperCoord : (![0, upper] : Site 2) = gamma'.1.2.1 := by
    ext i
    fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
  let W := rlc_ambientCrossingWalk gamma'.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).2
      hzPath
  let wTrace : (hypercubicLattice 2).Walk z
      (gamma'.1.2.1 : Site 2) := (W.takeUntil z hzW).reverse.append W
  let wAxis : (hypercubicLattice 2).Walk
      (gamma'.1.2.1 : Site 2) ![0, t + 1] :=
    (sw_vertSeg 0 upper (t + 1)).copy hupperCoord rfl
  let w := wTrace.append wAxis
  have hwNot : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    dsimp only [w] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvTrace | hvAxis
    · have hvW : v ∈ W.support := by
        dsimp only [wTrace] at hvTrace
        rw [SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.support_reverse] at hvTrace
        rcases hvTrace with hvTrace | hvTrace
        · exact W.support_takeUntil_subset_support hzW (by simpa using hvTrace)
        · exact hvTrace
      have hvPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 v).1 hvW
      exact rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno hvPath
    · change v ∈ ((sw_vertSeg 0 upper (t + 1)).copy _ _).support at hvAxis
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hvAxis
      obtain ⟨s, hs, rfl⟩ := hvAxis
      rw [Set.mem_uIcc] at hs
      rcases hs with hs | hs
      · exact habove s (by omega) (by omega)
      · exact habove s (by omega) (by omega)
  have hzNot : z ∈ Kᶜ := hwNot z w.start_mem_support
  have hqNot : (![0, t + 1] : Site 2) ∈ Kᶜ := hqExt.1
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨z, hzNot⟩ ⟨![0, t + 1], hqNot⟩ := ⟨w.induce Kᶜ hwNot⟩
  refine ⟨hzNot, ?_⟩
  exact (ConnectedComponent.sound hreach).trans hqExt.2


theorem rlc_centralFaceLowestFilledAxisGap_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceLowestFilledAxisGap gamma gamma' rho) := by
  classical
  let lower := (gamma.1.1 : Site 2) 1
  let upper := (gamma'.1.2.1 : Site 2) 1
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hlowerLt : lower < upper := by
    have hr := hposition.right_axis_strict
    have hl := hposition.left_axis_strict
    dsimp only [lower, upper]
    omega
  have hlowerPath : (![0, lower] : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    have haxis : (gamma.1.1 : Site 2) = ![0, lower] := by
      ext i
      fin_cases i <;> simp [lower, gamma.1.1.2.2]
    rw [← haxis]
    exact rlc_path_start_mem_vertices gamma.1
  have hupperPath : (![0, upper] : Site 2) ∈
      rlc_pathVertices gamma'.1 := by
    have haxis : (gamma'.1.2.1 : Site 2) = ![0, upper] := by
      ext i
      fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
    rw [← haxis]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hlower : (![0, lower] : Site 2) ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet
        gamma gamma' rho hlowerPath)
  have hupperExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hposition rho hno hupperPath
  have hupper : (![0, upper] : Site 2) ∉ H := by
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hupperExt
  let A : Finset Int := (Finset.Icc lower upper).filter
    (fun s => ![0, s] ∉ H)
  have hupperA : upper ∈ A := by
    simp [A, hupper, le_of_lt hlowerLt]
  have hA : A.Nonempty := ⟨upper, hupperA⟩
  let firstOutside := A.min' hA
  have hfirstA : firstOutside ∈ A := A.min'_mem hA
  have hfirstBounds : lower ≤ firstOutside ∧ firstOutside ≤ upper := by
    simpa [A] using (Finset.mem_filter.mp hfirstA).1
  have hfirstOut : (![0, firstOutside] : Site 2) ∉ H :=
    (Finset.mem_filter.mp hfirstA).2
  have hlowerFirst : lower < firstOutside := by
    apply lt_of_le_of_ne hfirstBounds.1
    intro heq
    exact hfirstOut (heq ▸ hlower)
  let t := firstOutside - 1
  have htLower : lower ≤ t := by
    dsimp only [t]
    omega
  have htUpper : t < upper := by
    dsimp only [t]
    omega
  have hbelow : ∀ s : Int, lower ≤ s → s ≤ t → (![0, s] : Site 2) ∈ H := by
    intro s hls hst
    by_contra hsOut
    have hsA : s ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hls, by omega⟩, hsOut⟩
    have hmin := A.min'_le s hsA
    change firstOutside ≤ s at hmin
    dsimp only [t] at hst
    omega
  have htIn : (![0, t] : Site 2) ∈ H := hbelow t htLower (le_refl _)
  have htOut : (![0, t + 1] : Site 2) ∉ H := by
    have hsucc : t + 1 = firstOutside := by
      dsimp only [t]
      omega
    rwa [hsucc]
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨{
    height := t
    height_lower := htLower
    height_upper := htUpper
    axis_inside := htIn
    axis_outside := htOut
    axis_below_inside := hbelow
    boundary := ⟨hadj, iff_of_true htIn htOut⟩
  }⟩



theorem RlcCentralFaceLowestFilledAxisGap.axis_successor_inside_of_lt
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.height) :
    (![0, s + 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  exact L.axis_below_inside (s + 1) (by omega) (by omega)



theorem RlcCentralFaceLowestFilledAxisGap.no_lower_axis_boundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.height) :
    ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  intro hboundary
  have hsIn := L.axis_below_inside s hsLower (by omega)
  have hsuccIn := L.axis_successor_inside_of_lt hsLower hs
  exact (hboundary.2.mp hsIn) hsuccIn



theorem rlc_centralFace_retainedAnchoredBoundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let T := phb_boundarySupport H hH
  obtain ⟨t, htLower, htUpper, htIn, htOut, htBoundary⟩ :=
    rlc_centralFaceFilled_verticalGap_boundary_of_failure
      gamma gamma' hposition rho hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces htBoundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact htBoundary.2
  have hconn : FaceBoundaryConnected H T := by
    simpa [H, hH, T] using
      (rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
        gamma gamma' rho)
  have hsupp : (faceBoundaryGraph H).support ⊆ (T : Set (Site 2)) := by
    intro z hz
    simpa [T, H, hH] using hz
  have hfT : f ∈ T := by
    simpa [T, H, hH] using hfg.mem_support_left
  have hcoversComponent :
      ∀ e ∈ (faceBoundaryGraph H).edgeSet,
        e ∈ (componentGraph H f).edgeSet :=
    componentCovers_of_faceBoundaryConnected hsupp hconn hfT
  obtain ⟨c, hcTrail, hcCovers⟩ :=
    dualCircuit_of_componentCovers hsupp hfT hcoversComponent
  have hanchor : s(f, g) ∈ c.edges := by
    apply hcCovers
    rw [SimpleGraph.mem_edgeSet]
    exact hfg
  exact ⟨{
    height := t
    firstFace := f
    secondFace := g
    contour := c
    height_lower := htLower
    height_upper := htUpper
    axis_inside := htIn
    axis_outside := htOut
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isTrail := hcTrail
    contour_covers := hcCovers
    anchor_mem := hanchor
  }⟩




structure RlcCentralFaceLowestRetainedAnchoredBoundary {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  boundary : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho
  axis_below_inside : ∀ s : Int,
    (gamma.1.1 : Site 2) 1 ≤ s → s ≤ boundary.height →
      ![0, s] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho



theorem rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceLowestRetainedAnchoredBoundary
      gamma gamma' rho) := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let T := phb_boundarySupport H hH
  let L := Classical.choice
    (rlc_centralFaceLowestFilledAxisGap_of_failure
      gamma gamma' hposition rho hno)
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces L.boundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact L.boundary.2
  have hconn : FaceBoundaryConnected H T := by
    simpa [H, hH, T] using
      (rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
        gamma gamma' rho)
  have hsupp : (faceBoundaryGraph H).support ⊆ (T : Set (Site 2)) := by
    intro z hz
    simpa [T, H, hH] using hz
  have hfT : f ∈ T := by
    simpa [T, H, hH] using hfg.mem_support_left
  have hcoversComponent :
      ∀ e ∈ (faceBoundaryGraph H).edgeSet,
        e ∈ (componentGraph H f).edgeSet :=
    componentCovers_of_faceBoundaryConnected hsupp hconn hfT
  obtain ⟨c, hcTrail, hcCovers⟩ :=
    dualCircuit_of_componentCovers hsupp hfT hcoversComponent
  have hanchor : s(f, g) ∈ c.edges := by
    apply hcCovers
    rw [SimpleGraph.mem_edgeSet]
    exact hfg
  let B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho := {
    height := L.height
    firstFace := f
    secondFace := g
    contour := c
    height_lower := L.height_lower
    height_upper := L.height_upper
    axis_inside := L.axis_inside
    axis_outside := L.axis_outside
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isTrail := hcTrail
    contour_covers := hcCovers
    anchor_mem := hanchor
  }
  exact ⟨{
    boundary := B
    axis_below_inside := L.axis_below_inside
  }⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_axis_boundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) :
    ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  intro hboundary
  have hsIn := L.axis_below_inside s hsLower (by omega)
  have hsuccIn := L.axis_below_inside (s + 1) (by omega) (by omega)
  exact (hboundary.2.mp hsIn) hsuccIn




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_contour_axis_crossing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} {s : Int}
    (hfg : s(f, g) ∈ L.boundary.contour.edges)
    (hshared : sharedPrimalEdge f g =
      s((![0, s] : Site 2), ![0, s + 1]))
    (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) : False := by
  apply L.no_lower_axis_boundary hsLower hs
  have hbd := (L.boundary.contour.adj_of_mem_edges hfg).2
  rw [hshared, bdEdge_mk] at hbd
  exact ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], hbd⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_reflected_axis_crossing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} {s : Int}
    (hfg : s(f, g) ∈ L.boundary.contour.edges)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, s + 1] : Site 2), ![0, s + 1]))
    (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) : False := by
  have hfgAdj := L.boundary.contour.adj_of_mem_edges hfg
  have hmap := congrArg rlc_pimsEdgeEquiv hreflected
  have hshared : sharedPrimalEdge f g =
      s((![0, s] : Site 2), ![0, s + 1]) := by
    rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfgAdj.1] at hmap
    calc
      sharedPrimalEdge f g =
          rlc_pimsEdgeEquiv
            s((![-1, s + 1] : Site 2), ![0, s + 1]) := hmap
      _ = s((![0, s] : Site 2), ![0, s + 1]) := by
        simpa using (rlc_pimsEdgeEquiv_horizontal (-1) (s + 1))
  exact L.no_lower_contour_axis_crossing hfg hshared hsLower hs



theorem rlc_faceBoundaryWalk_reflected_axis_crossing
    {H : Set (Site 2)} {a b : Site 2}
    (p : (faceBoundaryGraph H).Walk a b)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ p.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) := by
  let q : (hypercubicLattice 2).Walk a b :=
    p.mapLe (faceBoundaryGraph_le H)
  let S : Set (Site 2) := {z | (rlc_dualReflect z) 0 < 0}
  obtain ⟨f, g, hfgBoundary, hfgEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges S q (by simpa [S] using ha)
      (by simpa [S] using hb)
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfgBoundary.1
  have hsign :
      ((rlc_dualReflect f) 0 < 0 ↔
        ¬ (rlc_dualReflect g) 0 < 0) := by
    simpa [S] using hfgBoundary.2
  have hsignCases :
      (((rlc_dualReflect f) 0 < 0 ∧
          0 ≤ (rlc_dualReflect g) 0) ∨
        ((rlc_dualReflect g) 0 < 0 ∧
          0 ≤ (rlc_dualReflect f) 0)) := by
    by_cases hf : (rlc_dualReflect f) 0 < 0
    · left
      exact ⟨hf, by
        have hg := hsign.mp hf
        omega⟩
    · right
      have hg : (rlc_dualReflect g) 0 < 0 := by
        by_contra hg
        exact hf (hsign.mpr hg)
      exact ⟨hg, by omega⟩
  have hcross : ∃ k : Int,
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) := by
    rcases hsignCases with hfg | hgf
    · rcases adj_cases hfgAdj with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · exfalso
        omega
      · rcases h0 with h0 | h0
        all_goals
          refine ⟨(rlc_dualReflect f) 1, ?_⟩
          have hf0 : (rlc_dualReflect f) 0 = -1 := by omega
          have hg0 : (rlc_dualReflect g) 0 = 0 := by omega
          have hfg1 : (rlc_dualReflect g) 1 =
              (rlc_dualReflect f) 1 := by omega
          have hf : rlc_dualReflect f =
              (![-1, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hf0
            · simp
          have hg : rlc_dualReflect g =
              (![0, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hg0
            · simpa using hfg1
          simp [hf, hg]
    · rcases adj_cases hfgAdj with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · exfalso
        omega
      · rcases h0 with h0 | h0
        all_goals
          refine ⟨(rlc_dualReflect f) 1, ?_⟩
          have hf0 : (rlc_dualReflect f) 0 = 0 := by omega
          have hg0 : (rlc_dualReflect g) 0 = -1 := by omega
          have hfg1 : (rlc_dualReflect g) 1 =
              (rlc_dualReflect f) 1 := by omega
          have hf : rlc_dualReflect f =
              (![0, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hf0
            · simp
          have hg : rlc_dualReflect g =
              (![-1, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hg0
            · simpa using hfg1
          simp [hf, hg, Sym2.eq_swap]
  obtain ⟨k, hk⟩ := hcross
  refine ⟨f, g, k, ?_, hk⟩
  simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgEdge




theorem rlc_faceBoundaryWalk_first_reflected_axis_crossing
    {H : Set (Site 2)} {a b : Site 2}
    (p : (faceBoundaryGraph H).Walk a b)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0) :
    ∃ (u v : Site 2) (k : Int)
      (q : (faceBoundaryGraph H).Walk a u),
      (faceBoundaryGraph H).Adj u v ∧
        s(u, v) ∈ p.edges ∧
        (∀ e ∈ q.edges, e ∈ p.edges) ∧
        (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) =
          s((![-1, k] : Site 2), ![0, k]) := by
  let P : Site 2 → Prop := fun z => (rlc_dualReflect z) 0 < 0
  obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p P ha (by
      dsimp only [P]
      omega)
  let one : (faceBoundaryGraph H).Walk u v := .cons huv .nil
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing one
      (hqSafe u q.end_mem_support) (by
        dsimp only [P] at hv
        omega)
  have heq : s(f, g) = s(u, v) := by
    simpa [one] using hfg
  refine ⟨u, v, k, q, huv, huvEdge, hqEdges, hqSafe, ?_⟩
  calc
    s(rlc_dualReflect u, rlc_dualReflect v) =
        s(rlc_dualReflect f, rlc_dualReflect g) := by
      simpa [Sym2.map_mk] using
        congrArg (Sym2.map rlc_dualReflect) heq.symm
    _ = s((![-1, k] : Site 2), ![0, k]) := hreflected




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_axis_crossing_walk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a b : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0)
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) : False := by
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing p ha hb
  have hfHeight : (rlc_dualReflect f) 1 = k := by
    have hfMem : rlc_dualReflect f ∈
        s((![-1, k] : Site 2), ![0, k]) := by
      rw [← hreflected]
      exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_iff] at hfMem
    rcases hfMem with hfMem | hfMem
    · have h := congrArg (fun z : Site 2 => z 1) hfMem
      simpa only [Matrix.cons_val_one] using h
    · have h := congrArg (fun z : Site 2 => z 1) hfMem
      simpa only [Matrix.cons_val_one] using h
  have hfBand := hpBand f (p.fst_mem_support_of_mem_edges hfg)
  have hcontour : s(f, g) ∈ L.boundary.contour.edges := hpEdges _ hfg
  apply L.no_lower_reflected_axis_crossing hcontour
      (s := k - 1) (by simpa using hreflected)
  · omega
  · omega



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.lower_band_walk_same_halfplane
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a b : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) :
    ((rlc_dualReflect a) 0 < 0 ↔
      (rlc_dualReflect b) 0 < 0) := by
  constructor
  · intro ha
    by_contra hb
    exact L.no_lower_band_axis_crossing_walk p hpEdges ha (by omega) hpBand
  · intro hb
    by_contra ha
    apply L.no_lower_band_axis_crossing_walk p.reverse
    · intro e he
      apply hpEdges e
      simpa using he
    · simpa using hb
    · omega
    · intro z hz
      apply hpBand z
      simpa [SimpleGraph.Walk.support_reverse] using hz



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_strict_contact_arc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {x y : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk y x)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxNe : rlc_dualReflect x ≠ (gamma.1.1 : Site 2))
    (hyNe : rlc_dualReflect y ≠ (gamma'.1.2.1 : Site 2))
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) : False := by
  have hyNeg := hfaith.left_vertex_strict hyPath hyNe
  have hxPos := hfaith.right_vertex_strict hxPath hxNe
  have hsame := L.lower_band_walk_same_halfplane p hpEdges hpBand
  have hxNotNeg : ¬ (rlc_dualReflect x) 0 < 0 := by omega
  exact hxNotNeg (hsame.mp hyNeg)



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_arc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        ∀ e ∈ a.edges, e ∈ L.boundary.contour.edges := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let G := faceBoundaryGraph H
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph H
    (rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      G T hT (degree_faceBoundaryGraph_even H) L.boundary.anchor_adj
  have hreach : (G.deleteEdges
      {s(L.boundary.firstFace, L.boundary.secondFace)}).Reachable
        L.boundary.firstFace L.boundary.secondFace :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G)).mpr ⟨u, c, hcyc, hedge⟩ |>.2
  obtain ⟨a, ha⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := G)).mp hreach
  refine ⟨a, ha, ?_⟩
  intro e he
  apply L.boundary.contour_covers e
  exact a.edges_subset_edgeSet he



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_path_exact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      a.IsPath ∧
        s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        ∀ e : Sym2 (Site 2),
          e ∈ L.boundary.contour.edges ↔
            e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
              e ∈ a.edges := by
  obtain ⟨a, haPath, haAvoid, haCover⟩ :=
    L.boundary.exactComplementaryAnchorPath
  refine ⟨a.reverse, (SimpleGraph.Walk.isPath_reverse_iff _).2 haPath,
    ?_, ?_⟩
  · simpa [SimpleGraph.Walk.edges_reverse] using haAvoid
  · intro e
    simpa [SimpleGraph.Walk.edges_reverse] using haCover e




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ p.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing p
      huNeg (by omega)
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, L.boundary.height + 1] : Site 2),
          ![0, L.boundary.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hkNe : k ≠ L.boundary.height + 1 := by
    intro hk
    subst k
    have hmapped : Sym2.map rlc_dualReflect s(f, g) =
        Sym2.map rlc_dualReflect
          s(L.boundary.firstFace, L.boundary.secondFace) := by
      simpa [Sym2.map_mk] using hreflected.trans htarget.symm
    have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
    exact hpAvoid (heq ▸ hfg)
  refine ⟨f, g, k, hfg, hreflected, ?_⟩
  by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
  · exact Or.inl hkLower
  by_cases hkUpper : L.boundary.height + 1 < k
  · exact Or.inr hkUpper
  exfalso
  apply L.no_lower_reflected_axis_crossing (hpEdges _ hfg)
      (s := k - 1) (by simpa using hreflected)
  · omega
  · omega



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_exits_lower_anchor_band
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
    ∃ z ∈ p.support,
      (rlc_dualReflect z) 1 ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height < (rlc_dualReflect z) 1 := by
  obtain ⟨f, g, k, hfg, hreflected, hkLow | hkHigh⟩ :=
    L.middlePath_axis_crossing_extreme p huNeg hvPos hpEdges hpAvoid
  all_goals
    have hfMem : rlc_dualReflect f ∈
        s((![-1, k] : Site 2), ![0, k]) := by
      rw [← hreflected]
      exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_iff] at hfMem
    have hfHeight : (rlc_dualReflect f) 1 = k := by
      rcases hfMem with hfMem | hfMem
      all_goals
        have h := congrArg (fun z : Site 2 => z 1) hfMem
        simpa only [Matrix.cons_val_one] using h
    refine ⟨f, p.fst_mem_support_of_mem_edges hfg, ?_⟩
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ (a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace)
      (f g : Site 2) (k : Int),
      s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
        s(f, g) ∈ a.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨a, haAvoid, haEdges⟩ := L.complementary_axis_arc
  let anchorHeight := L.boundary.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) := by
    exact sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1
      hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, anchorHeight] : Site 2), ![0, anchorHeight]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [anchorHeight, Sym2.map_mk, rlc_dualReflect,
      rlc_dualReflectFun, Sym2.eq_swap] using hmap
  have extract {r s : Site 2}
      (p : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r s)
      (hpEdge : ∀ e ∈ p.edges, e ∈ a.edges)
      (hpStart : (rlc_dualReflect r) 0 < 0)
      (hpEnd : 0 ≤ (rlc_dualReflect s) 0) :
      ∃ (f g : Site 2) (k : Int),
        s(f, g) ∈ a.edges ∧
          s(rlc_dualReflect f, rlc_dualReflect g) =
            s((![-1, k] : Site 2), ![0, k]) ∧
          (k ≤ (gamma.1.1 : Site 2) 1 ∨
            L.boundary.height + 1 < k) := by
    obtain ⟨f, g, k, hfg, hreflected⟩ :=
      rlc_faceBoundaryWalk_reflected_axis_crossing p hpStart hpEnd
    have hfgA : s(f, g) ∈ a.edges := hpEdge _ hfg
    have hkNe : k ≠ anchorHeight := by
      intro hk
      subst k
      have hmapped :
          Sym2.map rlc_dualReflect s(f, g) =
            Sym2.map rlc_dualReflect
              s(L.boundary.firstFace, L.boundary.secondFace) := by
        simpa [Sym2.map_mk] using hreflected.trans htarget.symm
      have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
      exact haAvoid (heq ▸ hfgA)
    have hcontour : s(f, g) ∈ L.boundary.contour.edges :=
      haEdges _ hfgA
    have hextreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height + 1 < k := by
      by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
      · exact Or.inl hkLower
      by_cases hkUpper : L.boundary.height + 1 < k
      · exact Or.inr hkUpper
      exfalso
      apply L.no_lower_reflected_axis_crossing hcontour
          (s := k - 1) (by simpa using hreflected)
      · omega
      · dsimp only [anchorHeight] at hkNe
        omega
    exact ⟨f, g, k, hfgA, hreflected, hextreme⟩
  have htargetCases := htarget
  rw [Sym2.eq_iff] at htargetCases
  rcases htargetCases with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · have hstart : (rlc_dualReflect L.boundary.firstFace) 0 < 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    have hend : 0 ≤ (rlc_dualReflect L.boundary.secondFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨f, g, k, hfg, hreflected, hextreme⟩ :=
      extract a (fun _ he => he) hstart hend
    exact ⟨a, f, g, k, haAvoid, haEdges, hfg, hreflected, hextreme⟩
  · have hstart :
        (rlc_dualReflect L.boundary.secondFace) 0 < 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    have hend : 0 ≤ (rlc_dualReflect L.boundary.firstFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨f, g, k, hfg, hreflected, hextreme⟩ :=
      extract a.reverse (by intro e he; simpa using he) hstart hend
    exact ⟨a, f, g, k, haAvoid, haEdges, hfg, hreflected, hextreme⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ (a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace)
      (N u v : Site 2) (k : Int)
      (q : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u),
      (N = L.boundary.firstFace ∨ N = L.boundary.secondFace) ∧
        rlc_dualReflect N =
          (![-1, L.boundary.height + 1] : Site 2) ∧
        s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        a.IsPath ∧
        (∀ e : Sym2 (Site 2),
          e ∈ L.boundary.contour.edges ↔
            e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
              e ∈ a.edges) ∧
        (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
        (∀ e ∈ q.edges, e ∈ a.edges) ∧
        (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ a.edges ∧
        s(rlc_dualReflect u, rlc_dualReflect v) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨a, haPath, haAvoid, haExact⟩ :=
    L.complementary_axis_path_exact
  have haEdges : ∀ e ∈ a.edges, e ∈ L.boundary.contour.edges := by
    intro e he
    exact (haExact e).2 (Or.inr he)
  let anchorHeight := L.boundary.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, anchorHeight] : Site 2), ![0, anchorHeight]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [anchorHeight, Sym2.map_mk, rlc_dualReflect,
      rlc_dualReflectFun, Sym2.eq_swap] using hmap
  have extract {r t : Site 2}
      (p : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r t)
      (hr : r = L.boundary.firstFace ∨ r = L.boundary.secondFace)
      (hrEq : rlc_dualReflect r = (![-1, anchorHeight] : Site 2))
      (htNonneg : 0 ≤ (rlc_dualReflect t) 0)
      (hpEdge : ∀ e ∈ p.edges, e ∈ a.edges) :
      ∃ (u v : Site 2) (k : Int)
        (q : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r u),
        (∀ e ∈ q.edges, e ∈ a.edges) ∧
          (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
          s(u, v) ∈ a.edges ∧
          s(rlc_dualReflect u, rlc_dualReflect v) =
            s((![-1, k] : Site 2), ![0, k]) ∧
          (k ≤ (gamma.1.1 : Site 2) 1 ∨
            L.boundary.height + 1 < k) := by
    obtain ⟨u, v, k, q, huv, huvP, hqP, hqSafe, hreflected⟩ :=
      rlc_faceBoundaryWalk_first_reflected_axis_crossing p
        (by rw [hrEq]; simp) htNonneg
    have huvA := hpEdge _ huvP
    have hqA : ∀ e ∈ q.edges, e ∈ a.edges := by
      intro e he
      exact hpEdge e (hqP e he)
    have hkNe : k ≠ anchorHeight := by
      intro hk
      subst k
      have hmapped : Sym2.map rlc_dualReflect s(u, v) =
          Sym2.map rlc_dualReflect
            s(L.boundary.firstFace, L.boundary.secondFace) := by
        simpa [Sym2.map_mk] using hreflected.trans htarget.symm
      have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
      exact haAvoid (heq ▸ huvA)
    have hcontour := haEdges _ huvA
    have hextreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height + 1 < k := by
      by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
      · exact Or.inl hkLower
      by_cases hkUpper : L.boundary.height + 1 < k
      · exact Or.inr hkUpper
      exfalso
      apply L.no_lower_reflected_axis_crossing hcontour
          (s := k - 1) (by simpa using hreflected)
      · omega
      · dsimp only [anchorHeight] at hkNe
        omega
    exact ⟨u, v, k, q, hqA, hqSafe, huv, huvA,
      hreflected, hextreme⟩
  have hcases := htarget
  rw [Sym2.eq_iff] at hcases
  rcases hcases with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · have hend : 0 ≤ (rlc_dualReflect L.boundary.secondFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨u, v, k, q, hqA, hqSafe, huv, huvA, href, hextreme⟩ :=
      extract a (Or.inl rfl) hfirst hend (fun _ he => he)
    exact ⟨a, L.boundary.firstFace, u, v, k, q, Or.inl rfl,
      hfirst, haAvoid, haPath, haExact, haEdges, hqA, hqSafe, huv, huvA,
      href, hextreme⟩
  · have hend : 0 ≤ (rlc_dualReflect L.boundary.firstFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨u, v, k, q, hqA, hqSafe, huv, huvA, href, hextreme⟩ :=
      extract a.reverse (Or.inr rfl) hsecond hend
        (by intro e he; simpa using he)
    exact ⟨a, L.boundary.secondFace, u, v, k, q, Or.inr rfl,
      hsecond, haAvoid, haPath, haExact, haEdges, hqA, hqSafe, huv, huvA,
      href, hextreme⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.filledReachSet_eq_leftRegion
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho =
      jec_leftRegion (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))) := by
  apply rlc_leftRegion_eq_of_faceBoundaryTrail
  · exact rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  · exact B.contour_isTrail
  · exact B.contour_covers



theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedFilledReachSet_eq_leftRegion
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) =
      jec_leftRegion
        ((B.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom) := by
  exact rlc_reflectedRegion_eq_leftRegion_map_of_eq _ _
    B.filledReachSet_eq_leftRegion


theorem rlc_bdEdge_reflectedPrimalRegion_map (K : Set (Site 2))
    (e : Sym2 (Site 2)) :
    bdEdge (rlc_reflectedPrimalRegion K) (Sym2.map rlc_primalDualReflect e) ↔
      bdEdge K e := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      rw [Sym2.map_mk, bdEdge_mk, bdEdge_mk]
      simp only [rlc_mem_reflectedPrimalRegion_iff,
        Equiv.symm_apply_apply]




@[reducible] noncomputable def rlc_connectorCrossedBoxPlanar (n : Int) :
    Lattice.PlanarZ2Subgraph where
  V := rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2)
  finV := (rect_finite (-2 * n - 1) (2 * n + 1) (-n) (n + 2)).to_subtype
  decV := Classical.decEq _
  G := (hypercubicLattice 2).induce
    (rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2))
  emb := Function.Embedding.subtype _
  isSub := fun _ _ hxy => hxy



theorem rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect
    {a b c d : Int} {f g : Site 2}
    (hf : f ∈ rect a (b - 1) c (d - 1))
    (hfg : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rect a b c d ∧ q ∈ rect a b c d := by
  rw [mem_rect] at hf
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl
  · refine ⟨![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega

    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1], ![f 0, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge] <;> omega
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1], ![f 0 + 1, f 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge] <;> omega
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega




theorem rlc_reflectedCarrierFaces_mem_crossedBoxInterior {n : Int}
    {f g z : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hz : z ∈ sharedPrimalEdge f g)
    (hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n) :
    rlc_dualReflect f ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧
      rlc_dualReflect g ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl
  · have hz' : z = ![f 0 + 1, f 1] ∨
        z = ![f 0 + 1, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0 + 1, f 1] =
          s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_right (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -(f 0 + 1) - 1 ∧
          -(f 0 + 1) - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1] ∨ z = ![f 0, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0 - 1, f 1] =
          s(![f 0, f 1], ![f 0, f 1 + 1]) by
            simpa using sharedPrimalEdge_left (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -(f 0 - 1) - 1 ∧
          -(f 0 - 1) - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1 + 1] ∨
        z = ![f 0 + 1, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0, f 1 + 1] =
          s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_top (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 + 1 ∧ f 1 + 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1] ∨ z = ![f 0 + 1, f 1] := by
      rw [show sharedPrimalEdge f ![f 0, f 1 - 1] =
          s(![f 0, f 1], ![f 0 + 1, f 1]) by
            simpa using sharedPrimalEdge_bottom (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 - 1 + 1 ∧ f 1 - 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega



theorem rlc_sharedPrimalEdge_mem_crossedBoxImage {n : Int}
    {f g p q : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hp : p ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2))
    (hq : q ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2)) :
    sharedPrimalEdge f g ∈
      (imageGraph (rlc_connectorCrossedBoxPlanar n)).edgeSet := by
  obtain ⟨p', q', hpq', hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq'] at hshared ⊢
  rw [Sym2.eq_iff] at hshared
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨p', hp⟩, ⟨q', hq⟩, hpqAdj, rfl, rfl⟩
  · exact ⟨⟨p', hq⟩, ⟨q', hp⟩, hpqAdj, rfl, rfl⟩



theorem rlc_crossedBox_interiorFace_isolated {n : Int} {f g : Site 2}
    (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1)) :
    ¬ (whb_faceRegion
      (imageGraph (rlc_connectorCrossedBoxPlanar n))).Adj f g := by
  rintro ⟨hfg, hnot⟩
  have hf' : f ∈ rect (-2 * n - 1) ((2 * n + 1) - 1)
      (-n) ((n + 2) - 1) := by
    rw [mem_rect] at hf ⊢
    omega
  obtain ⟨p, q, hpq, _hpqAdj, hp, hq⟩ :=
    rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect hf' hfg
  exact hnot (rlc_sharedPrimalEdge_mem_crossedBoxImage hfg hpq hp hq)



theorem rlc_crossedBox_interiorFace_component_singleton {n : Int}
    {f g : Site 2}
    (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1))
    (hcomp : (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f =
      (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) :
    f = g := by
  have hreach := ConnectedComponent.exact hcomp
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _ => exact (rlc_crossedBox_interiorFace_isolated hf hadj).elim


noncomputable def rlc_connectorReflectedFilledColour {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (rlc_connectorCrossedBoxPlanar n).V := by
  classical
  exact fun x => decide (x.1 ∈ rlc_reflectedPrimalRegion
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))


noncomputable def rlc_connectorReflectedFilledCut {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)) :=
  Ising.kwg_cutSet
    (Ising.kwg_primalEnds (rlc_connectorCrossedBoxPlanar n))
    (rlc_connectorReflectedFilledColour gamma gamma' rho)


theorem rlc_connectorReflectedFilledCut_isEven {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Ising.kwg_IsEven
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n))
      (rlc_connectorReflectedFilledCut gamma gamma' rho) := by
  exact Ising.kwg_primalCut_isEven (rlc_connectorCrossedBoxPlanar n)
    (rlc_connectorReflectedFilledColour gamma gamma' rho)



theorem rlc_mem_reflectedFilledCut_iff_bdEdge_embedded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)) :
    e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho ↔
      bdEdge
        (rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
        (Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e) := by
  classical
  rw [rlc_connectorReflectedFilledCut, Ising.kwg_mem_cutSet]
  rcases e with ⟨ep, hep⟩
  induction ep using Sym2.inductionOn with
  | _ x y =>
      change
        ((decide (x.1 ∈ rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) : Bool) ≠
            decide (y.1 ∈ rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))) ↔
          bdEdge
            (rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
            s(x.1, y.1)
      rw [bdEdge_mk]
      by_cases hx : x.1 ∈ rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) <;>
        by_cases hy : y.1 ∈ rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) <;>
        simp [hx, hy]



theorem rlc_reflectedFilledBoundary_endpoints_mem_crossedBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q)) :
    rlc_primalDualReflect p ∈
        rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) ∧
      rlc_primalDualReflect q ∈
        rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) := by
  have near_of_mem {x y : Site 2}
      (hxy : (hypercubicLattice 2).Adj x y)
      (hx : x ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
      rlc_primalDualReflect x ∈
          rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) ∧
        rlc_primalDualReflect y ∈
          rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) := by
    have hxBox :=
      rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hx
    rw [mem_rect] at hxBox
    change
      ((-2 * n - 1 ≤ -x 0 ∧ -x 0 ≤ 2 * n + 1 ∧
          -n ≤ x 1 + 1 ∧ x 1 + 1 ≤ n + 2) ∧
        (-2 * n - 1 ≤ -y 0 ∧ -y 0 ≤ 2 * n + 1 ∧
          -n ≤ y 1 + 1 ∧ y 1 + 1 ≤ n + 2))
    rcases adj_cases hxy with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
    all_goals omega
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · exact near_of_mem hpq hp
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hbd.mpr hq)
    exact (near_of_mem hpq.symm hq).symm



theorem rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    rlc_dualReflect f ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧
      rlc_dualReflect g ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  obtain ⟨p, q, hpq, _hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfg.2
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · apply rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg.1
    · rw [hpq, Sym2.mem_iff]
      exact Or.inl rfl
    · exact rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hp
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hbd.mpr hq)
    apply rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg.1
    · rw [hpq, Sym2.mem_iff]
      exact Or.inr rfl
    · exact rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hq



theorem rlc_sharedPrimalEdge_dualReflect {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
      sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl <;>
    simp [sharedPrimalEdge, rlc_primalDualReflect,
      rlc_primalDualReflectFun, rlc_dualReflect, rlc_dualReflectFun]
  all_goals try split_ifs <;> try omega
  all_goals try simp [Sym2.eq_iff]
  all_goals ring



theorem rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho) :
    ∃ f g : Site 2,
      (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g ∧
        Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
  let P := rlc_connectorCrossedBoxPlanar n
  let F := Ising.kwg_flankLeft P e
  let G := Ising.kwg_flankRight P e
  let f := rlc_dualReflect.symm F
  let g := rlc_dualReflect.symm G
  have hFG : (hypercubicLattice 2).Adj F G := Ising.kwg_flanks_adj P e
  have hfg : (hypercubicLattice 2).Adj f g := by
    apply (rlc_adj_dualReflect f g).mpr
    simpa [f, g, F, G]
  have hsharedFG : sharedPrimalEdge F G =
      Ising.kwg_embeddedEdge P e := Ising.kwg_flanks_shared P e
  have hmap : Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
      Ising.kwg_embeddedEdge P e := by
    calc
      Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) :=
        rlc_sharedPrimalEdge_dualReflect hfg
      _ = sharedPrimalEdge F G := by simp [f, g, F, G]
      _ = Ising.kwg_embeddedEdge P e := hsharedFG
  have hbdRef :=
    (rlc_mem_reflectedFilledCut_iff_bdEdge_embedded gamma gamma' rho e).mp
      heCut
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
      (sharedPrimalEdge f g) := by
    rw [← hmap] at hbdRef
    exact (rlc_bdEdge_reflectedPrimalRegion_map _ _).mp hbdRef
  refine ⟨f, g, ⟨hfg, hbd⟩, ?_⟩
  calc
    Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
        sharedPrimalEdge F G := hsharedFG.symm
    _ = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
      simp [f, g, F, G]


def rlc_reflectedFilledBoundaryGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (Site 2) where
  Adj x y := (faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
      (rlc_dualReflect.symm x) (rlc_dualReflect.symm y)
  symm := fun _ _ hxy => hxy.symm
  loopless := ⟨fun _ hxx => hxx.ne rfl⟩




noncomputable def rlc_reflectedCutSupportHom {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hS : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho) :
    Ising.kwg_faceSupportGraph
        (fun e : ↑S => Ising.kwg_dualEnds
          (rlc_connectorCrossedBoxPlanar n) e.1) →g
      rlc_reflectedFilledBoundaryGraph gamma gamma' rho where
  toFun C := C.out
  map_rel' := by
    intro C D hCD
    obtain ⟨_hCDne, e, heEnds⟩ := hCD
    have heCut : e.1 ∈
        rlc_connectorReflectedFilledCut gamma gamma' rho := hS e.2
    obtain ⟨f, g, hfg, heEmbedded⟩ :=
      rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier
        gamma gamma' rho e.1 heCut
    have hrefAdj : (hypercubicLattice 2).Adj
        (rlc_dualReflect f) (rlc_dualReflect g) :=
      (rlc_adj_dualReflect f g).mp hfg.1
    have heCarrier : Ising.kwg_dualEnds
        (rlc_connectorCrossedBoxPlanar n) e.1 =
        s((whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect f),
          (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect g)) := by
      let P := rlc_connectorCrossedBoxPlanar n
      have hpair : s(Ising.kwg_flankLeft P e.1,
          Ising.kwg_flankRight P e.1) =
          s(rlc_dualReflect f, rlc_dualReflect g) :=
        (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj P e.1)
          hrefAdj).mpr ((Ising.kwg_flanks_shared P e.1).trans heEmbedded)
      unfold Ising.kwg_dualEnds
      rw [Sym2.eq_iff] at hpair ⊢
      rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact Or.inl ⟨congrArg _ hleft, congrArg _ hright⟩
      · exact Or.inr ⟨congrArg _ hleft, congrArg _ hright⟩
    have hpair : s(C, D) =
        s((whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect f),
          (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect g)) := heEnds.symm.trans heCarrier
    obtain ⟨hfInt, hgInt⟩ :=
      rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
        hn gamma gamma' rho hfg
    have rep_eq {A : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
        {x : Site 2}
        (hxInt : x ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1))
        (hxA : (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk x = A) :
        A.out = x := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hxInt
      exact hxA.trans A.out_eq.symm
    rw [Sym2.eq_iff] at hpair
    rcases hpair with ⟨hCf, hDg⟩ | ⟨hCg, hDf⟩
    · have hC : C.out = rlc_dualReflect f := rep_eq hfInt hCf.symm
      have hD : D.out = rlc_dualReflect g := rep_eq hgInt hDg.symm
      change (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
          (rlc_dualReflect.symm C.out) (rlc_dualReflect.symm D.out)
      rw [hC, hD, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hfg
    · have hC : C.out = rlc_dualReflect g := rep_eq hgInt hCg.symm
      have hD : D.out = rlc_dualReflect f := rep_eq hfInt hDf.symm
      change (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
          (rlc_dualReflect.symm C.out) (rlc_dualReflect.symm D.out)
      rw [hC, hD, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hfg.symm




theorem rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    ∃ e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n),
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧
        e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho := by
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfg.2
  obtain ⟨hpBox, hqBox⟩ :=
    rlc_reflectedFilledBoundary_endpoints_mem_crossedBox
      hn gamma gamma' rho hpqAdj hbd
  let rp : (rlc_connectorCrossedBoxPlanar n).V :=
    ⟨rlc_primalDualReflect p, hpBox⟩
  let rq : (rlc_connectorCrossedBoxPlanar n).V :=
    ⟨rlc_primalDualReflect q, hqBox⟩
  have hrpqAdj : (hypercubicLattice 2).Adj
      (rlc_primalDualReflect p) (rlc_primalDualReflect q) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqAdj ⊢
    simp only [rlc_primalDualReflect_zero, rlc_primalDualReflect_one]
    omega
  have hrprq : (rlc_connectorCrossedBoxPlanar n).G.Adj rp rq :=
    hrpqAdj
  let e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n) :=
    ⟨s(rp, rq), (SimpleGraph.mem_edgeSet _).mpr hrprq⟩
  refine ⟨e, ?_, ?_⟩
  · calc
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          s(rlc_primalDualReflect p, rlc_primalDualReflect q) := by
            rfl
      _ = Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) := by
        rw [hpq]
        rfl
      _ = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) :=
        rlc_sharedPrimalEdge_dualReflect hfg.1
  · rw [rlc_connectorReflectedFilledCut, Ising.kwg_mem_cutSet]
    change Ising.kwg_isSplit
      (rlc_connectorReflectedFilledColour gamma gamma' rho) s(rp, rq)
    rw [Ising.kwg_isSplit_mk]
    rw [bdEdge_mk] at hbd
    by_cases hp : p ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
    · have hq : q ∉
          rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := hbd.mp hp
      simp [rlc_connectorReflectedFilledColour, rp, rq, hp, hq]
    · have hq : q ∈
          rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
        by_contra hq
        exact hp (hbd.mpr hq)
      simp [rlc_connectorReflectedFilledColour, rp, rq, hp, hq]




theorem rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents {n : Int}
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
    (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
      sharedPrimalEdge f g) :
    Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e =
      s((whb_faceRegion
          (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f,
        (whb_faceRegion
          (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) := by
  let P := rlc_connectorCrossedBoxPlanar n
  have hpair : s(Ising.kwg_flankLeft P e, Ising.kwg_flankRight P e) =
      s(f, g) :=
    (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj P e) hfg).mpr
      ((Ising.kwg_flanks_shared P e).trans he)
  unfold Ising.kwg_dualEnds
  rw [Sym2.eq_iff] at hpair ⊢
  rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨congrArg _ hleft, congrArg _ hright⟩
  · exact Or.inr ⟨congrArg _ hleft, congrArg _ hright⟩


def RlcCentralFaceMinimalReflectedCutPiece {n : Int}
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))) : Prop :=
  S.Nonempty ∧
    Ising.kwg_IsEven
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) S ∧
    ∀ T : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)),
      T ⊆ S → T.Nonempty →
        Ising.kwg_IsEven
          (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) T →
        T = S



theorem rlc_reflectedFilledCut_incident_component_out_mem_interior {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
    {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hinc : Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    C.out ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  obtain ⟨f, g, hfg, heEmbedded⟩ :=
    rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier
      gamma gamma' rho e heCut
  have hrefAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfg.1
  have heCarrier :=
    rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      hrefAdj e heEmbedded
  rw [heCarrier, Ising.kwg_incidentMod2_mk] at hinc
  obtain ⟨hfInt, hgInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hfg
  rcases hinc with hinc | hinc
  · have hout : C.out = rlc_dualReflect f := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hfInt
      exact hinc.1.trans C.out_eq.symm
    simpa [hout] using hfInt
  · have hout : C.out = rlc_dualReflect g := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hgInt
      exact hinc.1.trans C.out_eq.symm
    simpa [hout] using hgInt


noncomputable def rlc_crossedBoxOuterFace (n : Int) :
    Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
  (whb_faceRegion
    (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
      (![-2 * n - 2, -n - 1] : Site 2)



theorem rlc_reflectedFilledCut_incident_component_ne_outer {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
    {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hinc : Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    C ≠ rlc_crossedBoxOuterFace n := by
  have hCInt := rlc_reflectedFilledCut_incident_component_out_mem_interior
    hn gamma gamma' rho heCut hinc
  intro houter
  have hcomp : (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk C.out =
      (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
          (![-2 * n - 2, -n - 1] : Site 2) := by
    calc
      _ = C := C.out_eq
      _ = rlc_crossedBoxOuterFace n := houter
      _ = _ := rfl
  have hout := rlc_crossedBox_interiorFace_component_singleton hCInt hcomp
  have h0 := congrArg (fun x : Site 2 => x 0) hout
  rw [mem_rect] at hCInt
  simp only [Matrix.cons_val_zero] at h0
  omega



theorem rlc_minimalReflectedCutPiece_carrierReachable {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
    (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
    {C D : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hCinc : ∃ e ∈ S, Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e))
    (hDinc : ∃ e ∈ S, Ising.kwg_incidentMod2 D
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable C.out D.out := by
  obtain ⟨eC, heCS, heCinc⟩ := hCinc
  obtain ⟨eD, heDS, heDinc⟩ := hDinc
  have hCout : C ≠ rlc_crossedBoxOuterFace n :=
    rlc_reflectedFilledCut_incident_component_ne_outer
      hn gamma gamma' rho (hSsub heCS) heCinc
  have hDout : D ≠ rlc_crossedBoxOuterFace n :=
    rlc_reflectedFilledCut_incident_component_ne_outer
      hn gamma gamma' rho (hSsub heDS) heDinc
  have hdual := Ising.kwg_minimalEvenFinset_nonOuter_reachable
    (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) S
      (rlc_crossedBoxOuterFace n) hSmin.1 hSmin.2.1 hSmin.2.2
      hCout hDout ⟨eC, heCS, heCinc⟩ ⟨eD, heDS, heDinc⟩
  let forgetOuter : Ising.kwg_deleteVertexGraph
        (Ising.kwg_faceSupportGraph
          (fun e : ↑S => Ising.kwg_dualEnds
            (rlc_connectorCrossedBoxPlanar n) e.1))
        (rlc_crossedBoxOuterFace n) →g
      Ising.kwg_faceSupportGraph
        (fun e : ↑S => Ising.kwg_dualEnds
          (rlc_connectorCrossedBoxPlanar n) e.1) :=
    { toFun := id
      map_rel' := fun {_ _} h => h.1 }
  have hsupport := hdual.map forgetOuter
  simpa [forgetOuter] using hsupport.map
    (rlc_reflectedCutSupportHom hn gamma gamma' rho S hSsub)



theorem rlc_minimalReflectedCutPiece_boundaryCarriers_reachable {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
    (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
    {f g p q : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
    (hpq : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj p q)
    {e e' : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heS : e ∈ S) (he'S : e' ∈ S)
    (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
      sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g))
    (he' : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e' =
      sharedPrimalEdge (rlc_dualReflect p) (rlc_dualReflect q)) :
    (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable
      (rlc_dualReflect f) (rlc_dualReflect p) := by
  let R := whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))
  let Cf : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect f)
  let Cg : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect g)
  let Cp : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect p)
  let Cq : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect q)
  obtain ⟨hfInt, hgInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hfg
  obtain ⟨hpInt, hqInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hpq
  have hCfCg : Cf ≠ Cg := by
    intro hEq
    have hrefEq : rlc_dualReflect f = rlc_dualReflect g :=
      rlc_crossedBox_interiorFace_component_singleton hfInt hEq
    exact hfg.1.ne (rlc_dualReflect.injective hrefEq)
  have hCpCq : Cp ≠ Cq := by
    intro hEq
    have hrefEq : rlc_dualReflect p = rlc_dualReflect q :=
      rlc_crossedBox_interiorFace_component_singleton hpInt hEq
    exact hpq.1.ne (rlc_dualReflect.injective hrefEq)
  have heEnds : Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e =
      s(Cf, Cg) := by
    exact rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      ((rlc_adj_dualReflect f g).mp hfg.1) e he
  have he'Ends : Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e' =
      s(Cp, Cq) := by
    exact rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      ((rlc_adj_dualReflect p q).mp hpq.1) e' he'
  have hCfInc : Ising.kwg_incidentMod2 Cf
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e) := by
    rw [heEnds, Ising.kwg_incidentMod2_mk]
    exact Or.inl ⟨rfl, hCfCg.symm⟩
  have hCpInc : Ising.kwg_incidentMod2 Cp
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e') := by
    rw [he'Ends, Ising.kwg_incidentMod2_mk]
    exact Or.inl ⟨rfl, hCpCq.symm⟩
  have hreach := rlc_minimalReflectedCutPiece_carrierReachable
    hn gamma gamma' rho S hSsub hSmin
      (C := Cf) (D := Cp) ⟨e, heS, hCfInc⟩ ⟨e', he'S, hCpInc⟩
  have hCfOut : Cf.out = rlc_dualReflect f := by
    symm
    apply rlc_crossedBox_interiorFace_component_singleton hfInt
    exact Cf.out_eq.symm
  have hCpOut : Cp.out = rlc_dualReflect p := by
    symm
    apply rlc_crossedBox_interiorFace_component_singleton hpInt
    exact Cp.out_eq.symm
  simpa [hCfOut, hCpOut] using hreach




theorem rlc_faceBoundaryEdge_exists_minimalReflectedCutPeel {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    ∃ (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
      (S R : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))),
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧
        S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho ∧
        e ∈ S ∧ RlcCentralFaceMinimalReflectedCutPiece S ∧
        R = rlc_connectorReflectedFilledCut gamma gamma' rho \ S ∧
        Ising.kwg_IsEven
          (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) R ∧
        Disjoint S R ∧
        S ∪ R = rlc_connectorReflectedFilledCut gamma gamma' rho := by
  obtain ⟨e, heEmbedded, heCut⟩ :=
    rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge
      hn gamma gamma' rho hfg
  obtain ⟨S, R, hSCut, heS, hSne, hSeven, hSmin,
      hR, hReven, hdisjoint, hunion⟩ :=
    Ising.kwg_exists_minimalEvenFinset_peel_mem
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) heCut
      (rlc_connectorReflectedFilledCut_isEven gamma gamma' rho)
  exact ⟨e, S, R, heEmbedded, hSCut, heS,
    ⟨hSne, hSeven, hSmin⟩, hR, hReven, hdisjoint, hunion⟩



theorem rlc_sharedPrimalEdge_eq_unshift_flankFaces {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    sharedPrimalEdge x y =
      Sym2.map phb_doubleDualEquiv.symm (flankFaces x y) := by
  rcases face_adj_dir hxy with rfl | rfl | rfl | rfl <;>
    simp [sharedPrimalEdge, flankFaces, phb_doubleDualEquiv]
  all_goals try split_ifs <;> try omega
  all_goals try simp [Sym2.eq_iff]
  all_goals ring



theorem rlc_map_flankFaces_primalDualReflect_symm {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q) :
    Sym2.map rlc_dualReflect
        (flankFaces (rlc_primalDualReflect.symm p)
          (rlc_primalDualReflect.symm q)) =
      flankFaces p q := by
  rcases face_adj_dir hpq with rfl | rfl | rfl | rfl <;>
    simp [flankFaces, rlc_dualReflect, rlc_dualReflectFun,
      rlc_primalDualReflect, rlc_primalDualReflectInvFun, Sym2.eq_iff]
  all_goals try split_ifs <;> try omega
  all_goals
    rw [Sym2.map_mk, Sym2.eq_iff]
    left
    constructor <;> ext i <;> fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun]



theorem rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
    {n : Int} {f g x : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfBox : f ∈ rlc_connectorFaceBox n)
    (_hgBox : g ∈ rlc_connectorFaceBox n)
    (hx : x ∈ sharedPrimalEdge f g) :
    x ∈ rlc_connectorBox n := by
  have hfRect : f ∈ rect (-2 * n) (2 * n - 1) (-n) (n - 1) := by
    simpa [rlc_connectorFaceBox] using hfBox
  obtain ⟨p, q, hshared, _hpq, hpBox, hqBox⟩ :=
    rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect hfRect hfg
  rw [hshared, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · simpa [rlc_connectorBox] using hpBox
  · simpa [rlc_connectorBox] using hqBox




theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_covers_leftRegionBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge
      (jec_leftRegion ((B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom)) s(p, q)) :
    flankFaces p q ∈
      ((B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom).edges := by
  let p0 := rlc_primalDualReflect.symm p
  let q0 := rlc_primalDualReflect.symm q
  have hpq0 : (hypercubicLattice 2).Adj p0 q0 := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq ⊢
    simp only [p0, q0, rlc_primalDualReflect_symm_zero,
      rlc_primalDualReflect_symm_one]
    omega
  have hbdRef : bdEdge
      (rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
      s(p, q) := by
    rwa [B.reflectedFilledReachSet_eq_leftRegion]
  have hmap : Sym2.map rlc_primalDualReflect s(p0, q0) = s(p, q) := by
    simp [p0, q0]
  have hbd0 : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p0, q0) := by
    apply (rlc_bdEdge_reflectedPrimalRegion_map
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p0, q0)).mp
    rwa [hmap]
  have hflankEdge : flankFaces p0 q0 ∈
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).edgeSet :=
    (phb_flankFaces_mem_faceBoundaryGraph_iff hpq0).2 hbd0
  have hflankContour : flankFaces p0 q0 ∈ B.contour.edges :=
    B.contour_covers _ hflankEdge
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  refine ⟨flankFaces p0 q0, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hflankContour
  · simpa [p0, q0] using rlc_map_flankFaces_primalDualReflect_symm hpq





theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} (hfg : s(f, g) ∈ B.contour.edges) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        (((rlc_primalDualReflect p ∈ jec_leftRegion C) ∧
            rlc_primalDualReflect q ∉ jec_leftRegion C) ∨
          (rlc_primalDualReflect p ∉ jec_leftRegion C ∧
            rlc_primalDualReflect q ∈ jec_leftRegion C)) := by
  dsimp only
  have hfgAdj := B.contour.adj_of_mem_edges hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfgAdj.1
  refine ⟨p, q, hpq, hpqAdj, ?_⟩
  have hpqBoundary : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfgAdj.2
  rw [bdEdge_mk] at hpqBoundary
  have hregion := B.reflectedFilledReachSet_eq_leftRegion
  have hp_mem : rlc_primalDualReflect p ∈
      rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ↔
      p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    rw [rlc_mem_reflectedPrimalRegion_iff]
    simp
  have hq_mem : rlc_primalDualReflect q ∈
      rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ↔
      q ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    rw [rlc_mem_reflectedPrimalRegion_iff]
    simp
  rw [hregion] at hp_mem hq_mem
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · left
    refine ⟨hp_mem.mpr hp, ?_⟩
    intro hq
    exact (hpqBoundary.mp hp) (hq_mem.mp hq)
  · right
    have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hpqBoundary.mpr hq)
    exact ⟨fun hp' => hp (hp_mem.mp hp'), hq_mem.mpr hq⟩




theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_shiftedFlank_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} (hfg : s(f, g) ∈ B.contour.edges) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ h k : Site 2,
      flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧
        (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
            phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
          (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
            phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
  dsimp only
  obtain ⟨p, q, hpq, _hpqAdj, hside⟩ :=
    B.reflectedContour_edge_sideToggle hfg
  have hfgAdj := B.contour.adj_of_mem_edges hfg
  have hrefAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfgAdj.1
  obtain ⟨h, k, hflank, _hkAdj⟩ := flankFaces_latAdj hrefAdj
  refine ⟨h, k, hflank, ?_⟩
  have hsites : s(rlc_primalDualReflect p, rlc_primalDualReflect q) =
      s(phb_doubleDualEquiv.symm h,
        phb_doubleDualEquiv.symm k) := by
    calc
      s(rlc_primalDualReflect p, rlc_primalDualReflect q) =
          Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) := by
            rw [hpq]
            rfl
      _ = sharedPrimalEdge (rlc_dualReflect f)
          (rlc_dualReflect g) := rlc_sharedPrimalEdge_dualReflect hfgAdj.1
      _ = Sym2.map phb_doubleDualEquiv.symm
          (flankFaces (rlc_dualReflect f) (rlc_dualReflect g)) :=
            rlc_sharedPrimalEdge_eq_unshift_flankFaces hrefAdj
      _ = s(phb_doubleDualEquiv.symm h,
          phb_doubleDualEquiv.symm k) := by rw [hflank]; rfl
  rw [Sym2.eq_iff] at hsites
  rcases hsites with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · simpa [← hp, ← hq] using hside
  · rcases hside with hside | hside
    · exact Or.inr ⟨by simpa [← hq] using hside.2,
        by simpa [← hp] using hside.1⟩
    · exact Or.inl ⟨by simpa [← hq] using hside.2,
        by simpa [← hp] using hside.1⟩



theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedBoundaryEdge_namedFlank_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g h : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
    (hh : h ∈ flankFaces (rlc_dualReflect f) (rlc_dualReflect g)) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ k : Site 2,
      flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧
        (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
            phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
          (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
            phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
  dsimp only
  have hfgContour : s(f, g) ∈ B.contour.edges :=
    B.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hfg)
  obtain ⟨a, b, hab, hside⟩ :=
    B.reflectedContour_edge_shiftedFlank_sideToggle hfgContour
  rw [hab, Sym2.mem_iff] at hh
  rcases hh with ha | hb
  · subst a
    exact ⟨b, hab, hside⟩
  · subst b
    refine ⟨a, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hab
    · rcases hside with hside | hside
      · exact Or.inr ⟨hside.2, hside.1⟩
      · exact Or.inl ⟨hside.2, hside.1⟩




theorem rlc_connectorCentralFaceRegion_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {h k : Site 2}
    (hh : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hk : k ∈ rlc_connectorCentralFaceRegion gamma gamma') :
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hkBox : k ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
        ⟨h, hhBox⟩ ⟨k, hkBox⟩ := by
  have hhSet : h ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hh
  have hkSet : k ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hk
  obtain ⟨hhBox, hsBox, hhReach⟩ := hhSet
  obtain ⟨hkBox, hsBox', hkReach⟩ := hkSet
  have hsEq : (⟨rlc_connectorCentralFace, hsBox⟩ :
      RlcConnectorFaceVertex n) = ⟨rlc_connectorCentralFace, hsBox'⟩ := rfl
  rw [hsEq] at hhReach
  exact ⟨hhBox, hkBox, hhReach.symm.trans hkReach⟩





theorem RlcCentralFaceRetainedAnchoredBoundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {t u h t' u' h' : Site 2}
    (htu : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t u)
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hhFlank : h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u))
    (ht'u' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t' u')
    (hh'Region : h' ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh'Flank : h' ∈ flankFaces
      (rlc_dualReflect t') (rlc_dualReflect u')) :
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hh'Box : h' ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
          ⟨h, hhBox⟩ ⟨h', hh'Box⟩ ∧
        ∃ k k' : Site 2,
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (B.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet
                gamma gamma' rho))).map rlc_dualReflectLatticeHom
           (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
                phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
              (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
                phb_doubleDualEquiv.symm k ∈ jec_leftRegion C))) ∧
          (let C := (B.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet
                gamma gamma' rho))).map rlc_dualReflectLatticeHom
           (((phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
                phb_doubleDualEquiv.symm k' ∉ jec_leftRegion C) ∨
              (phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C ∧
                phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) := by
  obtain ⟨hhBox, hh'Box, hreach⟩ :=
    rlc_connectorCentralFaceRegion_reachable hhRegion hh'Region
  obtain ⟨k, hkFlank, hkSide⟩ :=
    B.reflectedBoundaryEdge_namedFlank_sideToggle htu hhFlank
  obtain ⟨k', hk'Flank, hk'Side⟩ :=
    B.reflectedBoundaryEdge_namedFlank_sideToggle ht'u' hh'Flank
  exact ⟨hhBox, hh'Box, hreach, k, k', hkFlank, hk'Flank,
    hkSide, hk'Side⟩





theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_hits_reflectedContour_of_oppositeSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {h h' : Site 2} (hhBox : h ∈ rlc_connectorFaceBox n)
    (hh'Box : h' ∈ rlc_connectorFaceBox n)
    (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
    (hopposite :
      let C := (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom
      ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
    ∃ (z : RlcConnectorFaceVertex n) (f : Site 2),
      f ∈ B.contour.support ∧
        phb_doubleDualEquiv.symm z.1 = rlc_dualReflect f := by
  let C := (B.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  let cutToLattice : rlc_connectorFiniteFaceCutGraph gamma gamma' →g
      hypercubicLattice 2 :=
    { toFun := fun z : RlcConnectorFaceVertex n => z.1
      map_rel' := fun {x y} hxy =>
        ((rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' x.1 y.1).mp hxy).1 }
  let shiftUp : hypercubicLattice 2 →g hypercubicLattice 2 :=
    { toFun := phb_doubleDualEquiv.symm
      map_rel' := by
        intro x y hxy
        apply phb_doubleDualShift_latAdj.mp
        simpa [phb_doubleDualEquiv, phb_doubleDualShift] using hxy }
  obtain ⟨w⟩ := hreach
  let wShift := (w.map cutToLattice).map shiftUp
  have recover {x : Site 2} (hxC : x ∈ C.support)
      (hxW : x ∈ wShift.support) :
      ∃ (z : RlcConnectorFaceVertex n) (f : Site 2),
        f ∈ B.contour.support ∧
          phb_doubleDualEquiv.symm z.1 = rlc_dualReflect f := by
    change x ∈ ((B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom).support at hxC
    rw [SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hxC
    obtain ⟨f, hf, hfx⟩ := hxC
    change x ∈ ((w.map cutToLattice).map shiftUp).support at hxW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxW
    obtain ⟨y, hyW, hyx⟩ := hxW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hyW
    obtain ⟨z, _hz, hzy⟩ := hyW
    refine ⟨z, f, hf, ?_⟩
    calc
      phb_doubleDualEquiv.symm z.1 = shiftUp (cutToLattice z) := rfl
      _ = shiftUp y := congrArg shiftUp hzy
      _ = x := hyx
      _ = rlc_dualReflect f := hfx.symm
  dsimp only at hopposite
  rcases hopposite with hopposite | hopposite
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift hopposite.1 hopposite.2
    have hon := jec_leftRegion_bdEdge_support C hpq.1 hpq.2
    rcases hon with hpC | hqC
    · exact recover hpC (wShift.fst_mem_support_of_mem_edges hpqW)
    · exact recover hqC (wShift.snd_mem_support_of_mem_edges hpqW)
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift.reverse (by simpa [wShift] using hopposite.2)
        (by simpa [wShift] using hopposite.1)
    have hon := jec_leftRegion_bdEdge_support C hpq.1 hpq.2
    have hpqForward : s(p, q) ∈ wShift.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hpqW
    rcases hon with hpC | hqC
    · exact recover hpC (wShift.fst_mem_support_of_mem_edges hpqForward)
    · exact recover hqC (wShift.snd_mem_support_of_mem_edges hpqForward)




theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_goodContourEdge_of_oppositeSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {h h' : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hhBox : h ∈ rlc_connectorFaceBox n)
    (hh'Box : h' ∈ rlc_connectorFaceBox n)
    (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
    (hopposite :
      let C := (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom
      ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
    ∃ (f g : Site 2) (z z' : RlcConnectorFaceVertex n),
      s(f, g) ∈ B.contour.edges ∧
        (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' ∧
        z.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        z'.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(z.1, z'.1) ∧
        rlc_dualReflect f ∈ rlc_connectorBox n ∧
        rlc_dualReflect g ∈ rlc_connectorBox n ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  let C := (B.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  let cutToLattice : rlc_connectorFiniteFaceCutGraph gamma gamma' →g
      hypercubicLattice 2 :=
    { toFun := fun z : RlcConnectorFaceVertex n => z.1
      map_rel' := fun {x y} hxy =>
        ((rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' x.1 y.1).mp hxy).1 }
  let shiftUp : hypercubicLattice 2 →g hypercubicLattice 2 :=
    { toFun := phb_doubleDualEquiv.symm
      map_rel' := by
        intro x y hxy
        apply phb_doubleDualShift_latAdj.mp
        simpa [phb_doubleDualEquiv, phb_doubleDualShift] using hxy }
  obtain ⟨w⟩ := hreach
  let wShift := (w.map cutToLattice).map shiftUp
  have recover {p q : Site 2}
      (hpqW : s(p, q) ∈ wShift.edges)
      (hpqBoundary : bdEdge (jec_leftRegion C) s(p, q)) :
      ∃ (f g : Site 2) (z z' : RlcConnectorFaceVertex n),
        s(f, g) ∈ B.contour.edges ∧
          (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' ∧
          z.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          z'.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(z.1, z'.1) ∧
          rlc_dualReflect f ∈ rlc_connectorBox n ∧
          rlc_dualReflect g ∈ rlc_connectorBox n ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma' := by
    have hpqAdj : (hypercubicLattice 2).Adj p q :=
      wShift.adj_of_mem_edges hpqW
    change s(p, q) ∈ ((w.map cutToLattice).map shiftUp).edges at hpqW
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at hpqW
    obtain ⟨e, heW, heShift⟩ := hpqW
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at heW
    obtain ⟨e0, he0W, heCut⟩ := heW
    induction e0 using Sym2.inductionOn with
    | _ z z' =>
        have hzzCut : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' :=
          w.adj_of_mem_edges he0W
        have hzzData := (rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' z.1 z'.1).mp hzzCut
        have hmapped : s(shiftUp (cutToLattice z),
            shiftUp (cutToLattice z')) = s(p, q) := by
          calc
            s(shiftUp (cutToLattice z), shiftUp (cutToLattice z')) =
                Sym2.map shiftUp (Sym2.map cutToLattice s(z, z')) := rfl
            _ = Sym2.map shiftUp e := congrArg (Sym2.map shiftUp) heCut
            _ = s(p, q) := heShift
        have hshift : flankFaces (shiftUp (cutToLattice z))
            (shiftUp (cutToLattice z')) = sharedPrimalEdge z.1 z'.1 := by
          have h := phb_sharedPrimalEdge_shift_eq_flankFaces
            (shiftUp.map_rel hzzData.1)
          calc
            flankFaces (shiftUp (cutToLattice z))
                (shiftUp (cutToLattice z')) =
                sharedPrimalEdge
                  (phb_doubleDualShift (shiftUp (cutToLattice z)))
                  (phb_doubleDualShift (shiftUp (cutToLattice z'))) := h.symm
            _ = sharedPrimalEdge z.1 z'.1 := by
              have hz : phb_doubleDualShift (shiftUp (cutToLattice z)) = z.1 := by
                change phb_doubleDualEquiv (phb_doubleDualEquiv.symm z.1) = z.1
                exact Equiv.apply_symm_apply _ _
              have hz' : phb_doubleDualShift (shiftUp (cutToLattice z')) = z'.1 := by
                change phb_doubleDualEquiv (phb_doubleDualEquiv.symm z'.1) = z'.1
                exact Equiv.apply_symm_apply _ _
              rw [hz, hz']
        have hflankCut : flankFaces p q = sharedPrimalEdge z.1 z'.1 := by
          calc
            flankFaces p q = flankFacesSym s(p, q) := by rw [flankFacesSym_mk]
            _ = flankFacesSym
                s(shiftUp (cutToLattice z), shiftUp (cutToLattice z')) :=
              congrArg flankFacesSym hmapped.symm
            _ = flankFaces (shiftUp (cutToLattice z))
                (shiftUp (cutToLattice z')) := flankFacesSym_mk _ _
            _ = sharedPrimalEdge z.1 z'.1 := hshift
        have hcontour := B.reflectedContour_covers_leftRegionBoundary
          hpqAdj hpqBoundary
        change flankFaces p q ∈ C.edges at hcontour
        dsimp only [C] at hcontour
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_mapLe_eq_edges] at hcontour
        obtain ⟨e1, he1Contour, he1Map⟩ := hcontour
        induction e1 using Sym2.inductionOn with
        | _ f g =>
            have hcarrier : s(rlc_dualReflect f, rlc_dualReflect g) =
                sharedPrimalEdge z.1 z'.1 := by
              calc
                s(rlc_dualReflect f, rlc_dualReflect g) = flankFaces p q := by
                  simpa using he1Map
                _ = sharedPrimalEdge z.1 z'.1 := hflankCut
            have hflank : flankFaces (rlc_dualReflect f)
                (rlc_dualReflect g) = s(z.1, z'.1) := by
              calc
                flankFaces (rlc_dualReflect f) (rlc_dualReflect g) =
                    flankFacesSym s(rlc_dualReflect f,
                      rlc_dualReflect g) := by rw [flankFacesSym_mk]
                _ = flankFacesSym (sharedPrimalEdge z.1 z'.1) :=
                  congrArg flankFacesSym hcarrier
                _ = flankFacesSym (symPrimal z.1 z'.1) := by
                  rw [symPrimal_eq_shared hzzData.1]
                _ = s(z.1, z'.1) := flankFacesSym_symPrimal hzzData.1
            have hzW := w.fst_mem_support_of_mem_edges he0W
            have hz'W := w.snd_mem_support_of_mem_edges he0W
            have hzRegion := rlc_connectorCentralFaceRegion_of_cut_reachable
              gamma gamma' hhRegion hhBox z.2 ⟨w.takeUntil z hzW⟩
            have hz'Region := rlc_connectorCentralFaceRegion_of_cut_reachable
              gamma gamma' hhRegion hhBox z'.2 ⟨w.takeUntil z' hz'W⟩
            have hfShared : rlc_dualReflect f ∈
                sharedPrimalEdge z.1 z'.1 := by
              rw [← hcarrier, Sym2.mem_iff]
              exact Or.inl rfl
            have hgShared : rlc_dualReflect g ∈
                sharedPrimalEdge z.1 z'.1 := by
              rw [← hcarrier, Sym2.mem_iff]
              exact Or.inr rfl
            refine ⟨f, g, z, z', he1Contour, hzzCut, hzRegion,
              hz'Region, hflank, ?_, ?_, ?_⟩
            · exact rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
                hzzData.1 z.2 z'.2 hfShared
            · exact rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
                hzzData.1 z.2 z'.2 hgShared
            · rw [hcarrier]
              exact hzzData.2
  dsimp only at hopposite
  rcases hopposite with hopposite | hopposite
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift hopposite.1 hopposite.2
    exact recover hpqW hpq.2
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift.reverse (by simpa [wShift] using hopposite.2)
        (by simpa [wShift] using hopposite.1)
    have hpqForward : s(p, q) ∈ wShift.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hpqW
    exact recover hpqForward hpq.2



theorem rlc_flank_mem_vertexLoop_support
    {x z h : Site 2} (hxz : (hypercubicLattice 2).Adj x z)
    (hh : h ∈ flankFaces x z) :
    h ∈ (jwc_vertexLoop (x 0) (x 1)).support := by
  rcases adj_cases hxz with ⟨hx0, hx1⟩ | ⟨hx1, hx0⟩
  · rcases hx1 with hx1 | hx1
    · unfold flankFaces at hh
      simp [hx0, hx1] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
    · unfold flankFaces at hh
      simp [hx0, hx1] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
  · rcases hx0 with hx0 | hx0
    · unfold flankFaces at hh
      simp [hx1, hx0] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
    · unfold flankFaces at hh
      simp [hx1, hx0] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega



theorem rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (x : Site 2)
    (hx : x ∉ rlc_connectorBarrier gamma gamma') :
    ∀ e ∈ (jwc_vertexLoop (x 0) (x 1)).edges,
      e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
  intro e he
  simp only [jwc_vertexLoop, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_NE_NW _ _, ?_⟩
    rw [jwc_shared_NE_NW]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        left
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_NW_SW _ _, ?_⟩
    rw [jwc_shared_NW_SW]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        right
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_SW_SE _ _, ?_⟩
    rw [jwc_shared_SW_SE]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        right
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_SE_NE _ _, ?_⟩
    rw [jwc_shared_SE_NE]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        left
        ext i
        fin_cases i <;> simp)



theorem rlc_centralFaceRegion_flank_transfer_interior
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x z y h k : Site 2}
    (hxz : (hypercubicLattice 2).Adj x z)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hxNot : x ∉ rlc_connectorBarrier gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x z) (hk : k ∈ flankFaces x y) :
    k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let loop := jwc_vertexLoop (x 0) (x 1)
  have hloopBox : ∀ f ∈ loop.support, f ∈ rlc_connectorFaceBox n := by
    intro f hf
    dsimp only [loop] at hf
    simp only [jwc_vertexLoop, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_connectorFaceBox, mem_rect] <;> omega
  let cutLoop := loop.transfer
    (rlc_connectorFourTraceFaceCutGraph gamma gamma')
      (rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph
        gamma gamma' x hxNot)
  have hhLoop : h ∈ loop.support := rlc_flank_mem_vertexLoop_support hxz hh
  have hkLoop : k ∈ loop.support := rlc_flank_mem_vertexLoop_support hxy hk
  have hhCut : h ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hhLoop
  have hkCut : k ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hkLoop
  let a := rlc_centralFaceContactSubwalk cutLoop hhCut hkCut
  have haBox : ∀ f ∈ a.support, f ∈ rlc_connectorFaceBox n := by
    intro f hf
    dsimp only [a] at hf
    rw [rlc_centralFaceContactSubwalk,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hf
    rcases hf with hf | hf
    · have hfCut := cutLoop.support_takeUntil_subset_support hhCut
          (by simpa using hf)
      exact hloopBox f (by
        simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hfCut)
    · have hfCut := cutLoop.support_takeUntil_subset_support hkCut hf
      exact hloopBox f (by
        simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hfCut)
  let aFinite := a.induce (rlc_connectorFaceBox n : Set (Site 2)) haBox
  have hhBox := hloopBox h hhLoop
  have hkBox := hloopBox k hkLoop
  have hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨k, hkBox⟩ := ⟨aFinite⟩
  exact rlc_connectorCentralFaceRegion_of_cut_reachable
    gamma gamma' hhRegion hhBox hkBox hreach



theorem rlc_centralFaceRegion_other_flank_of_nonwall {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y h k : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x y)
    (hkBox : k ∈ rlc_connectorFaceBox n) :
    k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  by_cases heq : h = k
  · simpa [heq] using hhRegion
  obtain ⟨f, g, hfg, hfgAdj⟩ := flankFaces_latAdj hxy
  have hshared : sharedPrimalEdge f g = s(x, y) := by
    rw [← symPrimal_eq_shared hfgAdj, ← symPrimalSym_mk,
      ← hfg, symPrimalSym_flankFaces hxy]
  rw [hfg, Sym2.mem_iff] at hh hk
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
  · exact False.elim (heq rfl)
  · apply rlc_connectorCentralFaceRegion_of_cut_adj gamma gamma'
      hhRegion hkBox
    rw [rlc_connectorFourTraceFaceCutGraph_adj, hshared]
    exact ⟨hfgAdj, hnot⟩
  · apply rlc_connectorCentralFaceRegion_of_cut_adj gamma gamma'
      hhRegion hkBox
    rw [rlc_connectorFourTraceFaceCutGraph_adj,
      sharedPrimalEdge_comm_of_adj hfgAdj.symm, hshared]
    exact ⟨hfgAdj.symm, hnot⟩
  · exact False.elim (heq rfl)

set_option maxRecDepth 2000 in


theorem rlc_incident_flank_intersection_of_not_opposite
    {x a b : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1)) :
    ∃ k : Site 2, k ∈ flankFaces x a ∧ k ∈ flankFaces x b := by
  rcases face_adj_dir hxa with rfl | rfl | rfl | rfl <;>
    rcases face_adj_dir hxb with rfl | rfl | rfl | rfl
  all_goals
    simp [flankFaces] at hab hopp ⊢ <;>
    try omega
  all_goals
    rw [if_neg (by omega)] <;> simp



theorem rlc_flank_mem_connectorFaceBox_of_interior
    {n : Int} {x y h : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hh : h ∈ flankFaces x y) :
    h ∈ rlc_connectorFaceBox n := by
  have hhLoop := rlc_flank_mem_vertexLoop_support hxy hh
  simp only [jwc_vertexLoop, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hhLoop
  rcases hhLoop with rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_connectorFaceBox, mem_rect] <;> omega






theorem rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1))
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a) :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨k, hkIn, hkOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxb hab hopp
  have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxa hxInterior hkIn
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnot hhRegion hh hkIn hkBox
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb
  · simp [rlc_connectorBox, mem_rect]
    omega
  · simp [rlc_connectorBox, mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxb
    omega
  · exact hkRegion
  · exact hkOut




theorem rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1))
    (hxBox : x ∈ rlc_connectorBox n)
    (hbBox : b ∈ rlc_connectorBox n)
    (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a)
    (hcommonBox : ∀ k : Site 2,
      k ∈ flankFaces x a → k ∈ flankFaces x b →
        k ∈ rlc_connectorFaceBox n) :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨k, hkIn, hkOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxb hab hopp
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnot hhRegion hh hkIn (hcommonBox k hkIn hkOut)
  exact rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb hxBox hbBox hkRegion hkOut





theorem rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hnotIn : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a)
    (hside : ∃ y : Site 2,
      (hypercubicLattice 2).Adj x y ∧
      y ≠ a ∧ y ≠ b ∧
      ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1) ∧
      ¬ (y 0 + b 0 = 2 * x 0 ∧ y 1 + b 1 = 2 * x 1) ∧
      s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨y, hxy, hya, hyb, hay, hybOpp, hnotSide⟩ := hside
  obtain ⟨k, hkIn, hkSide⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxy hya.symm hay
  have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxa hxInterior hkIn
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnotIn hhRegion hh hkIn hkBox
  obtain ⟨l, hlSide, hlOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxy hxb hyb hybOpp
  have hlBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxy hxInterior hlSide
  have hlRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxy hnotSide hkRegion hkSide hlSide hlBox
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb
  · simp [rlc_connectorBox, mem_rect]
    omega
  · simp [rlc_connectorBox, mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxb
    omega
  · exact hlRegion
  · exact hlOut




noncomputable def rlc_flipXLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_flipXFun
  map_rel' := by
    intro x y hxy
    change (x 0 - y 0).natAbs + (x 1 - y 1).natAbs = 1 at hxy
    change (-x 0 - -y 0).natAbs + (x 1 - y 1).natAbs = 1
    have h0 : (-x 0 - -y 0).natAbs = (x 0 - y 0).natAbs := by
      rw [show -x 0 - -y 0 = -(x 0 - y 0) by ring, Int.natAbs_neg]
    rw [h0]
    exact hxy

@[simp] theorem rlc_doubleDualShift_flipX_eq_dualReflect_symm
    (z : Site 2) :
    phb_doubleDualShift (rlc_flipX z) = rlc_dualReflect.symm z := by
  ext i
  fin_cases i <;>
    simp [phb_doubleDualShift, rlc_flipX, rlc_flipXFun,
      rlc_dualReflect, rlc_dualReflectInvFun]



theorem rlc_doubleDualShift_endpoint_mem_flankFaces {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q) :
    phb_doubleDualShift p ∈ flankFaces p q ∨
      phb_doubleDualShift q ∈ flankFaces p q := by
  classical
  rcases adj_cases hpq with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · unfold flankFaces
    rw [if_pos h0]
    rcases h1 with hpq | hqp
    · left
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
    · right
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
  · unfold flankFaces
    rw [if_neg (by intro heq; omega)]
    rcases h0 with hpq | hqp
    · left
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
    · right
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega



theorem rlc_fourTrace_axis_vertex_height_eq_endpoint {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') (k : Int)
    (hk : (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma') :
    k = (gamma.1.1 : Site 2) 1 ∨
      k = (gamma'.1.2.1 : Site 2) 1 := by
  rw [rlc_axis_mem_connectorBarrier_iff] at hk
  rcases hk with hright | hleft
  · left
    have heq := hfaith.right_axis_unique hright (by simp)
    exact congrArg (fun z : Site 2 => z 1) heq
  · right
    have heq := hfaith.left_axis_unique hleft (by simp)
    exact congrArg (fun z : Site 2 => z 1) heq



theorem rlc_axisCrossEdge_not_mem_fourTrace_of_between {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hlower : (gamma.1.1 : Site 2) 1 < k)
    (hupper : k < (gamma'.1.2.1 : Site 2) 1) :
    s((![-1, k] : Site 2), ![0, k]) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
  intro he
  have hkBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_right _ _)
  rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith k hkBarrier with hk | hk <;> omega



theorem rlc_axisGapFace_mem_connectorCentralFaceRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {t : Int}
    (htLower : (gamma.1.1 : Site 2) 1 ≤ t)
    (htUpper : t < (gamma'.1.2.1 : Site 2) 1) :
    (![-1, t] : Site 2) ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  classical
  let S : Int := (gamma.1.1 : Site 2) 1
  let U : Int := (gamma'.1.2.1 : Site 2) 1
  have hSBounds : -n ≤ S ∧ S < 0 := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, hfaith.right_axis_strict⟩
  have hUBounds : 0 < U ∧ U ≤ n := by
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hfaith.left_axis_strict, hbox.2.2.2⟩
  have hn : 0 < n := by omega
  have hcentralBox := rlc_connectorCentralFace_mem_faceBox hn
  have hleftZeroBox : (![-1, 0] : Site 2) ∈
      rlc_connectorFaceBox n := by
    simp [rlc_connectorFaceBox, mem_rect]
    omega
  have htBox : (![-1, t] : Site 2) ∈ rlc_connectorFaceBox n := by
    simp [rlc_connectorFaceBox, mem_rect]
    omega
  have hbaseLat : (hypercubicLattice 2).Adj
      rlc_connectorCentralFace (![-1, 0] : Site 2) := by
    simp [rlc_connectorCentralFace, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have hbaseShared : sharedPrimalEdge rlc_connectorCentralFace ![-1, 0] =
      s((![0, 0] : Site 2), ![0, 1]) := by
    simp [rlc_connectorCentralFace, sharedPrimalEdge]
  have hbaseNotWall : sharedPrimalEdge rlc_connectorCentralFace ![-1, 0] ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    rw [hbaseShared]
    intro he
    have hzBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' he (Sym2.mem_mk_left _ _)
    rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
        gamma gamma' hfaith 0 (by simpa using hzBarrier) with h0 | h0
    · change 0 = S at h0
      omega
    · change 0 = U at h0
      omega
  have hbase : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj
      rlc_connectorCentralFace ![-1, 0] := by
    rw [rlc_connectorFourTraceFaceCutGraph_adj]
    exact ⟨hbaseLat, hbaseNotWall⟩
  let vertical : (hypercubicLattice 2).Walk
      (![-1, 0] : Site 2) ![-1, t] := sw_vertSeg (-1) 0 t
  have hverticalEdges : ∀ e ∈ vertical.edges,
      e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ f g =>
        have hfg := vertical.adj_of_mem_edges he
        have hfSupp := vertical.fst_mem_support_of_mem_edges he
        have hgSupp := vertical.snd_mem_support_of_mem_edges he
        change f ∈ (sw_vertSeg (-1) 0 t).support at hfSupp
        change g ∈ (sw_vertSeg (-1) 0 t).support at hgSupp
        rw [sw_vertSeg_mem_support] at hfSupp hgSupp
        obtain ⟨a, ha, rfl⟩ := hfSupp
        obtain ⟨b, hb, rfl⟩ := hgSupp
        rw [Set.mem_uIcc] at ha hb
        have hab : a = b + 1 ∨ b = a + 1 := by
          rcases adj_cases hfg with hvert | hhoriz
          · exact hvert.2
          · simp at hhoriz
        let k := max a b
        have hkLower : S < k := by
          rcases hab with hab | hab
          · have hk : k = a := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
          · have hk : k = b := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
        have hkUpper : k < U := by
          rcases hab with hab | hab
          · have hk : k = a := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
          · have hk : k = b := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
        rw [SimpleGraph.mem_edgeSet,
          rlc_connectorFourTraceFaceCutGraph_adj]
        refine ⟨hfg, ?_⟩
        have hshared : sharedPrimalEdge (![-1, a] : Site 2) ![-1, b] =
            s((![-1, k] : Site 2), ![0, k]) := by
          simp [sharedPrimalEdge, k]
        rw [hshared]
        exact rlc_axisCrossEdge_not_mem_fourTrace_of_between
          gamma gamma' hfaith (by simpa [S] using hkLower)
            (by simpa [U] using hkUpper)
  let verticalCut := vertical.transfer
    (rlc_connectorFourTraceFaceCutGraph gamma gamma') hverticalEdges
  let full : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Walk
      rlc_connectorCentralFace ![-1, t] :=
    (Walk.cons hbase Walk.nil).append verticalCut
  have hfullBox : ∀ z ∈ full.support, z ∈ rlc_connectorFaceBox n := by
    intro z hz
    dsimp only [full] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzBase | hzVertical
    · simp only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.mem_singleton] at hzBase
      rcases hzBase with rfl | hzBase
      · exact hcentralBox
      · rcases hzBase with rfl | hzNil
        · exact hleftZeroBox
        · simp at hzNil
    · have hzVertical : z ∈ vertical.support := by
        simpa [verticalCut, SimpleGraph.Walk.support_transfer] using hzVertical
      change z ∈ (sw_vertSeg (-1) 0 t).support at hzVertical
      rw [sw_vertSeg_mem_support] at hzVertical
      obtain ⟨a, ha, rfl⟩ := hzVertical
      rw [Set.mem_uIcc] at ha
      simp [rlc_connectorFaceBox, mem_rect]
      rcases ha with ha | ha <;> omega
  let finiteWalk := full.induce
    (rlc_connectorFaceBox n : Set (Site 2)) hfullBox
  have hset : (![-1, t] : Site 2) ∈
      rlc_connectorCentralFaceRegionSet gamma gamma' := by
    refine ⟨htBox, hcentralBox, ?_⟩
    exact ⟨finiteWalk⟩
  simpa [rlc_connectorCentralFaceRegion] using hset



theorem rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
    s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma'
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · exact rlc_axisGapFace_mem_connectorCentralFaceRegion
      gamma gamma' hfaith (t := k - 1) (by omega) (by omega)
  · simp [flankFaces]



theorem RlcCentralFaceRetainedAnchoredBoundary.anchor_reflected_mem_planar
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hfaith.right_axis_strict
    omega
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, B.height + 1] : Site 2), ![0, B.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have htLower := B.height_lower
  have htUpper := B.height_upper
  rw [htarget]
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma'
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · exact rlc_axisGapFace_mem_connectorCentralFaceRegion
      gamma gamma' hfaith B.height_lower B.height_upper
  · simp [flankFaces]




theorem rlc_faceBoundary_contact_of_flippedTrace_exit
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    (H : Set (Site 2))
    {u : Site 2} (huPath : u ∈ rlc_pathVertices tau)
    (huIn : rlc_flipX u ∈ H)
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices tau)
    (hzOut : rlc_flipX z ∉ H) :
    ∃ x : Site 2, x ∈ (faceBoundaryGraph H).support ∧
      rlc_dualReflect x ∈ rlc_pathVertices tau := by
  classical
  let W := rlc_ambientCrossingWalk tau
  let Wf : (hypercubicLattice 2).Walk
      (rlc_flipX (tau.1 : Site 2)) (rlc_flipX (tau.2.1 : Site 2)) :=
    W.map rlc_flipXLatticeHom
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau z).2 hzPath
  have huW : u ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau u).2 huPath
  have huWf : rlc_flipX u ∈ Wf.support := by
    change rlc_flipX u ∈ (W.map rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨u, huW, rfl⟩
  have hzWf : rlc_flipX z ∈ Wf.support := by
    change rlc_flipX z ∈ (W.map rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzW, rfl⟩
  let q : (hypercubicLattice 2).Walk (rlc_flipX u) (rlc_flipX z) :=
    (Wf.takeUntil (rlc_flipX u) huWf).reverse.append
      (Wf.takeUntil (rlc_flipX z) hzWf)
  obtain ⟨p, r, hprBoundary, hprEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges H q huIn hzOut
  have hqWf : ∀ v ∈ q.support, v ∈ Wf.support := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hv
    rcases hv with hv | hv
    · exact Wf.support_takeUntil_subset_support huWf (by simpa using hv)
    · exact Wf.support_takeUntil_subset_support hzWf hv
  have hpWf : p ∈ Wf.support :=
    hqWf p (q.fst_mem_support_of_mem_edges hprEdge)
  have hrWf : r ∈ Wf.support :=
    hqWf r (q.snd_mem_support_of_mem_edges hprEdge)
  change p ∈ (W.map rlc_flipXLatticeHom).support at hpWf
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hpWf
  obtain ⟨p0, hp0W, hp0Eq⟩ := hpWf
  change rlc_flipX p0 = p at hp0Eq
  change r ∈ (W.map rlc_flipXLatticeHom).support at hrWf
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hrWf
  obtain ⟨r0, hr0W, hr0Eq⟩ := hrWf
  change rlc_flipX r0 = r at hr0Eq
  have hp0Path : p0 ∈ rlc_pathVertices tau :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau p0).1 hp0W
  have hr0Path : r0 ∈ rlc_pathVertices tau :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau r0).1 hr0W
  have hflankEdge : flankFaces p r ∈ (faceBoundaryGraph H).edgeSet := by
    rw [phb_flankFaces_mem_faceBoundaryGraph_iff hprBoundary.1,
      bdEdge_mk]
    exact hprBoundary.2
  obtain ⟨f, g, hflank, hfgLat⟩ := flankFaces_latAdj hprBoundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    rw [← SimpleGraph.mem_edgeSet, ← hflank]
    exact hflankEdge
  rcases rlc_doubleDualShift_endpoint_mem_flankFaces hprBoundary.1 with
      hpShift | hrShift
  · rw [hflank, Sym2.mem_iff] at hpShift
    rcases hpShift with hpShift | hpShift
    · refine ⟨f, hfg.mem_support_left, ?_⟩
      have hpf : phb_doubleDualShift (rlc_flipX p0) = f := by
        rw [hp0Eq]
        exact hpShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hpf
      rw [← hpf]
      simpa using hp0Path
    · refine ⟨g, hfg.mem_support_right, ?_⟩
      have hpg : phb_doubleDualShift (rlc_flipX p0) = g := by
        rw [hp0Eq]
        exact hpShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hpg
      rw [← hpg]
      simpa using hp0Path
  · rw [hflank, Sym2.mem_iff] at hrShift
    rcases hrShift with hrShift | hrShift
    · refine ⟨f, hfg.mem_support_left, ?_⟩
      have hrf : phb_doubleDualShift (rlc_flipX r0) = f := by
        rw [hr0Eq]
        exact hrShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrf
      rw [← hrf]
      simpa using hr0Path
    · refine ⟨g, hfg.mem_support_right, ?_⟩
      have hrg : phb_doubleDualShift (rlc_flipX r0) = g := by
        rw [hr0Eq]
        exact hrShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrg
      rw [← hrg]
      simpa using hr0Path



def RlcBookFlippedTraceIntersection {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∃ z : Site 2, z ∈ rlc_pathVertices gamma.1 ∧
    rlc_flipX z ∈ rlc_pathVertices gamma'.1






theorem rlc_bookFlippedTraceIntersection_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcBookFlippedTraceIntersection gamma gamma' := by
  classical
  let L : Site 2 := gamma'.1.1
  let U : Site 2 := gamma'.1.2.1
  let S : Site 2 := gamma.1.1
  let T : Site 2 := gamma.1.2.1
  let alpha : Int := -2 * n - 1
  let beta : Int := 1
  let bottom : Int := -n - 1
  let top : Int := n + 1
  have hL0 : L 0 = -2 * n := by
    simpa [L] using gamma'.1.1.2.2
  have hU0 : U 0 = 0 := by
    simpa [U] using gamma'.1.2.1.2.2
  have hS0 : S 0 = 0 := by
    simpa [S] using gamma.1.1.2.2
  have hT0 : T 0 = 2 * n := by
    simpa [T] using gamma.1.2.1.2.2
  have hLy : -n ≤ L 1 ∧ L 1 ≤ 0 := by
    have hbox := gamma'.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, gamma'.2.1⟩
  have hUy : 0 < U 1 ∧ U 1 ≤ n := by
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hfaith.left_axis_strict, hbox.2.2.2⟩
  have hSy : -n ≤ S 1 ∧ S 1 < 0 := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, hfaith.right_axis_strict⟩
  have hTy : 0 ≤ T 1 ∧ T 1 ≤ n := by
    have hbox := gamma.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨gamma.2.2, hbox.2.2.2⟩
  have hn : 0 < n := by omega
  have hL : (![-2 * n, L 1] : Site 2) = L := by
    ext i
    fin_cases i <;> simp [hL0]
  have hU : (![0, U 1] : Site 2) = U := by
    ext i
    fin_cases i <;> simp [hU0]
  have hS : (![0, S 1] : Site 2) = S := by
    ext i
    fin_cases i <;> simp [hS0]
  have hflipT : (![-2 * n, T 1] : Site 2) = rlc_flipX T := by
    ext i
    fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0]
  let pre : (hypercubicLattice 2).Walk ![alpha, bottom] L :=
    ((sw_vertSeg alpha bottom (L 1)).append
      (sw_horizSeg (L 1) alpha (-2 * n))).copy rfl hL
  let post : (hypercubicLattice 2).Walk U ![beta, top] :=
    ((sw_horizSeg (U 1) 0 beta).append
      (sw_vertSeg beta (U 1) top)).copy hU rfl
  let leftWalk : (hypercubicLattice 2).Walk L U :=
    rlc_ambientCrossingWalk gamma'.1
  let V : (hypercubicLattice 2).Walk ![alpha, bottom] ![beta, top] :=
    (pre.append leftWalk).append post
  let reflectedRight : (hypercubicLattice 2).Walk (rlc_flipX T) S :=
    ((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse.copy
      rfl (by simpa [S] using (rlc_flipX_eq_self_of_zero hS0))
  let before : (hypercubicLattice 2).Walk
      ![alpha, T 1] (rlc_flipX T) :=
    (sw_horizSeg (T 1) alpha (-2 * n)).copy rfl hflipT
  let after : (hypercubicLattice 2).Walk S ![beta, S 1] :=
    (sw_horizSeg (S 1) 0 beta).copy hS rfl
  let H : (hypercubicLattice 2).Walk ![alpha, T 1] ![beta, S 1] :=
    (before.append reflectedRight).append after
  have hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [V] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzPre | hzLeft) | hzPost
    · dsimp only [pre] at hzPre
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hzPre
      rcases hzPre with hzVert | hzHoriz
      · rw [sw_vertSeg_mem_support] at hzVert
        obtain ⟨t, ht, rfl⟩ := hzVert
        rw [Set.mem_uIcc] at ht
        simp [mem_rect, alpha, beta, bottom, top]
        omega
      · rw [sw_horizSeg_mem_support] at hzHoriz
        obtain ⟨x, hx, rfl⟩ := hzHoriz
        rw [Set.mem_uIcc] at hx
        simp [mem_rect, alpha, beta, bottom, top]
        omega
    · have hzRect := rlc_pathVertex_mem_rect gamma'.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 z).1 hzLeft)
      rw [mem_rect] at hzRect ⊢
      simp only [alpha, beta, bottom, top]
      omega
    · dsimp only [post] at hzPost
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hzPost
      rcases hzPost with hzHoriz | hzVert
      · rw [sw_horizSeg_mem_support] at hzHoriz
        obtain ⟨x, hx, rfl⟩ := hzHoriz
        rw [Set.mem_uIcc] at hx
        simp [mem_rect, alpha, beta, bottom, top]
        omega
      · rw [sw_vertSeg_mem_support] at hzVert
        obtain ⟨t, ht, rfl⟩ := hzVert
        rw [Set.mem_uIcc] at ht
        simp [mem_rect, alpha, beta, bottom, top]
        omega
  have hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top := by
    intro z hz
    dsimp only [H] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hzBefore | hzRight) | hzAfter
    · dsimp only [before] at hzBefore
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
      obtain ⟨x, hx, rfl⟩ := hzBefore
      rw [Set.mem_uIcc] at hx
      simp [mem_rect, alpha, beta, bottom, top]
      omega
    · dsimp only [reflectedRight] at hzRight
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hzRight
      obtain ⟨q, hq, hqz⟩ := hzRight
      change rlc_flipX q = z at hqz
      rw [← hqz]
      have hqRect := rlc_pathVertex_mem_rect gamma.1
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
      rw [mem_rect] at hqRect ⊢
      simp only [alpha, beta, bottom, top]
      simp [rlc_flipX, rlc_flipXFun]
      omega
    · dsimp only [after] at hzAfter
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
      obtain ⟨x, hx, rfl⟩ := hzAfter
      rw [Set.mem_uIcc] at hx
      simp [mem_rect, alpha, beta, bottom, top]
      omega
  have hsep : ArcSeparatingSet {z | z ∈ V.support}
      alpha beta bottom top := by
    apply jec_arcSeparatingSet alpha beta bottom top alpha beta
      (by simp [alpha, beta]; omega) (by simp [bottom, top]; omega)
      (le_refl _) (by omega) (by omega) (le_refl _) V hVBox
    intro z hz
    exact hz
  obtain ⟨z, hzH, hzV⟩ := tpc_two_paths_cross_of_sep hsep
    (hHBox _ H.start_mem_support) (hHBox _ H.end_mem_support)
    (by rfl) (by rfl) H hHBox
  change z ∈ V.support at hzV
  dsimp only [V] at hzV
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzV
  dsimp only [H] at hzH
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hzH
  rcases hzV with (hzPre | hzLeft) | hzPost
  · dsimp only [pre] at hzPre
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hzPre
    rcases hzPre with hzPreVert | hzPreHoriz
    · rw [sw_vertSeg_mem_support] at hzPreVert
      obtain ⟨t, ht, rfl⟩ := hzPreVert
      rw [Set.mem_uIcc] at ht
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x, hx, heq⟩ := hzBefore
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        have heq1 := congrArg (fun q : Site 2 => q 1) heq
        simp [alpha] at heq0 heq1
        have hzero : T 1 = 0 ∧ L 1 = 0 := by omega
        refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
        have : rlc_flipX T = L := by
          ext i
          fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0, hL0,
            hzero.1, hzero.2]
        rw [this]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heq⟩ := hzRight
        change rlc_flipX q = (![alpha, t] : Site 2) at heq
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        simp [alpha, rlc_flipX, rlc_flipXFun] at heq0
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x, hx, heq⟩ := hzAfter
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0) heq
        simp at heq0
        omega
    · rw [sw_horizSeg_mem_support] at hzPreHoriz
      obtain ⟨x, hx, heqPre⟩ := hzPreHoriz
      rw [Set.mem_uIcc] at hx
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x', hx', heqH⟩ := hzBefore
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPre.symm.trans heqH)
        simp at heq1
        refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
        have : rlc_flipX T = L := by
          ext i
          fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hT0, hL0, heq1]
        rw [this]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPre)
        simp [rlc_flipX, rlc_flipXFun] at heq0
        have hq0 : q 0 = 2 * n := by omega
        have heqL : rlc_flipX q = L := by
          ext i
          fin_cases i
          · simp [rlc_flipX, rlc_flipXFun, hq0, hL0]
          · have heq1 := congrArg (fun q : Site 2 => q 1)
                (heqH.trans heqPre)
            simpa [rlc_flipX, rlc_flipXFun] using heq1
        refine ⟨q,
          (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq,
          ?_⟩
        rw [heqL]
        exact rlc_path_start_mem_vertices gamma'.1
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x', hx', heqH⟩ := hzAfter
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPre.symm.trans heqH)
        rw [Set.mem_uIcc] at hx'
        simp at heq0
        omega
  · have hzLeftPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzLeft
    rcases hzH with (hzBefore | hzRight) | hzAfter
    · dsimp only [before] at hzBefore
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
      obtain ⟨x, hx, heq⟩ := hzBefore
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzLeftPath
      rw [Set.mem_uIcc] at hx
      rw [mem_rect] at hzRect
      have heq0 := congrArg (fun q : Site 2 => q 0) heq
      simp at heq0
      have hzEq : z = rlc_flipX T := by
        ext i
        fin_cases i
        · simp [rlc_flipX, rlc_flipXFun, hT0]
          omega
        · simpa [rlc_flipX, rlc_flipXFun] using
            congrArg (fun q : Site 2 => q 1) heq
      refine ⟨T, rlc_connector_path_end_mem_vertices gamma.1, ?_⟩
      rwa [hzEq] at hzLeftPath
    · dsimp only [reflectedRight] at hzRight
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hzRight
      obtain ⟨q, hq, heq⟩ := hzRight
      change rlc_flipX q = z at heq
      refine ⟨q,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq,
        ?_⟩
      rwa [heq]
    · dsimp only [after] at hzAfter
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
      obtain ⟨x, hx, heq⟩ := hzAfter
      rw [Set.mem_uIcc] at hx
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzLeftPath
      rw [mem_rect] at hzRect
      have heq0 := congrArg (fun q : Site 2 => q 0) heq
      have hz0 : z 0 = 0 := by simp at heq0; omega
      have hzU : z = U := hfaith.left_axis_unique hzLeftPath hz0
      have hzU1 : z 1 = U 1 := congrArg (fun q : Site 2 => q 1) hzU
      have heq1 := congrArg (fun q : Site 2 => q 1) heq
      simp at heq1
      omega
  · dsimp only [post] at hzPost
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff] at hzPost
    rcases hzPost with hzPostHoriz | hzPostVert
    · rw [sw_horizSeg_mem_support] at hzPostHoriz
      obtain ⟨x, hx, heqPost⟩ := hzPostHoriz
      rw [Set.mem_uIcc] at hx
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x', hx', heqH⟩ := hzBefore
        rw [Set.mem_uIcc] at hx'
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        simp at heq0
        omega
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPost)
        simp [rlc_flipX, rlc_flipXFun] at heq0
        have hq0 : q 0 = 0 := by omega
        have hqS : q = S := hfaith.right_axis_unique
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
          hq0
        have hqS1 : q 1 = S 1 := congrArg (fun z : Site 2 => z 1) hqS
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqH.trans heqPost)
        simp [rlc_flipX, rlc_flipXFun] at heq1
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x', hx', heqH⟩ := hzAfter
        rw [Set.mem_uIcc] at hx'
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPost.symm.trans heqH)
        simp at heq1
        omega
    · rw [sw_vertSeg_mem_support] at hzPostVert
      obtain ⟨t, ht, heqPost⟩ := hzPostVert
      rw [Set.mem_uIcc] at ht
      rcases hzH with (hzBefore | hzRight) | hzAfter
      · dsimp only [before] at hzBefore
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzBefore
        obtain ⟨x, hx, heqH⟩ := hzBefore
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        simp [beta] at heq0
        omega
      · dsimp only [reflectedRight] at hzRight
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse,
          SimpleGraph.Walk.support_map, List.mem_map] at hzRight
        obtain ⟨q, hq, heqH⟩ := hzRight
        change rlc_flipX q = z at heqH
        have hqRect := rlc_pathVertex_mem_rect gamma.1
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hq)
        rw [mem_rect] at hqRect
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqH.trans heqPost)
        simp [beta, rlc_flipX, rlc_flipXFun] at heq0
        omega
      · dsimp only [after] at hzAfter
        rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzAfter
        obtain ⟨x, hx, heqH⟩ := hzAfter
        rw [Set.mem_uIcc] at hx
        have heq0 := congrArg (fun q : Site 2 => q 0)
          (heqPost.symm.trans heqH)
        have heq1 := congrArg (fun q : Site 2 => q 1)
          (heqPost.symm.trans heqH)
        simp [beta] at heq0 heq1
        omega





theorem rlc_bookFourTraceOrderedSides_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (rightSide : (hypercubicLattice 2).Walk
          (gamma.1.1 : Site 2) (gamma'.1.2.1 : Site 2))
      (leftSide : (hypercubicLattice 2).Walk
          (gamma'.1.2.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ rightSide.edges,
        e ∈ rlc_pathEdges gamma.1 ∨
          e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      (∀ z ∈ rightSide.support, 0 ≤ z 0) ∧
      (∀ e ∈ leftSide.edges,
        e ∈ rlc_pathEdges gamma'.1 ∨
          e ∈ rlc_reflectedPathEdges gamma.1) ∧
      ∀ z ∈ leftSide.support, z 0 ≤ 0 := by
  obtain ⟨p, hpRight, hpFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  let q := rlc_flipX p
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hpWR : p ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 p).2 hpRight
  have hqWL : q ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 q).2 hpFlipLeft
  let right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) p :=
    WR.takeUntil p hpWR
  let left : (hypercubicLattice 2).Walk q (gamma'.1.2.1 : Site 2) :=
    (WL.takeUntil q hqWL).reverse.append WL
  have hflipQ : rlc_flipX q = p := by simp [q]
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) = gamma'.1.2.1 :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) = gamma.1.1 :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk p (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy hflipQ hflipUpper
  let flipRightRev : (hypercubicLattice 2).Walk q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightSide := right.append flipLeft
  let leftSide := left.reverse.append flipRightRev
  have hrightEdges : ∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1 := by
    intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hpWR he
  have hleftEdges : ∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1 := by
    intro e he
    dsimp only [left] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    rcases he with he | he
    · exact WL.edges_takeUntil_subset hqWL he
    · exact he
  have hrightSupport : ∀ z ∈ right.support, 0 ≤ z 0 := by
    intro z hz
    have hzWR : z ∈ WR.support := by
      change z ∈ (WR.takeUntil p hpWR).support at hz
      exact WR.support_takeUntil_subset_support hpWR hz
    have hzPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzWR
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hzPath
    rw [mem_rect] at hzRect
    exact hzRect.1
  have hleftSupport : ∀ z ∈ left.support, z 0 ≤ 0 := by
    intro z hz
    dsimp only [left] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    have hzWL : z ∈ WL.support := hz.elim
      (fun hz => WL.support_takeUntil_subset_support hqWL hz) id
    have hzPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzWL
    have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzPath
    rw [mem_rect] at hzRect
    exact hzRect.2.1
  refine ⟨rightSide, leftSide, ?_, ?_, ?_, ?_⟩
  · intro e he
    change e ∈ (right.append flipLeft).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl (hrightEdges e he)
    · right
      dsimp only [flipLeft] at he
      rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, hleftEdges e0 he0, rfl⟩
  · intro z hz
    change z ∈ (right.append flipLeft).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hrightSupport z hz
    · dsimp only [flipLeft] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hleftSupport z0 hz0
      change 0 ≤ -z0 0
      omega
  · intro e he
    change e ∈ (left.reverse.append flipRightRev).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he
    · exact Or.inl (hleftEdges e he)
    · right
      dsimp only [flipRightRev] at he
      rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse, SimpleGraph.Walk.edges_map] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, hrightEdges e0 he0, rfl⟩
  · intro z hz
    change z ∈ (left.reverse.append flipRightRev).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact hleftSupport z hz
    · dsimp only [flipRightRev] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hrightSupport z0 hz0
      change -z0 0 ≤ 0
      omega



theorem rlc_connectorBarrier_positive_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz0 : 0 < z 0)
    (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma.1 ∨
      ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · exact Or.inl hright
  · have hzRect := rlc_pathVertex_mem_rect gamma'.1 hleft
    rw [mem_rect] at hzRect
    omega
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipRight
    have hwRect := rlc_pathVertex_mem_rect gamma.1 hw
    rw [mem_rect] at hwRect
    have hcoord := congrArg (fun q : Site 2 => q 0) hwz
    simp [rlc_flipX, rlc_flipXFun] at hcoord
    omega
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipLeft
    exact Or.inr ⟨w, hw, hwz.symm⟩



theorem rlc_connectorBarrier_negative_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz0 : z 0 < 0)
    (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma'.1 ∨
      ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · have hzRect := rlc_pathVertex_mem_rect gamma.1 hright
    rw [mem_rect] at hzRect
    omega
  · exact Or.inl hleft
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipRight
    exact Or.inr ⟨w, hw, hwz.symm⟩
  · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hflipLeft
    have hwRect := rlc_pathVertex_mem_rect gamma'.1 hw
    rw [mem_rect] at hwRect
    have hcoord := congrArg (fun q : Site 2 => q 0) hwz
    simp [rlc_flipX, rlc_flipXFun] at hcoord
    omega




theorem rlc_connectorBarrier_original_or_strict_reflected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma.1 ∨
      z ∈ rlc_pathVertices gamma'.1 ∨
      (0 < z 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w) ∨
      (z 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w) := by
  rcases lt_trichotomy (z 0) 0 with hzNeg | hzZero | hzPos
  · rcases rlc_connectorBarrier_negative_classify
      gamma gamma' hzNeg hz with hzLeft | hzFlipRight
    · exact Or.inr (Or.inl hzLeft)
    · exact Or.inr (Or.inr (Or.inr ⟨hzNeg, hzFlipRight⟩))
  · have hzEq : z = (![0, z 1] : Site 2) := by
      ext i
      fin_cases i
      · simpa using hzZero
      · rfl
    have hzAxis : (![0, z 1] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' := by
      rwa [← hzEq]
    rcases (rlc_axis_mem_connectorBarrier_iff
      gamma gamma' (z 1)).1 hzAxis with hzRight | hzLeft
    · exact Or.inl (by rwa [hzEq])
    · exact Or.inr (Or.inl (by rwa [hzEq]))
  · rcases rlc_connectorBarrier_positive_classify
      gamma gamma' hzPos hz with hzRight | hzFlipLeft
    · exact Or.inl hzRight
    · exact Or.inr (Or.inr (Or.inl ⟨hzPos, hzFlipLeft⟩))




theorem rlc_reflectedLeft_hit_sourceNE_not_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma'.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hw
  simpa only [rlc_connectorCentralFaceFilledReachSet,
    Set.mem_compl_iff, not_not] using hwExt




theorem rlc_reflectedRight_hit_sourceNE_mem_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u w : Site 2} (hw : w ∈ rlc_pathVertices gamma.1)
    (hu : rlc_dualReflect u = rlc_flipX w) :
    (![u 0 + 1, u 1 + 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  have hcorner : (![u 0 + 1, u 1 + 1] : Site 2) = w := by
    have h0 := congrArg (fun z : Site 2 => z 0) hu
    have h1 := congrArg (fun z : Site 2 => z 1) hu
    ext i
    fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  rw [hcorner]
  exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
    (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hw)




theorem rlc_faceBoundary_step_of_NE_not_mem
    (H : Set (Site 2)) {u v : Site 2}
    (huv : (faceBoundaryGraph H).Adj u v)
    (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∉ H) :
    (v = ![u 0 + 1, u 1] ∧
        (![u 0 + 1, u 1] : Site 2) ∈ H) ∨
      v = ![u 0 - 1, u 1] ∨
      (v = ![u 0, u 1 + 1] ∧
        (![u 0, u 1 + 1] : Site 2) ∈ H) ∨
      v = ![u 0, u 1 - 1] := by
  rcases face_adj_dir huv.1 with rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0 + 1, u 1] =
        s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact hbd.mpr hne
  · exact Or.inr (Or.inl rfl)
  · right; right; left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0, u 1 + 1] =
        s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact hbd.mpr hne
  · exact Or.inr (Or.inr (Or.inr rfl))



theorem rlc_faceBoundary_step_of_NE_mem
    (H : Set (Site 2)) {u v : Site 2}
    (huv : (faceBoundaryGraph H).Adj u v)
    (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∈ H) :
    (v = ![u 0 + 1, u 1] ∧
        (![u 0 + 1, u 1] : Site 2) ∉ H) ∨
      v = ![u 0 - 1, u 1] ∨
      (v = ![u 0, u 1 + 1] ∧
        (![u 0, u 1 + 1] : Site 2) ∉ H) ∨
      v = ![u 0, u 1 - 1] := by
  rcases face_adj_dir huv.1 with rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0 + 1, u 1] =
        s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact fun hse => (hbd.mp hse) hne
  · exact Or.inr (Or.inl rfl)
  · right; right; left
    refine ⟨rfl, ?_⟩
    have hbd := huv.2
    have hshared : sharedPrimalEdge u ![u 0, u 1 + 1] =
        s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) := by
      simp [sharedPrimalEdge]
    rw [hshared, bdEdge_mk] at hbd
    exact fun hnw => (hbd.mp hnw) hne
  · exact Or.inr (Or.inr (Or.inr rfl))





theorem rlc_reflectedHit_sharedPrimalEdge_right {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0 + 1, u 1] =
      s((![w 0, w 1 - 1] : Site 2), w) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0 + 1, u 1] =
      s((![u 0 + 1, u 1] : Site 2), ![u 0 + 1, u 1 + 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_top {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0, u 1 + 1] =
      s((![w 0 - 1, w 1] : Site 2), w) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0, u 1 + 1] =
      s((![u 0, u 1 + 1] : Site 2), ![u 0 + 1, u 1 + 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_left {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0 - 1, u 1] =
      s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0 - 1, w 1]) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0 - 1, u 1] =
      s((![u 0, u 1] : Site 2), ![u 0, u 1 + 1]) by
        simp [sharedPrimalEdge]; omega]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega

theorem rlc_reflectedHit_sharedPrimalEdge_bottom {u w : Site 2}
    (hu : rlc_dualReflect u = rlc_flipX w) :
    sharedPrimalEdge u ![u 0, u 1 - 1] =
      s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0, w 1 - 1]) := by
  have h0 := congrArg (fun z : Site 2 => z 0) hu
  have h1 := congrArg (fun z : Site 2 => z 1) hu
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at h0 h1
  rw [show sharedPrimalEdge u ![u 0, u 1 - 1] =
      s((![u 0, u 1] : Site 2), ![u 0 + 1, u 1]) by
        simp [sharedPrimalEdge]]
  rw [Sym2.eq_iff]
  left
  constructor <;> ext i <;> fin_cases i <;> simp <;> omega




theorem rlc_reflectedHit_boundary_step_ne_right_of_south_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0 + 1, u 1] := by
  intro hv
  subst v
  exact (rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    gamma gamma' rho hno huv)
      ((rlc_reflectedHit_sharedPrimalEdge_right hu).symm ▸ hsouth)



theorem rlc_reflectedHit_boundary_step_ne_top_of_west_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v w : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hu : rlc_dualReflect u = rlc_flipX w)
    (hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ≠ ![u 0, u 1 + 1] := by
  intro hv
  subst v
  exact (rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    gamma gamma' rho hno huv)
      ((rlc_reflectedHit_sharedPrimalEdge_top hu).symm ▸ hwest)


theorem rlc_pathVertex_incident_edge_of_ne_finish
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {w : Site 2} (hw : w ∈ rlc_pathVertices tau)
    (hne : w ≠ (tau.2.1 : Site 2)) :
    ∃ r : Site 2, s(w, r) ∈ rlc_pathEdges tau := by
  let W := rlc_ambientCrossingWalk tau
  have hwW : w ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau w).2 hw
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hwW
  rcases hwW with hwEnd | ⟨e, he, hwe⟩
  · exact False.elim (hne hwEnd)
  · induction e using Sym2.inductionOn with
    | _ x y =>
        rw [Sym2.mem_iff] at hwe
        rcases hwe with rfl | rfl
        · exact ⟨y, rlc_ambientCrossingWalk_edge_mem_pathEdges tau he⟩
        · exact ⟨x, by
            simpa [Sym2.eq_swap] using
              (rlc_ambientCrossingWalk_edge_mem_pathEdges tau he)⟩



theorem rlc_reflectedPathEdge_endpoint_mem_vertices
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_reflectedPathEdges tau)
    {z : Site 2} (hz : z ∈ e) :
    ∃ w ∈ rlc_pathVertices tau, z = rlc_flipX w := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨e0, he0, rfl⟩ := he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, Sym2.mem_iff] at hz
      have hends := rlc_pathEdge_endpoints_mem_vertices tau he0
      rcases hz with rfl | rfl
      · exact ⟨x, hends.1, rfl⟩
      · exact ⟨y, hends.2, rfl⟩


theorem rlc_mem_pathEdges_of_reflected_mk
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {x y : Site 2}
    (he : s(rlc_flipX x, rlc_flipX y) ∈ rlc_reflectedPathEdges tau) :
    s(x, y) ∈ rlc_pathEdges tau := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨e, he, heq⟩ := he
  have hmap := congrArg (Sym2.map rlc_flipX) heq
  have hinv : e = s(x, y) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
        simpa [Sym2.map_mk, rlc_flipX_involutive] using hmap
  simpa [← hinv] using he



theorem rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e)
    (hzRight : z ∉ rlc_pathVertices gamma.1)
    (hzLeft : z ∉ rlc_pathVertices gamma'.1)
    (hzFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1,
      z = rlc_flipX w) :
    e ∈ rlc_reflectedPathEdges gamma'.1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
      rcases he with horiginal | hreflected
      · rw [Finset.mem_union] at horiginal
        rcases horiginal with hright | hleft
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzRight (h ▸ hends.1))
            (fun h => hzRight (h ▸ hends.2)))
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzLeft (h ▸ hends.1))
            (fun h => hzLeft (h ▸ hends.2)))
      · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
        rcases hreflected with hflipRight | hflipLeft
        · exact False.elim (hzFlipRight
            (rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma.1 hflipRight hz))
        · exact hflipLeft



theorem rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e)
    (hzRight : z ∉ rlc_pathVertices gamma.1)
    (hzLeft : z ∉ rlc_pathVertices gamma'.1)
    (hzFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1,
      z = rlc_flipX w) :
    e ∈ rlc_reflectedPathEdges gamma.1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
      rcases he with horiginal | hreflected
      · rw [Finset.mem_union] at horiginal
        rcases horiginal with hright | hleft
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzRight (h ▸ hends.1))
            (fun h => hzRight (h ▸ hends.2)))
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          exact False.elim (hz.elim (fun h => hzLeft (h ▸ hends.1))
            (fun h => hzLeft (h ▸ hends.2)))
      · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
        rcases hreflected with hflipRight | hflipLeft
        · exact hflipRight
        · exact False.elim (hzFlipLeft
            (rlc_reflectedPathEdge_endpoint_mem_vertices
              gamma'.1 hflipLeft hz))


theorem rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') (k : Int) :
    s((![0, k - 1] : Site 2), ![0, k]) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
  intro he
  have hlow := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_left _ _)
  have hupp := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_right _ _)
  rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith (k - 1) hlow with hlo | hlo <;>
    rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith k hupp with hup | hup <;>
    have hs := hfaith.right_axis_strict <;>
    have hu := hfaith.left_axis_strict <;>
    omega





theorem rlc_bookFourTraceAxisLoop_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (gamma.1.1 : Site 2) ∈ c.support ∧
        (gamma'.1.2.1 : Site 2) ∈ c.support ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ k : Int,
          (gamma.1.1 : Site 2) 1 < k →
          k ≤ (gamma'.1.2.1 : Site 2) 1 →
          ¬ Even (jec_rayCount (![1, k] : Site 2) c)) := by
  obtain ⟨p, hpRight, hpFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  let q := rlc_flipX p
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hpWR : p ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 p).2 hpRight
  have hqWL : q ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 q).2 hpFlipLeft
  let right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) p :=
    WR.takeUntil p hpWR
  let left : (hypercubicLattice 2).Walk q (gamma'.1.2.1 : Site 2) :=
    (WL.takeUntil q hqWL).reverse.append WL
  have hflipQ : rlc_flipX q = p := by simp [q]
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) = gamma'.1.2.1 :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) = gamma.1.1 :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk p (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy hflipQ hflipUpper
  let flipRightRev : (hypercubicLattice 2).Walk q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightHalf := right.append flipLeft
  let leftHalf := left.reverse.append flipRightRev
  let c := rightHalf.append leftHalf
  have hrightEdges : ∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1 := by
    intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hpWR he
  have hleftEdges : ∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1 := by
    intro e he
    dsimp only [left] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    rcases he with he | he
    · exact WL.edges_takeUntil_subset hqWL he
    · exact he
  have hflipLeftEdges : ∀ e ∈ flipLeft.edges,
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    intro e he
    dsimp only [flipLeft] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hleftEdges e0 he0, rfl⟩
  have hflipRightEdges : ∀ e ∈ flipRightRev.edges,
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    intro e he
    dsimp only [flipRightRev] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hrightEdges e0 he0, rfl⟩
  refine ⟨c, c.start_mem_support, ?_, ?_, ?_⟩
  · dsimp only [c]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      show rightHalf = right.append flipLeft from rfl,
      SimpleGraph.Walk.mem_support_append_iff,
      show leftHalf = left.reverse.append flipRightRev from rfl]
    exact Or.inl (Or.inr flipLeft.end_mem_support)
  · intro e he
    dsimp only [c] at he
    change e ∈ (rightHalf.append leftHalf).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    change e ∈ (right.append flipLeft).edges ∨
      e ∈ (left.reverse.append flipRightRev).edges at he
    simp only [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rw [rlc_connectorFourTraceEdges,
      rlc_connectorReflectedTraceEdges]
    rcases he with (he | he) | (he | he)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hrightEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (hflipLeftEdges e he))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (hleftEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (hflipRightEdges e he))
  · intro k hkLower hkUpper
    have hrightSupport : ∀ z ∈ right.support, 0 ≤ z 0 := by
      intro z hz
      have hzWR : z ∈ WR.support := by
        change z ∈ (WR.takeUntil p hpWR).support at hz
        exact WR.support_takeUntil_subset_support hpWR hz
      have hzPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzWR
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hzPath
      rw [mem_rect] at hzRect
      exact hzRect.1
    have hleftSupport : ∀ z ∈ left.support, z 0 ≤ 0 := by
      intro z hz
      dsimp only [left] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      have hzWL : z ∈ WL.support := by
        rcases hz with hz | hz
        · exact WL.support_takeUntil_subset_support hqWL (by simpa using hz)
        · exact hz
      have hzPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzWL
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hzPath
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    have hflipLeftSupport : ∀ z ∈ flipLeft.support, 0 ≤ z 0 := by
      intro z hz
      dsimp only [flipLeft] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hleftSupport z0 hz0
      change 0 ≤ -z0 0
      omega
    have hflipRightSupport : ∀ z ∈ flipRightRev.support, z 0 ≤ 0 := by
      intro z hz
      dsimp only [flipRightRev] at hz
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      have hz0Bound := hrightSupport z0 hz0
      change -z0 0 ≤ 0
      omega
    have hrightHalfSupport : ∀ z ∈ rightHalf.support, 0 ≤ z 0 := by
      intro z hz
      change z ∈ (right.append flipLeft).support at hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.elim (hrightSupport z) (hflipLeftSupport z)
    have hleftHalfSupport : ∀ z ∈ leftHalf.support, z 0 ≤ 0 := by
      intro z hz
      change z ∈ (left.reverse.append flipRightRev).support at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      exact hz.elim (hleftSupport z) (hflipRightSupport z)
    have hrightHalfFour : ∀ e ∈ rightHalf.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
      intro e he
      change e ∈ (right.append flipLeft).edges at he
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      rcases he with he | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (hrightEdges e he))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (hflipLeftEdges e he))
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightHalf = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrightHalfSupport u
            (rightHalf.fst_mem_support_of_mem_edges he)
          have hv0 := hrightHalfSupport v
            (rightHalf.snd_mem_support_of_mem_edges he)
          have hfour := hrightHalfFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftHalf =
        crossCount (jec_belowSet k) leftHalf := by
      apply jec_ray_eq_below
      intro z hz
      have hz0 := hleftHalfSupport z hz
      simpa using hz0
    have hleftOdd : ¬ Even (jec_rayCount (![1, k] : Site 2) leftHalf) := by
      rw [hleftRay]
      intro heven
      have hsame := (crossCount_parity (jec_belowSet k) leftHalf).mp heven
      have hupperNot : (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      exact hupperNot (hsame.mpr hlowerIn)
    change ¬ Even (jec_rayCount (![1, k] : Site 2)
      (rightHalf.append leftHalf))
    rw [jec_rayCount_append, hrightRay, zero_add]
    exact hleftOdd




theorem rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      ∀ k : Int,
        (gamma.1.1 : Site 2) 1 < k →
        k ≤ (gamma'.1.2.1 : Site 2) 1 →
        ¬ Even (jec_rayCount (![0, k] : Site 2) c) := by
  obtain ⟨c, _hS, _hU, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_of_faithful gamma gamma' hfaith
  refine ⟨c, hcEdges, ?_⟩
  intro k hkLower hkUpper
  have heq : jec_rayCount (![0, k] : Site 2) c =
      jec_rayCount (![1, k] : Site 2) c := by
    rw [jec_rayCount, jec_rayCount]
    apply List.countP_congr
    intro e he
    simp only [decide_eq_true_eq]
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [jec_rayEdge_mk, jec_rayEdge_mk]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        constructor
        · rintro ⟨⟨huv0, hcol⟩, hrow⟩
          exact ⟨⟨huv0, by omega⟩, hrow⟩
        · rintro hright
          by_contra hleft
          have hcol : u 0 = 0 ∧ v 0 = 0 := by
            rcases hright with ⟨⟨huv0, hbound⟩, hrow⟩
            push Not at hleft
            have huNonneg : 0 ≤ u 0 := by omega
            exact ⟨by omega, by omega⟩
          rcases hright with ⟨⟨huv0, _hbound⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                rw [← huEq, ← hvEq]
                exact hcEdges s(u, v) he)
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                rw [← hvEq, ← huEq]
                simpa [Sym2.eq_swap] using hcEdges s(u, v) he)
  rw [heq]
  exact hcOdd k hkLower hkUpper



theorem rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      (∀ k : Int,
        (gamma.1.1 : Site 2) 1 < k →
        k ≤ (gamma'.1.2.1 : Site 2) 1 →
        ¬ Even (jec_rayCount (![0, k] : Site 2) c)) ∧
      ∀ k : Int,
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          (gamma'.1.2.1 : Site 2) 1 < k) →
        Even (jec_rayCount (![0, k] : Site 2) c) := by
  obtain ⟨rightSide, leftSide, hrEdges, hrSupport, hlEdges, hlSupport⟩ :=
    rlc_bookFourTraceOrderedSides_of_faithful gamma gamma' hfaith
  let c := rightSide.append leftSide
  have hrFour : ∀ e ∈ rightSide.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    rcases hrEdges e he with he | he
    · rw [rlc_connectorFourTraceEdges]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
  have hlFour : ∀ e ∈ leftSide.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    rcases hlEdges e he with he | he
    · rw [rlc_connectorFourTraceEdges]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · rw [rlc_connectorFourTraceEdges,
        rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ he)
  have hcFour : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    dsimp only [c] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    exact he.elim (hrFour e) (hlFour e)
  have ray_eq (k : Int) :
      jec_rayCount (![0, k] : Site 2) c =
        crossCount (jec_belowSet k) leftSide := by
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightSide = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrSupport u
            (rightSide.fst_mem_support_of_mem_edges he)
          have hv0 := hrSupport v
            (rightSide.snd_mem_support_of_mem_edges he)
          have hfour := hrFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftSide =
        crossCount (jec_belowSet k) leftSide := by
      apply jec_ray_eq_below
      intro z hz
      simpa using hlSupport z hz
    have hone : jec_rayCount (![1, k] : Site 2) c =
        crossCount (jec_belowSet k) leftSide := by
      dsimp only [c]
      rw [jec_rayCount_append, hrightRay, zero_add, hleftRay]
    have hzero : jec_rayCount (![0, k] : Site 2) c =
        jec_rayCount (![1, k] : Site 2) c := by
      rw [jec_rayCount, jec_rayCount]
      apply List.countP_congr
      intro e he
      simp only [decide_eq_true_eq]
      induction e using Sym2.inductionOn with
      | _ u v =>
          rw [jec_rayEdge_mk, jec_rayEdge_mk]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          constructor
          · rintro ⟨⟨huv0, hcol⟩, hrow⟩
            exact ⟨⟨huv0, by omega⟩, hrow⟩
          · rintro hright
            by_contra hleft
            have hcol : u 0 = 0 ∧ v 0 = 0 := by
              rcases hright with ⟨⟨huv0, hbound⟩, hrow⟩
              push Not at hleft
              have huNonneg : 0 ≤ u 0 := by omega
              exact ⟨by omega, by omega⟩
            rcases hright with ⟨⟨huv0, _hbound⟩,
                ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
            · have huEq : u = (![0, k - 1] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              have hvEq : v = (![0, k] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
                gamma gamma' hfaith k (by
                  rw [← huEq, ← hvEq]
                  exact hcFour s(u, v) he)
            · have huEq : u = (![0, k] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              have hvEq : v = (![0, k - 1] : Site 2) := by
                ext i
                fin_cases i <;> simp <;> omega
              exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
                gamma gamma' hfaith k (by
                  rw [← hvEq, ← huEq]
                  simpa [Sym2.eq_swap] using hcFour s(u, v) he)
    exact hzero.trans hone
  refine ⟨c, hcFour, ?_, ?_⟩
  · intro k hkLower hkUpper
    rw [ray_eq]
    intro heven
    have hsame := (crossCount_parity (jec_belowSet k) leftSide).mp heven
    have hupperNot : (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
      simp [jec_belowSet]
      omega
    have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
      simp [jec_belowSet]
      omega
    exact hupperNot (hsame.mpr hlowerIn)
  · intro k hkOutside
    rw [ray_eq]
    apply (crossCount_parity (jec_belowSet k) leftSide).mpr
    simp [jec_belowSet]
    have horder := hfaith.axis_contacts_strict
    rcases hkOutside with hk | hk <;> omega




theorem rlc_axisInside_to_axisOutside_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {kin kout : Int}
    (hinLower : (gamma.1.1 : Site 2) 1 < kin)
    (hinUpper : kin ≤ (gamma'.1.2.1 : Site 2) 1)
    (hout : kout ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < kout)
    (w : (hypercubicLattice 2).Walk
      (![0, kin] : Site 2) ![0, kout]) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, hcEdges, hcInside, hcOutside⟩ :=
    rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful
      gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![0, kin] : Site 2)} {(![0, kout] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hcInside kin hinLower hinUpper)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hcOutside kout hout)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩







theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boundaryPrefix_to_outsideAxis_meetsBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    ∃ (w : (hypercubicLattice 2).Walk
        (![0, L.boundary.height + 1] : Site 2) ![0, k]),
      (∀ z ∈ w.support,
        z = (![0, L.boundary.height + 1] : Site 2) ∨
          z = (![0, k] : Site 2) ∨
          ∃ f ∈ p.support, z = rlc_dualReflect f) ∧
      ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  have huEq : rlc_dualReflect u = (![-1, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨hu, _hv⟩ | ⟨hu, _hv⟩
    · exact hu
    · have h0 := congrArg (fun z : Site 2 => z 0) hu
      have h0' : (rlc_dualReflect u) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hstartAdj : (hypercubicLattice 2).Adj
      (![0, L.boundary.height + 1] : Site 2)
        ![-1, L.boundary.height + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hstartAdj' : (hypercubicLattice 2).Adj
      (![0, L.boundary.height + 1] : Site 2) (rlc_dualReflect N) := by
    rw [hN]
    exact hstartAdj
  let start : (hypercubicLattice 2).Walk
      (![0, L.boundary.height + 1] : Site 2) (rlc_dualReflect N) :=
    SimpleGraph.Walk.cons hstartAdj' SimpleGraph.Walk.nil
  let hle : faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ≤
      hypercubicLattice 2 :=
    faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  let reflected := (p.mapLe hle).map rlc_dualReflectLatticeHom
  have hendAdj : (hypercubicLattice 2).Adj
      (![-1, k] : Site 2) ![0, k] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hendAdj' : (hypercubicLattice 2).Adj
      (rlc_dualReflect u) (![0, k] : Site 2) := by
    rw [huEq]
    exact hendAdj
  let finish : (hypercubicLattice 2).Walk
      (rlc_dualReflect u) (![0, k] : Site 2) :=
    SimpleGraph.Walk.cons hendAdj' SimpleGraph.Walk.nil
  let w := start.append (reflected.append finish)
  have hwSupport : ∀ z ∈ w.support,
      z = (![0, L.boundary.height + 1] : Site 2) ∨
        z = (![0, k] : Site 2) ∨
        ∃ f ∈ p.support, z = rlc_dualReflect f := by
    intro z hz
    dsimp only [w] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzStart | hzRest
    · dsimp only [start] at hzStart
      change z ∈ ((![0, L.boundary.height + 1] : Site 2) ::
        [rlc_dualReflect N]) at hzStart
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzStart
      rcases hzStart with hzAxis | hzN
      · exact Or.inl hzAxis
      · exact Or.inr (Or.inr ⟨N, p.start_mem_support, hzN⟩)
    · have hzRest' :=
        (SimpleGraph.Walk.mem_support_append_iff reflected finish).mp hzRest
      rcases hzRest' with hzReflected | hzFinish
      dsimp only [reflected] at hzReflected
      rw [SimpleGraph.Walk.support_map, List.mem_map,
        SimpleGraph.Walk.support_mapLe_eq_support] at hzReflected
      obtain ⟨f, hf, rfl⟩ := hzReflected
      exact Or.inr (Or.inr ⟨f, hf, rfl⟩)
      dsimp only [finish] at hzFinish
      change z ∈ (rlc_dualReflect u :: [(![0, k] : Site 2)]) at hzFinish
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzFinish
      rcases hzFinish with hzU | hzAxis
      · exact Or.inr (Or.inr ⟨u, p.end_mem_support, hzU⟩)
      · exact Or.inr (Or.inl hzAxis)
  have hkLower : (gamma.1.1 : Site 2) 1 <
      L.boundary.height + 1 := by
    have := L.boundary.height_lower
    omega
  have hkUpper : L.boundary.height + 1 ≤
      (gamma'.1.2.1 : Site 2) 1 := by
    have := L.boundary.height_upper
    omega
  exact ⟨w, hwSupport,
    rlc_axisInside_to_axisOutside_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper hkOutside w⟩


theorem rlc_connectorBarrier_mem_connectorBox {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  simp only [rlc_connectorBarrier, Finset.mem_union] at hz
  rcases hz with ((hright | hleft) | hflipRight) | hflipLeft
  · exact rlc_rightPathVertex_mem_connectorBox gamma hright
  · exact rlc_leftPathVertex_mem_connectorBox gamma' hleft
  · obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hflipRight
    exact (rlc_mem_connectorBox_flipX z0).mp
      (rlc_rightPathVertex_mem_connectorBox gamma hz0)
  · obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hflipLeft
    exact (rlc_mem_connectorBox_flipX z0).mp
      (rlc_leftPathVertex_mem_connectorBox gamma' hz0)



theorem rlc_connectorBoxBoundary_detour_avoidsBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {k : Int} {z : Site 2}
    (hzBoundary : z 0 = -2 * n ∨ z 0 = 2 * n ∨
      z 1 = -n ∨ z 1 = n)
    (hzNot : z ∉ rlc_connectorBarrier gamma gamma') :
    ∃ p : (hypercubicLattice 2).Walk z (![2 * n + 1, k] : Site 2),
      ∀ w ∈ p.support, w ∉ rlc_connectorBarrier gamma gamma' := by
  have hzCoord : z = (![z 0, z 1] : Site 2) := by
    ext i
    fin_cases i <;> simp
  have houtside {w : Site 2}
      (hw : w ∉ rect (-2 * n) (2 * n) (-n) n) :
      w ∉ rlc_connectorBarrier gamma gamma' := by
    intro hwBarrier
    exact hw (rlc_connectorBarrier_mem_connectorBox gamma gamma' hwBarrier)
  rcases hzBoundary with hzLeft | hzRight | hzBottom | hzTop
  · let first : (hypercubicLattice 2).Walk z
        (![-2 * n - 1, z 1] : Site 2) :=
      (sw_horizSeg (z 1) (z 0) (-2 * n - 1)).copy hzCoord.symm rfl
    let second : (hypercubicLattice 2).Walk
        (![-2 * n - 1, z 1] : Site 2)
        (![-2 * n - 1, n + 1] : Site 2) :=
      sw_vertSeg (-2 * n - 1) (z 1) (n + 1)
    let third := sw_lshape (-2 * n - 1) (n + 1) (2 * n + 1) k
    let p := (first.append second).append third
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with (hw | hw) | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = -2 * n
      · have : (![t, z 1] : Site 2) = z := by
          rw [htEq, ← hzLeft]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · dsimp only [second] at hw
      rw [sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      apply houtside
      simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · change w ∈
        (sw_lshape (-2 * n - 1) (n + 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega
  · let p :=
      (sw_lshape (z 0) (z 1) (2 * n + 1) k).copy hzCoord.symm rfl
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.support_copy, sw_lshape_support_eq] at hw
    rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [Set.mem_uIcc] at ht
      by_cases htEq : t = 2 * n
      · have : (![t, z 1] : Site 2) = z := by
          rw [htEq, ← hzRight]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · apply houtside
      simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · let first : (hypercubicLattice 2).Walk z
        (![z 0, -n - 1] : Site 2) :=
      (sw_vertSeg (z 0) (z 1) (-n - 1)).copy hzCoord.symm rfl
    let second := sw_lshape (z 0) (-n - 1) (2 * n + 1) k
    let p := first.append second
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = -n
      · have : (![z 0, t] : Site 2) = z := by
          rw [htEq, ← hzBottom]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · change w ∈ (sw_lshape (z 0) (-n - 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega
  · let first : (hypercubicLattice 2).Walk z
        (![z 0, n + 1] : Site 2) :=
      (sw_vertSeg (z 0) (z 1) (n + 1)).copy hzCoord.symm rfl
    let second := sw_lshape (z 0) (n + 1) (2 * n + 1) k
    let p := first.append second
    refine ⟨p, ?_⟩
    intro w hw
    dsimp only [p] at hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · dsimp only [first] at hw
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rw [Set.mem_uIcc] at ht
      by_cases htEq : t = n
      · have : (![z 0, t] : Site 2) = z := by
          rw [htEq, ← hzTop]
          exact hzCoord.symm
        rwa [this]
      · apply houtside
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    · change w ∈ (sw_lshape (z 0) (n + 1) (2 * n + 1) k).support at hw
      rw [sw_lshape_support_eq] at hw
      rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
        apply houtside <;>
        simp only [mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        omega



theorem rlc_axisGap_to_rightExterior_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1)
    (w : (hypercubicLattice 2).Walk
      (![1, k] : Site 2) (![2 * n + 1, k] : Site 2)) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, _hS, _hU, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_of_faithful gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  have hfar : ∀ z ∈ c.support, z 0 ≤
      (![2 * n + 1, k] : Site 2) 0 - 1 := by
    intro z hz
    have hzBox := rlc_connectorBarrier_mem_connectorBox
      gamma gamma' (hcBarrier z hz)
    rw [mem_rect] at hzBox
    simpa using hzBox.2.1
  have hodd := hcOdd k hkLower hkUpper
  have heven := jec_ray_even_far c (![2 * n + 1, k] : Site 2) hfar
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![1, k] : Site 2)} {(![2 * n + 1, k] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hodd)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact heven)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩



theorem rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1)
    (w : (hypercubicLattice 2).Walk
      (![0, k] : Site 2) (![2 * n + 1, k] : Site 2)) :
    ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨c, hcEdges, hcOdd⟩ :=
    rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful
      gamma gamma' hfaith
  have hcBarrier : ∀ z ∈ c.support,
      z ∈ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · simp [rlc_connectorBarrier, rlc_path_start_mem_vertices gamma.1]
    · exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' (hcEdges e he) hze
  have hfar : ∀ z ∈ c.support, z 0 ≤
      (![2 * n + 1, k] : Site 2) 0 - 1 := by
    intro z hz
    have hzBox := rlc_connectorBarrier_mem_connectorBox
      gamma gamma' (hcBarrier z hz)
    rw [mem_rect] at hzBox
    simpa using hzBox.2.1
  have hodd := hcOdd k hkLower hkUpper
  have heven := jec_ray_even_far c (![2 * n + 1, k] : Site 2) hfar
  obtain ⟨z, hzw, hzc⟩ :=
    ccs_closedLoop_separatingSide_forces_cross c
      {(![0, k] : Site 2)} {(![2 * n + 1, k] : Site 2)}
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hodd)
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact heven)
      (by simp) (by simp) w
  exact ⟨z, hzw, hcBarrier z hzc⟩


def RlcCentralFaceFilledBoundaryContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y : Site 2,
    x ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support ∧
    y ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support ∧
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1



theorem rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hcross : RlcBookFlippedTraceIntersection gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  obtain ⟨z, hzRight, hzFlipLeft⟩ := hcross
  have hrightStartFlip :
      rlc_flipX (gamma.1.1 : Site 2) = (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hzFlipLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hzFlipExt
  obtain ⟨x, hxSupp, hxPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma.1 H
      (rlc_path_start_mem_vertices gamma.1) hrightStartH hzRight hzFlipOut
  let u : Site 2 := rlc_flipX z
  have huLeft : u ∈ rlc_pathVertices gamma'.1 := hzFlipLeft
  have huFlipH : rlc_flipX u ∈ H := by
    have huFlip : rlc_flipX u = z := by
      simp [u]
    rw [huFlip]
    exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hleftEndPath
  have hleftEndFlip :
      rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hleftEndFlip]
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hleftEndExt
  obtain ⟨y, hySupp, hyPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma'.1 H
      huLeft huFlipH hleftEndPath hleftEndOut
  exact ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩



theorem rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
  exact rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection
    gamma gamma' hfaith
      (rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith)
      rho hno




theorem rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2) (hx : x ∈ B.contour.support)
      (hy : y ∈ B.contour.support),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      B.firstFace ∈
        (rlc_centralFaceContactSubwalk B.contour hx hy).support ∧
      ∀ e ∈ (rlc_centralFaceContactSubwalk B.contour hx hy).edges,
        e ∈ B.contour.edges := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupp
  obtain ⟨y', hyy'⟩ := hySupp
  have hxe : s(x, x') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hxx')
  have hye : s(y, y') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hyy')
  have hx : x ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hxe
  have hy : y ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hye
  refine ⟨B, x, y, hx, hy, hxPath, hyPath, ?_,
    rlc_centralFaceContactSubwalk_edges_subset B.contour hx hy⟩
  rw [rlc_centralFaceContactSubwalk,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse]
  exact Or.inl (by
    simpa using (B.contour.takeUntil x hx).start_mem_support)





theorem rlc_centralFace_anchorToContacts_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2)
      (px : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace x)
      (py : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace y),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        (∀ e ∈ px.edges, e ∈ B.contour.edges) ∧
        ∀ e ∈ py.edges, e ∈ B.contour.edges := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, _hanchor, _hedges⟩ :=
    rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
      gamma gamma' hfaith rho hno
  let px := B.contour.takeUntil x hx
  let py := B.contour.takeUntil y hy
  refine ⟨B, x, y, px, py, hxPath, hyPath, ?_, ?_⟩
  · intro e he
    exact B.contour.edges_takeUntil_subset hx he
  · intro e he
    exact B.contour.edges_takeUntil_subset hy he





theorem rlc_contourContactArcs_support_cover
    {H : SimpleGraph (Site 2)} {u x y z : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hz : z ∈ c.support) :
    z ∈ (rlc_orderedContourArc c hx hy).support ∨
      z ∈ (rlc_complementaryContourArc c hx hy).support := by
  classical
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hzrot : z ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hz
  rw [← SimpleGraph.Walk.take_spec (c.rotate x hx) hy',
    SimpleGraph.Walk.mem_support_append_iff] at hzrot
  rcases hzrot with hprefix | hsuffix
  · exact Or.inl (by
      simpa [rlc_orderedContourArc, hy'] using hprefix)
  · exact Or.inr (by
      simpa [rlc_complementaryContourArc, hy',
        SimpleGraph.Walk.support_reverse] using hsuffix)





theorem rlc_contourContactArcs_edges_decompose
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (c.rotate x hx).edges =
      (rlc_orderedContourArc c hx hy).edges ++
        (rlc_complementaryContourArc c hx hy).edges.reverse := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  rw [← SimpleGraph.Walk.take_spec (c.rotate x hx) hy',
    SimpleGraph.Walk.edges_append]
  simp [rlc_orderedContourArc, rlc_complementaryContourArc, hy',
    SimpleGraph.Walk.edges_reverse]



theorem rlc_contourContactArcs_edges_cover
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support)
    {e : Sym2 (Site 2)} (he : e ∈ c.edges) :
    e ∈ (rlc_orderedContourArc c hx hy).edges ∨
      e ∈ (rlc_complementaryContourArc c hx hy).edges := by
  have heRot : e ∈ (c.rotate x hx).edges :=
    (SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff.mpr he
  rw [rlc_contourContactArcs_edges_decompose c hx hy,
    List.mem_append, List.mem_reverse] at heRot
  exact heRot


theorem rlc_contourContactArcs_edges_disjoint
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsTrail)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    List.Disjoint (rlc_orderedContourArc c hx hy).edges
      (rlc_complementaryContourArc c hx hy).edges := by
  have hnodup : (c.rotate x hx).edges.Nodup :=
    (hc.rotate hx).edges_nodup
  rw [rlc_contourContactArcs_edges_decompose c hx hy,
    List.nodup_append] at hnodup
  intro e heOrdered heComplementary
  exact hnodup.2.2 e heOrdered e (List.mem_reverse.mpr heComplementary) rfl


theorem rlc_orderedContourArc_isPath
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_orderedContourArc c hx hy).IsPath := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  exact (hc.rotate hx).isPath_takeUntil hy'



theorem rlc_complementaryContourArc_isPath
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support) (hxy : x ≠ y) :
    (rlc_complementaryContourArc c hx hy).IsPath := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hcycle : (((c.rotate x hx).takeUntil y hy').append
      ((c.rotate x hx).dropUntil y hy')).IsCycle := by
    rw [SimpleGraph.Walk.take_spec]
    exact hc.rotate hx
  have htake : ¬ ((c.rotate x hx).takeUntil y hy').Nil :=
    SimpleGraph.Walk.not_nil_of_ne hxy
  have hdrop : ((c.rotate x hx).dropUntil y hy').IsPath :=
    SimpleGraph.Walk.IsCycle.isPath_of_append_right htake hcycle
  exact (SimpleGraph.Walk.isPath_reverse_iff _).2 hdrop




def RlcCentralFaceFilledBoundaryAnchoredContactChoice {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2) (hx : x ∈ B.contour.support)
    (hy : y ∈ B.contour.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (B.firstFace ∈
          (rlc_orderedContourArc B.contour hx hy).support ∨
        B.firstFace ∈
          (rlc_complementaryContourArc B.contour hx hy).support)

theorem rlc_centralFace_anchoredContactChoice_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredContactChoice gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, _hanchor, _hedges⟩ :=
    rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
      gamma gamma' hfaith rho hno
  have hbase : B.firstFace ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges B.anchor_mem
  exact ⟨B, x, y, hx, hy, hxPath, hyPath,
    rlc_contourContactArcs_support_cover B.contour hx hy hbase⟩




def RlcCentralFaceFilledBoundaryAnchoredSupportedSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2) (hx : x ∈ B.contour.support)
    (hy : y ∈ B.contour.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ((B.firstFace ∈
            (rlc_orderedContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈ (rlc_orderedContourArc B.contour hx hy).edges →
              s(rlc_dualReflect f, rlc_dualReflect g) ∈
                rlc_connectorCentralFacePlanarEdges gamma gamma') ∨
        (B.firstFace ∈
            (rlc_complementaryContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈
                (rlc_complementaryContourArc B.contour hx hy).edges →
              s(rlc_dualReflect f, rlc_dualReflect g) ∈
                rlc_connectorCentralFacePlanarEdges gamma gamma'))




def RlcCentralFaceReflectedEdgeCarrierGeometry {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' ∨
    (rlc_dualReflect f ∈ rlc_connectorBox n ∧
      rlc_dualReflect g ∈ rlc_connectorBox n ∧
      ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect f) (rlc_dualReflect g))

theorem rlc_reflectedEdgeCarrierGeometry_iff_planarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  symm
  exact rlc_mem_connectorCentralFacePlanarEdges_iff gamma gamma'
    ((rlc_adj_dualReflect f g).mp hfg)



theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {h h' : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hhBox : h ∈ rlc_connectorFaceBox n)
    (hh'Box : h' ∈ rlc_connectorFaceBox n)
    (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
    (hopposite :
      let C := (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom
      ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
    ∃ f g : Site 2,
      s(f, g) ∈ B.contour.edges ∧
        RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨f, g, z, z', hfgContour, _hzz, hzRegion, _hz'Region,
    hflank, hfBox, hgBox, hnonwall⟩ :=
    B.centralCutPath_goodContourEdge_of_oppositeSide
      hhRegion hhBox hh'Box hreach hopposite
  refine ⟨f, g, hfgContour, Or.inr ⟨hfBox, hgBox, z.1, hzRegion, ?_⟩,
    hnonwall⟩
  rw [hflank, Sym2.mem_iff]
  exact Or.inl rfl



theorem rlc_reflected_axisCrossing_carrier_of_between {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hfg).2
  rw [hreflected]
  exact rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges
    gamma gamma' hfaith hkLower hkUpper




theorem rlc_reflected_axisCrossing_carrier_of_right_contact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfNeg : (rlc_dualReflect f) 0 < 0)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma.1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  have hgEq : rlc_dualReflect g = (![0, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨_hf, hg⟩ | ⟨hg, _hf⟩
    · exact hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      have h0' : (rlc_dualReflect f) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hgStart : rlc_dualReflect g = (gamma.1.1 : Site 2) :=
    hfaith.right_axis_unique hgPath (by rw [hgEq]; simp)
  have hstartEq : (gamma.1.1 : Site 2) = (![0, k] : Site 2) := by
    rw [← hgStart, hgEq]
  let W := rlc_ambientCrossingWalk gamma.1
  have hn : 0 < n := by
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hsneg := hfaith.right_axis_strict
    omega
  have hstartEnd : (gamma.1.1 : Site 2) ≠
      (gamma.1.2.1 : Site 2) := by
    intro heq
    have h0 := congrArg (fun z : Site 2 => z 0) heq
    change (gamma.1.1 : Site 2) 0 =
      (gamma.1.2.1 : Site 2) 0 at h0
    have hs0 : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
    have he0 : (gamma.1.2.1 : Site 2) 0 = 2 * n :=
      gamma.1.2.1.2.2
    rw [hs0, he0] at h0
    omega
  have hWnil : ¬ W.Nil := W.not_nil_of_ne hstartEnd
  have hsndSupport : W.snd ∈ W.support :=
    List.mem_of_mem_tail (W.snd_mem_tail_support hWnil)
  have hsndPath : W.snd ∈ rlc_pathVertices gamma.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices gamma.1 hsndSupport
  have hsndNe : W.snd ≠ (gamma.1.1 : Site 2) :=
    (W.adj_snd hWnil).ne.symm
  have hsndPos : 0 < W.snd 0 :=
    hfaith.right_vertex_strict hsndPath hsndNe
  have hsndEq : W.snd = (![1, k] : Site 2) := by
    have hadj := W.adj_snd hWnil
    rcases adj_cases hadj with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hs0 := gamma.1.1.2.2
      omega
    · ext i
      fin_cases i
      · have hs0 := gamma.1.1.2.2
        rcases h0 with h0 | h0 <;> simp <;> omega
      · have hstart1 := congrArg (fun z : Site 2 => z 1) hstartEq
        simpa only [Matrix.cons_val_one] using h1.symm.trans hstart1
  have hfirst : s((gamma.1.1 : Site 2), W.snd) ∈
      rlc_pathEdges gamma.1 :=
    rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
      (W.mk_start_snd_mem_edges hWnil)
  have hreflectedFirst : s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_reflectedPathEdges gamma.1 := by
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    refine ⟨s((gamma.1.1 : Site 2), W.snd), hfirst, ?_⟩
    have hedgeEq : s((gamma.1.1 : Site 2), W.snd) =
        s((![0, k] : Site 2), ![1, k]) :=
      congrArg₂ Sym2.mk hstartEq hsndEq
    have hmapped := congrArg (Sym2.map rlc_flipX) hedgeEq
    simpa [Sym2.map_mk, rlc_flipX, rlc_flipXFun,
      Sym2.eq_swap] using hmapped
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  left
  rw [hreflected]
  simp [rlc_connectorFourTraceEdges,
    rlc_connectorReflectedTraceEdges, hreflectedFirst]



theorem rlc_axisCrossing_carrier_of_left_contact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfNeg : (rlc_dualReflect f) 0 < 0)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma'.1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  have hgEq : rlc_dualReflect g = (![0, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨_hf, hg⟩ | ⟨hg, _hf⟩
    · exact hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      have h0' : (rlc_dualReflect f) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hgEnd : rlc_dualReflect g = (gamma'.1.2.1 : Site 2) :=
    hfaith.left_axis_unique hgPath (by rw [hgEq]; simp)
  have hendEq : (gamma'.1.2.1 : Site 2) = (![0, k] : Site 2) := by
    rw [← hgEnd, hgEq]
  let W := rlc_ambientCrossingWalk gamma'.1
  have hn : 0 < n := by
    have hebox := gamma'.1.2.1.2.1
    rw [mem_rect] at hebox
    have hepos := hfaith.left_axis_strict
    omega
  have hstartEnd : (gamma'.1.1 : Site 2) ≠
      (gamma'.1.2.1 : Site 2) := by
    intro heq
    have h0 := congrArg (fun z : Site 2 => z 0) heq
    change (gamma'.1.1 : Site 2) 0 =
      (gamma'.1.2.1 : Site 2) 0 at h0
    have hs0 : (gamma'.1.1 : Site 2) 0 = -2 * n :=
      gamma'.1.1.2.2
    have he0 : (gamma'.1.2.1 : Site 2) 0 = 0 :=
      gamma'.1.2.1.2.2
    rw [hs0, he0] at h0
    omega
  have hWnil : ¬ W.Nil := W.not_nil_of_ne hstartEnd
  have hpenSupport : W.penultimate ∈ W.support :=
    List.mem_of_mem_dropLast (W.penultimate_mem_dropLast_support hWnil)
  have hpenPath : W.penultimate ∈ rlc_pathVertices gamma'.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices gamma'.1 hpenSupport
  have hpenNe : W.penultimate ≠ (gamma'.1.2.1 : Site 2) :=
    (W.adj_penultimate hWnil).ne
  have hpenNeg : W.penultimate 0 < 0 :=
    hfaith.left_vertex_strict hpenPath hpenNe
  have hpenEq : W.penultimate = (![-1, k] : Site 2) := by
    have hadj := W.adj_penultimate hWnil
    rcases adj_cases hadj with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have he0 := gamma'.1.2.1.2.2
      omega
    · ext i
      fin_cases i
      · have he0 := gamma'.1.2.1.2.2
        rcases h0 with h0 | h0 <;> simp <;> omega
      · have hend1 := congrArg (fun z : Site 2 => z 1) hendEq
        simpa only [Matrix.cons_val_one] using h1.trans hend1
  have hlast : s(W.penultimate, (gamma'.1.2.1 : Site 2)) ∈
      rlc_pathEdges gamma'.1 :=
    rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
      (W.mk_penultimate_end_mem_edges hWnil)
  have haxisEdge : s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_pathEdges gamma'.1 := by
    have hedgeEq : s(W.penultimate, (gamma'.1.2.1 : Site 2)) =
        s((![-1, k] : Site 2), ![0, k]) :=
      congrArg₂ Sym2.mk hpenEq hendEq
    rwa [← hedgeEq]
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  left
  rw [hreflected]
  simp [rlc_connectorFourTraceEdges, haxisEdge]






theorem rlc_reflectedLeft_opposite_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
      gamma gamma' rho hno huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl





theorem rlc_reflectedRight_opposite_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
      gamma gamma' rho hno huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl





theorem rlc_reflectedLeft_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1
  · exact rlc_reflectedLeft_opposite_continuation_carrier
      gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
        hvFlipRight hopp hvInterior hnotIn hhRegion hh
  · apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      apply hub
      apply rlc_dualReflect.injective
      exact heq
    · exact hopp
    · exact hvInterior
    · simpa [Sym2.eq_swap] using hnotIn
    · exact hhRegion
    · simpa [flankFaces_comm] using hh



theorem rlc_reflectedRight_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1
  · exact rlc_reflectedRight_opposite_continuation_carrier
      gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
        hvFlipLeft hopp hvInterior hnotIn hhRegion hh
  · apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      apply hub
      apply rlc_dualReflect.injective
      exact heq
    · exact hopp
    · exact hvInterior
    · simpa [Sym2.eq_swap] using hnotIn
    · exact hhRegion
    · simpa [flankFaces_comm] using hh



theorem rlc_positiveBarrier_continuation_or_right_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hvRight : rlc_dualReflect v ∈ rlc_pathVertices gamma.1
  · exact Or.inl hvRight
  · right
    rcases rlc_connectorBarrier_positive_classify gamma gamma' hvPos hvBarrier with
      hvRight' | ⟨w, hw, hvflip⟩
    · exact False.elim (hvRight hvRight')
    · have hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1 := by
        intro hv
        have hvRect := rlc_pathVertex_mem_rect gamma'.1 hv
        rw [mem_rect] at hvRect
        omega
      have hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
          rlc_dualReflect v = rlc_flipX r := by
        rintro ⟨r, hr, heq⟩
        have hvPosCoord := hvPos
        have hrRect := rlc_pathVertex_mem_rect gamma.1 hr
        rw [mem_rect] at hrRect
        have heq0 := congrArg (fun z : Site 2 => z 0) heq
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun] at hvPosCoord heq0
        omega
      exact rlc_reflectedLeft_continuation_carrier
        gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
          hvFlipRight hvInterior hnotIn hhRegion hh



theorem rlc_negativeBarrier_continuation_or_left_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvNeg : (rlc_dualReflect v) 0 < 0)
    (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hvLeft : rlc_dualReflect v ∈ rlc_pathVertices gamma'.1
  · exact Or.inl hvLeft
  · right
    rcases rlc_connectorBarrier_negative_classify gamma gamma' hvNeg hvBarrier with
      hvLeft' | ⟨w, hw, hvflip⟩
    · exact False.elim (hvLeft hvLeft')
    · have hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1 := by
        intro hv
        have hvRect := rlc_pathVertex_mem_rect gamma.1 hv
        rw [mem_rect] at hvRect
        omega
      have hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
          rlc_dualReflect v = rlc_flipX r := by
        rintro ⟨r, hr, heq⟩
        have hvNegCoord := hvNeg
        have hrRect := rlc_pathVertex_mem_rect gamma'.1 hr
        rw [mem_rect] at hrRect
        have heq0 := congrArg (fun z : Site 2 => z 0) heq
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun] at hvNegCoord heq0
        omega
      exact rlc_reflectedRight_continuation_carrier
        gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
          hvFlipLeft hvInterior hnotIn hhRegion hh



theorem rlc_positiveBarrier_bad_exit_forces_right_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a u v : Site 2}
    (hau : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
    (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' a u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hav : a ≠ v)
    (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_pathVertices gamma.1 := by
  rcases hauCarrier with hwall | ⟨_haBox, _huBox, h, hhRegion, hh⟩
  · exact False.elim (hnotWall hwall)
  · rcases rlc_positiveBarrier_continuation_or_right_contact
      gamma gamma' rho hno hau huv hav huPos huBarrier huInterior
        (by simpa [Sym2.eq_swap] using hnotWall) hhRegion
        (by simpa [flankFaces_comm] using hh) with huRight | hcarrier
    · exact huRight
    · exact False.elim (hbad hcarrier)



theorem rlc_negativeBarrier_bad_exit_forces_left_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a u v : Site 2}
    (hau : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
    (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' a u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hav : a ≠ v)
    (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 := by
  rcases hauCarrier with hwall | ⟨_haBox, _huBox, h, hhRegion, hh⟩
  · exact False.elim (hnotWall hwall)
  · rcases rlc_negativeBarrier_continuation_or_left_contact
      gamma gamma' rho hno hau huv hav huNeg huBarrier huInterior
        (by simpa [Sym2.eq_swap] using hnotWall) hhRegion
        (by simpa [flankFaces_comm] using hh) with huLeft | hcarrier
    · exact huLeft
    · exact False.elim (hbad hcarrier)






theorem rlc_reflectedLeft_rightBoundary_continuation_carrier
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRightBoundary : (rlc_dualReflect v) 0 = 2 * n)
    (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hHRect : H ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
      hn gamma gamma' rho
  have hv0 : v 0 = -2 * n - 1 := by
    simp [rlc_dualReflect, rlc_dualReflectFun] at hvRightBoundary
    omega
  have hne : (![v 0 + 1, v 1 + 1] : Site 2) ∉ H :=
    rlc_reflectedLeft_hit_sourceNE_not_filled
      gamma gamma' hfaith rho hno hw hvflip
  have neighborDir {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t) :
      t = ![v 0 + 1, v 1] ∨ t = ![v 0, v 1 - 1] := by
    rcases rlc_faceBoundary_step_of_NE_not_mem H hvt hne with
      ⟨ht, _⟩ | ht | ⟨ht, htH⟩ | ht
    · exact Or.inl ht
    · exfalso
      subst t
      have hp : (![v 0, v 1] : Site 2) ∉ H := by
        intro hp
        have hpRect := hHRect hp
        rw [mem_rect] at hpRect
        simp at hpRect
        omega
      have hq : (![v 0, v 1 + 1] : Site 2) ∉ H := by
        intro hq
        have hqRect := hHRect hq
        rw [mem_rect] at hqRect
        simp at hqRect
        omega
      have hshared : sharedPrimalEdge v ![v 0 - 1, v 1] =
          s((![v 0, v 1] : Site 2), ![v 0, v 1 + 1]) := by
        simp [sharedPrimalEdge]
        omega
      have hbd := hvt.2
      rw [hshared, bdEdge_mk] at hbd
      simp [hp, hq] at hbd
    · exfalso
      subst t
      have htRect := hHRect htH
      rw [mem_rect] at htRect
      simp at htRect
      omega
    · exact Or.inr ht
  have huDir := neighborDir huv.symm
  have hbDir := neighborDir hvb
  have bottomLower {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t)
      (ht : t = ![v 0, v 1 - 1]) : -n ≤ v 1 := by
    subst t
    by_contra hv1
    have hp : (![v 0, v 1] : Site 2) ∉ H := by
      intro hp
      have hpRect := hHRect hp
      rw [mem_rect] at hpRect
      simp at hpRect
      omega
    have hq : (![v 0 + 1, v 1] : Site 2) ∉ H := by
      intro hq
      have hqRect := hHRect hq
      rw [mem_rect] at hqRect
      simp at hqRect
      omega
    have hshared : sharedPrimalEdge v ![v 0, v 1 - 1] =
        s((![v 0, v 1] : Site 2), ![v 0 + 1, v 1]) := by
      simp [sharedPrimalEdge]
    have hbd := hvt.2
    rw [hshared, bdEdge_mk] at hbd
    simp [hp, hq] at hbd
  have hvRect : rlc_dualReflect v ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hvBox
  rw [mem_rect] at hvRect
  simp [rlc_dualReflect, rlc_dualReflectFun] at hvRect
  rcases huDir with huDir | huDir <;>
    rcases hbDir with hbDir | hbDir
  · exact False.elim (hub (huDir.trans hbDir.symm))
  · have hv1Lower := bottomLower hvb hbDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · have hv1Lower := bottomLower huv.symm huDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · exact False.elim (hub (huDir.trans hbDir.symm))





theorem rlc_reflectedLeft_bottomBoundary_continuation_carrier
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvBottom : (rlc_dualReflect v) 1 = -n)
    (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hHRect : H ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
      hn gamma gamma' rho
  have hv1 : v 1 = -n - 1 := by
    simp [rlc_dualReflect, rlc_dualReflectFun] at hvBottom
    omega
  have hne : (![v 0 + 1, v 1 + 1] : Site 2) ∉ H :=
    rlc_reflectedLeft_hit_sourceNE_not_filled
      gamma gamma' hfaith rho hno hw hvflip
  have neighborDir {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t) :
      t = ![v 0 - 1, v 1] ∨ t = ![v 0, v 1 + 1] := by
    rcases rlc_faceBoundary_step_of_NE_not_mem H hvt hne with
      ⟨ht, htH⟩ | ht | ⟨ht, _⟩ | ht
    · exfalso
      subst t
      have htRect := hHRect htH
      rw [mem_rect] at htRect
      simp at htRect
      omega
    · exact Or.inl ht
    · exact Or.inr ht
    · exfalso
      subst t
      have hp : (![v 0, v 1] : Site 2) ∉ H := by
        intro hp
        have hpRect := hHRect hp
        rw [mem_rect] at hpRect
        simp at hpRect
        omega
      have hq : (![v 0 + 1, v 1] : Site 2) ∉ H := by
        intro hq
        have hqRect := hHRect hq
        rw [mem_rect] at hqRect
        simp at hqRect
        omega
      have hshared : sharedPrimalEdge v ![v 0, v 1 - 1] =
          s((![v 0, v 1] : Site 2), ![v 0 + 1, v 1]) := by
        simp [sharedPrimalEdge]
      have hbd := hvt.2
      rw [hshared, bdEdge_mk] at hbd
      simp [hp, hq] at hbd
  have leftLower {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t)
      (ht : t = ![v 0 - 1, v 1]) : -2 * n ≤ v 0 := by
    subst t
    by_contra hv0
    have hp : (![v 0, v 1] : Site 2) ∉ H := by
      intro hp
      have hpRect := hHRect hp
      rw [mem_rect] at hpRect
      simp at hpRect
      omega
    have hq : (![v 0, v 1 + 1] : Site 2) ∉ H := by
      intro hq
      have hqRect := hHRect hq
      rw [mem_rect] at hqRect
      simp at hqRect
      omega
    have hshared : sharedPrimalEdge v ![v 0 - 1, v 1] =
        s((![v 0, v 1] : Site 2), ![v 0, v 1 + 1]) := by
      simp [sharedPrimalEdge]
      omega
    have hbd := hvt.2
    rw [hshared, bdEdge_mk] at hbd
    simp [hp, hq] at hbd
  have huDir := neighborDir huv.symm
  have hbDir := neighborDir hvb
  have hvRect : rlc_dualReflect v ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hvBox
  rw [mem_rect] at hvRect
  simp [rlc_dualReflect, rlc_dualReflectFun] at hvRect
  rcases huDir with huDir | huDir <;>
    rcases hbDir with hbDir | hbDir
  · exact False.elim (hub (huDir.trans hbDir.symm))
  · have hv0Lower := leftLower huv.symm huDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · have hv0Lower := leftLower hvb hbDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · exact False.elim (hub (huDir.trans hbDir.symm))


theorem rlc_reflectedEdgeCarrierGeometry_comm {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' g f := by
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  constructor
  · rintro (hwall | ⟨hf, hg, hregion⟩)
    · exact Or.inl (by simpa [Sym2.eq_swap] using hwall)
    · refine Or.inr ⟨hg, hf, ?_⟩
      simpa [flankFaces_comm] using hregion
  · rintro (hwall | ⟨hg, hf, hregion⟩)
    · exact Or.inl (by simpa [Sym2.eq_swap] using hwall)
    · refine Or.inr ⟨hf, hg, ?_⟩
      simpa [flankFaces_comm] using hregion





noncomputable def rlc_connectorCentralFaceGoodBoundaryGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (Site 2) where
  Adj f g :=
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g ∧
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g
  symm := by
    rintro f g ⟨hfg, hgood⟩
    exact ⟨hfg.symm,
      (rlc_reflectedEdgeCarrierGeometry_comm gamma gamma' f g).1 hgood⟩
  loopless := ⟨fun f hff => hff.1.ne rfl⟩

theorem rlc_connectorCentralFaceGoodBoundaryGraph_le {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := by
  intro f g hfg
  exact hfg.1

theorem RlcCentralFaceRetainedAnchoredBoundary.anchor_mem_goodBoundaryGraph
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj
      B.firstFace B.secondFace := by
  refine ⟨B.anchor_adj, ?_⟩
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' B.anchor_adj.1).2
      (B.anchor_reflected_mem_planar hfaith)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          N z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (![0, L.boundary.height + 1] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' ∨
      (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma' := by
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le
    gamma gamma' rho
  let p := q.mapLe hle
  obtain ⟨w, hwSupport, z, hzw, hzBarrier⟩ :=
    L.boundaryPrefix_to_outsideAxis_meetsBarrier hfaith p hN huNeg
      hreflected hkOutside
  rcases hwSupport z hzw with hzAnchor | hzOutside | ⟨f, hf, hzf⟩
  · exact Or.inr (Or.inl (by simpa [hzAnchor] using hzBarrier))
  · exact Or.inr (Or.inr (by simpa [hzOutside] using hzBarrier))
  · left
    have hfQ : f ∈ q.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hf
    refine ⟨f, ⟨q.takeUntil f hfQ⟩, ?_⟩
    rwa [hzf] at hzBarrier



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeAnchor_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {N : Site 2}
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2)) :
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
      L.boundary.firstFace N := by
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, L.boundary.height + 1] : Site 2),
          ![0, L.boundary.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hmem : rlc_dualReflect N ∈
      s(rlc_dualReflect L.boundary.firstFace,
        rlc_dualReflect L.boundary.secondFace) := by
    rw [htarget, hN]
    exact Sym2.mem_mk_left _ _
  rw [Sym2.mem_iff] at hmem
  rcases hmem with hmem | hmem
  · have hEq : N = L.boundary.firstFace :=
      rlc_dualReflect.injective hmem
    subst N
    exact Reachable.refl _
  · have hEq : N = L.boundary.secondFace :=
      rlc_dualReflect.injective hmem
    subst N
    exact (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable




theorem rlc_goodBoundary_reachable_dualReflect_mem_box_of_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x z : Site 2}
    (hx : rlc_dualReflect x ∈ rlc_connectorBox n)
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x z) :
    rlc_dualReflect z ∈ rlc_connectorBox n := by
  obtain ⟨w⟩ := hz
  induction w with
  | nil => exact hx
  | @cons u v t huv p ih =>
      apply ih
      have hplanar :=
        (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
          gamma gamma' huv.1.1).1 huv.2
      exact rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
        gamma gamma' hplanar (Sym2.mem_mk_right _ _)

theorem rlc_goodBoundary_reachable_dualReflect_mem_box
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    rlc_dualReflect z ∈ rlc_connectorBox n := by
  have hstart : rlc_dualReflect B.firstFace ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box gamma gamma'
      (B.anchor_reflected_mem_planar hfaith)
      (Sym2.mem_mk_left _ _)
  exact rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hstart hz





theorem rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ A : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, B.height + 1] : Site 2) ∧
        (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
          rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') := by
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, B.height + 1] : Site 2), ![0, B.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hzeroMem : (![0, B.height + 1] : Site 2) ∈
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) := by
    rw [htarget]
    exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hzeroMem
  obtain ⟨A, hfirstA, hAfirst, hAzero⟩ :
      ∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, B.height + 1] : Site 2) := by
    rcases hzeroMem with hfirst | hsecond
    · exact ⟨B.firstFace, Reachable.refl _, Reachable.refl _, hfirst.symm⟩
    · exact ⟨B.secondFace, hanchor.reachable,
        hanchor.reachable.symm, hsecond.symm⟩
  refine ⟨A, hfirstA, hAfirst, hAzero, ?_⟩
  by_cases hbarrier : (![0, B.height + 1] : Site 2) ∈
      rlc_connectorBarrier gamma gamma'
  · rcases (rlc_axis_mem_connectorBarrier_iff
      gamma gamma' (B.height + 1)).1 hbarrier with hright | hleft
    · have haxis := hfaith.right_axis_unique hright (by simp)
      have hheight := congrArg (fun z : Site 2 => z 1) haxis
      have hlower := B.height_lower
      simp at hheight
      omega
    · exact Or.inl (by simpa [hAzero] using hleft)
  · exact Or.inr (by simpa [hAzero] using hbarrier)



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.axisAnchor_barrier_forces_reachable_left_contact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hbarrier : (![0, L.boundary.height + 1] : Site 2) ∈
      rlc_connectorBarrier gamma gamma') :
    ∃ A : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace A ∧
        rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 := by
  obtain ⟨A, hfirstA, _hAfirst, hAzero, hleft | hoff⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  · exact ⟨A, hfirstA, hleft⟩
  · exact False.elim (hoff (by simpa [hAzero] using hbarrier))




theorem rlc_faithful_axisOutside_barrier_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hbarrier : (![0, k] : Site 2) ∈
      rlc_connectorBarrier gamma gamma') :
    (k ≤ (gamma.1.1 : Site 2) 1 →
      (![0, k] : Site 2) ∈ rlc_pathVertices gamma.1) ∧
    ((gamma'.1.2.1 : Site 2) 1 < k → False) := by
  have haxis := (rlc_axis_mem_connectorBarrier_iff gamma gamma' k).1 hbarrier
  constructor
  · intro hk
    rcases haxis with hright | hleft
    · exact hright
    · have heq := hfaith.left_axis_unique hleft (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      have horder := hfaith.axis_contacts_strict
      simp at heq1
      omega
  · intro hk
    rcases haxis with hright | hleft
    · have heq := hfaith.right_axis_unique hright (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      have horder := hfaith.axis_contacts_strict
      simp at heq1
      omega
    · have heq := hfaith.left_axis_unique hleft (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      simp at heq1
      omega





theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_contact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace A ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1) ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma.1 := by
  have hfirstN := L.negativeAnchor_reachable hfaith hN
  rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint
      hfaith q hN huNeg hreflected hkOutside with
    ⟨z, hNz, hzBarrier⟩ | hAnchor | hOutside
  · exact Or.inl ⟨z, hfirstN.trans hNz, hzBarrier⟩
  · exact Or.inr (Or.inl
      (L.axisAnchor_barrier_forces_reachable_left_contact
        hfaith hAnchor))
  · have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
      rw [Sym2.eq_iff] at hreflected
      rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
      · exact hv
      · have h0 := congrArg (fun z : Site 2 => z 0) hu
        have h0' : (rlc_dualReflect u) 0 = 0 := by
          simpa only [Matrix.cons_val_zero] using h0
        omega
    rcases hkOutside with hkLow | hkHigh
    · exact Or.inr (Or.inr (by
        rw [hvEq]
        exact (rlc_faithful_axisOutside_barrier_classify
          gamma gamma' hfaith hOutside).1 hkLow))
    · exact False.elim
        ((rlc_faithful_axisOutside_barrier_classify
          gamma gamma' hfaith hOutside).2 hkHigh)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
  rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_contact
      hfaith q hN huNeg hreflected hkOutside with
    hbarrier | hleft | hright
  · exact Or.inl hbarrier
  · exact Or.inr (Or.inl hleft)
  · have hcarrier := rlc_reflected_axisCrossing_carrier_of_right_contact
      gamma gamma' hfaith huNeg hreflected hright
    have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
    have hfirstN := L.negativeAnchor_reachable hfaith hN
    exact Or.inr (Or.inr ⟨v,
      hfirstN.trans (q.reachable.trans huvGood.reachable), hright⟩)








theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_extremeAxis_reachableBarrier_contact_or_higherAxis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkExtreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
      L.boundary.height + 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1 := by
  rcases hkExtreme with hkLow | hkHigh
  · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
        hfaith q hN huNeg huv hreflected (Or.inl hkLow) with
      hbarrier | hleft | hright
    · exact Or.inl hbarrier
    · exact Or.inr (Or.inl hleft)
    · exact Or.inr (Or.inr (Or.inl hright))
  · by_cases hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1
    · have hcarrier := rlc_reflected_axisCrossing_carrier_of_between
        gamma gamma' hfaith huv.1 hreflected (by
          have hlower := L.boundary.height_lower
          omega) hkUpper
      have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
      have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
        rw [Sym2.eq_iff] at hreflected
        rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
        · exact hv
        · have h0 := congrArg (fun z : Site 2 => z 0) hu
          have h0' : (rlc_dualReflect u) 0 = 0 := by
            simpa only [Matrix.cons_val_zero] using h0
          omega
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      exact Or.inr (Or.inr (Or.inr ⟨v,
        hfirstN.trans (q.reachable.trans huvGood.reachable),
        hvEq, hkHigh, hkUpper⟩))
    · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
          hfaith q hN huNeg huv hreflected (Or.inr (by omega)) with
        hbarrier | hleft | hright
      · exact Or.inl hbarrier
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))




theorem rlc_goodBoundary_walk_to_boxBoundary_meets_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (pGood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    ∃ z ∈ pGood.support,
      rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra hnone
  push Not at hnone
  have hpAvoid : ∀ z ∈ pGood.support,
      rlc_dualReflect z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    exact hnone z hz
  let hle : rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      hypercubicLattice 2 := fun _ _ h => h.1.1
  let pDual := (pGood.mapLe hle).map rlc_dualReflectLatticeHom
  let pAxis : (hypercubicLattice 2).Walk
      (![0, B.height + 1] : Site 2) (rlc_dualReflect u) :=
    pDual.copy hAzero rfl
  have hpAxisAvoid : ∀ z ∈ pAxis.support,
      z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    dsimp only [pAxis, pDual] at hz
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    exact hpAvoid z0 hz0
  have huNot : rlc_dualReflect u ∉
      rlc_connectorBarrier gamma gamma' :=
    hpAvoid u pGood.end_mem_support
  obtain ⟨pOut, hpOutAvoid⟩ :=
    rlc_connectorBoxBoundary_detour_avoidsBarrier
      gamma gamma' huBoundary huNot
  let p := pAxis.append pOut
  have hkLower : (gamma.1.1 : Site 2) 1 < B.height + 1 := by
    have hlower := B.height_lower
    omega
  have hkUpper : B.height + 1 ≤ (gamma'.1.2.1 : Site 2) 1 := by
    have hupper := B.height_upper
    omega
  obtain ⟨z, hz, hzBarrier⟩ :=
    rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper p
  dsimp only [p] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  exact hz.elim (fun hz => hpAxisAvoid z hz hzBarrier)
    (fun hz => hpOutAvoid z hz hzBarrier)





theorem rlc_goodBoundary_barrier_hit_before_boxBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    ∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  let k := B.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, k] : Site 2), ![0, k]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [k, Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hzeroMem : (![0, k] : Site 2) ∈
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) := by
    rw [htarget]
    exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hzeroMem
  obtain ⟨A, hfirstA, hAfirst, hAzero⟩ :
      ∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, k] : Site 2) := by
    rcases hzeroMem with hfirst | hsecond
    · exact ⟨B.firstFace, Reachable.refl _, Reachable.refl _, hfirst.symm⟩
    · exact ⟨B.secondFace, hanchor.reachable,
        hanchor.reachable.symm, hsecond.symm⟩
  by_contra hnone
  push Not at hnone
  obtain ⟨pGood⟩ := hAfirst.trans hu
  have hpAvoid : ∀ z ∈ pGood.support,
      rlc_dualReflect z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz hbarrier
    apply hnone z (hfirstA.trans ⟨pGood.takeUntil z hz⟩)
    exact hbarrier
  let hle : rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      hypercubicLattice 2 := fun _ _ h => h.1.1
  let pDual := (pGood.mapLe hle).map rlc_dualReflectLatticeHom
  let pAxis : (hypercubicLattice 2).Walk
      (![0, k] : Site 2) (rlc_dualReflect u) := pDual.copy hAzero rfl
  have hpAxisAvoid : ∀ z ∈ pAxis.support,
      z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    dsimp only [pAxis, pDual] at hz
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    exact hpAvoid z0 hz0
  have huNot : rlc_dualReflect u ∉
      rlc_connectorBarrier gamma gamma' := hnone u hu
  obtain ⟨pOut, hpOutAvoid⟩ :=
    rlc_connectorBoxBoundary_detour_avoidsBarrier
      gamma gamma' huBoundary huNot
  let p := pAxis.append pOut
  have hkLower : (gamma.1.1 : Site 2) 1 < k := by
    have hlower := B.height_lower
    dsimp only [k]
    omega
  have hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1 := by
    have hupper := B.height_upper
    dsimp only [k]
    omega
  obtain ⟨z, hz, hzBarrier⟩ :=
    rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper p
  dsimp only [p] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  exact hz.elim (fun hz => hpAxisAvoid z hz hzBarrier)
    (fun hz => hpOutAvoid z hz hzBarrier)




theorem rlc_goodBoundary_reachable_wall_or_region_incident
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj
            (rlc_dualReflect z) (rlc_dualReflect w) ∧
          rlc_dualReflect w ∈ rlc_connectorBox n ∧
          ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
            h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hincident : ∃ w : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj z w := by
    by_cases hzFirst : z = B.firstFace
    · subst z
      exact ⟨B.secondFace, hanchor⟩
    · obtain ⟨p⟩ := hz.symm
      cases p with
      | nil => exact False.elim (hzFirst rfl)
      | @cons a w c haw p => exact ⟨w, haw⟩
  obtain ⟨w, hzw⟩ := hincident
  rcases hzw.2 with hwall | ⟨hzBox, hwBox, hregion⟩
  · exact Or.inl (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _))
  · exact Or.inr ⟨w, (rlc_adj_dualReflect z w).mp hzw.1.1,
      hwBox, hregion⟩




theorem rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x z : Site 2}
    (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x z) :
    rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj
            (rlc_dualReflect z) (rlc_dualReflect w) ∧
          rlc_dualReflect w ∈ rlc_connectorBox n ∧
          ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
            h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
  by_cases hzx : z = x
  · subst z
    exact Or.inl hxBarrier
  · obtain ⟨p⟩ := hz.symm
    have hincident : ∃ w : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj z w := by
      cases p with
      | nil => exact False.elim (hzx rfl)
      | @cons a w c haw p => exact ⟨w, haw⟩
    obtain ⟨w, hzw⟩ := hincident
    rcases hzw.2 with hwall | ⟨_hzBox, hwBox, hregion⟩
    · exact Or.inl (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hwall (Sym2.mem_mk_left _ _))
    · exact Or.inr ⟨w, (rlc_adj_dualReflect z w).mp hzw.1.1,
        hwBox, hregion⟩





theorem rlc_walk_subgraph_prefix_or_first_exit
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, ∀ e ∈ q.edges, e ∈ w.edges) ∨
      ∃ (u v : V) (q : G.Walk x u),
        H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧
          ∀ e ∈ q.edges, e ∈ w.edges := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, by simp⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, huv, huvW, huvBad, hq⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
        · right
          refine ⟨u, v, .cons habG q, huv, by simp [huvW], huvBad, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
      · right
        exact ⟨a, b, .nil, hab, by simp, habG, by simp⟩




theorem rlc_walk_subgraph_exact_or_first_exit
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, q.edges = w.edges) ∨
      ∃ (u v : V) (q : G.Walk x u),
        H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧
          ∀ e ∈ q.edges, e ∈ w.edges := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, huv, huvW, huvBad, hq⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          simp [SimpleGraph.Walk.edges_cons, hq]
        · right
          refine ⟨u, v, .cons habG q, huv, by simp [huvW], huvBad, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
      · right
        exact ⟨a, b, .nil, hab, by simp, habG, by simp⟩




theorem rlc_walk_subgraph_lift_or_first_exit_decomp
    {V : Type*} {G H : SimpleGraph V} (hle : G ≤ H)
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, q.mapLe hle = w) ∨
      ∃ (u v : V) (q : G.Walk x u) (r : H.Walk v y)
        (huv : H.Adj u v),
        ¬ G.Adj u v ∧
          w = (q.mapLe hle).append (.cons huv r) := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          simp only [SimpleGraph.Walk.map_cons]
          change q.map (.ofLE hle) = p at hq
          rw [hq]
          apply SimpleGraph.Walk.ext_support
          rfl
        · right
          refine ⟨u, v, .cons habG q, r, huv, huvBad, ?_⟩
          rw [hdecomp]
          apply SimpleGraph.Walk.ext_support
          simp [SimpleGraph.Walk.support_append,
            SimpleGraph.Walk.support_mapLe_eq_support]
      · right
        exact ⟨a, b, .nil, p, hab, habG, by simp⟩



theorem rlc_goodBoundary_prefix_or_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y,
      ∀ e ∈ q.edges, e ∈ w.edges) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u),
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ w.edges ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ∀ e ∈ q.edges, e ∈ w.edges := by
  rcases rlc_walk_subgraph_prefix_or_first_exit
      (G := rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho)
      w with hgood | hbad
  · exact Or.inl hgood
  · right
    obtain ⟨u, v, q, huv, huvW, huvBad, hq⟩ := hbad
    refine ⟨u, v, q, huv, huvW, ?_, hq⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩


theorem rlc_goodBoundary_exact_or_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y, q.edges = w.edges) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u),
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ w.edges ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ∀ e ∈ q.edges, e ∈ w.edges := by
  rcases rlc_walk_subgraph_exact_or_first_exit
      (G := rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho)
      w with hgood | ⟨u, v, q, huv, huvW, huvBad, hq⟩
  · exact Or.inl hgood
  · right
    refine ⟨u, v, q, huv, huvW, ?_, hq⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩



theorem rlc_goodBoundary_lift_or_first_bad_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y,
      q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le
        gamma gamma' rho) = w) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u)
        (r : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v y)
        (huv : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v),
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          w = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le
            gamma gamma' rho)).append (.cons huv r) := by
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle w with
      ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
  · exact Or.inl ⟨q, hq⟩
  · right
    refine ⟨u, v, q, r, huv, ?_, hdecomp⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩





theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  let last : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' u' :=
    hu'v'.symm.toWalk
  let m : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u u' :=
    .cons huv (t.reverse.append last)
  have huvA : s(u, v) ∈ a.edges := by
    rw [hdecomp, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_cons, List.mem_append]
    exact Or.inr (by simp)
  have hrA {e : Sym2 (Site 2)} (he : e ∈ r.edges) : e ∈ a.edges := by
    rw [hdecomp, SimpleGraph.Walk.edges_append, List.mem_append]
    exact Or.inr (by simp [he])
  have htR {e : Sym2 (Site 2)} (he : e ∈ t.edges) : e ∈ r.edges := by
    have heRev : e ∈ r.reverse.edges := by
      rw [hdecomp', SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_cons, List.mem_append]
      exact Or.inr (by simp [he])
    simpa [SimpleGraph.Walk.edges_reverse] using heRev
  have hu'v'R : s(u', v') ∈ r.edges := by
    have heRev : s(u', v') ∈ r.reverse.edges := by
      rw [hdecomp', SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_cons, List.mem_append]
      exact Or.inr (by simp)
    simpa [SimpleGraph.Walk.edges_reverse] using heRev
  have hmA : ∀ e ∈ m.edges, e ∈ a.edges := by
    intro e he
    simp only [m, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_append, List.mem_cons, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with rfl | he | he
    · exact huvA
    · exact hrA (htR he)
    · have heEq : e = s(v', u') := by
        simpa [last] using he
      subst e
      simpa [Sym2.eq_swap] using hrA hu'v'R
  obtain ⟨f, g, k, hfgM, hreflected, hextreme⟩ :=
    L.middlePath_axis_crossing_extreme m huNeg hu'Pos
      (by
        intro e he
        exact (haExact e).2 (Or.inr (hmA e he)))
      (by
        intro he
        exact haAvoid (hmA _ he))
  exact ⟨f, g, k, (haExact _).2 (Or.inr (hmA _ hfgM)),
    hreflected, hextreme⟩





theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_location_twoBadMiddle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    {f g : Site 2} (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
    (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(L.boundary.firstFace, L.boundary.secondFace) ∨
      s(f, g) ∈ q.edges ∨ s(f, g) ∈ q'.edges ∨ s(f, g) ∈ t.edges := by
  have bad_ne {x y : Site 2}
      (hxyBad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' x y)
      (heq : s(f, g) = s(x, y)) : False := by
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hfx, hgy⟩ | ⟨hfy, hgx⟩
    · subst f
      subst g
      exact hxyBad hfgGood
    · subst f
      subst g
      exact hxyBad
        ((rlc_reflectedEdgeCarrierGeometry_comm gamma gamma' y x).1 hfgGood)
  rcases (haExact s(f, g)).1 hfgContour with hanchor | hfa
  · exact Or.inl hanchor
  right
  rw [hdecomp, SimpleGraph.Walk.edges_append, List.mem_append] at hfa
  rcases hfa with hfq | hfr
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfq)
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hfr
  rcases hfr with hbadEdge | hfr
  · exact (bad_ne hbad hbadEdge).elim
  have hfrReverse : s(f, g) ∈ r.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hfr
  rw [hdecomp', SimpleGraph.Walk.edges_append, List.mem_append] at hfrReverse
  rcases hfrReverse with hfq' | hft
  · exact Or.inr (Or.inl (by
      simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfq'))
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hft
  rcases hft with hbadEdge' | hft
  · exact (bad_ne hbad' hbadEdge').elim
  · exact Or.inr (Or.inr hft)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_mem_middle_of_avoids_anchor_prefixes
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    {f g : Site 2} (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
    (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g)
    (havoidAnchor : s(f, g) ≠
      s(L.boundary.firstFace, L.boundary.secondFace))
    (havoidQ : s(f, g) ∉ q.edges) (havoidQ' : s(f, g) ∉ q'.edges) :
    s(f, g) ∈ t.edges := by
  rcases L.goodContourEdge_location_twoBadMiddle haExact q r huv hbad
      hdecomp q' t hu'v' hbad' hdecomp' hfgContour hfgGood with
    hanchor | hq | hq' | ht
  · exact (havoidAnchor hanchor).elim
  · exact (havoidQ hq).elim
  · exact (havoidQ' hq').elim
  · exact ht




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementaryPath_good_or_two_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      a.IsPath ∧
      (∀ e : Sym2 (Site 2),
        e ∈ L.boundary.contour.edges ↔
          e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
            e ∈ a.edges) ∧
      ((∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk L.boundary.firstFace L.boundary.secondFace,
          q.edges = a.edges) ∨
        ∃ (u v u' v' : Site 2)
          (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
            L.boundary.firstFace u)
          (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
            L.boundary.secondFace u'),
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
          s(u, v) ∈ a.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v' ∧
          s(u', v') ∈ a.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') := by
  obtain ⟨a, haPath, _haAvoid, haExact⟩ :=
    L.complementary_axis_path_exact
  refine ⟨a, haPath, haExact, ?_⟩
  rcases rlc_goodBoundary_exact_or_first_bad a with
      ⟨q, hqEdges⟩ | ⟨u, v, q, huv, huvA, hbad, _hqA⟩
  · exact Or.inl ⟨q, hqEdges⟩
  · rcases rlc_goodBoundary_exact_or_first_bad a.reverse with
        ⟨q', hq'Edges⟩ | ⟨u', v', q', hu'v', hu'v'A, hbad', _hq'A⟩
    · exfalso
      have huvRev : s(u, v) ∈ a.reverse.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using huvA
      have huvQ : s(u, v) ∈ q'.edges := by
        rw [hq'Edges]
        exact huvRev
      exact hbad (q'.adj_of_mem_edges huvQ).2
    · exact Or.inr ⟨u, v, u', v', q, q', huv, huvA, hbad, hu'v',
        by simpa [SimpleGraph.Walk.edges_reverse] using hu'v'A, hbad'⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.reachableFaithfulContacts_of_complementaryPath_good
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace L.boundary.secondFace)
    (hqEdges : q.edges = a.edges) :
    ∃ x y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x y ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
  have hanchorGood := L.boundary.anchor_mem_goodBoundaryGraph hfaith
  have reachable_of_contour {z : Site 2}
      (hz : z ∈ L.boundary.contour.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace z := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with hz | ⟨e, he, hze⟩
    · subst z
      exact Reachable.refl _
    · rcases (haExact e).1 he with heAnchor | heA
      · subst e
        rw [Sym2.mem_iff] at hze
        rcases hze with rfl | rfl
        · exact Reachable.refl _
        · exact hanchorGood.reachable
      · have heQ : e ∈ q.edges := by
          rw [hqEdges]
          exact heA
        have hzQ : z ∈ q.support := by
          rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
          exact Or.inr ⟨e, heQ, hze⟩
        exact ⟨q.takeUntil z hzQ⟩
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupport
  obtain ⟨y', hyy'⟩ := hySupport
  have hxe : s(x, x') ∈ L.boundary.contour.edges :=
    L.boundary.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hxx')
  have hye : s(y, y') ∈ L.boundary.contour.edges :=
    L.boundary.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hyy')
  have hxContour := L.boundary.contour.fst_mem_support_of_mem_edges hxe
  have hyContour := L.boundary.contour.fst_mem_support_of_mem_edges hye
  exact ⟨x, y, (reachable_of_contour hxContour).symm.trans
    (reachable_of_contour hyContour), hxPath, hyPath⟩





theorem rlc_goodBoundary_first_barrier_incoming_region_flank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {A z : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A z)
    (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
    (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
    ∃ (u v : Site 2)
      (q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk A u),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj u v ∧
        s(u, v) ∈ p.edges ∧
        (∀ e ∈ q.edges, e ∈ p.edges) ∧
        (∀ w ∈ q.support,
          rlc_dualReflect w ∉ rlc_connectorBarrier gamma gamma') ∧
        rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  let P : Site 2 → Prop := fun w =>
    rlc_dualReflect w ∉ rlc_connectorBarrier gamma gamma'
  obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqAvoid, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p P hA (by
      simpa only [P, not_not] using hz)
  have hvBarrier : rlc_dualReflect v ∈
      rlc_connectorBarrier gamma gamma' := by
    simpa only [P, not_not] using hv
  have hnotWall : s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    intro hwall
    have huBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _)
    exact (hqAvoid u q.end_mem_support) huBarrier
  rcases huv.2 with hwall | hregion
  · have huBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _)
    exact False.elim ((hqAvoid u q.end_mem_support) huBarrier)
  · exact ⟨u, v, q, huv, huvEdge, hqEdges, hqAvoid, hvBarrier, hnotWall,
      hregion.1, hregion.2.1, hregion.2.2⟩





theorem rlc_goodBoundary_first_barrier_contact_boundary_or_extend
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {A z : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A z)
    (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
    (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
    ∃ (u v b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable A v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧
      u ≠ b ∧
      rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧
      (rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
        rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
        ¬ (-2 * n < (rlc_dualReflect v) 0 ∧
          (rlc_dualReflect v) 0 < 2 * n ∧
          -n < (rlc_dualReflect v) 1 ∧
          (rlc_dualReflect v) 1 < n) ∨
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj v b) := by
  obtain ⟨u, v, q, huv, _huvEdge, _hqEdges, _hqAvoid,
      hvBarrier, hnotIn, _huBox, _hvBox, h, hhRegion, hh⟩ :=
    rlc_goodBoundary_first_barrier_incoming_region_flank p hA hz
  obtain ⟨b, hvb, hub⟩ :=
    rlc_connectorCentralFaceFilledBoundary_other_neighbor
      gamma gamma' rho huv.1
  refine ⟨u, v, b, q.reachable.trans huv.reachable, hvb, hub,
    hvBarrier, ?_⟩
  by_cases hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n
  · rcases lt_trichotomy (rlc_dualReflect v 0) 0 with hvNeg | hvZero | hvPos
    · rcases rlc_negativeBarrier_continuation_or_left_contact
        gamma gamma' rho hno huv.1 hvb hub hvNeg hvBarrier hvInterior
          (by simpa [Sym2.eq_swap] using hnotIn) hhRegion
          (by simpa [flankFaces_comm] using hh) with
          hvLeft | hcarrier
      · exact Or.inr (Or.inl hvLeft)
      · exact Or.inr (Or.inr (Or.inr ⟨hvb, hcarrier⟩))
    · have hvEq : rlc_dualReflect v =
          (![0, (rlc_dualReflect v) 1] : Site 2) := by
        ext i
        fin_cases i
        · simpa using hvZero
        · rfl
      have hvBarrier' : (![0, (rlc_dualReflect v) 1] : Site 2) ∈
          rlc_connectorBarrier gamma gamma' := by
        rwa [← hvEq]
      have hvAxis := (rlc_axis_mem_connectorBarrier_iff gamma gamma'
        ((rlc_dualReflect v) 1)).1 hvBarrier'
      rcases hvAxis with hvRight | hvLeft
      · exact Or.inl (by rwa [hvEq])
      · exact Or.inr (Or.inl (by rwa [hvEq]))
    · rcases rlc_positiveBarrier_continuation_or_right_contact
        gamma gamma' rho hno huv.1 hvb hub hvPos hvBarrier hvInterior
          (by simpa [Sym2.eq_swap] using hnotIn) hhRegion
          (by simpa [flankFaces_comm] using hh) with
          hvRight | hcarrier
      · exact Or.inl hvRight
      · exact Or.inr (Or.inr (Or.inr ⟨hvb, hcarrier⟩))
  · exact Or.inr (Or.inr (Or.inl hvInterior))





theorem rlc_goodBoundary_first_bad_toward
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {z : Site 2}
    (hz : z ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    ∃ u v : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace u ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace v := by
  have hfirst : B.firstFace ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support :=
    B.anchor_adj.mem_support_left
  obtain ⟨w⟩ := rlc_connectorCentralFaceFilledFaceBoundary_reachable
    gamma gamma' rho hfirst hz
  obtain ⟨u, v, huvEdge, hu, hv⟩ := rlc_walk_pred_first_exit w
    (fun a => (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace a)
    (Reachable.refl _) hzNot
  have huv := w.adj_of_mem_edges huvEdge
  refine ⟨u, v, hu, huv, ?_, hv⟩
  intro hcarrier
  have hgood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
  exact hv (hu.trans hgood.reachable)



theorem rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x u v : Site 2}
    (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
    (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra huBarrier
  rcases rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start
      hxBarrier hu with huWall | ⟨w, huw, _hwBox, h, hhRegion, hhFlank⟩
  · exact huBarrier huWall
  · have huvTarget := (rlc_adj_dualReflect u v).mp huv.1
    have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box_of_start
      hxBox hu
    have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
      omega
    generalize hkEq : flankFaces (rlc_dualReflect u) (rlc_dualReflect v) = e
    induction e using Sym2.inductionOn with
    | _ k l =>
        have hkFlank : k ∈
            flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
          rw [hkEq]
          exact Sym2.mem_mk_left _ _
        have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
          gamma gamma' huw huvTarget huInterior huBarrier
            hhRegion hhFlank hkFlank
        apply hbad
        exact Or.inr ⟨huBox, hvBox, k, hkRegion, hkFlank⟩




theorem rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra huBarrier
  rcases rlc_goodBoundary_reachable_wall_or_region_incident
      B hfaith hu with huWall | ⟨w, huw, _hwBox, h, hhRegion, hhFlank⟩
  · exact huBarrier huWall
  · have huvTarget := (rlc_adj_dualReflect u v).mp huv.1
    have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      B hfaith hu
    have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
      omega
    generalize hkEq : flankFaces (rlc_dualReflect u) (rlc_dualReflect v) = e
    induction e using Sym2.inductionOn with
    | _ k l =>
        have hkFlank : k ∈
            flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
          rw [hkEq]
          exact Sym2.mem_mk_left _ _
        have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
          gamma gamma' huw huvTarget huInterior huBarrier
            hhRegion hhFlank hkFlank
        apply hbad
        exact Or.inr ⟨huBox, hvBox, k, hkRegion, hkFlank⟩





theorem rlc_badExit_interior_nonwall_box_noCentralFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    s(rlc_dualReflect u, rlc_dualReflect v) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      rlc_dualReflect u ∈ rlc_connectorBox n ∧
      rlc_dualReflect v ∈ rlc_connectorBox n ∧
      ∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have huvTarget : (hypercubicLattice 2).Adj
      (rlc_dualReflect u) (rlc_dualReflect v) :=
    (rlc_adj_dualReflect u v).mp huv.1
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    omega
  have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
    omega
  have hnotWall : s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    intro hwall
    exact hbad (Or.inl hwall)
  refine ⟨hnotWall, huBox, hvBox, ?_⟩
  intro h hhRegion hhFlank
  exact hbad (Or.inr ⟨huBox, hvBox, h, hhRegion, hhFlank⟩)



theorem rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
      (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · exact Or.inl
      (rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        B hfaith hu huv hbad huInterior)
  · push Not at huInterior
    omega




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      ∃ w ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect u = rlc_flipX w ∧
          ∀ a : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Adj a u →
            a ≠ v →
            s(rlc_dualReflect a, rlc_dualReflect u) ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    L.boundary hfaith hu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr (Or.inl huBoundary)
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        L.boundary hfaith hu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · have huRect := rlc_pathVertex_mem_rect gamma.1 huRight
      rw [mem_rect] at huRect
      omega
    · exact Or.inl ⟨u, hu, huLeft⟩
    · omega
    · obtain ⟨_huNeg, w, hw, huw⟩ := huFlipRight
      by_cases hwall : ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr (Or.inr ⟨w, hw, huw, hwall⟩)
      · simp only [not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huLeft := rlc_negativeBarrier_bad_exit_forces_left_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall huNeg
            huBarrier huInterior hbad
        exact Or.inl ⟨u, hu, huLeft⟩




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w ∧
          ∀ a : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Adj a u →
            a ≠ v →
            s(rlc_dualReflect a, rlc_dualReflect u) ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    L.boundary hfaith hu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr (Or.inl huBoundary)
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        L.boundary hfaith hu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, hu, huRight⟩
    · have huRect := rlc_pathVertex_mem_rect gamma'.1 huLeft
      rw [mem_rect] at huRect
      omega
    · obtain ⟨_huPos, w, hw, huw⟩ := huFlipLeft
      by_cases hwall : ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr (Or.inr ⟨w, hw, huw, hwall⟩)
      · simp only [not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huRight := rlc_positiveBarrier_bad_exit_forces_right_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall huPos
            huBarrier huInterior hbad
        exact Or.inl ⟨u, hu, huRight⟩
    · omega




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno hu huNeg huv hbad with hleft | hboundary | hwall
  · exact Or.inl hleft
  · exact Or.inr (rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu hboundary)
  · obtain ⟨w, hw, huw, _hwall⟩ := hwall
    refine Or.inr ⟨u, hu, ?_⟩
    simp [rlc_connectorBarrier, huw, hw]



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
      hfaith hno hu huPos huv hbad with hright | hboundary | hwall
  · exact Or.inl hright
  · exact Or.inr (rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu hboundary)
  · obtain ⟨w, hw, huw, _hwall⟩ := hwall
    refine Or.inr ⟨u, hu, ?_⟩
    simp [rlc_connectorBarrier, huw, hw]






theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachable_or_negativeBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ (x : Site 2) (k : Int),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1) ∨
      ∃ u v : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace u ∧
          (rlc_dualReflect u) 0 < 0 ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
              u v ∧
          s(u, v) ∈ L.boundary.contour.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
            (rlc_dualReflect u) 0 = -2 * n ∨
            (rlc_dualReflect u) 0 = 2 * n ∨
            (rlc_dualReflect u) 1 = -n ∨
            (rlc_dualReflect u) 1 = n) := by
  obtain ⟨a, N, u, v, k, q, _hNside, hN, _haAvoid, _haPath, _haExact,
      haEdges, hqA, hqNeg, huv, _huvA, hreflected, hkLow | hkHigh⟩ :=
    L.complementary_first_axis_crossing_extreme
  · rcases rlc_goodBoundary_prefix_or_first_bad q with
      ⟨qGood, _hqGood⟩ |
        ⟨ub, vb, qGood, hubv, hubvQ, hbad, _hqGood⟩
    · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
          hfaith qGood hN (hqNeg u q.end_mem_support) huv hreflected
            (Or.inl hkLow) with hbarrier | hleft | hright
      · exact Or.inl hbarrier
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))
    · have hubNeg := hqNeg ub (q.fst_mem_support_of_mem_edges hubvQ)
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      have hubReach := hfirstN.trans qGood.reachable
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ub, vb, hubReach,
        hubNeg, hubv, haEdges _ (hqA _ hubvQ), hbad,
        rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          L.boundary hfaith hubReach hubv hbad⟩)))
  · rcases rlc_goodBoundary_prefix_or_first_bad q with
      ⟨qGood, _hqGood⟩ |
        ⟨ub, vb, qGood, hubv, hubvQ, hbad, _hqGood⟩
    · have huNeg := hqNeg u q.end_mem_support
      by_cases hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1
      · have hcarrier := rlc_reflected_axisCrossing_carrier_of_between
          gamma gamma' hfaith huv.1 hreflected (by
            have hlower := L.boundary.height_lower
            omega) hkUpper
        have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
        have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
          rw [Sym2.eq_iff] at hreflected
          rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
          · exact hv
          · have h0 := congrArg (fun z : Site 2 => z 0) hu
            have h0' : (rlc_dualReflect u) 0 = 0 := by
              simpa only [Matrix.cons_val_zero] using h0
            omega
        have hfirstN := L.negativeAnchor_reachable hfaith hN
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, k,
          hfirstN.trans (qGood.reachable.trans huvGood.reachable),
          hvEq, hkHigh, hkUpper⟩)))
      · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
            hfaith qGood hN huNeg huv hreflected (Or.inr (by omega)) with
          hbarrier | hleft | hright
        · exact Or.inl hbarrier
        · exact Or.inr (Or.inl hleft)
        · exact Or.inr (Or.inr (Or.inl hright))
    · have hubNeg := hqNeg ub (q.fst_mem_support_of_mem_edges hubvQ)
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      have hubReach := hfirstN.trans qGood.reachable
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ub, vb, hubReach,
        hubNeg, hubv, haEdges _ (hqA _ hubvQ), hbad,
        rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          L.boundary hfaith hubReach hubv hbad⟩)))




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachableBarrier_contact_or_higherAxis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (x : Site 2) (k : Int),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1 := by
  rcases L.complementary_first_axis_crossing_reachable_or_negativeBad
      hfaith with hbarrier | hleft | hright | hhigher |
        ⟨u, v, hu, huNeg, huv, _huvContour, hbad, _huClass⟩
  · exact Or.inl hbarrier
  · exact Or.inr (Or.inl hleft)
  · exact Or.inr (Or.inr (Or.inl hright))
  · exact Or.inr (Or.inr (Or.inr hhigher))
  · rcases L.negativeBadExit_reachable_left_or_barrier
        hfaith hno hu huNeg huv hbad with hleft | hbarrier
    · exact Or.inr (Or.inl hleft)
    · exact Or.inl hbarrier




theorem rlc_goodBoundary_walk_barrier_before_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u v : Site 2}
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A B.firstFace)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk B.firstFace u)
    (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    ∃ z ∈ (pA.append q).support,
      rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  have hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u := q.reachable
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · refine ⟨u, ?_, rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
      B hfaith hu huv hbad huInterior⟩
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr q.end_mem_support
  · have huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n := by
      push Not at huInterior
      omega
    exact rlc_goodBoundary_walk_to_boxBoundary_meets_barrier
      B hfaith (pA.append q) hAzero huBoundary





theorem rlc_goodBoundary_barrier_hit_before_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    ∃ u : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace u ∧
        rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨u, v, hu, huv, hbad, _hv⟩ :=
    rlc_goodBoundary_first_bad_toward B hz hzNot
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · exact ⟨u, hu,
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        B hfaith hu huv hbad huInterior⟩
  · have huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n := by
      push Not at huInterior
      omega
    exact rlc_goodBoundary_barrier_hit_before_boxBoundary
      B hfaith hu huBoundary




def RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2),
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj
        B.firstFace B.secondFace ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x B.firstFace ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        B.firstFace y ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1





def RlcCentralFaceFilledBoundaryGoodComponentContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y : Site 2,
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x y ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1





def RlcCentralFaceFilledBoundaryBadCarrierSeparation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v y



theorem rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcontacts : RlcCentralFaceFilledBoundaryContacts gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ := hcontacts
  by_cases hxy : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x y
  · exact Or.inl ⟨x, y, hxy, hxPath, hyPath⟩
  · right
    obtain ⟨w⟩ := rlc_connectorCentralFaceFilledFaceBoundary_reachable
      gamma gamma' rho hxSupport hySupport
    rcases rlc_goodBoundary_prefix_or_first_bad
        (gamma := gamma) (gamma' := gamma') (rho := rho) w with
      ⟨q, _hqEdges⟩ | ⟨u, v, q, huv, _huvEdge, hbad, _hqEdges⟩
    · exact False.elim (hxy q.reachable)
    · refine ⟨x, y, u, v, hxPath, hyPath, q.reachable, huv, hbad, ?_⟩
      exact rlc_connectorCentralFaceFilledFaceBoundary_reachable
        gamma gamma' rho huv.mem_support_right hySupport



theorem rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
  exact rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts
    gamma gamma' rho
      (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
        gamma gamma' hfaith rho hno)






def RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v y ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
        (0 < (rlc_dualReflect u) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n))



theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparation
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparation
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy⟩ := hsep
  have hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hxPath]
  have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma.1 hxPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hxBox hxu
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hxBarrier hxBox hxu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad,
        hvy, Or.inl huRight⟩
    · exact Or.inl ⟨x, u, hxu, hxPath, huLeft⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad,
        hvy, Or.inr (Or.inl huFlipLeft)⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad,
        hvy, Or.inr (Or.inr (Or.inl huFlipRight))⟩
  · right
    refine ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
      Or.inr (Or.inr (Or.inr ?_))⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
    rw [mem_rect] at huBox
    push Not at huInterior
    omega



theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparation
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_classifiedBadCarrierSeparation
      gamma gamma' rho hsep




def RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        y u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v x

theorem rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcontacts : RlcCentralFaceFilledBoundaryContacts gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ := hcontacts
  by_cases hyx : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable y x
  · exact Or.inl ⟨x, y, hyx.symm, hxPath, hyPath⟩
  · right
    obtain ⟨w⟩ := rlc_connectorCentralFaceFilledFaceBoundary_reachable
      gamma gamma' rho hySupport hxSupport
    rcases rlc_goodBoundary_prefix_or_first_bad
        (gamma := gamma) (gamma' := gamma') (rho := rho) w with
      ⟨q, _hqEdges⟩ | ⟨u, v, q, huv, _huvEdge, hbad, _hqEdges⟩
    · exact False.elim (hyx q.reachable)
    · refine ⟨x, y, u, v, hxPath, hyPath, q.reachable, huv, hbad, ?_⟩
      exact rlc_connectorCentralFaceFilledFaceBoundary_reachable
        gamma gamma' rho huv.mem_support_right hxSupport


def RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        y u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v x ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨
        (0 < (rlc_dualReflect u) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n))

theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx⟩ := hsep
  have hyBarrier : rlc_dualReflect y ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hyPath]
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma'.1 hyPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hyBox hyu
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hyBarrier hyBox hyu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inl huLeft⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inr (Or.inl huFlipLeft)⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inr (Or.inr (Or.inl huFlipRight))⟩
  · right
    refine ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
      Or.inr (Or.inr (Or.inr ?_))⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
    rw [mem_rect] at huBox
    push Not at huInterior
    omega



theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts
        gamma gamma' rho
          (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
            gamma gamma' hfaith rho hno) with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft
      gamma gamma' rho hsep




def RlcCentralFaceBadExitAllIncomingWall {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u v : Site 2) : Prop :=
  ∀ a : Site 2,
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u →
      a ≠ v →
      s(rlc_dualReflect a, rlc_dualReflect u) ∈
        rlc_connectorFourTraceEdges gamma gamma'

theorem rlc_badExit_exists_incomingWall_of_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x u v : Site 2}
    (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (hxuNe : x ≠ u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨p⟩ := hxu.symm
  cases p with
  | nil => exact False.elim (hxuNe rfl)
  | @cons a b c hab p =>
      have hba := hab.symm
      have hbNe : b ≠ v := by
        intro hbv
        subst b
        exact hbad hab.2
      exact ⟨b, hba, hbNe, hwall b hba hbNe⟩



theorem rlc_rightBased_negative_badExit_incoming_reflectedRight
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho)
    {x u v : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 := by
  have hxuNe : x ≠ u := by
    intro hxuEq
    subst u
    have hxRect := rlc_pathVertex_mem_rect gamma.1 hxPath
    rw [mem_rect] at hxRect
    omega
  obtain ⟨a, hau, hav, hauWall⟩ :=
    rlc_badExit_exists_incomingWall_of_reachable hxu hxuNe hbad hwall
  have huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma.1 hu
    rw [mem_rect] at huRect
    omega
  have huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    exact hnoGood ⟨x, u, hxu, hxPath, hu⟩
  have huFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX w := by
    rintro ⟨w, hw, huw⟩
    have hwRect := rlc_pathVertex_mem_rect gamma'.1 hw
    rw [mem_rect] at hwRect
    have huw0 := congrArg (fun z : Site 2 => z 0) huw
    have huNeg' := huNeg
    simp [rlc_dualReflect, rlc_dualReflectFun] at huNeg'
    simp [rlc_flipX, rlc_flipXFun] at huw0
    omega
  refine ⟨a, hau, hav, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    gamma gamma' hauWall (Sym2.mem_mk_right _ _)
      huRight huLeft huFlipLeft



theorem rlc_leftBased_positive_badExit_incoming_reflectedLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho)
    {y u v : Site 2}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable y u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  have hyuNe : y ≠ u := by
    intro hyuEq
    subst u
    have hyRect := rlc_pathVertex_mem_rect gamma'.1 hyPath
    rw [mem_rect] at hyRect
    omega
  obtain ⟨a, hau, hav, hauWall⟩ :=
    rlc_badExit_exists_incomingWall_of_reachable hyu hyuNe hbad hwall
  have huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    exact hnoGood ⟨u, y, hyu.symm, hu, hyPath⟩
  have huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX w := by
    rintro ⟨w, hw, huw⟩
    have hwRect := rlc_pathVertex_mem_rect gamma.1 hw
    rw [mem_rect] at hwRect
    have huw0 := congrArg (fun z : Site 2 => z 0) huw
    have huPos' := huPos
    simp [rlc_dualReflect, rlc_dualReflectFun] at huPos'
    simp [rlc_flipX, rlc_flipXFun] at huw0
    omega
  refine ⟨a, hau, hav, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hauWall (Sym2.mem_mk_right _ _)
      huRight huLeft huFlipRight




def RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v y ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
        (0 < (rlc_dualReflect u) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n) ∨
        RlcCentralFaceBadExitAllIncomingWall gamma gamma' rho u v)

theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparation
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy⟩ := hsep
  have hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hxPath]
  have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma.1 hxPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hxBox hxu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
      Or.inr (Or.inr (Or.inl huBoundary))⟩
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hxBarrier hxBox hxu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
        Or.inl huRight⟩
    · exact Or.inl ⟨x, u, hxu, hxPath, huLeft⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
        Or.inr (Or.inl huFlipLeft)⟩
    · by_cases hwall : RlcCentralFaceBadExitAllIncomingWall
          gamma gamma' rho u v
      · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
          Or.inr (Or.inr (Or.inr hwall))⟩
      · simp only [RlcCentralFaceBadExitAllIncomingWall, not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huLeft := rlc_negativeBarrier_bad_exit_forces_left_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall
            huFlipRight.1 huBarrier huInterior hbad
        exact Or.inl ⟨x, u, hxu, hxPath, huLeft⟩



def RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        y u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v x ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨
        ((rlc_dualReflect u) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n) ∨
        RlcCentralFaceBadExitAllIncomingWall gamma gamma' rho u v)

theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx⟩ := hsep
  have hyBarrier : rlc_dualReflect y ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hyPath]
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma'.1 hyPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hyBox hyu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
      Or.inr (Or.inr (Or.inl huBoundary))⟩
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hyBarrier hyBox hyu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
        Or.inl huLeft⟩
    · by_cases hwall : RlcCentralFaceBadExitAllIncomingWall
          gamma gamma' rho u v
      · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
          Or.inr (Or.inr (Or.inr hwall))⟩
      · simp only [RlcCentralFaceBadExitAllIncomingWall, not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huRight := rlc_positiveBarrier_bad_exit_forces_right_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall
            huFlipLeft.1 huBarrier huInterior hbad
        exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
        Or.inr (Or.inl huFlipRight)⟩



theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_reducedBadCarrierSeparation
      gamma gamma' rho hno hsep


theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts
        gamma gamma' rho
          (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
            gamma gamma' hfaith rho hno) with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft
      gamma gamma' rho hno hsep



theorem rlc_goodComponentContacts_or_twoSidedReducedBadCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      (RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
          gamma gamma' rho ∧
        RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
          gamma gamma' rho) := by
  rcases
      rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | hright
  · exact Or.inl hgood
  · rcases
        rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure
          gamma gamma' hfaith rho hno with hgood | hleft
    · exact Or.inl hgood
    · exact Or.inr ⟨hright, hleft⟩




def RlcCentralFaceLowestAnchorOrderedBadExitAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (x y z : Site 2)
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace z)
    (u v : Site 2)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u),
    x ∈ L.boundary.contour.support ∧
      y ∈ L.boundary.contour.support ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (z = x ∨ z = y) ∧
      (∀ e ∈ p.edges, e ∈ L.boundary.contour.edges) ∧
      (∀ e ∈ q.edges, e ∈ p.edges) ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      s(u, v) ∈ p.edges ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
        (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n)

def RlcCentralFaceLowestAnchorOrderedBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L




theorem rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorOrderedBadExit gamma gamma' rho := by
  classical
  let L := Classical.choice
    (rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  let B := L.boundary
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupport
  obtain ⟨y', hyy'⟩ := hySupport
  have hxe : s(x, x') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hxx')
  have hye : s(y, y') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hyy')
  have hx : x ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hxe
  have hy : y ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hye
  let px := B.contour.takeUntil x hx
  let py := B.contour.takeUntil y hy
  rcases rlc_goodBoundary_prefix_or_first_bad px with
      ⟨qx, hqx⟩ | ⟨ux, vx, qx, huvx, huvxEdge, hbadx, hqx⟩
  · rcases rlc_goodBoundary_prefix_or_first_bad py with
        ⟨qy, hqy⟩ | ⟨uy, vy, qy, huvy, huvyEdge, hbady, hqy⟩
    · left
      exact ⟨x, y, qx.reachable.symm.trans qy.reachable, hxPath, hyPath⟩
    · right
      refine ⟨L, x, y, y, py, uy, vy, qy, hx, hy, hxPath, hyPath,
        Or.inr rfl, ?_, hqy, huvy, huvyEdge, hbady, ?_⟩
      · exact B.contour.edges_takeUntil_subset hy
      · exact rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          B hfaith qy.reachable huvy hbady
  · right
    refine ⟨L, x, y, x, px, ux, vx, qx, hx, hy, hxPath, hyPath,
      Or.inl rfl, ?_, hqx, huvx, huvxEdge, hbadx, ?_⟩
    · exact B.contour.edges_takeUntil_subset hx
    · exact rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
        B hfaith qx.reachable huvx hbadx

def RlcCentralFaceLowestAnchorComplementaryCrossingBelow {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace)
    (f g : Site 2) (k : Int),
    s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
      (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
      s(f, g) ∈ a.edges ∧
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) ∧
      k ≤ (gamma.1.1 : Site 2) 1

def RlcCentralFaceLowestAnchorComplementaryCrossingAbove {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace)
    (f g : Site 2) (k : Int),
    s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
      (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
      s(f, g) ∈ a.edges ∧
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) ∧
      L.boundary.height + 1 < k

def RlcCentralFaceLowestAnchorLowerOrderBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L ∧
      RlcCentralFaceLowestAnchorComplementaryCrossingBelow
        gamma gamma' rho L

def RlcCentralFaceLowestAnchorUpperOrderBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L ∧
      RlcCentralFaceLowestAnchorComplementaryCrossingAbove
        gamma gamma' rho L





theorem rlc_goodComponentContacts_or_lowestAnchor_lower_or_upper_orderBadExit_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorLowerOrderBadExit gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorUpperOrderBadExit gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | ⟨L, hbad⟩
  · exact Or.inl hgood
  · obtain ⟨a, f, g, k, ha, haEdges, hfg, hreflected, hk | hk⟩ :=
      L.complementary_axis_crossing_extreme
    · exact Or.inr (Or.inl ⟨L, hbad,
        a, f, g, k, ha, haEdges, hfg, hreflected, hk⟩)
    · exact Or.inr (Or.inr ⟨L, hbad,
        a, f, g, k, ha, haEdges, hfg, hreflected, hk⟩)

theorem rlc_goodComponentContacts_of_anchoredGoodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
  obtain ⟨_B, x, y, _hanchor, hx, hy, hxPath, hyPath⟩ := hcomponent
  exact ⟨x, y, hx.trans hy, hxPath, hyPath⟩






theorem rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho ∨
      ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
        (z : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            B.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  by_cases hx : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace x
  · by_cases hy : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace y
    · left
      exact ⟨B, x, y, B.anchor_mem_goodBoundaryGraph hfaith,
        hx.symm, hy, hxPath, hyPath⟩
    · right
      obtain ⟨z, hz, hzBarrier⟩ :=
        rlc_goodBoundary_barrier_hit_before_first_bad
          B hfaith hySupport hy
      exact ⟨B, z, hz, hzBarrier⟩
  · right
    obtain ⟨z, hz, hzBarrier⟩ :=
      rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hxSupport hx
    exact ⟨B, z, hz, hzBarrier⟩





theorem rlc_anchoredGoodComponentContacts_or_reachableClassifiedBarrier_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho ∨
      ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
        (z : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            B.firstFace z ∧
          (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨
            rlc_dualReflect z ∈ rlc_pathVertices gamma'.1 ∨
            (0 < (rlc_dualReflect z) 0 ∧
              ∃ w ∈ rlc_pathVertices gamma'.1,
                rlc_dualReflect z = rlc_flipX w) ∨
            ((rlc_dualReflect z) 0 < 0 ∧
              ∃ w ∈ rlc_pathVertices gamma.1,
                rlc_dualReflect z = rlc_flipX w)) := by
  rcases
      rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure
        gamma gamma' hfaith rho hno with hcontacts | ⟨B, z, hz, hzBarrier⟩
  · exact Or.inl hcontacts
  · exact Or.inr ⟨B, z, hz,
      rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' hzBarrier⟩





theorem rlc_anchorToFaithfulContacts_reachable_or_barrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        ((rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Reachable B.firstFace x ∨
          ∃ z : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace z ∧
              rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∧
        ((rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Reachable B.firstFace y ∨
          ∃ z : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace z ∧
              rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  refine ⟨B, x, y, hxPath, hyPath, ?_, ?_⟩
  · by_cases hx : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace x
    · exact Or.inl hx
    · exact Or.inr (rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hxSupport hx)
  · by_cases hy : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace y
    · exact Or.inl hy
    · exact Or.inr (rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hySupport hy)





def RlcCentralFaceFilledBoundaryAnchoredGeometricSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2) (hx : x ∈ B.contour.support)
    (hy : y ∈ B.contour.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ((B.firstFace ∈
            (rlc_orderedContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈ (rlc_orderedContourArc B.contour hx hy).edges →
              RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) ∨
        (B.firstFace ∈
            (rlc_complementaryContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈
                (rlc_complementaryContourArc B.contour hx hy).edges →
              RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g))

theorem rlc_anchoredSupportedSide_of_anchoredGeometricSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgeom :
      RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, hside⟩ := hgeom
  refine ⟨B, x, y, hx, hy, hxPath, hyPath, ?_⟩
  rcases hside with hordered | hcomplementary
  · left
    refine ⟨hordered.1, ?_⟩
    intro f g hfg
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma'
        ((rlc_orderedContourArc B.contour hx hy).adj_of_mem_edges hfg).1).1
        (hordered.2 hfg)
  · right
    refine ⟨hcomplementary.1, ?_⟩
    intro f g hfg
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma'
        ((rlc_complementaryContourArc B.contour hx hy).adj_of_mem_edges hfg).1).1
        (hcomplementary.2 hfg)



def RlcCentralFaceFilledBoundaryContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_connectorCentralFacePlanarEdges gamma gamma'

theorem rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨_B, x, y, _hanchor, hx, hy, hxPath, hyPath⟩ := hcomponent
  obtain ⟨px⟩ := hx
  obtain ⟨py⟩ := hy
  let pGood := px.append py
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  let p := pGood.mapLe hle
  refine ⟨x, y, p, hxPath, hyPath, ?_⟩
  intro f g hfg
  have hfgGood : s(f, g) ∈ pGood.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
  have hgood := (pGood.adj_of_mem_edges hfgGood).2
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' (pGood.adj_of_mem_edges hfgGood).1.1).1 hgood



theorem rlc_filledBoundaryContactSegment_of_goodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨x, y, hxy, hxPath, hyPath⟩ := hcomponent
  obtain ⟨pGood⟩ := hxy
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  let p := pGood.mapLe hle
  refine ⟨x, y, p, hxPath, hyPath, ?_⟩
  intro f g hfg
  have hfgGood : s(f, g) ∈ pGood.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
  have hgood := (pGood.adj_of_mem_edges hfgGood).2
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' (pGood.adj_of_mem_edges hfgGood).1.1).1 hgood

theorem rlc_filledBoundaryContactSegment_of_anchoredSupportedSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hside :
      RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, hside⟩ := hside
  rcases hside with hordered | hcomplementary
  · exact ⟨x, y, rlc_orderedContourArc B.contour hx hy,
      hxPath, hyPath, hordered.2⟩
  · exact ⟨x, y, rlc_complementaryContourArc B.contour hx hy,
      hxPath, hyPath, hcomplementary.2⟩



theorem rlc_boundaryContactArc_of_filledBoundaryContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsegment :
      RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
    RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
  obtain ⟨x, y, p, hxPath, hyPath, hpTarget⟩ := hsegment
  let hfill :=
    rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' rho
  let a := p.mapLe hfill
  refine ⟨x, y, a, hxPath, hyPath, ?_⟩
  dsimp only
  let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
  let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
  intro e he
  have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
      (a.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgA : s(f, g) ∈ a.edges := by
        rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
      have hfgP : s(f, g) ∈ p.edges := by
        dsimp only [a] at hfgA
        rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at hfgA
      change s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma'
      exact hpTarget hfgP


theorem rlc_centralFacePIMS_success_of_filledBoundaryContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsegment :
      RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_boundaryContactArc gamma gamma' rho
    (rlc_boundaryContactArc_of_filledBoundaryContactSegment
      gamma gamma' rho hsegment)




theorem rlc_centralFacePIMS_success_of_anchoredGoodComponentContacts
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts
        gamma gamma' rho hcomponent)



theorem rlc_centralFacePIMS_success_of_goodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_goodComponentContacts
        gamma gamma' rho hcomponent)


theorem rlc_centralFacePIMS_success_of_anchoredGeometricSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgeom :
      RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  apply rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
  apply rlc_filledBoundaryContactSegment_of_anchoredSupportedSide
  exact rlc_anchoredSupportedSide_of_anchoredGeometricSide
    gamma gamma' rho hgeom




def RlcCentralFaceNegativeBadExitResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u v : Site 2) : Prop :=
  ((rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) ∨
    ∃ w ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX w ∧
        ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'



def RlcCentralFacePositiveBadExitResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u v : Site 2) : Prop :=
  ((rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) ∨
    ∃ w ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX w ∧
        ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_exactResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨
      RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v' := by
  have huReach := q.reachable
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno huReach huNeg huv hbad with
    hleft | hnegativeBoundary | hnegativeWall
  · rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with
      hright | hpositiveBoundary | hpositiveWall
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · exact Or.inr (Or.inr (Or.inl hpositiveBoundary))
    · exact Or.inr (Or.inr (Or.inr hpositiveWall))
  · exact Or.inr (Or.inl (Or.inl hnegativeBoundary))
  · exact Or.inr (Or.inl (Or.inr hnegativeWall))






theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_reachableBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  have huReach := q.reachable
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  rcases L.negativeBadExit_reachable_left_or_barrier
      hfaith hno huReach huNeg huv hbad with hleft | hbarrier
  · rcases L.positiveBadExit_reachable_right_or_barrier
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with hright | hbarrier
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · exact Or.inr hbarrier
  · exact Or.inr hbarrier






theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_reachableBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        ∃ z : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable L.boundary.firstFace z ∧
            rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact L.twoSignedBadExits_PIMS_or_reachableBarrier
      hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_exactResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨
        RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact L.twoSignedBadExits_PIMS_or_exactResidue
      hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos


noncomputable def rlc_bookFlippedTraceIntersectionSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  (rlc_pathVertices gamma.1).filter fun z =>
    rlc_flipX z ∈ rlc_pathVertices gamma'.1

theorem rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (rlc_bookFlippedTraceIntersectionSet gamma gamma').Nonempty := by
  obtain ⟨z, hzRight, hzLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  exact ⟨z, by
    simp [rlc_bookFlippedTraceIntersectionSet, hzRight, hzLeft]⟩


noncomputable def rlc_bookFlippedTraceIntersectionRank {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma')) : Nat := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hzRight : z.1 ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp z.2).1
  have hzW : z.1 ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z.1).2
      hzRight
  exact (W.takeUntil z.1 hzW).length

theorem rlc_exists_first_bookFlippedTraceIntersection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
      ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
        rlc_bookFlippedTraceIntersectionRank gamma gamma' z ≤
          rlc_bookFlippedTraceIntersectionRank gamma gamma' q := by
  classical
  have hne := rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful
    gamma gamma' hfaith
  letI : Nonempty ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma')).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'))
    (rlc_bookFlippedTraceIntersectionRank gamma gamma') huniv
  exact ⟨z, fun q => hmin q (by simp)⟩




theorem rlc_bookFirstFlippedTraceIntersection_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    let W := rlc_ambientCrossingWalk gamma.1
    ∃ (z : Site 2) (hzW : z ∈ W.support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        (∀ q ∈ (W.takeUntil z hzW).support,
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 → q = z) ∧
        ∀ q (hqW : q ∈ W.support),
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 →
            (W.takeUntil z hzW).length ≤
              (W.takeUntil q hqW).length := by
  classical
  let W := rlc_ambientCrossingWalk gamma.1
  obtain ⟨zs, hmin⟩ :=
    rlc_exists_first_bookFlippedTraceIntersection gamma gamma' hfaith
  have hzMem := Finset.mem_filter.mp zs.2
  have hzRight : zs.1 ∈ rlc_pathVertices gamma.1 := hzMem.1
  have hzLeft : rlc_flipX zs.1 ∈ rlc_pathVertices gamma'.1 := hzMem.2
  have hzW : zs.1 ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 zs.1).2
      hzRight
  refine ⟨zs.1, hzW, hzRight, hzLeft, ?_, ?_⟩
  · intro q hqPrefix hqLeft
    by_contra hqz
    have hqW : q ∈ W.support :=
      W.support_takeUntil_subset_support hzW hqPrefix
    have hqRight : q ∈ rlc_pathVertices gamma.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hqW
    have hqSet : q ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
      simp [rlc_bookFlippedTraceIntersectionSet, hqRight, hqLeft]
    let qs : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
      ⟨q, hqSet⟩
    have hlen : (W.takeUntil q hqW).length <
        (W.takeUntil zs.1 hzW).length := by
      have h := (W.takeUntil zs.1 hzW).length_takeUntil_lt
        hqPrefix hqz
      rwa [W.takeUntil_takeUntil hzW hqPrefix] at h
    have hrankLt : rlc_bookFlippedTraceIntersectionRank gamma gamma' qs <
        rlc_bookFlippedTraceIntersectionRank gamma gamma' zs := by
      simpa [rlc_bookFlippedTraceIntersectionRank, W] using hlen
    exact (not_lt_of_ge (hmin qs)) hrankLt
  · intro q hqW hqLeft
    have hqRight : q ∈ rlc_pathVertices gamma.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hqW
    have hqSet : q ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
      simp [rlc_bookFlippedTraceIntersectionSet, hqRight, hqLeft]
    let qs : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
      ⟨q, hqSet⟩
    simpa [rlc_bookFlippedTraceIntersectionRank, W] using hmin qs


theorem rlc_ambientCrossingWalk_isPath
    {a b c d : Int} (tau : RlcCrossingPath a b c d) :
    (rlc_ambientCrossingWalk tau).IsPath := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  let p : ((hypercubicLattice 2).induce (rect a b c d)).Walk _ _ :=
    tau.2.2.1
  change (p.map hom).IsPath
  apply p.map_isPath_of_injective
  · intro x y hxy
    exact Subtype.ext (by simpa [hom] using hxy)
  · exact (tau.2.2).2



theorem rlc_isPath_start_not_mem_tail {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnodup := hp.support_nodup
  rw [← SimpleGraph.Walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1



theorem rlc_append_isPath_of_endpoint_intersection
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  refine List.Nodup.append hp.support_nodup
    ((List.tail_sublist _).nodup hq.support_nodup) ?_
  rw [List.disjoint_left]
  intro x hxp hxqTail
  have hxq : x ∈ q.support := List.tail_subset _ hxqTail
  have hxv := hinter x hxp hxq
  subst x
  exact rlc_isPath_start_not_mem_tail hq hxqTail



theorem rlc_append_isCycle_of_endpoint_intersection
    {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support →
      x = u ∨ x = v)
    (hedges : p.edges.Disjoint q.edges) :
    (p.append q).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def,
      SimpleGraph.Walk.edges_append]
    exact List.Nodup.append hp.edges_nodup hq.edges_nodup hedges
  · intro hnil
    have hlen : p.length + q.length = 0 := by
      rw [← SimpleGraph.Walk.length_append, hnil]
      rfl
    exact huv (SimpleGraph.Walk.eq_of_length_eq_zero
      (Nat.eq_zero_of_add_eq_zero_right hlen))
  · rw [SimpleGraph.Walk.tail_support_append]
    refine List.Nodup.append
      ((List.tail_sublist _).nodup hp.support_nodup)
      ((List.tail_sublist _).nodup hq.support_nodup) ?_
    rw [List.disjoint_left]
    intro x hxpTail hxqTail
    have hxp : x ∈ p.support := List.tail_subset _ hxpTail
    have hxq : x ∈ q.support := List.tail_subset _ hxqTail
    rcases hinter x hxp hxq with rfl | rfl
    · exact rlc_isPath_start_not_mem_tail hp hxpTail
    · exact rlc_isPath_start_not_mem_tail hq hxqTail

private theorem rlc_cfct_vertexLoop_edges_mem_cycleFaceCut
    {a : Site 2} (c : (hypercubicLattice 2).Walk a a)
    (x : Site 2) (hx : x ∉ c.support) :
    ∀ e ∈ (jwc_vertexLoop (x 0) (x 1)).edges,
      e ∈ (whb_faceRegion c.toSubgraph.spanningCoe).edgeSet := by
  intro e he
  simp only [jwc_vertexLoop, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  have noCycleEdge {u v : Site 2} (huv : s(u, v) ∈ c.edges)
      (hxu : x = u ∨ x = v) : False := by
    rcases hxu with rfl | rfl
    · exact hx (c.fst_mem_support_of_mem_edges huv)
    · exact hx (c.snd_mem_support_of_mem_edges huv)
  rcases he with rfl | rfl | rfl | rfl
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_NE_NW _ _, ?_⟩
    rw [jwc_shared_NE_NW]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inl (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_NW_SW _ _, ?_⟩
    rw [jwc_shared_NW_SW]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inr (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_SW_SE _ _, ?_⟩
    rw [jwc_shared_SW_SE]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inr (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_SE_NE _ _, ?_⟩
    rw [jwc_shared_SE_NE]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inl (cons_eq_site rfl rfl).symm)



private theorem rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
    {a x y z h k : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxz : (hypercubicLattice 2).Adj x z)
    (hxoff : x ∉ c.support)
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x z) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable h k := by
  let loop := jwc_vertexLoop (x 0) (x 1)
  let cutLoop := loop.transfer
    (whb_faceRegion c.toSubgraph.spanningCoe)
      (rlc_cfct_vertexLoop_edges_mem_cycleFaceCut c x hxoff)
  have hhLoop : h ∈ loop.support :=
    rlc_flank_mem_vertexLoop_support hxy hh
  have hkLoop : k ∈ loop.support :=
    rlc_flank_mem_vertexLoop_support hxz hk
  have hhCut : h ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hhLoop
  have hkCut : k ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hkLoop
  exact ⟨rlc_centralFaceContactSubwalk cutLoop hhCut hkCut⟩



private theorem rlc_cfct_cycleFaceCut_reachable_flanks_of_not_cycleEdge
    {a x y h k : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hnot : s(x, y) ∉ c.edges)
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x y) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable h k := by
  obtain ⟨f, g, hflank, hfg⟩ := flankFaces_latAdj hxy
  have hshared : sharedPrimalEdge f g = s(x, y) := by
    calc
      sharedPrimalEdge f g = symPrimal f g :=
        (symPrimal_eq_shared hfg).symm
      _ = symPrimalSym s(f, g) := rfl
      _ = symPrimalSym (flankFaces x y) :=
        congrArg symPrimalSym hflank.symm
      _ = s(x, y) := symPrimalSym_flankFaces hxy
  have hfgCut : (whb_faceRegion c.toSubgraph.spanningCoe).Adj f g := by
    rw [whb_faceRegion_adj]
    refine ⟨hfg, ?_⟩
    rw [hshared]
    simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] using hnot
  rw [hflank, Sym2.mem_iff] at hh hk
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
  · exact Reachable.refl _
  · exact hfgCut.reachable
  · exact hfgCut.symm.reachable
  · exact Reachable.refl _




private theorem rlc_cfct_cycleFaceCut_pathFlanks_reachable
    {a s t : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (p : (hypercubicLattice 2).Walk s t)
    (hp : p.IsPath)
    (hoff : ∀ x ∈ p.support, x ≠ t → x ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges)
    {f g : Site 2}
    (hf : ∃ x y : Site 2, s(x, y) ∈ p.edges ∧ f ∈ flankFaces x y)
    (hg : ∃ x y : Site 2, s(x, y) ∈ p.edges ∧ g ∈ flankFaces x y) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable f g := by
  induction p generalizing f g with
  | nil =>
      obtain ⟨x, y, hxy, _hf⟩ := hf
      simp at hxy
  | @cons u v w huv q ih =>
      have hqPath : q.IsPath := hp.of_cons
      have hqOff : ∀ x ∈ q.support, x ≠ w → x ∉ c.support := by
        intro x hx hxw
        apply hoff x
        · simp [SimpleGraph.Walk.support_cons, hx]
        · exact hxw
      have hqEdges : ∀ e ∈ q.edges, e ∉ c.edges := by
        intro e he
        exact hedges e (by simp [he])
      obtain ⟨xf, yf, hef, hff⟩ := hf
      obtain ⟨xg, yg, heg, hgg⟩ := hg
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hef heg
      have firstFlank {x y z : Site 2}
          (heq : s(x, y) = s(u, v)) (hz : z ∈ flankFaces x y) :
          z ∈ flankFaces u v := by
        have hm : flankFaces x y = flankFaces u v := by
          change flankFacesSym s(x, y) = flankFacesSym s(u, v)
          rw [heq]
        rwa [← hm]
      rcases hef with hef | hef <;> rcases heg with heg | heg
      · have hfFirst := firstFlank hef hff
        have hgFirst := firstFlank heg hgg
        apply rlc_cfct_cycleFaceCut_reachable_flanks_of_not_cycleEdge
          c huv (hedges _ (by simp)) hfFirst hgFirst
      · have hfFirst := firstFlank hef hff
        have hgTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ g ∈ flankFaces x y :=
          ⟨xg, yg, heg, hgg⟩
        have hqNotNil : ¬ q.Nil := by
          intro hnil
          have hqEdgesNil : q.edges = [] := by
            simpa [hnil.eq]
          have : s(xg, yg) ∈ ([] : List (Sym2 (Site 2))) :=
            hqEdgesNil ▸ heg
          simp at this
        have hvw : v ≠ w := by
          intro hvw
          apply rlc_isPath_start_not_mem_tail hqPath
          simpa [hvw] using q.end_mem_tail_support hqNotNil
        have hvOff : v ∉ c.support :=
          hoff v (by simp [SimpleGraph.Walk.support_cons]) hvw
        obtain ⟨k, l, hklFlank, hkl⟩ :=
          flankFaces_latAdj (q.adj_snd hqNotNil)
        have hk : k ∈ flankFaces v q.snd := by
          rw [hklFlank]
          exact Sym2.mem_mk_left _ _
        have hlocal :=
          rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
            c huv.symm (q.adj_snd hqNotNil) hvOff
              (by simpa [flankFaces_comm] using hfFirst) hk
        have hkTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ k ∈ flankFaces x y :=
          ⟨v, q.snd, q.mk_start_snd_mem_edges hqNotNil, hk⟩
        exact hlocal.trans (ih hqPath hqOff hqEdges hkTail hgTail)
      · have hgFirst := firstFlank heg hgg
        have hfTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ f ∈ flankFaces x y :=
          ⟨xf, yf, hef, hff⟩
        have hqNotNil : ¬ q.Nil := by
          intro hnil
          have hqEdgesNil : q.edges = [] := by
            simpa [hnil.eq]
          have : s(xf, yf) ∈ ([] : List (Sym2 (Site 2))) :=
            hqEdgesNil ▸ hef
          simp at this
        have hvw : v ≠ w := by
          intro hvw
          apply rlc_isPath_start_not_mem_tail hqPath
          simpa [hvw] using q.end_mem_tail_support hqNotNil
        have hvOff : v ∉ c.support :=
          hoff v (by simp [SimpleGraph.Walk.support_cons]) hvw
        obtain ⟨k, l, hklFlank, hkl⟩ :=
          flankFaces_latAdj (q.adj_snd hqNotNil)
        have hk : k ∈ flankFaces v q.snd := by
          rw [hklFlank]
          exact Sym2.mem_mk_left _ _
        have hlocal :=
          rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
            c huv.symm (q.adj_snd hqNotNil) hvOff
              (by simpa [flankFaces_comm] using hgFirst) hk
        have hkTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ k ∈ flankFaces x y :=
          ⟨v, q.snd, q.mk_start_snd_mem_edges hqNotNil, hk⟩
        exact (ih hqPath hqOff hqEdges hfTail hkTail).trans hlocal.symm
      · exact ih hqPath hqOff hqEdges
          ⟨xf, yf, hef, hff⟩ ⟨xg, yg, heg, hgg⟩



private theorem rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    {a f g : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hcycle : c.IsCycle)
    (hreach : (whb_faceRegion c.toSubgraph.spanningCoe).Reachable f g) :
    fwr_faceInside c f ↔ fwr_faceInside c g := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w huv q ih =>
      have huvData : (hypercubicLattice 2).Adj u v ∧
          sharedPrimalEdge u v ∉ c.toSubgraph.spanningCoe.edgeSet := by
        rwa [whb_faceRegion_adj] at huv
      have hnot : sharedPrimalEdge u v ∉ c.edges := by
        intro hc
        apply huvData.2
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          c.mem_edges_toSubgraph]
        exact hc
      have hmatch := fwr_faceCutMatch_of_nodup
        c hcycle.edges_nodup huvData.1
      have hsame : fwr_faceInside c u ↔ fwr_faceInside c v := by
        have hnosplit : ¬ (fwr_faceInside c u ↔
            ¬ fwr_faceInside c v) := by
          intro hsplit
          exact hnot (hmatch.mp hsplit)
        tauto
      exact hsame.trans ih



private theorem rlc_cfct_pathFlanks_outside_of_pinnedBoundaryFlank
    {a s t f₀ : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hcycle : c.IsCycle)
    (p : (hypercubicLattice 2).Walk s t)
    (hp : p.IsPath) (hpNotNil : ¬ p.Nil)
    (hoff : ∀ x ∈ p.support, x ≠ t → x ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges)
    (hf₀ : f₀ ∈ flankFaces s p.snd)
    (hf₀Outside : phb_doubleDualEquiv.symm f₀ ∉ jec_leftRegion c) :
    ∀ {x y f : Site 2}, s(x, y) ∈ p.edges →
      f ∈ flankFaces x y →
      phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  intro x y f hxy hf
  have hf₀Witness : ∃ u v : Site 2,
      s(u, v) ∈ p.edges ∧ f₀ ∈ flankFaces u v :=
    ⟨s, p.snd, p.mk_start_snd_mem_edges hpNotNil, hf₀⟩
  have hfWitness : ∃ u v : Site 2,
      s(u, v) ∈ p.edges ∧ f ∈ flankFaces u v :=
    ⟨x, y, hxy, hf⟩
  have hreach := rlc_cfct_cycleFaceCut_pathFlanks_reachable
    c p hp hoff hedges hf₀Witness hfWitness
  have hsame := rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    c hcycle hreach
  have hf₀Face : ¬ fwr_faceInside c f₀ := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using hf₀Outside
  have hfFace : ¬ fwr_faceInside c f := by
    exact fun hfIn => hf₀Face (hsame.mpr hfIn)
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hfFace



private theorem rlc_cfct_rightBoundaryEdge_flank_outside_firstCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {c : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)}
    (hcycle : c.IsCycle)
    (hedges : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {x y f : Site 2}
    (hxRight : x 0 = 2 * n)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxoff : x ∉ c.support)
    (hf : f ∈ flankFaces x y) :
    phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  have hn : 0 ≤ n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs0 := gamma.1.1.2.2
    omega
  let up : Site 2 := ![x 0, x 1 + 1]
  let eastFace : Site 2 := ![x 0, x 1]
  have hxup : (hypercubicLattice 2).Adj x up := by
    simp [up, hypercubicLattice_adj, Fin.sum_univ_two]
  have heastFlank : eastFace ∈ flankFaces x up := by
    simp [eastFace, up, flankFaces]
  have hreach := rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
    c hxup hxy hxoff heastFlank hf
  have hsame := rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    c hcycle hreach
  have hfar : ∀ p ∈ c.support,
      p 0 ≤ (phb_doubleDualEquiv.symm eastFace) 0 - 1 := by
    intro p hp
    have hpBound : p 0 ≤ 2 * n := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hp
      rcases hp with rfl | ⟨e, he, hpe⟩
      · have hs0 := gamma.1.1.2.2
        omega
      · have hpBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' (hedges e he) hpe
        have hpBox := rlc_connectorBarrier_mem_connectorBox
          gamma gamma' hpBarrier
        rw [mem_rect] at hpBox
        exact hpBox.2.1
    simpa [eastFace, phb_doubleDualEquiv, phb_doubleDualShift,
      hxRight] using hpBound
  have heastOutside : phb_doubleDualEquiv.symm eastFace ∉
      jec_leftRegion c := by
    rw [jec_mem_leftRegion, not_not]
    exact jec_ray_even_far c _ hfar
  have heastFace : ¬ fwr_faceInside c eastFace := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using heastOutside
  have hfFace : ¬ fwr_faceInside c f := by
    exact fun hfIn => heastFace (hsame.mpr hfIn)
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hfFace




private theorem rlc_cfct_rightBoundaryTail_flanks_outside_firstCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {c : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)}
    (hcycle : c.IsCycle)
    (hcEdges : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {x z : Site 2} (p : (hypercubicLattice 2).Walk x z)
    (hxRight : x 0 = 2 * n)
    (hp : p.IsPath) (hpNotNil : ¬ p.Nil)
    (hoff : ∀ w ∈ p.support, w ≠ z → w ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges) :
    ∀ {u v f : Site 2}, s(u, v) ∈ p.edges →
      f ∈ flankFaces u v →
      phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  obtain ⟨f₀, g₀, hflank₀, _hfg₀⟩ :=
    flankFaces_latAdj (p.adj_snd hpNotNil)
  have hf₀ : f₀ ∈ flankFaces x p.snd := by
    rw [hflank₀]
    exact Sym2.mem_mk_left _ _
  have hxoff : x ∉ c.support := by
    apply hoff x p.start_mem_support
    intro hxz
    apply rlc_isPath_start_not_mem_tail hp
    simpa [hxz] using p.end_mem_tail_support hpNotNil
  have hf₀Outside := rlc_cfct_rightBoundaryEdge_flank_outside_firstCycle
    gamma gamma' hcycle hcEdges hxRight (p.adj_snd hpNotNil) hxoff hf₀
  intro u v f huv hf
  exact rlc_cfct_pathFlanks_outside_of_pinnedBoundaryFlank
    c hcycle p hp hpNotNil hoff hedges hf₀ hf₀Outside huv hf




theorem rlc_isPath_idxOf_le_of_mem_dropUntil
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z q : V} (W : G.Walk a b) (hW : W.IsPath)
    (hz : z ∈ W.support) (hq : q ∈ (W.dropUntil z hz).support) :
    W.support.idxOf z ≤ W.support.idxOf q := by
  have hidxLt : W.support.idxOf z < W.support.length :=
    List.idxOf_lt_length_of_mem hz
  rw [SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hq
  have hle : W.support.idxOf z ≤ W.length := by
    rw [SimpleGraph.Walk.length_support] at hidxLt
    omega
  rw [Nat.min_eq_left hle, List.mem_drop_iff_getElem] at hq
  obtain ⟨j, hj, hget⟩ := hq
  have hidxQ : W.support.idxOf q = W.support.idxOf z + j := by
    rw [← hget]
    simpa [Nat.add_comm] using hW.support_nodup.idxOf_getElem _ hj
  omega






theorem rlc_bookFirstIntersection_truncatedSides_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (z : Site 2)
      (right : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) z)
      (left : (hypercubicLattice 2).Walk
        (rlc_flipX z) (gamma'.1.2.1 : Site 2))
      (flipLeft : (hypercubicLattice 2).Walk
        z (gamma'.1.2.1 : Site 2))
      (preFlipLeft : (hypercubicLattice 2).Walk
        (rlc_flipX (gamma'.1.1 : Site 2)) z),
        z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        (∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1) ∧
        (∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1) ∧
        (∀ e ∈ flipLeft.edges,
          e ∈ rlc_reflectedPathEdges gamma'.1) ∧
        (∀ x ∈ right.support, x ∈ flipLeft.support → x = z) ∧
        (∀ x : Site 2,
          x ∈ flipLeft.support ↔ rlc_flipX x ∈ left.support) ∧
        (∀ x ∈ flipLeft.support,
          (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
            (rlc_ambientCrossingWalk gamma'.1).support.idxOf
              (rlc_flipX x)) ∧
        (∀ x ∈ preFlipLeft.support,
          x ∈ right.support → x = z) ∧
        (∀ x ∈ preFlipLeft.support,
          x ∈ flipLeft.support → x = z) ∧
        (∀ x ∈ preFlipLeft.support, x ≠ z → 0 < x 0) ∧
        right.IsPath ∧ left.IsPath ∧ flipLeft.IsPath ∧
        preFlipLeft.IsPath ∧
        (∀ e ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).edges,
          e ∈ preFlipLeft.edges ∨ e ∈ flipLeft.edges) ∧
        (right.append flipLeft).IsPath ∧
        right.length =
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
        ∀ q (hq : q ∈ rlc_pathVertices gamma.1),
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 →
            right.length ≤
              (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
  classical
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  obtain ⟨z, hzWR, hzRight, hzLeft, hfirst, hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  let right : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) z := WR.takeUntil z hzWR
  let left : (hypercubicLattice 2).Walk
      (rlc_flipX z) (gamma'.1.2.1 : Site 2) :=
    WL.dropUntil (rlc_flipX z) hzWL
  let preLeft : (hypercubicLattice 2).Walk
      (gamma'.1.1 : Site 2) (rlc_flipX z) :=
    WL.takeUntil (rlc_flipX z) hzWL
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk
      z (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy
      (rlc_flipX_involutive z) hflipUpper
  let preFlipLeft : (hypercubicLattice 2).Walk
      (rlc_flipX (gamma'.1.1 : Site 2)) z :=
    (preLeft.map rlc_flipXLatticeHom).copy rfl
      (rlc_flipX_involutive z)
  have hrightPath : right.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma.1).takeUntil hzWR
  have hleftPath : left.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma'.1).dropUntil hzWL
  have hpreLeftPath : preLeft.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma'.1).takeUntil hzWL
  have hflipLeftPath : flipLeft.IsPath := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.isPath_copy]
    apply left.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hleftPath
  have hpreFlipLeftPath : preFlipLeft.IsPath := by
    dsimp only [preFlipLeft]
    rw [SimpleGraph.Walk.isPath_copy]
    apply preLeft.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hpreLeftPath
  have hinter : ∀ x ∈ right.support,
      x ∈ flipLeft.support → x = z := by
    intro x hxRight hxFlipLeft
    have hxWR : x ∈ (WR.takeUntil z hzWR).support := by
      simpa [right] using hxRight
    have hxMapped : x ∈ (left.map rlc_flipXLatticeHom).support := by
      simpa [flipLeft] using hxFlipLeft
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxMapped
    obtain ⟨y, hyLeft, hyx⟩ := hxMapped
    change rlc_flipX y = x at hyx
    have hyWL : y ∈ WL.support :=
      WL.support_dropUntil_subset hzWL hyLeft
    have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 y).1
        hyWL
    have hflipX : rlc_flipX x = y := by
      rw [← hyx]
      simp
    exact hfirst x hxWR (by simpa [hflipX] using hyPath)
  have hflipLeftSupport (x : Site 2) :
      x ∈ flipLeft.support ↔ rlc_flipX x ∈ left.support := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change rlc_flipX (rlc_flipX y) ∈ left.support
      simpa using hy
    · intro hx
      exact ⟨rlc_flipX x, hx, rlc_flipX_involutive x⟩
  have hflipLeftRank : ∀ x ∈ flipLeft.support,
      WL.support.idxOf (rlc_flipX z) ≤
        WL.support.idxOf (rlc_flipX x) := by
    intro x hx
    apply rlc_isPath_idxOf_le_of_mem_dropUntil WL
      (rlc_ambientCrossingWalk_isPath gamma'.1) hzWL
    exact hflipLeftSupport x |>.1 hx
  have hpreFlipLeftSupport (x : Site 2) :
      x ∈ preFlipLeft.support ↔ rlc_flipX x ∈ preLeft.support := by
    dsimp only [preFlipLeft]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change rlc_flipX (rlc_flipX y) ∈ preLeft.support
      simpa using hy
    · intro hx
      exact ⟨rlc_flipX x, hx, rlc_flipX_involutive x⟩
  have hpreRightInter : ∀ x ∈ preFlipLeft.support,
      x ∈ right.support → x = z := by
    intro x hxPre hxRight
    have hflipPre : rlc_flipX x ∈ preLeft.support :=
      (hpreFlipLeftSupport x).1 hxPre
    have hflipWL : rlc_flipX x ∈ WL.support :=
      WL.support_takeUntil_subset_support hzWL hflipPre
    have hflipPath : rlc_flipX x ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX x)).1 hflipWL
    have hxWR : x ∈ (WR.takeUntil z hzWR).support := by
      simpa [right] using hxRight
    exact hfirst x hxWR hflipPath
  have hpreSuffixRaw : ∀ y ∈ preLeft.support,
      y ∈ left.support → y = rlc_flipX z := by
    intro y hyPre hyLeft
    by_contra hyq
    have hwhole : (preLeft.append left).IsPath := by
      have hWPath := rlc_ambientCrossingWalk_isPath gamma'.1
      simpa [preLeft, left] using hWPath
    exact (hwhole.ne_of_mem_support_of_append hyq hyPre hyLeft) rfl
  have hpreSuffixInter : ∀ x ∈ preFlipLeft.support,
      x ∈ flipLeft.support → x = z := by
    intro x hxPre hxSuffix
    have hxPre' := (hpreFlipLeftSupport x).1 hxPre
    have hxSuffix' := (hflipLeftSupport x).1 hxSuffix
    have hxEq := hpreSuffixRaw _ hxPre' hxSuffix'
    apply rlc_flipX.injective
    simpa using hxEq
  have hprePositive : ∀ x ∈ preFlipLeft.support,
      x ≠ z → 0 < x 0 := by
    intro x hxPre hxz
    have hxPre' := (hpreFlipLeftSupport x).1 hxPre
    have hxWL : rlc_flipX x ∈ WL.support :=
      WL.support_takeUntil_subset_support hzWL hxPre'
    have hxPath : rlc_flipX x ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX x)).1 hxWL
    have hxNeEnd : rlc_flipX x ≠ (gamma'.1.2.1 : Site 2) := by
      intro hxEnd
      have hEndLeft : (gamma'.1.2.1 : Site 2) ∈ left.support :=
        left.end_mem_support
      have hxJoin := hpreSuffixRaw _ hxPre' (by simpa [hxEnd] using hEndLeft)
      apply hxz
      apply rlc_flipX.injective
      simpa [hxEnd] using hxJoin
    have hxNeg := hfaith.left_vertex_strict hxPath hxNeEnd
    change -x 0 < 0 at hxNeg
    omega
  have hflipLeftEdges : ∀ e ∈ flipLeft.edges,
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    intro e he
    dsimp only [flipLeft] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    refine ⟨e0, ?_, rfl⟩
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    exact WL.edges_dropUntil_subset hzWL he0
  refine ⟨z, right, left, flipLeft, preFlipLeft,
    hzRight, hzLeft, ?_, ?_, hflipLeftEdges, hinter,
    hflipLeftSupport, hflipLeftRank, hpreRightInter, hpreSuffixInter,
    hprePositive, hrightPath, hleftPath, hflipLeftPath,
    hpreFlipLeftPath, ?_, ?_, ?_, ?_⟩
  · intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hzWR he
  · intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    exact WL.edges_dropUntil_subset hzWL he
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    change e0 ∈ WL.edges at he0
    have htake := SimpleGraph.Walk.take_spec WL hzWL
    rw [← htake, SimpleGraph.Walk.edges_append,
      List.mem_append] at he0
    rcases he0 with hePre | heSuffix
    · left
      dsimp only [preFlipLeft]
      rw [SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨e0, hePre, rfl⟩
    · right
      dsimp only [flipLeft]
      rw [SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨e0, heSuffix, rfl⟩
  · exact rlc_append_isPath_of_endpoint_intersection
      hrightPath hflipLeftPath hinter
  · simp [right, WR, SimpleGraph.Walk.length_takeUntil]
  · intro q hq hqLeft
    have hqWR :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2 hq
    simpa [right, WR, SimpleGraph.Walk.length_takeUntil] using
      hglobalMin q hqWR hqLeft

set_option maxHeartbeats 2000000 in




theorem rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      c.IsCycle ∧
        (gamma.1.1 : Site 2) ∈ c.support ∧
        (gamma'.1.2.1 : Site 2) ∈ c.support ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ k : Int,
          (gamma.1.1 : Site 2) 1 < k →
          k ≤ (gamma'.1.2.1 : Site 2) 1 →
          ¬ Even (jec_rayCount (![1, k] : Site 2) c)) ∧
        ∀ {x y : Site 2},
          s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).edges →
          s(x, y) ∈ c.edges ∨
            ∀ h ∈ flankFaces x y,
              phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
  obtain ⟨z, right, left, flipLeft, preFlipLeft, hzRight, hzLeft,
    hrightEdges, hleftEdges, hflipLeftEdges, hinter, hflipLeftSupport,
    _hflipLeftRank, hpreRightInter, hpreSuffixInter, hprePositive,
    hrightPath, hleftPath, _hflipLeftPath, hpreFlipLeftPath,
    hleftMappedSplit, hrightHalfPath, _hrankRealized, _hglobalMin⟩ :=
      rlc_bookFirstIntersection_truncatedSides_of_faithful
        gamma gamma' hfaith
  let q := rlc_flipX z
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipRightRev : (hypercubicLattice 2).Walk
      q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightHalf := right.append flipLeft
  let leftHalf := left.reverse.append flipRightRev
  let c := rightHalf.append leftHalf
  have hflipRightPath : flipRightRev.IsPath := by
    dsimp only [flipRightRev]
    rw [SimpleGraph.Walk.isPath_copy,
      SimpleGraph.Walk.isPath_reverse_iff]
    apply right.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hrightPath
  have hleftFlipInter : ∀ x ∈ left.reverse.support,
      x ∈ flipRightRev.support → x = q := by
    intro x hxLeftRev hxFlipRight
    have hxLeft : x ∈ left.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hxLeftRev
    dsimp only [flipRightRev] at hxFlipRight
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_map, List.mem_map] at hxFlipRight
    obtain ⟨y, hyRight, hyx⟩ := hxFlipRight
    change rlc_flipX y = x at hyx
    have hyFlipLeft : y ∈ flipLeft.support :=
      (hflipLeftSupport y).2 (by simpa [hyx] using hxLeft)
    have hyz := hinter y hyRight hyFlipLeft
    subst y
    simpa [q] using hyx.symm
  have hleftHalfPath : leftHalf.IsPath := by
    exact rlc_append_isPath_of_endpoint_intersection
      hleftPath.reverse hflipRightPath hleftFlipInter
  have hflipRightEdges : ∀ e ∈ flipRightRev.edges,
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    intro e he
    dsimp only [flipRightRev] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hrightEdges e0 he0, rfl⟩
  have hrightHalfFour : ∀ e ∈ rightHalf.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    change e ∈ (right.append flipLeft).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hrightEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (hflipLeftEdges e he))
  have hleftHalfFour : ∀ e ∈ leftHalf.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    change e ∈ (left.reverse.append flipRightRev).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (hleftEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (hflipRightEdges e he))
  have hrightSupport : ∀ x ∈ right.support,
      x ∈ rlc_pathVertices gamma.1 := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
    rcases hx with rfl | ⟨e, he, hxe⟩
    · exact hzRight
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := rlc_pathEdge_endpoints_mem_vertices gamma.1
            (hrightEdges s(a, b) he)
          rw [Sym2.mem_iff] at hxe
          exact hxe.elim (fun h ↦ h ▸ hab.1) (fun h ↦ h ▸ hab.2)
  have hleftSupport : ∀ x ∈ left.support,
      x ∈ rlc_pathVertices gamma'.1 := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
    rcases hx with rfl | ⟨e, he, hxe⟩
    · exact rlc_connector_path_end_mem_vertices gamma'.1
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := rlc_pathEdge_endpoints_mem_vertices gamma'.1
            (hleftEdges s(a, b) he)
          rw [Sym2.mem_iff] at hxe
          exact hxe.elim (fun h ↦ h ▸ hab.1) (fun h ↦ h ▸ hab.2)
  have hrightHalfNonneg : ∀ x ∈ rightHalf.support, 0 ≤ x 0 := by
    intro x hx
    change x ∈ (right.append flipLeft).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · have hrect := rlc_pathVertex_mem_rect gamma.1
        (hrightSupport x hx)
      rw [mem_rect] at hrect
      exact hrect.1
    · have hrect := rlc_pathVertex_mem_rect gamma'.1
        (hleftSupport _ ((hflipLeftSupport x).1 hx))
      rw [mem_rect] at hrect
      have hxBound := hrect.2.1
      change -(x 0) ≤ 0 at hxBound
      omega
  have hleftHalfNonpos : ∀ x ∈ leftHalf.support, x 0 ≤ 0 := by
    intro x hx
    change x ∈ (left.reverse.append flipRightRev).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    rcases hx with hx | hx
    · have hrect := rlc_pathVertex_mem_rect gamma'.1
        (hleftSupport x hx)
      rw [mem_rect] at hrect
      exact hrect.2.1
    · dsimp only [flipRightRev] at hx
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hrect := rlc_pathVertex_mem_rect gamma.1
        (hrightSupport y hy)
      rw [mem_rect] at hrect
      change -y 0 ≤ 0
      omega
  have hrightHalfAxis : ∀ x ∈ rightHalf.support, x 0 = 0 →
      x = (gamma.1.1 : Site 2) ∨ x = (gamma'.1.2.1 : Site 2) := by
    intro x hx hx0
    change x ∈ (right.append flipLeft).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact Or.inl (hfaith.right_axis_unique
        (hrightSupport x hx) hx0)
    · right
      have hxLeft := hleftSupport _ ((hflipLeftSupport x).1 hx)
      have hflip0 : (rlc_flipX x) 0 = 0 := by
        change -(x 0) = 0
        omega
      have hleftEnd := hfaith.left_axis_unique hxLeft hflip0
      have hself := rlc_flipX_eq_self_of_zero hx0
      rwa [hself] at hleftEnd
  have hhalvesInter : ∀ x, x ∈ rightHalf.support →
      x ∈ leftHalf.support →
      x = (gamma.1.1 : Site 2) ∨ x = (gamma'.1.2.1 : Site 2) := by
    intro x hxRight hxLeft
    have hx0 : x 0 = 0 := by
      have hr := hrightHalfNonneg x hxRight
      have hl := hleftHalfNonpos x hxLeft
      omega
    exact hrightHalfAxis x hxRight hx0
  have hhalfEdges : rightHalf.edges.Disjoint leftHalf.edges := by
    rw [List.disjoint_left]
    intro e heRight heLeft
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hx := hhalvesInter x
          (rightHalf.fst_mem_support_of_mem_edges heRight)
          (leftHalf.fst_mem_support_of_mem_edges heLeft)
        have hy := hhalvesInter y
          (rightHalf.snd_mem_support_of_mem_edges heRight)
          (leftHalf.snd_mem_support_of_mem_edges heLeft)
        have hxy := rightHalf.adj_of_mem_edges heRight
        have hedge : s(x, y) =
            s((gamma.1.1 : Site 2), (gamma'.1.2.1 : Site 2)) := by
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact False.elim (hxy.ne rfl)
          · rfl
          · exact Sym2.eq_swap
          · exact False.elim (hxy.ne rfl)
        have horder := hfaith.axis_contacts_strict
        have hstep : (gamma'.1.2.1 : Site 2) 1 =
            (gamma.1.1 : Site 2) 1 + 1 := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp_all <;> omega
        have haxisEdge :
            s((gamma.1.1 : Site 2), (gamma'.1.2.1 : Site 2)) =
              s((![0, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
                ![0, (gamma'.1.2.1 : Site 2) 1]) := by
          rw [Sym2.eq_iff]
          left
          constructor <;> ext i <;> fin_cases i <;>
            simp [gamma.1.1.2.2, gamma'.1.2.1.2.2] <;> omega
        apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
          gamma gamma' hfaith ((gamma'.1.2.1 : Site 2) 1)
        rw [← haxisEdge, ← hedge]
        exact hrightHalfFour s(x, y) heRight
  have hcycle : c.IsCycle := by
    have hcontactsNe : (gamma.1.1 : Site 2) ≠
        (gamma'.1.2.1 : Site 2) := by
      intro h
      have hrow := congrArg (fun x : Site 2 => x 1) h
      exact (ne_of_lt hfaith.axis_contacts_strict) hrow
    exact rlc_append_isCycle_of_endpoint_intersection
      hrightHalfPath hleftHalfPath
        hcontactsNe hhalvesInter hhalfEdges
  have hcFour : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    dsimp only [c] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    exact he.elim (hrightHalfFour e) (hleftHalfFour e)
  have hpreOff : ∀ x ∈ preFlipLeft.support,
      x ≠ z → x ∉ c.support := by
    intro x hxPre hxz hxc
    change x ∈ (rightHalf.append leftHalf).support at hxc
    rw [SimpleGraph.Walk.mem_support_append_iff] at hxc
    rcases hxc with hxRightHalf | hxLeftHalf
    · change x ∈ (right.append flipLeft).support at hxRightHalf
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxRightHalf
      rcases hxRightHalf with hxRight | hxSuffix
      · exact hxz (hpreRightInter x hxPre hxRight)
      · exact hxz (hpreSuffixInter x hxPre hxSuffix)
    · have hxPos := hprePositive x hxPre hxz
      have hxNonpos := hleftHalfNonpos x hxLeftHalf
      omega
  have hpreEdges : ∀ e ∈ preFlipLeft.edges, e ∉ c.edges := by
    intro e hePre heCycle
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy := preFlipLeft.adj_of_mem_edges hePre
        have hxPre := preFlipLeft.fst_mem_support_of_mem_edges hePre
        have hyPre := preFlipLeft.snd_mem_support_of_mem_edges hePre
        have hxCycle := c.fst_mem_support_of_mem_edges heCycle
        have hyCycle := c.snd_mem_support_of_mem_edges heCycle
        by_cases hxz : x = z
        · have hyz : y ≠ z := by
            intro hyz
            exact hxy.ne (hxz.trans hyz.symm)
          exact hpreOff y hyPre hyz hyCycle
        · exact hpreOff x hxPre hxz hxCycle
  have hpreStartRight :
      (rlc_flipX (gamma'.1.1 : Site 2)) 0 = 2 * n := by
    change -(gamma'.1.1 : Site 2) 0 = 2 * n
    rw [gamma'.1.1.2.2]
    ring
  have hpreExterior {x y h : Site 2}
      (hxy : s(x, y) ∈ preFlipLeft.edges)
      (hh : h ∈ flankFaces x y) :
      phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
    have hpreNotNil : ¬ preFlipLeft.Nil := by
      intro hnil
      have hnilEdges : preFlipLeft.edges = [] := by
        simpa [hnil.eq]
      have : s(x, y) ∈ ([] : List (Sym2 (Site 2))) :=
        hnilEdges ▸ hxy
      simp at this
    exact rlc_cfct_rightBoundaryTail_flanks_outside_firstCycle
      gamma gamma' hcycle hcFour preFlipLeft hpreStartRight
        hpreFlipLeftPath hpreNotNil hpreOff hpreEdges hxy hh
  have hleftMappedCover {x y : Site 2}
      (hxy : s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).edges) :
      s(x, y) ∈ c.edges ∨
        ∀ h ∈ flankFaces x y,
          phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
    rcases hleftMappedSplit s(x, y) hxy with hePre | heSuffix
    · right
      intro h hh
      apply hpreExterior (x := x) (y := y)
      · exact hePre
      · exact hh
    · left
      have hrightHalf : s(x, y) ∈
          rightHalf.edges := by
        change s(x, y) ∈
          (right.append flipLeft).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inr heSuffix
      change s(x, y) ∈ (rightHalf.append leftHalf).edges
      rw [SimpleGraph.Walk.edges_append, List.mem_append]
      exact Or.inl hrightHalf
  refine ⟨c, hcycle, c.start_mem_support, ?_, hcFour, ?_, ?_⟩
  · dsimp only [c]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl rightHalf.end_mem_support
  · intro k hkLower hkUpper
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightHalf = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrightHalfNonneg u
            (rightHalf.fst_mem_support_of_mem_edges he)
          have hv0 := hrightHalfNonneg v
            (rightHalf.snd_mem_support_of_mem_edges he)
          have hfour := hrightHalfFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftHalf =
        crossCount (jec_belowSet k) leftHalf := by
      apply jec_ray_eq_below
      intro x hx
      simpa using hleftHalfNonpos x hx
    have hleftOdd :
        ¬ Even (jec_rayCount (![1, k] : Site 2) leftHalf) := by
      rw [hleftRay]
      intro heven
      have hsame := (crossCount_parity (jec_belowSet k) leftHalf).mp heven
      have hupperNot :
          (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      exact hupperNot (hsame.mpr hlowerIn)
    change ¬ Even (jec_rayCount (![1, k] : Site 2)
      (rightHalf.append leftHalf))
    rw [jec_rayCount_append, hrightRay, zero_add]
    exact hleftOdd
  · intro x y hxy
    exact hleftMappedCover hxy



theorem rlc_cycleEdge_oppositeFlank_outside
    {a x y h k : Site 2}
    {c : (hypercubicLattice 2).Walk a a}
    (hcycle : c.IsCycle)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hflank : flankFaces x y = s(h, k))
    (hedge : s(x, y) ∈ c.edges)
    (hhInside : phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) :
    phb_doubleDualEquiv.symm k ∉ jec_leftRegion c := by
  obtain ⟨f, g, hfgFlank, hfgAdj⟩ := flankFaces_latAdj hxy
  have hhk : s(h, k) = s(f, g) := hflank.symm.trans hfgFlank
  have hhkAdj : (hypercubicLattice 2).Adj h k := by
    rw [Sym2.eq_iff] at hhk
    rcases hhk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hfgAdj
    · exact hfgAdj.symm
  have hshared : sharedPrimalEdge h k = s(x, y) := by
    calc
      sharedPrimalEdge h k = symPrimal h k :=
        (symPrimal_eq_shared hhkAdj).symm
      _ = symPrimalSym s(h, k) := rfl
      _ = symPrimalSym (flankFaces x y) :=
        congrArg symPrimalSym hflank.symm
      _ = s(x, y) := symPrimalSym_flankFaces hxy
  have hsplit := (fwr_faceCutMatch_of_nodup
    c hcycle.edges_nodup hhkAdj).2 (by rwa [hshared])
  have hhFace : fwr_faceInside c h := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using hhInside
  have hkFace : ¬ fwr_faceInside c k := hsplit.mp hhFace
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hkFace





theorem rlc_centralRegion_inside_firstIntersectionCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      c.IsCycle ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) ∧
        ∀ {x y : Site 2},
          s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).edges →
          s(x, y) ∈ c.edges ∨
            ∀ h ∈ flankFaces x y,
              phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
  obtain ⟨c, hcycle, _hlower, _hupper, hedges, hodd,
    hleftDichotomy⟩ :=
    rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful
      gamma gamma' hfaith
  refine ⟨c, hcycle, hedges, ?_, hleftDichotomy⟩
  intro h hhRegion
  have hn : 0 < n := by
    have hrect := rlc_pathVertex_mem_rect gamma.1
      (rlc_path_start_mem_vertices gamma.1)
    rw [mem_rect] at hrect
    have := hfaith.right_axis_strict
    omega
  have hcentralRegion : rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion gamma gamma' :=
    rlc_connectorCentralFace_mem_region gamma gamma' hn
  obtain ⟨hsBox, hhBox, hreach⟩ :=
    rlc_connectorCentralFaceRegion_reachable hcentralRegion hhRegion
  obtain ⟨w⟩ := hreach
  have hstep {x y : RlcConnectorFaceVertex n}
      (hxy : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj x y) :
      fwr_faceInside c x.1 ↔ fwr_faceInside c y.1 := by
    have hcut := (rlc_connectorFourTraceFaceCutGraph_adj
      gamma gamma' x.1 y.1).mp hxy
    have hnot : sharedPrimalEdge x.1 y.1 ∉ c.edges := by
      intro hc
      exact hcut.2 (hedges _ hc)
    have hmatch := fwr_faceCutMatch_of_nodup
      c hcycle.edges_nodup hcut.1
    have hnosplit : ¬ (fwr_faceInside c x.1 ↔
        ¬ fwr_faceInside c y.1) := by
      intro hsplit
      exact hnot (hmatch.mp hsplit)
    tauto
  have hpropagate {x y : RlcConnectorFaceVertex n}
      (p : (rlc_connectorFiniteFaceCutGraph gamma gamma').Walk x y) :
      fwr_faceInside c x.1 → fwr_faceInside c y.1 := by
    intro hx
    induction p with
    | nil => exact hx
    | @cons u v z huv p ih =>
        exact ih ((hstep huv).mp hx)
  have hcentralInside : fwr_faceInside c rlc_connectorCentralFace := by
    have hgap := hodd 1 (by
        have := hfaith.right_axis_strict
        omega) (by
        have := hfaith.left_axis_strict
        omega)
    simpa [fwr_faceInside, rlc_connectorCentralFace] using hgap
  have hhInside := hpropagate w hcentralInside
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hhInside




theorem rlc_walk_all_edges_or_last_failure_decomp
    {V : Type*} {G : SimpleGraph V} (P : Sym2 V → Prop)
    {x y : V} (w : G.Walk x y) :
    (∀ e ∈ w.edges, P e) ∨
      ∃ (u v : V) (p : G.Walk x u) (r : G.Walk v y)
        (huv : G.Adj u v),
        ¬ P s(u, v) ∧
          (∀ e ∈ r.edges, P e) ∧
          w = p.append (.cons huv r) := by
  induction w with
  | nil =>
      left
      simp
  | @cons a b c hab t ih =>
      rcases ih with hall | ⟨u, v, p, r, huv, hfail, hsuffix, hdecomp⟩
      · by_cases habP : P s(a, b)
        · left
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          exact he.elim (fun h => h ▸ habP) (fun h => hall e h)
        · right
          exact ⟨a, b, .nil, t, hab, habP, hall, by simp⟩
      · right
        refine ⟨u, v, .cons hab p, r, huv, hfail, hsuffix, ?_⟩
        rw [hdecomp]
        rfl





def RlcCentralFaceNegativeWallRunSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A a b : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect u = rlc_flipX w




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRun
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hresidue : RlcCentralFaceNegativeBadExitResidue
      gamma gamma' rho u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u := by
  obtain ⟨A, hfirstA, hAfirst, hAzero, hleft | hAoff⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  · exact Or.inl ⟨A, hfirstA, hleft⟩
  rcases hresidue with hboundary | ⟨w, hw, huw, hallIncoming⟩
  · exact Or.inr (Or.inl hboundary)
  · obtain ⟨pA⟩ := hAfirst
    let Q := pA.append q
    let P : Sym2 (Site 2) → Prop := fun e =>
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
    rcases rlc_walk_all_edges_or_last_failure_decomp P Q with
      hall | ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
    · exfalso
      have hANeU : A ≠ u := by
        intro hAu
        have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
          congrArg rlc_dualReflect hAu
        have h0 := congrArg (fun z : Site 2 => z 0) hreflect
        rw [hAzero] at h0
        simp only [Matrix.cons_val_zero] at h0
        omega
      have hQNotNil : ¬ Q.Nil := Q.not_nil_of_ne hANeU
      have hfirstEdge := Q.mk_start_snd_mem_edges hQNotNil
      have hfirstWall := hall _ hfirstEdge
      have hAbarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hfirstWall (by
          change rlc_dualReflect A ∈
            Sym2.map rlc_dualReflect s(A, Q.snd)
          simp [Sym2.map_mk])
      exact hAoff hAbarrier
    · have hrNotNil : ¬ r.Nil := by
        intro hrNil
        have hbu : b = u := hrNil.eq
        subst b
        have hav : a ≠ v := by
          intro hav
          subst a
          apply hbad
          exact (rlc_reflectedEdgeCarrierGeometry_comm
            gamma gamma' v u).1 hab.2
        have hauWall := hallIncoming a hab hav
        apply hnotWall
        simpa [P, Sym2.map_mk] using hauWall
      exact Or.inr (Or.inr ⟨A, a, b, p, r, hab, hAzero, hAoff,
        by simpa [P, Sym2.map_mk] using hnotWall, hrWall, hrNotNil,
        w, hw, huw⟩)

def RlcCentralFacePositiveWallRunSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A a b : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w




def RlcCentralFacePositiveAxisAllWallRunAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u),
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
      (∀ e ∈ p.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hresidue : RlcCentralFacePositiveBadExitResidue
      gamma gamma' rho u v) :
    ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u ∨
      RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u := by
  rcases hresidue with hboundary | ⟨w, hw, huw, hallIncoming⟩
  · exact Or.inl hboundary
  · obtain ⟨A, hfirstA, hAfirst, hAzero, hstart⟩ :=
      rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
        L.boundary hfaith
    obtain ⟨pA⟩ := hAfirst
    let hanchor := L.boundary.anchor_mem_goodBoundaryGraph hfaith
    let Q := pA.append (.cons hanchor q)
    let P : Sym2 (Site 2) → Prop := fun e =>
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
    rcases rlc_walk_all_edges_or_last_failure_decomp P Q with
      hall | ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
    · rcases hstart with hleft | hAoff
      · exact Or.inr (Or.inl ⟨A, Q, hAzero, hleft, hall,
          w, hw, huw⟩)
      · exfalso
        have hANeU : A ≠ u := by
          intro hAu
          have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
            congrArg rlc_dualReflect hAu
          have h0 := congrArg (fun z : Site 2 => z 0) hreflect
          rw [hAzero] at h0
          simp only [Matrix.cons_val_zero] at h0
          omega
        have hQNotNil : ¬ Q.Nil := Q.not_nil_of_ne hANeU
        have hfirstEdge := Q.mk_start_snd_mem_edges hQNotNil
        have hfirstWall := hall _ hfirstEdge
        have hAbarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hfirstWall (by
            change rlc_dualReflect A ∈
              Sym2.map rlc_dualReflect s(A, Q.snd)
            simp [Sym2.map_mk])
        exact hAoff hAbarrier
    · have hrNotNil : ¬ r.Nil := by
        intro hrNil
        have hbu : b = u := hrNil.eq
        subst b
        have hav : a ≠ v := by
          intro hav
          subst a
          apply hbad
          exact (rlc_reflectedEdgeCarrierGeometry_comm
            gamma gamma' v u).1 hab.2
        have hauWall := hallIncoming a hab hav
        apply hnotWall
        simpa [P, Sym2.map_mk] using hauWall
      exact Or.inr (Or.inr ⟨A, a, b, p, r, hab, hAzero, hstart,
        by simpa [P, Sym2.map_mk] using hnotWall, hrWall, hrNotNil,
        w, hw, huw⟩)



def RlcCentralFacePairedBadExitSurgeryResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u u' : Site 2) : Prop :=
  ((rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) ∨
    RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u ∨
    ((rlc_dualReflect u') 0 = -2 * n ∨
      (rlc_dualReflect u') 0 = 2 * n ∨
      (rlc_dualReflect u') 1 = -n ∨
      (rlc_dualReflect u') 1 = n) ∨
    RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u' ∨
    RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u'




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_surgeryResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      RlcCentralFacePairedBadExitSurgeryResidue gamma gamma' rho L u u' := by
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  have finishPositive :
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) →
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        RlcCentralFacePairedBadExitSurgeryResidue
          gamma gamma' rho L u u') := by
    intro hleft
    rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with
      hright | hboundary | hwall
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · right
      exact Or.inr (Or.inr (Or.inl hboundary))
    · rcases L.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun
          hfaith q' hu'Pos hu'v' hbad' (Or.inr hwall) with
        hboundary | haxisRun | hlastRun
      · exact Or.inr (Or.inr (Or.inr (Or.inl hboundary)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl haxisRun))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlastRun))))
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno q.reachable huNeg huv hbad with
    hleft | hboundary | hwall
  · exact finishPositive hleft
  · exact Or.inr (Or.inl hboundary)
  · rcases L.negativeBadExitResidue_left_boundary_or_wallRun
        hfaith q huNeg huv hbad (Or.inr hwall) with
      hleft | hboundary | hlastRun
    · exact finishPositive hleft
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hlastRun))



theorem rlc_negativeWallRun_lastEdge_reflectedRight
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  let t := r.penultimate
  have htu := r.adj_penultimate hrNotNil
  have htuEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hwall := hrWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipLeft




theorem rlc_positiveWallRun_lastEdge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  let t := r.penultimate
  have htu := r.adj_penultimate hrNotNil
  have htuEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hwall := hrWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipRight



theorem rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  obtain ⟨A, p, hAzero, hALeft, hpWall, w, hw, huw⟩ := hrun
  have hANeU : A ≠ u := by
    intro hAu
    have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
      congrArg rlc_dualReflect hAu
    have h0 := congrArg (fun z : Site 2 => z 0) hreflect
    rw [hAzero] at h0
    simp only [Matrix.cons_val_zero] at h0
    omega
  have hpNotNil : ¬ p.Nil := p.not_nil_of_ne hANeU
  let t := p.penultimate
  have htu := p.adj_penultimate hpNotNil
  have htuEdge := p.mk_penultimate_end_mem_edges hpNotNil
  have hwall := hpWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipRight




theorem rlc_negativeWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma.1 ∧
        w ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_negativeWallRun_lastEdge_reflectedRight
      hrun huNeg huNotLeft
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma.1 he'⟩

theorem rlc_positiveWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma'.1 ∧
        w ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma'.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_positiveWallRun_lastEdge_reflectedLeft
      hrun huPos huNotRight
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma'.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma'.1 he'⟩

theorem rlc_positiveAxisAllWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma'.1 ∧
        w ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma'.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft
      hrun huPos huNotRight
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma'.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma'.1 he'⟩






theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_nonnegativePath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        p.IsPath ∧
          rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
          (∀ e ∈ p.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma') ∧
          (∀ z ∈ p.support,
            rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧
          ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0 := by
  obtain ⟨A, w, hAzero, hALeft, hwWall, zEnd, hzEnd, huEnd⟩ := hrun
  let p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u := w.toPath
  have hpPath : p.IsPath := w.toPath.isPath
  have hpEdges : ∀ e ∈ p.edges, e ∈ w.edges := by
    intro e he
    exact w.edges_toPath_subset he
  have hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    exact hwWall e (hpEdges e he)
  obtain ⟨A0, hfirstA0, _hA0first, hA0zero, _hA0class⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  have hA0A : A0 = A := by
    apply rlc_dualReflect.injective
    exact hA0zero.trans hAzero.symm
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := by
    simpa [hA0A] using hfirstA0
  by_cases hright : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hxP, hxRight⟩ := hright
    exact ⟨x, hfirstA.trans ⟨p.takeUntil x hxP⟩, hxRight⟩
  · right
    push Not at hright
    refine ⟨A, p, hpPath, hAzero, hALeft, hpWall, hright, ?_⟩
    intro y hyP
    by_contra hyNonneg
    have hyNeg : (rlc_dualReflect y) 0 < 0 := by omega
    let tailGood := p.dropUntil y hyP
    let tail := tailGood.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)
    obtain ⟨f, g, k, hfgTail, hreflected⟩ :=
      rlc_faceBoundaryWalk_reflected_axis_crossing tail
        (by simpa [tail, tailGood] using hyNeg) (by
          simpa [tail, tailGood] using (le_of_lt huPos))
    have hfgGood : s(f, g) ∈ tailGood.edges := by
      simpa [tail, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgTail
    have hfgP : s(f, g) ∈ p.edges :=
      p.edges_dropUntil_subset hyP hfgGood
    have hwallAxis : s((![-1, k] : Site 2), ![0, k]) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [← hreflected]
      simpa [Sym2.map_mk] using hpWall _ hfgP
    have hzeroBarrier : (![0, k] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' :=
      rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hwallAxis (Sym2.mem_mk_right _ _)
    obtain ⟨c, hcTail, hcEq⟩ : ∃ c : Site 2,
        c ∈ tailGood.support ∧
          rlc_dualReflect c = (![0, k] : Site 2) := by
      rw [Sym2.eq_iff] at hreflected
      rcases hreflected with ⟨hf, hg⟩ | ⟨hf, hg⟩
      · exact ⟨g, tailGood.snd_mem_support_of_mem_edges hfgGood, hg⟩
      · exact ⟨f, tailGood.fst_mem_support_of_mem_edges hfgGood, hf⟩
    rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma' k).1
        hzeroBarrier with hzeroRight | hzeroLeft
    · have hcRight : rlc_dualReflect c ∈
          rlc_pathVertices gamma.1 := by
        rwa [hcEq]
      have hcP : c ∈ p.support :=
        p.support_dropUntil_subset hyP hcTail
      exact hright c hcP hcRight
    · have hAEnd := hfaith.left_axis_unique hALeft (by
          rw [hAzero]
          simp)
      have hcLeft : rlc_dualReflect c ∈
          rlc_pathVertices gamma'.1 := by
        simpa [hcEq] using hzeroLeft
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hcEq]
        rfl
      have hcEnd := hfaith.left_axis_unique hcLeft hcZero
      have hAc : A = c := by
        apply rlc_dualReflect.injective
        exact hAEnd.trans hcEnd.symm
      have hyc : y ≠ c := by
        intro hyc
        have hyZero : (rlc_dualReflect y) 0 = 0 := by
          simpa [hyc] using hcZero
        omega
      have hAinPrefix : A ∈ (p.takeUntil y hyP).support :=
        (p.takeUntil y hyP).start_mem_support
      have happPath : ((p.takeUntil y hyP).append
          (p.dropUntil y hyP)).IsPath := by
        rw [p.take_spec hyP]
        exact hpPath
      have hAneC := happPath.ne_of_mem_support_of_append
        hyc.symm hAinPrefix hcTail
      exact hAneC hAc




theorem rlc_nonnegative_wallPath_edge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hpNoRight : ∀ z ∈ p.support,
      rlc_dualReflect z ∉ rlc_pathVertices gamma.1)
    (hpNonneg : ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0)
    {f g : Site 2} (hfg : s(f, g) ∈ p.edges) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_reflectedPathEdges gamma'.1 := by
  have hfP := p.fst_mem_support_of_mem_edges hfg
  have hgP := p.snd_mem_support_of_mem_edges hfg
  have hfNonneg := hpNonneg f hfP
  have hgNonneg := hpNonneg g hgP
  have hfgWall : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.map_mk] using hpWall _ hfg
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp (p.adj_of_mem_edges hfg).1.1
  have hsomePos : 0 < (rlc_dualReflect f) 0 ∨
      0 < (rlc_dualReflect g) 0 := by
    by_contra hnot
    push Not at hnot
    have hfZero : (rlc_dualReflect f) 0 = 0 := by omega
    have hgZero : (rlc_dualReflect g) 0 = 0 := by omega
    rcases face_adj_dir hfgAdj with hg | hg | hg | hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect g) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect g) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect g) 1]) := by
        rw [Sym2.eq_iff]
        left
        constructor <;> ext i <;> fin_cases i <;>
          simp_all
      rwa [← hedge]
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect f) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect f) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect f) 1]) := by
        rw [Sym2.eq_iff]
        right
        constructor <;> ext i <;> fin_cases i <;>
          simp_all
      rwa [← hedge]
  rcases hsomePos with hfPos | hgPos
  · have hfNotLeft : rlc_dualReflect f ∉
        rlc_pathVertices gamma'.1 := by
      intro hfLeft
      have hfRect := rlc_pathVertex_mem_rect gamma'.1 hfLeft
      rw [mem_rect] at hfRect
      omega
    have hfNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect f = rlc_flipX z := by
      rintro ⟨z, hz, hfz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hfz
      change (rlc_dualReflect f) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_left _ _)
        (hpNoRight f hfP) hfNotLeft hfNotFlipRight
  · have hgNotLeft : rlc_dualReflect g ∉
        rlc_pathVertices gamma'.1 := by
      intro hgLeft
      have hgRect := rlc_pathVertex_mem_rect gamma'.1 hgLeft
      rw [mem_rect] at hgRect
      omega
    have hgNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect g = rlc_flipX z := by
      rintro ⟨z, hz, hgz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hgz
      change (rlc_dualReflect g) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_right _ _)
        (hpNoRight g hgP) hgNotLeft hgNotFlipRight



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        p.IsPath ∧
          rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
          (∀ z ∈ p.support,
            rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧
          ∀ {f g : Site 2}, s(f, g) ∈ p.edges →
            s(rlc_dualReflect f, rlc_dualReflect g) ∈
              rlc_reflectedPathEdges gamma'.1 := by
  rcases L.positiveAxisAllWallRun_reachableRight_or_nonnegativePath
      hfaith hrun huPos with hright | hpath
  · exact Or.inl hright
  · right
    obtain ⟨A, p, hpPath, hAzero, hALeft, hpWall,
      hpNoRight, hpNonneg⟩ := hpath
    refine ⟨A, p, hpPath, hAzero, hALeft, hpNoRight, ?_⟩
    intro f g hfg
    exact rlc_nonnegative_wallPath_edge_reflectedLeft
      hfaith p hpWall hpNoRight hpNonneg hfg



theorem rlc_pathSuffix_closed_under_pathEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (hxSuffix : x ∈ (W.dropUntil z hz).support) (hxNe : x ≠ z)
    (hxy : s(x, y) ∈ W.edges) :
    y ∈ (W.dropUntil z hz).support := by
  classical
  have hsplit : (W.takeUntil z hz).append (W.dropUntil z hz) = W :=
    W.take_spec hz
  have hxySplit : s(x, y) ∈
      ((W.takeUntil z hz).append (W.dropUntil z hz)).edges := by
    rwa [hsplit]
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at hxySplit
  rcases hxySplit with hxyPrefix | hxySuffix
  · have hxPrefix :=
      (W.takeUntil z hz).fst_mem_support_of_mem_edges hxyPrefix
    have hsplitPath :
        ((W.takeUntil z hz).append (W.dropUntil z hz)).IsPath := by
      rwa [hsplit]
    exact False.elim ((hsplitPath.ne_of_mem_support_of_append
      hxNe hxPrefix hxSuffix) rfl)
  · exact (W.dropUntil z hz).snd_mem_support_of_mem_edges hxySuffix



theorem rlc_walk_end_mem_pathSuffix_of_avoid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (q : G.Walk x y)
    (hxSuffix : x ∈ (W.dropUntil z hz).support)
    (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
    (hqAvoid : z ∉ q.support) :
    y ∈ (W.dropUntil z hz).support := by
  induction q with
  | nil => exact hxSuffix
  | @cons x v y hxv q ih =>
      have hxNe : x ≠ z := by
        intro hxz
        apply hqAvoid
        simp [hxz]
      have hxvEdge : s(x, v) ∈ W.edges := by
        apply hqEdges
        simp
      have hvSuffix := rlc_pathSuffix_closed_under_pathEdge
        W hW hz hxSuffix hxNe hxvEdge
      apply ih hvSuffix
      · intro e he
        apply hqEdges e
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr he
      · intro hzq
        apply hqAvoid
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr hzq



theorem rlc_walk_end_mem_pathSuffix_iff_of_avoid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (q : G.Walk x y)
    (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
    (hqAvoid : z ∉ q.support) :
    x ∈ (W.dropUntil z hz).support ↔
      y ∈ (W.dropUntil z hz).support := by
  constructor
  · intro hx
    exact rlc_walk_end_mem_pathSuffix_of_avoid
      W hW hz q hx hqEdges hqAvoid
  · intro hy
    apply rlc_walk_end_mem_pathSuffix_of_avoid
      W hW hz q.reverse hy
    · intro e he
      apply hqEdges e
      simpa [SimpleGraph.Walk.edges_reverse] using he
    · intro hzq
      apply hqAvoid
      simpa [SimpleGraph.Walk.support_reverse] using hzq



theorem rlc_walk_all_positive_or_last_nonpositive_decomp
    {V : Type*} {G : SimpleGraph V} (f : V → Int)
    {x y : V} (w : G.Walk x y) (hy : 0 < f y) :
    (∀ z ∈ w.support, 0 < f z) ∨
      ∃ (a b : V) (p : G.Walk x a) (r : G.Walk b y)
        (hab : G.Adj a b),
        f a ≤ 0 ∧
          0 < f b ∧
          (∀ z ∈ r.support, 0 < f z) ∧
          w = p.append (.cons hab r) := by
  induction w with
  | nil =>
      left
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hy
  | @cons a b y hab t ih =>
      rcases ih hy with hall | ⟨c, d, p, r, hcd,
        hcNonpos, hdPos, hrPos, hdecomp⟩
      · by_cases haPos : 0 < f a
        · left
          intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          exact hz.elim (fun h => h ▸ haPos) (hall z)
        · right
          refine ⟨a, b, .nil, t, hab, by omega, ?_, hall, by simp⟩
          exact hall b t.start_mem_support
      · right
        refine ⟨c, d, .cons hab p, r, hcd,
          hcNonpos, hdPos, hrPos, ?_⟩
        rw [hdecomp]
        rfl



theorem rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges tau) :
    e ∈ (rlc_ambientCrossingWalk tau).edges := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  let p : ((hypercubicLattice 2).induce (rect a b c d)).Walk _ _ :=
    tau.2.2.1
  change e ∈ (p.map hom).edges
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  rw [rlc_pathEdges, Finset.mem_image] at he
  obtain ⟨f, hf, hfe⟩ := he
  exact ⟨f, by simpa [p] using hf, by simpa [hom] using hfe⟩


theorem rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_reflectedPathEdges tau) :
    e ∈ ((rlc_ambientCrossingWalk tau).map
      rlc_flipXLatticeHom).edges := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨f, hf, hfe⟩ := he
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  exact ⟨f,
    rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges tau hf,
    hfe⟩


theorem rlc_reflectedAmbientCrossingWalk_isPath
    {a b c d : Int} (tau : RlcCrossingPath a b c d) :
    ((rlc_ambientCrossingWalk tau).map
      rlc_flipXLatticeHom).IsPath := by
  apply (rlc_ambientCrossingWalk tau).map_isPath_of_injective
  · exact rlc_flipX.injective
  · exact rlc_ambientCrossingWalk_isPath tau




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (z : Site 2)
        (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support)
        (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          p.IsPath ∧
          (∀ x ∈ p.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support := by
  rcases L.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath
      hfaith hrun huPos with hright | hpath
  · exact Or.inl hright
  · right
    obtain ⟨A, p, hpPath, hAzero, hALeft,
      hpNoRight, hpReflectedLeft⟩ := hpath
    obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
      rlc_bookFirstFlippedTraceIntersection_of_faithful
        gamma gamma' hfaith
    let W := (rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom
    have hflipZWL : rlc_flipX z ∈
        (rlc_ambientCrossingWalk gamma'.1).support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX z)).2 hzLeft
    have hzW : z ∈ W.support := by
      change z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨rlc_flipX z, hflipZWL, ?_⟩
      exact rlc_flipX_involutive z
    let hDual :
        rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
          hypercubicLattice 2 := {
      toFun := rlc_dualReflect
      map_rel' := fun {f g} hfg =>
        (rlc_adj_dualReflect f g).mp hfg.1.1
    }
    let q : (hypercubicLattice 2).Walk
        (rlc_dualReflect A) (rlc_dualReflect u) := p.map hDual
    have hqEdges : ∀ e ∈ q.edges, e ∈ W.edges := by
      intro e he
      change e ∈ (p.map hDual).edges at he
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      induction e0 using Sym2.inductionOn with
      | _ f g =>
          apply rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma'.1
          exact hpReflectedLeft he0
    have hqAvoid : z ∉ q.support := by
      intro hzq
      change z ∈ (p.map hDual).support at hzq
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
      obtain ⟨x, hxP, hxz⟩ := hzq
      change rlc_dualReflect x = z at hxz
      exact hpNoRight x hxP (by simpa [hxz] using hzRight)
    have hAZero : (rlc_dualReflect A) 0 = 0 := by
      rw [hAzero]
      rfl
    have hAEnd := hfaith.left_axis_unique hALeft hAZero
    have hupperFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
      rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
    have hAInSuffix : rlc_dualReflect A ∈
        (W.dropUntil z hzW).support := by
      rw [hAEnd]
      have hend : rlc_flipX (gamma'.1.2.1 : Site 2) ∈
          (W.dropUntil z hzW).support :=
        (W.dropUntil z hzW).end_mem_support
      rw [hupperFlip] at hend
      exact hend
    have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
        hzW q hAInSuffix hqEdges hqAvoid
    exact ⟨z, hzW, A, p, hzRight, hzLeft, hpPath,
      hpNoRight, huSuffix⟩



def RlcCentralFacePositiveReflectedLeftAxisSuffixAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u : Site 2) : Prop :=
  ∃ (c : Site 2)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u),
    rlc_dualReflect c = (gamma'.1.2.1 : Site 2) ∧
      (∀ x ∈ q.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1



def RlcCentralFacePositiveStrictWallEntryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A a b : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      ¬ r.Nil




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveReflectedLeftAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  obtain ⟨A0, hfirstA0, _hA0first, hA0zero, _hA0class⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  have hA0A : A0 = A := by
    apply rlc_dualReflect.injective
    exact hA0zero.trans hAzero.symm
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := by
    simpa [hA0A] using hfirstA0
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace x := by
    exact hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hright : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hx, hxRight⟩ := hright
    exact ⟨x, reach_of_mem_r x hx, hxRight⟩
  · push Not at hright
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => (rlc_dualReflect x) 0) r huPos with
      hallPos | ⟨c, d, pr, s, hcd, hcNonpos, hdPos,
        hsPos, hrDecomp⟩
    · right; right
      refine ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
        hallPos, hright, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonnegative_wallPath_edge_reflectedLeft
        hfaith r hrWall hright
          (fun x hx => le_of_lt (hallPos x hx)) hfg
    · have hcdR : s(c, d) ∈ r.edges := by
        rw [hrDecomp, SimpleGraph.Walk.edges_append]
        simp
      have hcdWall : s(rlc_dualReflect c, rlc_dualReflect d) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
        simpa [Sym2.map_mk] using hrWall _ hcdR
      have hcdTarget : (hypercubicLattice 2).Adj
          (rlc_dualReflect c) (rlc_dualReflect d) :=
        (rlc_adj_dualReflect c d).mp hcd.1.1
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcdTarget
        omega
      have hcBarrier : rlc_dualReflect c ∈
          rlc_connectorBarrier gamma gamma' :=
        rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hcdWall (Sym2.mem_mk_left _ _)
      have hcEq : rlc_dualReflect c =
          (![0, (rlc_dualReflect c) 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hcZero]
      rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma'
          ((rlc_dualReflect c) 1)).1 (by
            rwa [← hcEq]) with hcRight | hcLeft
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by
          rwa [hcEq]⟩
      · right; left
        let q : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have hqSupport : ∀ x ∈ q.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have hqNoRight : ∀ x ∈ q.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1 := by
          intro x hx
          exact hright x (hqSupport x hx)
        have hqWall : ∀ e ∈ q.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have hqNonneg : ∀ x ∈ q.support,
            0 ≤ (rlc_dualReflect x) 0 := by
          intro x hx
          simp only [q, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero.symm
          · exact le_of_lt (hsPos x hx)
        have hcLeft' : rlc_dualReflect c ∈
            rlc_pathVertices gamma'.1 := by
          rwa [hcEq]
        have hcEnd := hfaith.left_axis_unique hcLeft' hcZero
        refine ⟨c, q, hcEnd, hqNoRight, ?_⟩
        intro f g hfg
        exact rlc_nonnegative_wallPath_edge_reflectedLeft
          hfaith q hqWall hqNoRight hqNonneg hfg




theorem rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {c u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u)
    (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
    (hqNoRight : ∀ x ∈ q.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
    (hqReflectedLeft : ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma'.1) :
    ∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).dropUntil z hz).support := by
  obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  have hflipZWL : rlc_flipX z ∈
      (rlc_ambientCrossingWalk gamma'.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  have hzW : z ∈ W.support := by
    change z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_flipX z, hflipZWL, rlc_flipX_involutive z⟩
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect c) (rlc_dualReflect u) := q.map hDual
  have hqDualEdges : ∀ e ∈ qDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (q.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        apply rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma'.1
        exact hqReflectedLeft he0
  have hqDualAvoid : z ∉ qDual.support := by
    intro hzq
    change z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = z at hxz
    exact hqNoRight x hxQ (by simpa [hxz] using hzRight)
  have hupperFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil z hzW).support := by
    rw [hcEnd]
    have hend : rlc_flipX (gamma'.1.2.1 : Site 2) ∈
        (W.dropUntil z hzW).support :=
      (W.dropUntil z hzW).end_mem_support
    rw [hupperFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨z, hzW, hzRight, hzLeft, huSuffix⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ (z : Site 2)
        (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) ∨
      RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  rcases L.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry
      hfaith hrun huPos with hright | haxis | hstrict
  · exact Or.inl hright
  · right; left
    obtain ⟨c, q, hcEnd, hqNoRight, hqLeft⟩ := haxis
    exact rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix
      hfaith q hcEnd hqNoRight hqLeft
  · exact Or.inr (Or.inr hstrict)



theorem rlc_nonpositive_wallPath_edge_reflectedRight
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hpNoLeft : ∀ z ∈ p.support,
      rlc_dualReflect z ∉ rlc_pathVertices gamma'.1)
    (hpNonpos : ∀ z ∈ p.support, (rlc_dualReflect z) 0 ≤ 0)
    {f g : Site 2} (hfg : s(f, g) ∈ p.edges) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_reflectedPathEdges gamma.1 := by
  have hfP := p.fst_mem_support_of_mem_edges hfg
  have hgP := p.snd_mem_support_of_mem_edges hfg
  have hfNonpos := hpNonpos f hfP
  have hgNonpos := hpNonpos g hgP
  have hfgWall : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.map_mk] using hpWall _ hfg
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp (p.adj_of_mem_edges hfg).1.1
  have hsomeNeg : (rlc_dualReflect f) 0 < 0 ∨
      (rlc_dualReflect g) 0 < 0 := by
    by_contra hnot
    push Not at hnot
    have hfZero : (rlc_dualReflect f) 0 = 0 := by omega
    have hgZero : (rlc_dualReflect g) 0 = 0 := by omega
    rcases face_adj_dir hfgAdj with hg | hg | hg | hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect g) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect g) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect g) 1]) := by
        rw [Sym2.eq_iff]
        left
        constructor <;> ext i <;> fin_cases i <;> simp_all
      rwa [← hedge]
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect f) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect f) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect f) 1]) := by
        rw [Sym2.eq_iff]
        right
        constructor <;> ext i <;> fin_cases i <;> simp_all
      rwa [← hedge]
  rcases hsomeNeg with hfNeg | hgNeg
  · have hfNotRight : rlc_dualReflect f ∉
        rlc_pathVertices gamma.1 := by
      intro hfRight
      have hfRect := rlc_pathVertex_mem_rect gamma.1 hfRight
      rw [mem_rect] at hfRect
      omega
    have hfNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect f = rlc_flipX z := by
      rintro ⟨z, hz, hfz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hfz
      change (rlc_dualReflect f) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_left _ _)
        hfNotRight (hpNoLeft f hfP) hfNotFlipLeft
  · have hgNotRight : rlc_dualReflect g ∉
        rlc_pathVertices gamma.1 := by
      intro hgRight
      have hgRect := rlc_pathVertex_mem_rect gamma.1 hgRight
      rw [mem_rect] at hgRect
      omega
    have hgNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect g = rlc_flipX z := by
      rintro ⟨z, hz, hgz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hgz
      change (rlc_dualReflect g) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_right _ _)
        hgNotRight (hpNoLeft g hgP) hgNotFlipLeft



def RlcCentralFaceNegativeReflectedRightAxisSuffixAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u : Site 2) : Prop :=
  ∃ (c : Site 2)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u),
    rlc_dualReflect c = (gamma.1.1 : Site 2) ∧
      (∀ x ∈ q.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma'.1) ∧
      ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma.1



def RlcCentralFaceNegativeStrictWallEntryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A a b : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma'.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma.1) ∧
      ¬ r.Nil


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeReflectedRightAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  obtain ⟨A0, hfirstA0, _hA0first, hA0zero, _hA0class⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  have hA0A : A0 = A := by
    apply rlc_dualReflect.injective
    exact hA0zero.trans hAzero.symm
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := by
    simpa [hA0A] using hfirstA0
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace x := by
    exact hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hleft : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma'.1
  · left
    obtain ⟨x, hx, hxLeft⟩ := hleft
    exact ⟨x, reach_of_mem_r x hx, hxLeft⟩
  · push Not at hleft
    have huNeg' : 0 < -(rlc_dualReflect u) 0 := by omega
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => -(rlc_dualReflect x) 0) r huNeg' with
      hallNeg | ⟨c, d, pr, s, hcd, hcNonneg, hdNeg,
        hsNeg, hrDecomp⟩
    · right; right
      have hallNeg' : ∀ x ∈ r.support,
          (rlc_dualReflect x) 0 < 0 := by
        intro x hx
        have := hallNeg x hx
        omega
      refine ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
        hallNeg', hleft, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonpositive_wallPath_edge_reflectedRight
        hfaith r hrWall hleft
          (fun x hx => le_of_lt (hallNeg' x hx)) hfg
    · have hcdR : s(c, d) ∈ r.edges := by
        rw [hrDecomp, SimpleGraph.Walk.edges_append]
        simp
      have hcdWall : s(rlc_dualReflect c, rlc_dualReflect d) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
        simpa [Sym2.map_mk] using hrWall _ hcdR
      have hcdTarget : (hypercubicLattice 2).Adj
          (rlc_dualReflect c) (rlc_dualReflect d) :=
        (rlc_adj_dualReflect c d).mp hcd.1.1
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcdTarget
        omega
      have hcBarrier : rlc_dualReflect c ∈
          rlc_connectorBarrier gamma gamma' :=
        rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hcdWall (Sym2.mem_mk_left _ _)
      have hcEq : rlc_dualReflect c =
          (![0, (rlc_dualReflect c) 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hcZero]
      rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma'
          ((rlc_dualReflect c) 1)).1 (by
            rwa [← hcEq]) with hcRight | hcLeft
      · right; left
        let q : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have hqSupport : ∀ x ∈ q.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have hqNoLeft : ∀ x ∈ q.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma'.1 := by
          intro x hx
          exact hleft x (hqSupport x hx)
        have hqWall : ∀ e ∈ q.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have hqNonpos : ∀ x ∈ q.support,
            (rlc_dualReflect x) 0 ≤ 0 := by
          intro x hx
          simp only [q, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero
          · have := hsNeg x hx
            omega
        have hcRight' : rlc_dualReflect c ∈
            rlc_pathVertices gamma.1 := by
          rwa [hcEq]
        have hcStart := hfaith.right_axis_unique hcRight' hcZero
        refine ⟨c, q, hcStart, hqNoLeft, ?_⟩
        intro f g hfg
        exact rlc_nonpositive_wallPath_edge_reflectedRight
          hfaith q hqWall hqNoLeft hqNonpos hfg
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩




theorem rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {c u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u)
    (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
    (hqNoLeft : ∀ x ∈ q.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
    (hqReflectedRight : ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma.1) :
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          ((((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).dropUntil
              (rlc_flipX z) hz).support := by
  obtain ⟨z, hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have hzMapped : rlc_flipX z ∈
      ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzWR, rfl⟩
  have hzW : rlc_flipX z ∈ W.support := by
    simpa [W, SimpleGraph.Walk.support_reverse] using hzMapped
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect c) (rlc_dualReflect u) := q.map hDual
  have hqDualEdges : ∀ e ∈ qDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (q.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        have hforward :=
          rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma.1 (hqReflectedRight he0)
        simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hqDualAvoid : rlc_flipX z ∉ qDual.support := by
    intro hzq
    change rlc_flipX z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = rlc_flipX z at hxz
    exact hqNoLeft x hxQ (by simpa [hxz] using hzLeft)
  have hlowerFlip : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil (rlc_flipX z) hzW).support := by
    rw [hcStart]
    have hend : rlc_flipX (gamma.1.1 : Site 2) ∈
        (W.dropUntil (rlc_flipX z) hzW).support :=
      (W.dropUntil (rlc_flipX z) hzW).end_mem_support
    rw [hlowerFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨z, hzW, hzRight, hzLeft, huSuffix⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      (∃ (z : Site 2)
        (hz : rlc_flipX z ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) ∨
      RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  rcases L.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry
      hfaith hrun huNeg with hleft | haxis | hstrict
  · exact Or.inl hleft
  · right; left
    obtain ⟨c, q, hcStart, hqNoLeft, hqRight⟩ := haxis
    exact rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix
      hfaith q hcStart hqNoLeft hqRight
  · exact Or.inr (Or.inr hstrict)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictReflectedBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          0 < (rlc_dualReflect z) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect z = rlc_flipX w) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          (rlc_dualReflect z) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect z = rlc_flipX w := by
  obtain ⟨z, hzReach, hzBarrier⟩ :=
    rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu huBoundary
  rcases rlc_connectorBarrier_original_or_strict_reflected
      gamma gamma' hzBarrier with
    hzRight | hzLeft | hzFlipLeft | hzFlipRight
  · exact Or.inl ⟨z, hzReach, hzRight⟩
  · exact Or.inr (Or.inl ⟨z, hzReach, hzLeft⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨z, hzReach, hzFlipLeft⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨z, hzReach, hzFlipRight⟩))


def RlcCentralFaceStrictReflectedBarrierResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ z : Site 2,
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace z ∧
      ((0 < (rlc_dualReflect z) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect z = rlc_flipX w) ∨
        ((rlc_dualReflect z) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect z = rlc_flipX w))



def RlcCentralFaceStrictSurgeryResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u u' : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u ∨
    RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u' ∨
    RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L := by
  rcases L.boxBoundary_reachableContacts_or_strictReflectedBarrier
      hfaith hu huBoundary with hright | hleft | hpos | hneg
  · exact Or.inl hright
  · exact Or.inr (Or.inl hleft)
  · right; right
    obtain ⟨z, hzReach, hzPos, w, hw, hzw⟩ := hpos
    exact ⟨z, hzReach, Or.inl ⟨hzPos, w, hw, hzw⟩⟩
  · right; right
    obtain ⟨z, hzReach, hzNeg, w, hw, hzw⟩ := hneg
    exact ⟨z, hzReach, Or.inr ⟨hzNeg, w, hw, hzw⟩⟩



theorem rlc_positiveStrictWallEntry_firstIntersection_sameSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        rlc_dualReflect u ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        (rlc_dualReflect b ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support ↔
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hnonwall,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  have hflipZWL : rlc_flipX z ∈
      (rlc_ambientCrossingWalk gamma'.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  have hzW : z ∈ W.support := by
    change z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_flipX z, hflipZWL, rlc_flipX_involutive z⟩
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        exact rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma'.1 (hrLeft he0)
  have hrDualAvoid : z ∉ rDual.support := by
    intro hzq
    change z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxR, hxz⟩ := hzq
    change rlc_dualReflect x = z at hxz
    exact hrNoRight x hxR (by simpa [hxz] using hzRight)
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(b, r.snd), hfirstEdge, ?_⟩
      rfl)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(r.penultimate, u), hlastEdge, ?_⟩
      rfl)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨z, hzW, b, hzRight, hzLeft, hbW, huW, hsame⟩



theorem rlc_negativeStrictWallEntry_firstIntersection_sameSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        (rlc_dualReflect b ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support ↔
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hnonwall,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  obtain ⟨z, hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have hzMapped : rlc_flipX z ∈
      ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzWR, rfl⟩
  have hzW : rlc_flipX z ∈ W.support := by
    simpa [W, SimpleGraph.Walk.support_reverse] using hzMapped
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        have hforward :=
          rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma.1 (hrRight he0)
        simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hrDualAvoid : rlc_flipX z ∉ rDual.support := by
    intro hzq
    change rlc_flipX z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxR, hxz⟩ := hzq
    change rlc_dualReflect x = rlc_flipX z at hxz
    exact hrNoLeft x hxR (by simpa [hxz] using hzLeft)
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(b, r.snd), hfirstEdge, ?_⟩
      rfl)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(r.penultimate, u), hlastEdge, ?_⟩
      rfl)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨z, hzW, b, hzRight, hzLeft, hbW, huW, hsame⟩



theorem rlc_positiveStrictWallEntry_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hentry : RlcCentralFacePositiveStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (a b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧
        s(rlc_dualReflect a, rlc_dualReflect b) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect a ∈ rlc_connectorBox n ∧
        rlc_dualReflect b ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hnonwall,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  refine ⟨a, b, hab, hnonwall, ?_⟩
  rcases hab.2 with hwall | hregion
  · exact False.elim (hnonwall hwall)
  · exact hregion


theorem rlc_negativeStrictWallEntry_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hentry : RlcCentralFaceNegativeStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (a b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧
        s(rlc_dualReflect a, rlc_dualReflect b) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect a ∈ rlc_connectorBox n ∧
        rlc_dualReflect b ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hnonwall,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  refine ⟨a, b, hab, hnonwall, ?_⟩
  rcases hab.2 with hwall | hregion
  · exact False.elim (hnonwall hwall)
  · exact hregion



def RlcCentralFacePositiveStrictCarrierSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v : Site 2) : Prop :=
  RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u ∧
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v


def RlcCentralFaceNegativeStrictCarrierSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u ∧
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v


def RlcCentralFaceStrictCarrierSurgeryResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v u' v' : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictCarrierSurgeryAt
      gamma gamma' rho L u v ∨
    RlcCentralFacePositiveStrictCarrierSurgeryAt
      gamma gamma' rho L u' v' ∨
    RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L



def RlcCentralFaceNegativeWallRunDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append q = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect u = rlc_flipX w



def RlcCentralFacePositiveWallRunDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hanchor : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj L.boundary.firstFace L.boundary.secondFace)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append (.cons hanchor q) = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRunDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hresidue : RlcCentralFaceNegativeBadExitResidue
      gamma gamma' rho u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      RlcCentralFaceNegativeWallRunDecompAt gamma gamma' rho L q := by
  obtain ⟨A, hfirstA, hAfirst, hAzero, hleft | hAoff⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  · exact Or.inl ⟨A, hfirstA, hleft⟩
  rcases hresidue with hboundary | ⟨w, hw, huw, hallIncoming⟩
  · exact Or.inr (Or.inl hboundary)
  · obtain ⟨pA⟩ := hAfirst
    let Q := pA.append q
    let P : Sym2 (Site 2) → Prop := fun e =>
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
    rcases rlc_walk_all_edges_or_last_failure_decomp P Q with
      hall | ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
    · exfalso
      have hANeU : A ≠ u := by
        intro hAu
        have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
          congrArg rlc_dualReflect hAu
        have h0 := congrArg (fun z : Site 2 => z 0) hreflect
        rw [hAzero] at h0
        simp only [Matrix.cons_val_zero] at h0
        omega
      have hQNotNil : ¬ Q.Nil := Q.not_nil_of_ne hANeU
      have hfirstEdge := Q.mk_start_snd_mem_edges hQNotNil
      have hfirstWall := hall _ hfirstEdge
      have hAbarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hfirstWall (by
          change rlc_dualReflect A ∈
            Sym2.map rlc_dualReflect s(A, Q.snd)
          simp [Sym2.map_mk])
      exact hAoff hAbarrier
    · have hrNotNil : ¬ r.Nil := by
        intro hrNil
        have hbu : b = u := hrNil.eq
        subst b
        have hav : a ≠ v := by
          intro hav
          subst a
          apply hbad
          exact (rlc_reflectedEdgeCarrierGeometry_comm
            gamma gamma' v u).1 hab.2
        have hauWall := hallIncoming a hab hav
        apply hnotWall
        simpa [P, Sym2.map_mk] using hauWall
      exact Or.inr (Or.inr ⟨A, a, b, pA, p, r, hab,
        by simpa [Q] using hdecomp, hAzero, hAoff,
        by simpa [P, Sym2.map_mk] using hnotWall,
        hrWall, hrNotNil, w, hw, huw⟩)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_wallRunDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hresidue : RlcCentralFacePositiveBadExitResidue
      gamma gamma' rho u v) :
    ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u ∨
      RlcCentralFacePositiveWallRunDecompAt gamma gamma' rho L q := by
  rcases hresidue with hboundary | ⟨w, hw, huw, hallIncoming⟩
  · exact Or.inl hboundary
  · obtain ⟨A, hfirstA, hAfirst, hAzero, hstart⟩ :=
      rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
        L.boundary hfaith
    obtain ⟨pA⟩ := hAfirst
    let hanchor := L.boundary.anchor_mem_goodBoundaryGraph hfaith
    let Q := pA.append (.cons hanchor q)
    let P : Sym2 (Site 2) → Prop := fun e =>
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
    rcases rlc_walk_all_edges_or_last_failure_decomp P Q with
      hall | ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
    · rcases hstart with hleft | hAoff
      · exact Or.inr (Or.inl ⟨A, Q, hAzero, hleft, hall,
          w, hw, huw⟩)
      · exfalso
        have hANeU : A ≠ u := by
          intro hAu
          have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
            congrArg rlc_dualReflect hAu
          have h0 := congrArg (fun z : Site 2 => z 0) hreflect
          rw [hAzero] at h0
          simp only [Matrix.cons_val_zero] at h0
          omega
        have hQNotNil : ¬ Q.Nil := Q.not_nil_of_ne hANeU
        have hfirstEdge := Q.mk_start_snd_mem_edges hQNotNil
        have hfirstWall := hall _ hfirstEdge
        have hAbarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hfirstWall (by
            change rlc_dualReflect A ∈
              Sym2.map rlc_dualReflect s(A, Q.snd)
            simp [Sym2.map_mk])
        exact hAoff hAbarrier
    · have hrNotNil : ¬ r.Nil := by
        intro hrNil
        have hbu : b = u := hrNil.eq
        subst b
        have hav : a ≠ v := by
          intro hav
          subst a
          apply hbad
          exact (rlc_reflectedEdgeCarrierGeometry_comm
            gamma gamma' v u).1 hab.2
        have hauWall := hallIncoming a hab hav
        apply hnotWall
        simpa [P, Sym2.map_mk] using hauWall
      exact Or.inr (Or.inr ⟨A, a, b, pA, p, r, hanchor, hab,
        by simpa [Q] using hdecomp, hAzero, hstart,
        by simpa [P, Sym2.map_mk] using hnotWall,
        hrWall, hrNotNil, w, hw, huw⟩)



def RlcCentralFacePositiveStrictWallEntryDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hanchor : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj L.boundary.firstFace L.boundary.secondFace)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append (.cons hanchor q) = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      ¬ r.Nil



def RlcCentralFaceNegativeStrictWallEntryDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append q = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma'.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma.1) ∧
      ¬ r.Nil



theorem RlcCentralFaceNegativeStrictWallEntryDecompAt.nonwallGoodContourEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    ∃ f g : Site 2,
      s(f, g) ∈ L.boundary.contour.edges ∧
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨_A, a, b, _pA, _p, _r, hab, _hdecomp, _hAzero,
    _hAoff, hentryNot, _hrNeg, _hrNoLeft, _hrRight,
    _hrNotNil⟩ := hentry
  refine ⟨a, b, L.boundary.contour_covers s(a, b) ?_, hab.2,
    hentryNot⟩
  rw [SimpleGraph.mem_edgeSet]
  exact hab.1




def RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (f g : Site 2) : Prop :=
  s(f, g) ∈ B.contour.edges ∧
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
    s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    ((∀ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
          ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable f x ∧
          ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable g x) ∨
      ∃ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable f x ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable g x ∧
        ∀ y : Site 2,
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
            ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable f y ∧
            ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable g y)



theorem rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hfgContour : s(f, g) ∈ B.contour.edges)
    (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g)
    (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence B f g := by
  have hfgBoundary : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g :=
    B.contour.adj_of_mem_edges hfgContour
  have hfgGood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj f g := ⟨hfgBoundary, hcarrier⟩
  have hfgReach := hfgGood.reachable
  by_cases hgood : RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho
  · exact Or.inl hgood
  right
  refine ⟨hfgContour, hcarrier, hnonwall, ?_⟩
  by_cases hright : ∃ x : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable f x
  · right
    obtain ⟨x, hxRight, hfx⟩ := hright
    refine ⟨x, hxRight, hfx, hfgReach.symm.trans hfx, ?_⟩
    intro y hyLeft
    constructor
    · intro hfy
      exact hgood ⟨x, y, hfx.symm.trans hfy, hxRight, hyLeft⟩
    · intro hgy
      have hfy := hfgReach.trans hgy
      exact hgood ⟨x, y, hfx.symm.trans hfy, hxRight, hyLeft⟩
  · left
    intro x hxRight
    constructor
    · intro hfx
      exact hright ⟨x, hxRight, hfx⟩
    · intro hgx
      exact hright ⟨x, hxRight, hfgReach.trans hgx⟩



def RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (f g : Site 2) : Prop :=
  s(f, g) ∈ B.contour.edges ∧
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
    s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace f ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace g ∧
    ((∀ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
          ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable B.firstFace x) ∨
      ∃ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace x ∧
        ∀ y : Site 2,
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
            ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace y)



theorem RlcCentralFaceNegativeStrictWallEntryDecompAt.anchoredNonwallGoodContourEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    ∃ f g : Site 2,
      s(f, g) ∈ L.boundary.contour.edges ∧
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace f ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace g := by
  obtain ⟨_A, a, b, pA, p, _r, hab, _hdecomp, _hAzero,
    _hAoff, hentryNot, _hrNeg, _hrNoLeft, _hrRight,
    _hrNotNil⟩ := hentry
  have haReach : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace a :=
    ⟨pA.reverse.append p⟩
  refine ⟨a, b, L.boundary.contour_covers s(a, b) ?_, hab.2,
    hentryNot, haReach, haReach.trans hab.reachable⟩
  rw [SimpleGraph.mem_edgeSet]
  exact hab.1



theorem rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hfgContour : s(f, g) ∈ B.contour.edges)
    (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g)
    (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hfirstF : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace f)
    (hfirstG : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace g) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
        B f g := by
  by_cases hright : ∃ x : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace x
  · obtain ⟨x, hxRight, hfirstX⟩ := hright
    by_cases hleft : ∃ y : Site 2,
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace y
    · obtain ⟨y, hyLeft, hfirstY⟩ := hleft
      exact Or.inl ⟨x, y, hfirstX.symm.trans hfirstY, hxRight, hyLeft⟩
    · right
      refine ⟨hfgContour, hcarrier, hnonwall, hfirstF, hfirstG,
        Or.inr ⟨x, hxRight, hfirstX, ?_⟩⟩
      intro y hyLeft hfirstY
      exact hleft ⟨y, hyLeft, hfirstY⟩
  · right
    refine ⟨hfgContour, hcarrier, hnonwall, hfirstF, hfirstG,
      Or.inl ?_⟩
    intro x hxRight hfirstX
    exact hright ⟨x, hxRight, hfirstX⟩



def RlcCentralFaceRetainedAnchorTraceIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace x ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∧
    ∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace y ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1



theorem rlc_goodComponentContacts_of_retainedAnchorTraceIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
  obtain ⟨⟨x, hfirstX, hxRight⟩, y, hfirstY, hyLeft⟩ := hinc
  exact ⟨x, y, hfirstX.symm.trans hfirstY, hxRight, hyLeft⟩



theorem rlc_not_anchoredMissingIncidence_of_retainedAnchorTraceIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    ¬ RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
      B f g := by
  rintro ⟨_hfgContour, _hcarrier, _hnonwall, _hfirstF, _hfirstG,
    hmissing⟩
  rcases hinc with ⟨⟨x, hfirstX, hxRight⟩, y, hfirstY, hyLeft⟩
  rcases hmissing with hnoRight | ⟨_x, _hxRight, _hfirstX, hnoLeft⟩
  · exact hnoRight x hxRight hfirstX
  · exact hnoLeft y hyLeft hfirstY



theorem rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  apply rlc_centralFacePIMS_success_of_goodComponentContacts
  exact rlc_goodComponentContacts_of_retainedAnchorTraceIncidence hinc



def RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append q = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma'.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma.1) ∧
      ¬ r.Nil ∧
      ∀ x ∈ p.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma'.1



def RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hanchor : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj L.boundary.firstFace L.boundary.secondFace)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append (.cons hanchor q) = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      ¬ r.Nil ∧
      ∀ x ∈ p.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1



theorem rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  by_cases hcontact : ∃ y ∈ p.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1
  · left
    obtain ⟨y, hyP, hyPath⟩ := hcontact
    exact ⟨y, ⟨pA.reverse.append (p.takeUntil y hyP)⟩, hyPath⟩
  · right
    refine ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
      hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil, ?_⟩
    intro y hyP hyPath
    exact hcontact ⟨y, hyP, hyPath⟩



theorem rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.secondFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  by_cases hcontact : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hxP, hxPath⟩ := hcontact
    exact ⟨x, ⟨hanchor.symm.toWalk.append
      (pA.reverse.append (p.takeUntil x hxP))⟩, hxPath⟩
  · right
    refine ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
      hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil, ?_⟩
    intro x hxP hxPath
    exact hcontact ⟨x, hxP, hxPath⟩




theorem rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') ∨
      RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q ∨
      RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q' := by
  rcases rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact
      hneg with hleft | hnegAvoid
  · rcases rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact
        hpos with hright | hposAvoid
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReachSecond, hxPath⟩ := hright
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans
          hxReachSecond
      have hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts
          gamma gamma' rho :=
        ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
      exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
        gamma gamma' rho
          (rlc_filledBoundaryContactSegment_of_goodComponentContacts
            gamma gamma' rho hcomponent)
    · exact Or.inr (Or.inr hposAvoid)
  · exact Or.inr (Or.inl hnegAvoid)




theorem rlc_centralFacePIMS_success_of_no_strictEntryPrefixAvoidance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (hnegAvoid : ¬ RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
      gamma gamma' rho L q)
    (hposAvoid : ¬ RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
      gamma gamma' rho L q') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  rcases rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance
      hfaith hneg hpos with hsuccess | hnegResidue | hposResidue
  · exact hsuccess
  · exact (hnegAvoid hnegResidue).elim
  · exact (hposAvoid hposResidue).elim

theorem rlc_positiveStrictWallEntry_of_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (h : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentry, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := h
  exact ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩

theorem rlc_negativeStrictWallEntry_of_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (h : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero,
    hAoff, hentry, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := h
  exact ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩

@[simp] theorem rlc_site_eta (x : Site 2) :
    (![x 0, x 1] : Site 2) = x := by
  exact cons_eq_site rfl rfl

@[simp] theorem rlc_site_mk_eq_site (a b : Int) (x : Site 2) :
    ((![a, b] : Site 2) = x ↔ a = x 0 ∧ b = x 1) := by
  constructor
  · intro h
    subst x
    simp
  · rintro ⟨ha, hb⟩
    exact cons_eq_site ha hb

@[simp] theorem rlc_int_self_ne_add_one (a : Int) : a ≠ a + 1 := by omega
@[simp] theorem rlc_int_self_ne_sub_one (a : Int) : a ≠ a - 1 := by omega
@[simp] theorem rlc_int_add_one_ne_self (a : Int) : a + 1 ≠ a := by omega
@[simp] theorem rlc_int_sub_one_ne_self (a : Int) : a - 1 ≠ a := by omega
@[simp] theorem rlc_int_add_two_ne_self (a : Int) : a + 1 + 1 ≠ a := by omega
@[simp] theorem rlc_int_sub_two_ne_self (a : Int) : a - 1 - 1 ≠ a := by omega
@[simp] theorem rlc_int_self_ne_add_two (a : Int) : a ≠ a + 1 + 1 := by omega
@[simp] theorem rlc_int_self_ne_sub_two (a : Int) : a ≠ a - 1 - 1 := by omega
@[simp] theorem rlc_int_sub_one_ne_add_one (a : Int) : a - 1 ≠ a + 1 := by omega
@[simp] theorem rlc_int_add_one_ne_sub_one (a : Int) : a + 1 ≠ a - 1 := by omega

@[simp] theorem rlc_flankFaces_step_right (x : Site 2) :
    flankFaces x ![x 0 + 1, x 1] =
      s((![x 0, x 1 - 1] : Site 2), x) := by
  simp [flankFaces]

@[simp] theorem rlc_flankFaces_step_left (x : Site 2) :
    flankFaces x ![x 0 - 1, x 1] =
      s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0 - 1, x 1]) := by
  simp [flankFaces] <;> omega

@[simp] theorem rlc_flankFaces_step_top (x : Site 2) :
    flankFaces x ![x 0, x 1 + 1] =
      s((![x 0 - 1, x 1] : Site 2), x) := by
  simp [flankFaces]

@[simp] theorem rlc_flankFaces_step_bottom (x : Site 2) :
    flankFaces x ![x 0, x 1 - 1] =
      s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0, x 1 - 1]) := by
  simp [flankFaces]



theorem rlc_isPath_incident_edge_eq_of_two
    {V : Type*} {G : SimpleGraph V} {start finish x y z w : V}
    (p : G.Walk start finish) (hp : p.IsPath)
    (hxy : s(x, y) ∈ p.edges) (hyz : s(y, z) ∈ p.edges)
    (hxz : x ≠ z) (hyw : s(y, w) ∈ p.edges) :
    w = x ∨ w = z := by
  have hySupport : y ∈ p.support := p.snd_mem_support_of_mem_edges hxy
  obtain ⟨i, hiy, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
  by_cases hiZero : i = 0
  · have hyStart : y = start := by
      rw [← hiy, hiZero, p.getVert_zero]
    have hxEdge : s(start, x) ∈ p.edges := by
      simpa [hyStart, Sym2.eq_swap] using hxy
    have hzEdge : s(start, z) ∈ p.edges := by
      simpa [hyStart] using hyz
    have hxSnd := hp.eq_snd_of_mem_edges hxEdge
    have hzSnd := hp.eq_snd_of_mem_edges hzEdge
    exact False.elim (hxz (hxSnd.trans hzSnd.symm))
  by_cases hiEnd : i = p.length
  · have hyEnd : y = finish := by
      rw [← hiy, hiEnd, p.getVert_length]
    have hxEdge : s(finish, x) ∈ p.edges := by
      simpa [hyEnd, Sym2.eq_swap] using hxy
    have hzEdge : s(finish, z) ∈ p.edges := by
      simpa [hyEnd] using hyz
    have hxPen := hp.eq_penultimate_of_mem_edges hxEdge
    have hzPen := hp.eq_penultimate_of_mem_edges hzEdge
    exact False.elim (hxz (hxPen.trans hzPen.symm))
  have hiLt : i < p.length := lt_of_le_of_ne hi hiEnd
  have hneighbors := hp.neighborSet_toSubgraph_internal hiZero hiLt
  have mem_neighbors {v : V} (hyv : s(y, v) ∈ p.edges) :
      v ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [SimpleGraph.Subgraph.mem_neighborSet]
    apply p.adj_toSubgraph_iff_mem_edges.mpr
    simpa [hiy] using hyv
  have hxEdge : s(y, x) ∈ p.edges := by
    simpa [Sym2.eq_swap] using hxy
  have hxN := mem_neighbors (v := x) hxEdge
  have hzN := mem_neighbors (v := z) hyz
  have hwN := mem_neighbors (v := w) hyw
  rw [hneighbors] at hxN hzN hwN
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxN hzN hwN
  rcases hxN with hxPrev | hxNext <;>
    rcases hzN with hzPrev | hzNext <;>
    rcases hwN with hwPrev | hwNext
  · exact False.elim (hxz (hxPrev.trans hzPrev.symm))
  · exact False.elim (hxz (hxPrev.trans hzPrev.symm))
  · exact Or.inl (hwPrev.trans hxPrev.symm)
  · exact Or.inr (hwNext.trans hzNext.symm)
  · exact Or.inr (hwPrev.trans hzPrev.symm)
  · exact Or.inl (hwNext.trans hxNext.symm)
  · exact False.elim (hxz (hxNext.trans hzNext.symm))
  · exact False.elim (hxz (hxNext.trans hzNext.symm))



theorem rlc_isPath_exists_other_incident_edge
    {V : Type*} {G : SimpleGraph V} {start finish b c : V}
    (p : G.Walk start finish) (hp : p.IsPath)
    (hbc : s(b, c) ∈ p.edges)
    (hbStart : b ≠ start) (hbFinish : b ≠ finish) :
    ∃ d : V, s(b, d) ∈ p.edges ∧ d ≠ c := by
  have hbSupport : b ∈ p.support := p.fst_mem_support_of_mem_edges hbc
  obtain ⟨i, hib, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbSupport
  have hiZero : i ≠ 0 := by
    intro hi0
    apply hbStart
    rw [← hib, hi0, p.getVert_zero]
  have hiEnd : i ≠ p.length := by
    intro hil
    apply hbFinish
    rw [← hib, hil, p.getVert_length]
  have hiLt : i < p.length := lt_of_le_of_ne hi hiEnd
  let prev := p.getVert (i - 1)
  let next := p.getVert (i + 1)
  have hprevMem : prev ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [hp.neighborSet_toSubgraph_internal hiZero hiLt]
    exact Set.mem_insert _ _
  have hnextMem : next ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [hp.neighborSet_toSubgraph_internal hiZero hiLt]
    exact Or.inr (Set.mem_singleton _)
  have hprevEdge : s(b, prev) ∈ p.edges := by
    apply p.adj_toSubgraph_iff_mem_edges.mp
    have := (SimpleGraph.Subgraph.mem_neighborSet
      p.toSubgraph (p.getVert i) prev).mp hprevMem
    simpa [hib] using this
  have hnextEdge : s(b, next) ∈ p.edges := by
    apply p.adj_toSubgraph_iff_mem_edges.mp
    have := (SimpleGraph.Subgraph.mem_neighborSet
      p.toSubgraph (p.getVert i) next).mp hnextMem
    simpa [hib] using this
  have hprevNext : prev ≠ next := by
    intro heq
    have hinj := hp.getVert_injOn
      (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) heq
    omega
  by_cases hcPrev : c = prev
  · exact ⟨next, hnextEdge, fun h =>
      hprevNext (hcPrev.symm.trans h.symm)⟩
  · exact ⟨prev, hprevEdge, fun h => hcPrev h.symm⟩



theorem rlc_positive_reflectedLeft_third_incident_nonwall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z w : Site 2}
    (hyPos : 0 < y 0)
    (hyNoRight : y ∉ rlc_pathVertices gamma.1)
    (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma'.1)
    (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma'.1)
    (hxz : x ≠ z)
    (hywNeX : s(y, w) ≠ s(x, y))
    (hywNeZ : s(y, w) ≠ s(y, z)) :
    s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
  intro hywWall
  have hyNoLeft : y ∉ rlc_pathVertices gamma'.1 := by
    intro hyLeft
    have hyRect := rlc_pathVertex_mem_rect gamma'.1 hyLeft
    rw [mem_rect] at hyRect
    omega
  have hyNoFlipRight : ¬ ∃ q ∈ rlc_pathVertices gamma.1,
      y = rlc_flipX q := by
    rintro ⟨q, hq, hyq⟩
    have hqRect := rlc_pathVertex_mem_rect gamma.1 hq
    rw [mem_rect] at hqRect
    have h0 := congrArg (fun a : Site 2 => a 0) hyq
    change y 0 = -q 0 at h0
    omega
  have hywLeft : s(y, w) ∈ rlc_reflectedPathEdges gamma'.1 :=
    rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hywWall (Sym2.mem_mk_left _ _)
        hyNoRight hyNoLeft hyNoFlipRight
  let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom
  have hxyW : s(x, y) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hxy
  have hyzW : s(y, z) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hyz
  have hywW : s(y, w) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hywLeft
  rcases rlc_isPath_incident_edge_eq_of_two W
      (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hxyW hyzW hxz hywW with rfl | rfl
  · exact hywNeX (by simp [Sym2.eq_swap])
  · exact hywNeZ rfl


theorem rlc_negative_reflectedRight_third_incident_nonwall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z w : Site 2}
    (hyNeg : y 0 < 0)
    (hyNoLeft : y ∉ rlc_pathVertices gamma'.1)
    (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma.1)
    (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma.1)
    (hxz : x ≠ z)
    (hywNeX : s(y, w) ≠ s(x, y))
    (hywNeZ : s(y, w) ≠ s(y, z)) :
    s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
  intro hywWall
  have hyNoRight : y ∉ rlc_pathVertices gamma.1 := by
    intro hyRight
    have hyRect := rlc_pathVertex_mem_rect gamma.1 hyRight
    rw [mem_rect] at hyRect
    omega
  have hyNoFlipLeft : ¬ ∃ q ∈ rlc_pathVertices gamma'.1,
      y = rlc_flipX q := by
    rintro ⟨q, hq, hyq⟩
    have hqRect := rlc_pathVertex_mem_rect gamma'.1 hq
    rw [mem_rect] at hqRect
    have h0 := congrArg (fun a : Site 2 => a 0) hyq
    change y 0 = -q 0 at h0
    omega
  have hywRight : s(y, w) ∈ rlc_reflectedPathEdges gamma.1 :=
    rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hywWall (Sym2.mem_mk_left _ _)
        hyNoRight hyNoLeft hyNoFlipLeft
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have toW {e : Sym2 (Site 2)}
      (he : e ∈ rlc_reflectedPathEdges gamma.1) : e ∈ W.edges := by
    have hf :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma.1 he
    simpa [W, SimpleGraph.Walk.edges_reverse] using hf
  have hxyW := toW hxy
  have hyzW := toW hyz
  have hywW := toW hywRight
  rcases rlc_isPath_incident_edge_eq_of_two W
      (rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse
      hxyW hyzW hxz hywW with rfl | rfl
  · exact hywNeX (by simp [Sym2.eq_swap])
  · exact hywNeZ rfl

set_option maxHeartbeats 800000 in



theorem rlc_centralFaceRegion_continue_consecutive_wall_flank
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z h : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hyz : (hypercubicLattice 2).Adj y z)
    (hxz : x ≠ z)
    (hyInterior : -2 * n < y 0 ∧ y 0 < 2 * n ∧
      -n < y 1 ∧ y 1 < n)
    (hother : ∀ w : Site 2,
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x y) :
    ∃ k ∈ flankFaces y z,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have sideIff {w f g : Site 2}
      (hyw : (hypercubicLattice 2).Adj y w)
      (hflank : flankFaces y w = s(f, g))
      (hneIn : s(y, w) ≠ s(x, y))
      (hneOut : s(y, w) ≠ s(y, z)) :
      (f ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        g ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    have hnot := hother w hyw hneIn hneOut
    have hf : f ∈ flankFaces y w := by
      rw [hflank, Sym2.mem_iff]
      exact Or.inl rfl
    have hg : g ∈ flankFaces y w := by
      rw [hflank, Sym2.mem_iff]
      exact Or.inr rfl
    have hfBox := rlc_flank_mem_connectorFaceBox_of_interior
      hyw hyInterior hf
    have hgBox := rlc_flank_mem_connectorFaceBox_of_interior
      hyw hyInterior hg
    constructor
    · intro hfRegion
      exact rlc_centralFaceRegion_other_flank_of_nonwall
        gamma gamma' hyw hnot hfRegion hf hg hgBox
    · intro hgRegion
      exact rlc_centralFaceRegion_other_flank_of_nonwall
        gamma gamma' hyw hnot hgRegion hg hf hfBox
  let NE : Site 2 := y
  let NW : Site 2 := ![y 0 - 1, y 1]
  let SW : Site 2 := ![y 0 - 1, y 1 - 1]
  let SE : Site 2 := ![y 0, y 1 - 1]
  have hUp : s(y, ![y 0, y 1 + 1]) ≠ s(x, y) →
      s(y, ![y 0, y 1 + 1]) ≠ s(y, z) →
      (NW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [NW, NE] using rlc_flankFaces_step_top y)
      hneIn hneOut
  have hLeft : s(y, ![y 0 - 1, y 1]) ≠ s(x, y) →
      s(y, ![y 0 - 1, y 1]) ≠ s(y, z) →
      (SW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NW ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SW, NW] using rlc_flankFaces_step_left y)
      hneIn hneOut
  have hDown : s(y, ![y 0, y 1 - 1]) ≠ s(x, y) →
      s(y, ![y 0, y 1 - 1]) ≠ s(y, z) →
      (SW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        SE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SW, SE] using rlc_flankFaces_step_bottom y)
      hneIn hneOut
  have hRight : s(y, ![y 0 + 1, y 1]) ≠ s(x, y) →
      s(y, ![y 0 + 1, y 1]) ≠ s(y, z) →
      (SE ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SE, NE] using rlc_flankFaces_step_right y)
      hneIn hneOut
  rcases face_adj_dir hxy with rfl | rfl | rfl | rfl <;>
    rcases face_adj_dir hyz with rfl | rfl | rfl | rfl
  all_goals
    simp only [rlc_flankFaces_step_right, rlc_flankFaces_step_left,
      rlc_flankFaces_step_top, rlc_flankFaces_step_bottom] at hh ⊢
    rw [Sym2.mem_iff] at hh
    simp only [Sym2.mem_iff]
    simp [NE, NW, SW, SE, Sym2.eq_iff] at hUp hLeft hDown hRight
    rcases hh with rfl | rfl <;>
      simp [NE, NW, SW, SE] at hhRegion ⊢ <;> tauto




theorem rlc_walk_terminal_regionFlank_of_consecutive_detours
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {b u : Site 2} (q : (hypercubicLattice 2).Walk b u)
    (hqNotNil : ¬ q.Nil)
    (hqInterior : ∀ y ∈ q.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n)
    (hthird : ∀ {x y z w : Site 2},
      s(x, y) ∈ q.edges → s(y, z) ∈ q.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces b q.snd) :
    ∃ k ∈ flankFaces q.penultimate u,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  induction q generalizing h with
  | nil => exact False.elim (hqNotNil SimpleGraph.Walk.nil_nil)
  | @cons a c u hac t ih =>
      cases t with
      | nil =>
          exact ⟨h, by simpa, hhRegion⟩
      | @cons c d u hcd s =>
          have hacEdge : s(a, c) ∈
              (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by simp
          have hcdEdge : s(c, d) ∈
              (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by simp
          have htailEdges : ∀ e ∈ (SimpleGraph.Walk.cons hcd s).edges,
              e ∈ (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by
            intro e he
            rw [SimpleGraph.Walk.edges_cons]
            exact List.mem_cons_of_mem _ he
          have htailSupport : ∀ y ∈
              (SimpleGraph.Walk.cons hcd s).support,
              y ∈ (SimpleGraph.Walk.cons hac (.cons hcd s)).support := by
            intro y hy
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ hy
          have htailInterior : ∀ y ∈
              (SimpleGraph.Walk.cons hcd s).support,
              -2 * n < y 0 ∧ y 0 < 2 * n ∧
                -n < y 1 ∧ y 1 < n := by
            intro y hy
            exact hqInterior y (htailSupport y hy)
          have htailThird : ∀ {x y z w : Site 2},
              s(x, y) ∈ (SimpleGraph.Walk.cons hcd s).edges →
              s(y, z) ∈ (SimpleGraph.Walk.cons hcd s).edges →
              x ≠ z → (hypercubicLattice 2).Adj y w →
              s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
              s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
            intro x y z w hxy hyz hxz hyw hneIn hneOut
            exact hthird (htailEdges _ hxy) (htailEdges _ hyz)
              hxz hyw hneIn hneOut
          have hnext : ∃ k ∈ flankFaces c d,
              k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
            by_cases had : a = d
            · subst d
              exact ⟨h, by simpa [flankFaces_comm] using hh, hhRegion⟩
            · apply rlc_centralFaceRegion_continue_consecutive_wall_flank
                gamma gamma' hac hcd had
                  (hqInterior c (by simp))
              · intro w hcw hneIn hneOut
                exact hthird hacEdge hcdEdge had hcw hneIn hneOut
              · exact hhRegion
              · exact hh
          obtain ⟨k, hkFlank, hkRegion⟩ := hnext
          exact ih (h := k) (by simp) htailInterior htailThird
            hkRegion (by simpa using hkFlank)


theorem rlc_positive_reflectedLeft_walk_terminal_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {b u : Site 2}
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk b u)
    (hrPos : ∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0)
    (hrNoRight : ∀ x ∈ r.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
    (hrLeft : ∀ {f g : Site 2}, s(f, g) ∈ r.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma'.1)
    (hrNotNil : ¬ r.Nil)
    (hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n)
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect b)
      (rlc_dualReflect r.snd)) :
    ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate)
        (rlc_dualReflect u),
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg => (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualNotNil : ¬ rDual.Nil := by
    simpa [rDual] using hrNotNil
  have hrDualInterior : ∀ y ∈ rDual.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n := by
    intro y hy
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrInterior x hx
  have hrDualPos {y : Site 2} (hy : y ∈ rDual.support) : 0 < y 0 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrPos x hx
  have hrDualNoRight {y : Site 2} (hy : y ∈ rDual.support) :
      y ∉ rlc_pathVertices gamma.1 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNoRight x hx
  have hrDualLeft {e : Sym2 (Site 2)} (he : e ∈ rDual.edges) :
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g => exact hrLeft he0
  have hrDualThird : ∀ {x y z w : Site 2},
      s(x, y) ∈ rDual.edges → s(y, z) ∈ rDual.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
    intro x y z w hxy hyz hxz hyw hneIn hneOut
    have hySupport := rDual.snd_mem_support_of_mem_edges hxy
    exact rlc_positive_reflectedLeft_third_incident_nonwall
      gamma gamma' (hrDualPos hySupport) (hrDualNoRight hySupport)
        (hrDualLeft hxy) (hrDualLeft hyz) hxz hneIn hneOut
  have hout := rlc_walk_terminal_regionFlank_of_consecutive_detours
    gamma gamma' rDual hrDualNotNil hrDualInterior hrDualThird
      hhRegion (by simpa [rDual] using hh)
  simpa [rDual] using hout


theorem rlc_negative_reflectedRight_walk_terminal_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {b u : Site 2}
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk b u)
    (hrNeg : ∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0)
    (hrNoLeft : ∀ x ∈ r.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
    (hrRight : ∀ {f g : Site 2}, s(f, g) ∈ r.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma.1)
    (hrNotNil : ¬ r.Nil)
    (hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n)
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect b)
      (rlc_dualReflect r.snd)) :
    ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate)
        (rlc_dualReflect u),
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg => (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualNotNil : ¬ rDual.Nil := by
    simpa [rDual] using hrNotNil
  have hrDualInterior : ∀ y ∈ rDual.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n := by
    intro y hy
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrInterior x hx
  have hrDualNeg {y : Site 2} (hy : y ∈ rDual.support) : y 0 < 0 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNeg x hx
  have hrDualNoLeft {y : Site 2} (hy : y ∈ rDual.support) :
      y ∉ rlc_pathVertices gamma'.1 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNoLeft x hx
  have hrDualRight {e : Sym2 (Site 2)} (he : e ∈ rDual.edges) :
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g => exact hrRight he0
  have hrDualThird : ∀ {x y z w : Site 2},
      s(x, y) ∈ rDual.edges → s(y, z) ∈ rDual.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
    intro x y z w hxy hyz hxz hyw hneIn hneOut
    have hySupport := rDual.snd_mem_support_of_mem_edges hxy
    exact rlc_negative_reflectedRight_third_incident_nonwall
      gamma gamma' (hrDualNeg hySupport) (hrDualNoLeft hySupport)
        (hrDualRight hxy) (hrDualRight hyz) hxz hneIn hneOut
  have hout := rlc_walk_terminal_regionFlank_of_consecutive_detours
    gamma gamma' rDual hrDualNotNil hrDualInterior hrDualThird
      hhRegion (by simpa [rDual] using hh)
  simpa [rDual] using hout





theorem rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {a b c d h : Site 2}
    (hba : (hypercubicLattice 2).Adj b a)
    (hbc : (hypercubicLattice 2).Adj b c)
    (hbd : (hypercubicLattice 2).Adj b d)
    (hac : a ≠ c) (hdc : d ≠ c)
    (hentryNot : s(a, b) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hbdWall : s(b, d) ∈ rlc_connectorFourTraceEdges gamma gamma')
    (hbInterior : -2 * n < b 0 ∧ b 0 < 2 * n ∧
      -n < b 1 ∧ b 1 < n)
    (hother : ∀ w : Site 2,
      (hypercubicLattice 2).Adj b w →
      s(b, w) ≠ s(d, b) → s(b, w) ≠ s(b, c) →
      s(b, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces a b) :
    ∃ k ∈ flankFaces b c,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hentryNot' : s(b, a) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.eq_swap] using hentryNot
  have hh' : h ∈ flankFaces b a := by
    simpa [flankFaces_comm] using hh
  have entryRegion {k : Site 2} (hk : k ∈ flankFaces b a) :
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
    have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
      hba hbInterior hk
    exact rlc_centralFaceRegion_other_flank_of_nonwall
      gamma gamma' hba hentryNot' hhRegion hh' hk hkBox
  by_cases hoppAC : a 0 + c 0 = 2 * b 0 ∧
      a 1 + c 1 = 2 * b 1
  · have had : a ≠ d := by
      intro had
      subst d
      exact hentryNot' hbdWall
    have hnoppAD : ¬ (a 0 + d 0 = 2 * b 0 ∧
        a 1 + d 1 = 2 * b 1) := by
      intro hoppAD
      apply hdc
      have h0 : d 0 = c 0 := by omega
      have h1 : d 1 = c 1 := by omega
      funext i
      fin_cases i
      · exact h0
      · exact h1
    obtain ⟨k, hkEntry, hkSecond⟩ :=
      rlc_incident_flank_intersection_of_not_opposite
        hba hbd had hnoppAD
    have hkRegion := entryRegion hkEntry
    exact rlc_centralFaceRegion_continue_consecutive_wall_flank
      gamma gamma' hbd.symm hbc hdc hbInterior hother
        hkRegion (by simpa [flankFaces_comm] using hkSecond)
  · obtain ⟨k, hkEntry, hkOut⟩ :=
      rlc_incident_flank_intersection_of_not_opposite
        hba hbc hac hoppAC
    exact ⟨k, hkOut, entryRegion hkEntry⟩




theorem rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace x :=
    hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n
  · right
    let c := r.snd
    have hbcSource : s(b, c) ∈ r.edges := by
      exact r.mk_start_snd_mem_edges hrNotNil
    have hbcLeft : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_reflectedPathEdges gamma'.1 := hrLeft hbcSource
    have hbcWall : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hbcLeft)
    let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom
    have hbcW : s(rlc_dualReflect b, rlc_dualReflect c) ∈ W.edges :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma'.1 hbcLeft
    have hbStart : rlc_dualReflect b ≠
        rlc_flipX (gamma'.1.1 : Site 2) := by
      intro heq
      have hbInt := hrInterior b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 =
        -(gamma'.1.1 : Site 2) 0 at h0
      have hs : (gamma'.1.1 : Site 2) 0 = -2 * n :=
        gamma'.1.1.2.2
      omega
    have hbFinish : rlc_dualReflect b ≠
        rlc_flipX (gamma'.1.2.1 : Site 2) := by
      intro heq
      have hbPos := hrPos b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 =
        -(gamma'.1.2.1 : Site 2) 0 at h0
      have hs : (gamma'.1.2.1 : Site 2) 0 = 0 :=
        gamma'.1.2.1.2.2
      omega
    obtain ⟨d, hbdW, hdc⟩ := rlc_isPath_exists_other_incident_edge
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
        hbcW hbStart hbFinish
    have hbdLeft : s(rlc_dualReflect b, d) ∈
        rlc_reflectedPathEdges gamma'.1 := by
      change s(rlc_dualReflect b, d) ∈
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).edges at hbdW
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at hbdW
      obtain ⟨e0, he0, heq⟩ := hbdW
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, rlc_ambientCrossingWalk_edge_mem_pathEdges
        gamma'.1 he0, heq⟩
    have hbdWall : s(rlc_dualReflect b, d) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hbdLeft)
    have hac : rlc_dualReflect a ≠ rlc_dualReflect c := by
      intro hac
      apply hentryNot
      simpa [hac, Sym2.eq_swap] using hbcWall
    have hbAdjC : (hypercubicLattice 2).Adj
        (rlc_dualReflect b) (rlc_dualReflect c) :=
      (rlc_adj_dualReflect b c).mp (r.adj_snd hrNotNil).1.1
    have hbAdjD : (hypercubicLattice 2).Adj (rlc_dualReflect b) d :=
      W.adj_of_mem_edges hbdW
    have hbNoRight := hrNoRight b r.start_mem_support
    have hother : ∀ w : Site 2,
        (hypercubicLattice 2).Adj (rlc_dualReflect b) w →
        s(rlc_dualReflect b, w) ≠ s(d, rlc_dualReflect b) →
        s(rlc_dualReflect b, w) ≠
          s(rlc_dualReflect b, rlc_dualReflect c) →
        s(rlc_dualReflect b, w) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
      intro w hbw hneD hneC
      exact rlc_positive_reflectedLeft_third_incident_nonwall
        gamma gamma' (hrPos b r.start_mem_support) hbNoRight
          (by simpa [Sym2.eq_swap] using hbdLeft) hbcLeft hdc hneD hneC
    have hregion : ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
      rcases hab.2 with hwall | hregion
      · exact False.elim (hentryNot hwall)
      · exact hregion.2.2
    obtain ⟨h0, hh0Region, hh0⟩ := hregion
    obtain ⟨k, hkFirst, hkRegion⟩ :=
      rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
        gamma gamma'
          ((rlc_adj_dualReflect b a).mp hab.1.1.symm)
          hbAdjC hbAdjD hac hdc hentryNot hbdWall
          (hrInterior b r.start_mem_support) hother hh0Region hh0
    obtain ⟨k', hk'Flank, hk'Region⟩ :=
      rlc_positive_reflectedLeft_walk_terminal_regionFlank
        r hrPos hrNoRight hrLeft hrNotNil hrInterior hkRegion
          (by simpa [c] using hkFirst)
    refine ⟨r.penultimate, k', r.adj_penultimate hrNotNil, ?_,
      hk'Region, hk'Flank⟩
    exact hrLeft (r.mk_penultimate_end_mem_edges hrNotNil)
  · push Not at hrInterior
    obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
    left
    have hxReach := reach_of_mem_r x hx
    have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      L.boundary hfaith hxReach
    refine ⟨x, hxReach, ?_⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
    rw [mem_rect] at hxBox
    omega


theorem rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace x :=
    hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n
  · right
    let c := r.snd
    have hbcSource : s(b, c) ∈ r.edges := r.mk_start_snd_mem_edges hrNotNil
    have hbcRight : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_reflectedPathEdges gamma.1 := hrRight hbcSource
    have hbcWall : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hbcRight)
    let W := ((rlc_ambientCrossingWalk gamma.1).map
      rlc_flipXLatticeHom).reverse
    have hbcW : s(rlc_dualReflect b, rlc_dualReflect c) ∈ W.edges := by
      have hf :=
        rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma.1 hbcRight
      simpa [W, SimpleGraph.Walk.edges_reverse] using hf
    have hbStart : rlc_dualReflect b ≠
        rlc_flipX (gamma.1.2.1 : Site 2) := by
      intro heq
      have hbInt := hrInterior b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 = -(gamma.1.2.1 : Site 2) 0 at h0
      have hs : (gamma.1.2.1 : Site 2) 0 = 2 * n :=
        gamma.1.2.1.2.2
      omega
    have hbFinish : rlc_dualReflect b ≠
        rlc_flipX (gamma.1.1 : Site 2) := by
      intro heq
      have hbNeg := hrNeg b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 = -(gamma.1.1 : Site 2) 0 at h0
      have hs : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
      omega
    obtain ⟨d, hbdW, hdc⟩ := rlc_isPath_exists_other_incident_edge
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse
        hbcW hbStart hbFinish
    have hbdRight : s(rlc_dualReflect b, d) ∈
        rlc_reflectedPathEdges gamma.1 := by
      have hbdForward : s(rlc_dualReflect b, d) ∈
          ((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).edges := by
        simpa [W, SimpleGraph.Walk.edges_reverse] using hbdW
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at hbdForward
      obtain ⟨e0, he0, heq⟩ := hbdForward
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, rlc_ambientCrossingWalk_edge_mem_pathEdges
        gamma.1 he0, heq⟩
    have hbdWall : s(rlc_dualReflect b, d) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hbdRight)
    have hac : rlc_dualReflect a ≠ rlc_dualReflect c := by
      intro hac
      apply hentryNot
      simpa [hac, Sym2.eq_swap] using hbcWall
    have hbAdjC : (hypercubicLattice 2).Adj
        (rlc_dualReflect b) (rlc_dualReflect c) :=
      (rlc_adj_dualReflect b c).mp (r.adj_snd hrNotNil).1.1
    have hbAdjD : (hypercubicLattice 2).Adj (rlc_dualReflect b) d :=
      W.adj_of_mem_edges hbdW
    have hbNoLeft := hrNoLeft b r.start_mem_support
    have hother : ∀ w : Site 2,
        (hypercubicLattice 2).Adj (rlc_dualReflect b) w →
        s(rlc_dualReflect b, w) ≠ s(d, rlc_dualReflect b) →
        s(rlc_dualReflect b, w) ≠
          s(rlc_dualReflect b, rlc_dualReflect c) →
        s(rlc_dualReflect b, w) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
      intro w hbw hneD hneC
      exact rlc_negative_reflectedRight_third_incident_nonwall
        gamma gamma' (hrNeg b r.start_mem_support) hbNoLeft
          (by simpa [Sym2.eq_swap] using hbdRight) hbcRight hdc hneD hneC
    have hregion : ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
      rcases hab.2 with hwall | hregion
      · exact False.elim (hentryNot hwall)
      · exact hregion.2.2
    obtain ⟨h0, hh0Region, hh0⟩ := hregion
    obtain ⟨k, hkFirst, hkRegion⟩ :=
      rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
        gamma gamma' ((rlc_adj_dualReflect b a).mp hab.1.1.symm)
          hbAdjC hbAdjD hac hdc hentryNot hbdWall
          (hrInterior b r.start_mem_support) hother hh0Region hh0
    obtain ⟨k', hk'Flank, hk'Region⟩ :=
      rlc_negative_reflectedRight_walk_terminal_regionFlank
        r hrNeg hrNoLeft hrRight hrNotNil hrInterior hkRegion
          (by simpa [c] using hkFirst)
    refine ⟨r.penultimate, k', r.adj_penultimate hrNotNil, ?_,
      hk'Region, hk'Flank⟩
    exact hrRight (r.mk_penultimate_end_mem_edges hrNotNil)
  · push Not at hrInterior
    obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
    left
    have hxReach := reach_of_mem_r x hx
    have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      L.boundary hfaith hxReach
    refine ⟨x, hxReach, ?_⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
    rw [mem_rect] at hxBox
    omega





theorem rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
          k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have hentry' := hentry
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  rcases rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank
      hfaith hentry' with hboundary | ⟨t, h, htu, htuLeft,
        hhRegion, hhFlank⟩
  · exact Or.inl hboundary
  · by_cases hrInterior : ∀ x ∈ r.support,
        -2 * n < (rlc_dualReflect x) 0 ∧
          (rlc_dualReflect x) 0 < 2 * n ∧
          -n < (rlc_dualReflect x) 1 ∧
          (rlc_dualReflect x) 1 < n
    · have hout := rlc_badExit_interior_nonwall_box_noCentralFlank
          huv (hrInterior u r.end_mem_support) hbad
      exact Or.inr ⟨t, h, htu, htuLeft, hhRegion, hhFlank,
        hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
    · push Not at hrInterior
      obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
      have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
      have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
        L.boundary hfaith hxReach
      left
      refine ⟨x, hxReach, ?_⟩
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
      rw [mem_rect] at hxBox
      omega


theorem rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
          k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have hentry' := hentry
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  rcases rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank
      hfaith hentry' with hboundary | ⟨t, h, htu, htuRight,
        hhRegion, hhFlank⟩
  · exact Or.inl hboundary
  · by_cases hrInterior : ∀ x ∈ r.support,
        -2 * n < (rlc_dualReflect x) 0 ∧
          (rlc_dualReflect x) 0 < 2 * n ∧
          -n < (rlc_dualReflect x) 1 ∧
          (rlc_dualReflect x) 1 < n
    · have hout := rlc_badExit_interior_nonwall_box_noCentralFlank
          huv (hrInterior u r.end_mem_support) hbad
      exact Or.inr ⟨t, h, htu, htuRight, hhRegion, hhFlank,
        hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
    · push Not at hrInterior
      obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
      have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
      have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
        L.boundary hfaith hxReach
      left
      refine ⟨x, hxReach, ?_⟩
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
      rw [mem_rect] at hxBox
      omega





def RlcCentralFaceStrictEntryOriginalContactSurgery {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  (∀ {u : Site 2}
      {q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk L.boundary.firstFace u},
    RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q →
      ∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∧
    (∀ {u : Site 2}
      {q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk L.boundary.secondFace u},
    RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q →
      ∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.secondFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1)



theorem rlc_retainedAnchorTraceIncidence_of_strictEntryOriginalContactSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery
      gamma gamma' rho L)
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    RlcCentralFaceRetainedAnchorTraceIncidence L.boundary := by
  obtain ⟨y, hfirstY, hyLeft⟩ := hsurgery.1 hneg
  obtain ⟨x, hsecondX, hxRight⟩ := hsurgery.2 hpos
  have hfirstSecond :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable
  exact ⟨⟨x, hfirstSecond.trans hsecondX, hxRight⟩,
    y, hfirstY, hyLeft⟩



theorem rlc_centralFacePIMS_success_of_strictEntryOriginalContactSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery
      gamma gamma' rho L)
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  obtain ⟨y, hyReach, hyPath⟩ := hsurgery.1 hneg
  obtain ⟨x, hxReachSecond, hxPath⟩ := hsurgery.2 hpos
  have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace x :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans
      hxReachSecond
  have hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho :=
    ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_goodComponentContacts
        gamma gamma' rho hcomponent)




def RlcCentralFacePairedTerminalSideChange {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v u' v' : Site 2) : Prop :=
  ∃ (t h t' h' : Site 2),
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
    s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_reflectedPathEdges gamma.1 ∧
    h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
    h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
    s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    rlc_dualReflect u ∈ rlc_connectorBox n ∧
    rlc_dualReflect v ∈ rlc_connectorBox n ∧
    (∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
      k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v)) ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t' u' ∧
    s(rlc_dualReflect t', rlc_dualReflect u') ∈
      rlc_reflectedPathEdges gamma'.1 ∧
    h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
    h' ∈ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') ∧
    s(rlc_dualReflect u', rlc_dualReflect v') ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    rlc_dualReflect u' ∈ rlc_connectorBox n ∧
    rlc_dualReflect v' ∈ rlc_connectorBox n ∧
    (∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
      k ∉ flankFaces (rlc_dualReflect u') (rlc_dualReflect v')) ∧
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hh'Box : h' ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
          ⟨h, hhBox⟩ ⟨h', hh'Box⟩ ∧
      ∃ k k' : Site 2,
        flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
        flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
        (let C := (L.boundary.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom
         (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
              phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
            (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
              phb_doubleDualEquiv.symm k ∈ jec_leftRegion C))) ∧
        (let C := (L.boundary.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom
         (((phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
              phb_doubleDualEquiv.symm k' ∉ jec_leftRegion C) ∨
            (phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C ∧
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C)))



theorem RlcCentralFacePairedTerminalSideChange.positiveIncoming_firstIntersectionCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hpaired : RlcCentralFacePairedTerminalSideChange
      gamma gamma' rho L u v u' v') :
    ∃ (t' h' k' : Site 2)
      (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj t' u' ∧
      s(rlc_dualReflect t', rlc_dualReflect u') ∈
        rlc_reflectedPathEdges gamma'.1 ∧
      h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
      flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
      c.IsCycle ∧
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      phb_doubleDualEquiv.symm h' ∈ jec_leftRegion c ∧
      s(rlc_dualReflect t', rlc_dualReflect u') ∈ c.edges ∧
      phb_doubleDualEquiv.symm k' ∉ jec_leftRegion c := by
  obtain ⟨_t, _h, t', h', _htu, _htuRight, _hhRegion, _hhFlank,
    _huvNonwall, _huBox, _hvBox, _huvNoCentral,
    ht'u', ht'u'Left, hh'Region, hh'Flank,
    _hu'v'Nonwall, _hu'Box, _hv'Box, _hu'v'NoCentral,
    _hhBox, _hh'Box, _hreach, _k, k', _hflank, hflank',
    _hside, _hside'⟩ := hpaired
  obtain ⟨c, hcycle, hedges, hcentral, hleftDichotomy⟩ :=
    rlc_centralRegion_inside_firstIntersectionCycle
      gamma gamma' hfaith
  have hambient : s(rlc_dualReflect t', rlc_dualReflect u') ∈
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 ht'u'Left
  have hh'Inside := hcentral h' hh'Region
  have hedge : s(rlc_dualReflect t', rlc_dualReflect u') ∈ c.edges := by
    rcases hleftDichotomy hambient with hedge | hexterior
    · exact hedge
    · exact False.elim ((hexterior h' hh'Flank) hh'Inside)
  have hadj : (hypercubicLattice 2).Adj
      (rlc_dualReflect t') (rlc_dualReflect u') :=
    (rlc_adj_dualReflect t' u').mp ht'u'.1.1
  have hk'Outside := rlc_cycleEdge_oppositeFlank_outside
    hcycle hadj hflank' hedge hh'Inside
  exact ⟨t', h', k', c, ht'u', ht'u'Left, hh'Region, hflank',
    hcycle, hedges, hh'Inside, hedge, hk'Outside⟩





theorem RlcCentralFacePairedTerminalSideChange.nonwallGoodContourEdge_or_sameWindingSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (hpaired : RlcCentralFacePairedTerminalSideChange
      gamma gamma' rho L u v u' v') :
    (∃ f g : Site 2,
      s(f, g) ∈ L.boundary.contour.edges ∧
        RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      ∃ t h t' h' k k' : Site 2,
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (L.boundary.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
                rlc_dualReflectLatticeHom
           (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
            (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C)) := by
  obtain ⟨t, h, t', h', _htu, _htuRight, hhRegion, _hhFlank,
    _huvNonwall, _huBox, _hvBox, _huvNoCentral,
    _ht'u', _ht'u'Left, hh'Region, _hh'Flank,
    _hu'v'Nonwall, _hu'Box, _hv'Box, _hu'v'NoCentral,
    hhBox, hh'Box, hreach, k, k', hflank, hflank', hside, hside'⟩ := hpaired
  let C := (L.boundary.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  by_cases hopposite :
      (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C)
  · left
    exact L.boundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide
      hhRegion hhBox hh'Box hreach hopposite
  · right
    refine ⟨t, h, t', h', k, k', hhRegion, hh'Region,
      hflank, hflank', ?_⟩
    dsimp only at hside hside' ⊢
    have hsame :
        (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) := by
      constructor
      · intro hh
        by_contra hh'
        exact hopposite (Or.inl ⟨hh, hh'⟩)
      · intro hh'
        by_contra hh
        exact hopposite (Or.inr ⟨hh, hh'⟩)
    refine ⟨hsame, ?_⟩
    rcases hside with hside | hside
    · rcases hside' with hside' | hside'
      · exact ⟨fun hk => (hside.2 hk).elim,
          fun hk' => (hside'.2 hk').elim⟩
      · exact (hside'.1 (hsame.mp hside.1)).elim
    · rcases hside' with hside' | hside'
      · exact (hside.1 (hsame.mpr hside'.1)).elim
      · exact ⟨fun _ => hside'.2, fun _ => hside.2⟩



theorem rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      RlcCentralFacePairedTerminalSideChange
        gamma gamma' rho L u v u' v' := by
  rcases rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hneg huv hbad with hboundary | hnegTerminal
  · exact Or.inl hboundary
  rcases rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hpos hu'v' hbad' with hboundary | hposTerminal
  · exact Or.inl hboundary
  right
  obtain ⟨t, h, htu, htuRight, hhRegion, hhFlank,
    huvNonwall, huBox, hvBox, huvNoCentral⟩ := hnegTerminal
  obtain ⟨t', h', ht'u', ht'u'Left, hh'Region, hh'Flank,
    hu'v'Nonwall, hu'Box, hv'Box, hu'v'NoCentral⟩ := hposTerminal
  have hpaired :=
    L.boundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle
      htu.1 hhRegion hhFlank ht'u'.1 hh'Region hh'Flank
  exact ⟨t, h, t', h', htu, htuRight, hhRegion, hhFlank,
    huvNonwall, huBox, hvBox, huvNoCentral, ht'u', ht'u'Left,
    hh'Region, hh'Flank, hu'v'Nonwall, hu'Box, hv'Box,
    hu'v'NoCentral, hpaired⟩





def RlcCentralFacePairedFirstIntersectionSideData {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (u u' : Site 2) : Prop :=
  (∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        rlc_dualReflect u' ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        (rlc_dualReflect b ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support ↔
          rlc_dualReflect u' ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support)) ∧
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        (rlc_dualReflect b ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support ↔
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support)





theorem rlc_pairedStrictWallEntryDecomp_boundary_or_nonwall_or_orderedSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v') :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      (∃ f g : Site 2,
        s(f, g) ∈ L.boundary.contour.edges ∧
          RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
      ((∃ t h t' h' k k' : Site 2,
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (L.boundary.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
                rlc_dualReflectLatticeHom
           (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
            (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) ∧
        RlcCentralFacePairedFirstIntersectionSideData gamma gamma' u u') := by
  exact Or.inr (Or.inl hneg.nonwallGoodContourEdge)




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_boundary_or_pairedTerminal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      ((∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          ((rlc_dualReflect x) 0 = -2 * n ∨
            (rlc_dualReflect x) 0 = 2 * n ∨
            (rlc_dualReflect x) 1 = -n ∨
            (rlc_dualReflect x) 1 = n)) ∨
        RlcCentralFacePairedTerminalSideChange
          gamma gamma' rho L u v u' v') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hneg hpos huv hbad hu'v' hbad'




theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_nonwallGoodContourEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      ∃ f g : Site 2,
        s(f, g) ∈ L.boundary.contour.edges ∧
          RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma' := by
  exact ⟨L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos,
    hneg.nonwallGoodContourEdge⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_missingIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
        ∃ f g : Site 2,
          RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence
            L.boundary f g) := by
  obtain ⟨hextreme, f, g, hfgContour, hcarrier, hnonwall⟩ :=
    L.twoBadMiddle_extreme_and_nonwallGoodContourEdge
      haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp'
        huNeg hu'Pos hneg
  refine ⟨hextreme, ?_⟩
  rcases rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence
      hfgContour hcarrier hnonwall with hgood | hmissing
  · exact Or.inl hgood
  · exact Or.inr ⟨f, g, hmissing⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_anchoredMissingIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
        ∃ f g : Site 2,
          RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
            L.boundary f g) := by
  have hextreme := L.twoBadMiddle_axis_crossing_extreme
    haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  obtain ⟨f, g, hfgContour, hcarrier, hnonwall, hfirstF, hfirstG⟩ :=
    hneg.anchoredNonwallGoodContourEdge
  refine ⟨hextreme, ?_⟩
  rcases rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence
      hfgContour hcarrier hnonwall hfirstF hfirstG with hgood | hmissing
  · exact Or.inl hgood
  · exact Or.inr ⟨f, g, hmissing⟩



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRunDecomp_reachableRight_or_axisSuffix_or_strictEntryDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hrun : RlcCentralFacePositiveWallRunDecompAt
      gamma gamma' rho L q)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveReflectedLeftAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFacePositiveStrictWallEntryDecompAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentry, hrWall, hrNotNil, w, hw, huw⟩ := hrun
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace x := by
    exact hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hright : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hx, hxRight⟩ := hright
    exact ⟨x, reach_of_mem_r x hx, hxRight⟩
  · push Not at hright
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => (rlc_dualReflect x) 0) r huPos with
      hallPos | ⟨c, d, pr, s, hcd, hcNonpos, hdPos,
        hsPos, hrDecomp⟩
    · right; right
      refine ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp,
        hAzero, hAstart, hentry, hallPos, hright, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonnegative_wallPath_edge_reflectedLeft
        hfaith r hrWall hright
          (fun x hx => le_of_lt (hallPos x hx)) hfg
    · have hcdR : s(c, d) ∈ r.edges := by
        rw [hrDecomp, SimpleGraph.Walk.edges_append]
        simp
      have hcdWall : s(rlc_dualReflect c, rlc_dualReflect d) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
        simpa [Sym2.map_mk] using hrWall _ hcdR
      have hcdTarget : (hypercubicLattice 2).Adj
          (rlc_dualReflect c) (rlc_dualReflect d) :=
        (rlc_adj_dualReflect c d).mp hcd.1.1
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcdTarget
        omega
      have hcBarrier : rlc_dualReflect c ∈
          rlc_connectorBarrier gamma gamma' :=
        rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hcdWall (Sym2.mem_mk_left _ _)
      have hcEq : rlc_dualReflect c =
          (![0, (rlc_dualReflect c) 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hcZero]
      rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma'
          ((rlc_dualReflect c) 1)).1 (by
            rwa [← hcEq]) with hcRight | hcLeft
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩
      · right; left
        let t : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have htSupport : ∀ x ∈ t.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have htNoRight : ∀ x ∈ t.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1 := by
          intro x hx
          exact hright x (htSupport x hx)
        have htWall : ∀ e ∈ t.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have htNonneg : ∀ x ∈ t.support,
            0 ≤ (rlc_dualReflect x) 0 := by
          intro x hx
          simp only [t, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero.symm
          · exact le_of_lt (hsPos x hx)
        have hcLeft' : rlc_dualReflect c ∈
            rlc_pathVertices gamma'.1 := by
          rwa [hcEq]
        have hcEnd := hfaith.left_axis_unique hcLeft' hcZero
        refine ⟨c, t, hcEnd, htNoRight, ?_⟩
        intro f g hfg
        exact rlc_nonnegative_wallPath_edge_reflectedLeft
          hfaith t htWall htNoRight htNonneg hfg



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRunDecomp_reachableLeft_or_axisSuffix_or_strictEntryDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hrun : RlcCentralFaceNegativeWallRunDecompAt
      gamma gamma' rho L q)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeReflectedRightAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFaceNegativeStrictWallEntryDecompAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentry, hrWall, hrNotNil, w, hw, huw⟩ := hrun
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace x := by
    exact hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hleft : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma'.1
  · left
    obtain ⟨x, hx, hxLeft⟩ := hleft
    exact ⟨x, reach_of_mem_r x hx, hxLeft⟩
  · push Not at hleft
    have huNeg' : 0 < -(rlc_dualReflect u) 0 := by omega
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => -(rlc_dualReflect x) 0) r huNeg' with
      hallNeg | ⟨c, d, pr, s, hcd, hcNonneg, hdNeg,
        hsNeg, hrDecomp⟩
    · right; right
      have hallNeg' : ∀ x ∈ r.support,
          (rlc_dualReflect x) 0 < 0 := by
        intro x hx
        have := hallNeg x hx
        omega
      refine ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
        hentry, hallNeg', hleft, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonpositive_wallPath_edge_reflectedRight
        hfaith r hrWall hleft
          (fun x hx => le_of_lt (hallNeg' x hx)) hfg
    · have hcdR : s(c, d) ∈ r.edges := by
        rw [hrDecomp, SimpleGraph.Walk.edges_append]
        simp
      have hcdWall : s(rlc_dualReflect c, rlc_dualReflect d) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
        simpa [Sym2.map_mk] using hrWall _ hcdR
      have hcdTarget : (hypercubicLattice 2).Adj
          (rlc_dualReflect c) (rlc_dualReflect d) :=
        (rlc_adj_dualReflect c d).mp hcd.1.1
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcdTarget
        omega
      have hcBarrier : rlc_dualReflect c ∈
          rlc_connectorBarrier gamma gamma' :=
        rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hcdWall (Sym2.mem_mk_left _ _)
      have hcEq : rlc_dualReflect c =
          (![0, (rlc_dualReflect c) 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hcZero]
      rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma'
          ((rlc_dualReflect c) 1)).1 (by
            rwa [← hcEq]) with hcRight | hcLeft
      · right; left
        let t : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have htSupport : ∀ x ∈ t.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have htNoLeft : ∀ x ∈ t.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma'.1 := by
          intro x hx
          exact hleft x (htSupport x hx)
        have htWall : ∀ e ∈ t.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have htNonpos : ∀ x ∈ t.support,
            (rlc_dualReflect x) 0 ≤ 0 := by
          intro x hx
          simp only [t, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero
          · have := hsNeg x hx
            omega
        have hcRight' : rlc_dualReflect c ∈
            rlc_pathVertices gamma.1 := by
          rwa [hcEq]
        have hcStart := hfaith.right_axis_unique hcRight' hcZero
        refine ⟨c, t, hcStart, htNoLeft, ?_⟩
        intro f g hfg
        exact rlc_nonpositive_wallPath_edge_reflectedRight
          hfaith t htWall htNoLeft htNonpos hfg
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩



theorem rlc_strictSurgeryResidue_of_strictCarrierSurgeryResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (h : RlcCentralFaceStrictCarrierSurgeryResidue
      gamma gamma' rho L u v u' v') :
    RlcCentralFaceStrictSurgeryResidue gamma gamma' rho L u u' := by
  rcases h with hneg | hpos | hbarrier
  · exact Or.inl hneg.1
  · exact Or.inr (Or.inl hpos.1)
  · exact Or.inr (Or.inr hbarrier)



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictCarrierSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ (z : Site 2)
        (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) ∨
      RlcCentralFacePositiveStrictCarrierSurgeryAt
        gamma gamma' rho L u v := by
  rcases L.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry
      hfaith hrun huPos with hright | hsuffix | hstrict
  · exact Or.inl hright
  · exact Or.inr (Or.inl hsuffix)
  · exact Or.inr (Or.inr ⟨hstrict, huv, hbad⟩)



theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictCarrierSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ (z : Site 2)
        (hz : rlc_flipX z ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) ∨
      RlcCentralFaceNegativeStrictCarrierSurgeryAt
        gamma gamma' rho L u v := by
  rcases L.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry
      hfaith hrun huNeg with hleft | hsuffix | hstrict
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hsuffix)
  · exact Or.inr (Or.inr ⟨hstrict, huv, hbad⟩)

end

end StatMech.Universality
