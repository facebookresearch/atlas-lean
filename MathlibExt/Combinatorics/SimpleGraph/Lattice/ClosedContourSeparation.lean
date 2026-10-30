/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleSpace
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourLinksExits

/-!
# Closed walks separate their inside from their outside

A closed lattice walk `Vc` separates sites of odd ray count from sites of even ray count: every
lattice edge crossing between them has an endpoint on `Vc`, so every walk from inside to outside
meets `Vc`. If a set `K` is exactly the inside of some closed walk (`ccs_OrbitIsLoop K`), then `K`
equals that inside and walks leaving `K` meet the walk.

## Main definitions

* `StatMech.Lattice.ccs_OrbitIsLoop K`: some closed walk has odd ray count exactly at the sites of
  `K`.

## Main results

* `StatMech.Lattice.ccs_closedLoop_outside_far`, `StatMech.Lattice.ccs_closedLoop_outside_left`:
  sites to the right or left of the whole walk are outside.
* `StatMech.Lattice.ccs_closedLoop_separation`: a closed walk is a separating side between its
  inside and its outside.
* `StatMech.Lattice.ccs_cluster_eq_leftRegion`: a set realized by a closed walk is its inside.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

theorem ccs_closedLoop_outside_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact jec_ray_even_far Vc z hfar

theorem ccs_closedLoop_outside_left {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hleft : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not, jec_rayCount_eq_zero_of_right z Vc hleft]
  exact Even.zero

theorem ccs_closedLoop_separation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (inside outside : Set (Site 2))
    (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc)) :
    jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} inside outside := by
  refine ⟨jec_leftRegion Vc, ?_, ?_, ?_⟩
  · intro z hz; exact hin z hz
  · intro z hz; rw [jec_mem_leftRegion, not_not]; exact hout z hz
  · intro u v _huD _hvD hadj huS hvS
    refine jec_leftRegion_bdEdge_support Vc hadj ?_
    rw [bdEdge_mk]; exact ⟨fun _ => hvS, fun _ => huS⟩

theorem ccs_closedLoop_separatingSide_forces_cross {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (inside outside : Set (Site 2))
    (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc))
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ z ∈ w.support, z ∈ Vc.support :=
  jcu_separatingSide_forces_cross (ccs_closedLoop_separation Vc inside outside hin hout) hx hy w
    (fun z _ => Set.mem_univ z)

theorem ccs_closedLoop_hasSeparatingSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
    jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} {p} {q} := by
  refine ccs_closedLoop_separation Vc {p} {q} ?_ ?_
  · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; exact hp
  · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; exact jec_ray_even_far Vc q hq

theorem ccs_closedLoop_two_components {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  have hpS : p ∈ jec_leftRegion Vc := hp
  have hqS : q ∉ jec_leftRegion Vc := ccs_closedLoop_outside_far Vc hq
  exact jcs_two_components_of_sides (jec_leftRegion Vc) hpS hqS hin hout

/-- Some closed lattice walk has odd ray count exactly at the sites of `K`, so `K` is the inside
of that walk. -/
def ccs_OrbitIsLoop (K : Set (Site 2)) : Prop :=
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
    (∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc)) ∧
    (∀ z, z ∉ K → Even (jec_rayCount z Vc))

theorem ccs_clusterSeparatingSide {K : Set (Site 2)} (h : ccs_OrbitIsLoop K) :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} K Kᶜ := by
  obtain ⟨a, Vc, hin, hout⟩ := h
  refine ⟨a, Vc, ccs_closedLoop_separation Vc K Kᶜ ?_ ?_⟩
  · intro z hz; exact hin z hz
  · intro z hz; exact hout z hz

theorem ccs_cluster_forces_cross {K : Set (Site 2)} (h : ccs_OrbitIsLoop K)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K) (w : (hypercubicLattice 2).Walk x y) :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      (∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc)) ∧
      (∀ z, z ∉ K → Even (jec_rayCount z Vc)) ∧
      ∃ z ∈ w.support, z ∈ Vc.support := by
  obtain ⟨a, Vc, hin, hout⟩ := h
  refine ⟨a, Vc, hin, hout, ?_⟩
  exact ccs_closedLoop_separatingSide_forces_cross Vc K Kᶜ hin hout hx hy w

theorem ccs_cluster_eq_leftRegion {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    K = jec_leftRegion Vc := by
  ext z
  rw [jec_mem_leftRegion]
  constructor
  · intro hz; exact hin z hz
  · intro hz; by_contra hzK; exact hz (hout z hzK)

theorem ccs_cluster_two_components {K : Set (Site 2)} (h : ccs_OrbitIsLoop K)
    {p q : Site 2} (hp : p ∈ K) (hq : q ∉ K)
    (hin : ∀ s t : Site 2, s ∈ K → t ∈ K → (latticeMinusBarrier K).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ K → t ∉ K → (latticeMinusBarrier K).Reachable s t) :
    Nat.card (latticeMinusBarrier K).ConnectedComponent = 2 ∧
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), K = jec_leftRegion Vc := by
  obtain ⟨a, Vc, hLin, hLout⟩ := h
  refine ⟨jcs_two_components_of_sides K hp hq hin hout, a, Vc,
    ccs_cluster_eq_leftRegion Vc hLin hLout⟩

open StatMech.Percolation in
theorem ccs_pcSeparation_discharged
    (hloop : ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite →
        ccs_OrbitIsLoop (cluster 2 ω (origin 2))) :
    ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite →
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
        jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support}
          (cluster 2 ω (origin 2)) (cluster 2 ω (origin 2))ᶜ :=
  fun ω hfin => ccs_clusterSeparatingSide (hloop ω hfin)

end Lattice

end StatMech
