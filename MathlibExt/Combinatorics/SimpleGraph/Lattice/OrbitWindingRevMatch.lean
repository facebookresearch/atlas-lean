/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchStarHull
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding

/-!
# The reverse boundary-edge inclusion for a winding region

For a boundary orbit of a finite set `K`, the file derives `OrbitWindingRevMatch` (every boundary
edge of the winding region is a boundary edge of `K`) from inclusions between `K` and the winding
region, and from an exterior hypothesis `hExt` together with an odd interior witness. It also shows
that `hExt` fails for some boundary dart of every finite nonempty set, so it cannot be assumed for
all boundary darts of a cluster.

## Main results

* `StatMech.Lattice.owr_leftRegion_subset_of_exterior`: under `hExt`, the winding region lies in
  `K`.
* `StatMech.Lattice.owr_exists_not_exteriorHyp`: for finite nonempty `K`, `hExt` fails for the
  leftward dart out of a leftmost site of `K`.
* `StatMech.Lattice.owr_revMatch_of_inclusions`: if `K` equals the winding region, the reverse
  inclusion holds.
* `StatMech.Lattice.owr_revMatch_of_winding`, `StatMech.Lattice.owr_orbitSeparates_of_winding`: the
  reverse inclusion, and separation by the orbit, from `hExt` and an odd interior witness.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- If every site outside `K` is joined, by a lattice path avoiding the orbit loop of `e`, to a site
weakly left of the loop, then sites outside `K` have even ray count, so the winding region lies in
`K`. The exterior hypothesis `hExt` fails whenever the orbit of `e` contains the leftward dart out
of a leftmost site of `K` (`owr_exists_not_exteriorHyp`); no boundary dart is shown here to satisfy
it. -/
theorem owr_leftRegion_subset_of_exterior (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
    jec_leftRegion (olb_orbitLoop K hK e he) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  by_contra hzK
  exact hz (oee_outsideHalf_of_exteriorEq K hK e he hExt z hzK)

/-- The exterior hypothesis `hExt` used in this file (every site outside `K` is joined, by a lattice
path avoiding the support of the orbit loop of `e`, to a site weakly left of that loop) fails for
some boundary dart of every finite nonempty `K`. Take `c ∈ K` with least first coordinate and `e`
the dart from `c` to `c - (1,0)`: the face label `dartFace e = c - (1,1)` lies outside `K` and on
the orbit loop of `e`, so no path from it avoids the loop. In particular `hExt` cannot hold for all
boundary darts of a finite nonempty set. -/
theorem owr_exists_not_exteriorHyp (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ (e : Dart) (he : IsBoundaryDart K e),
      ¬ ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
        (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0) := by
  obtain ⟨c, hc, hmin⟩ := Set.exists_min_image K (fun z : Site 2 => z 0) hK hne
  have hnot : ∀ z : Site 2, z 0 < c 0 → z ∉ K := fun z hz hzK =>
    absurd (hmin z hzK) (not_le.mpr hz)
  have hg : unitWt (![-1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  have he : IsBoundaryDart K (mkDart c ![-1, 0] hg) :=
    ⟨by rw [mkDart_tail]; exact hc, hnot _ (by simp)⟩
  refine ⟨mkDart c ![-1, 0] hg, he, fun hExt => ?_⟩
  have hface : dartFace (mkDart c ![-1, 0] hg) 0 = c 0 - 1 := by
    rw [dartFace_of_dir_left _ (mkDart_dir _ _ _)]; simp
  obtain ⟨z0, p, hp, -⟩ := hExt (dartFace (mkDart c ![-1, 0] hg))
    (hnot _ (by rw [hface]; omega))
  exact hp _ p.start_mem_support (olb_orbitLoop K hK _ he).start_mem_support

/-- Let `L` be the inside (odd ray count) of a closed walk `Vc`. If `L ⊆ K` and no lattice edge
joins a site of `L` to a site of `K` outside `L`, every boundary edge of `L` is a boundary edge of
`K`. -/
theorem owr_revMatch_of_subset_and_noCross (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hsub : jec_leftRegion Vc ⊆ K)
    (hnoCross : ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) := by
  intro x y hadj hbd
  rw [bdEdge_mk] at hbd ⊢
  by_cases hxL : x ∈ jec_leftRegion Vc
  · have hyL : y ∉ jec_leftRegion Vc := hbd.mp hxL
    have hxK : x ∈ K := hsub hxL
    exact ⟨fun _ hyK => hyL (hnoCross x y hadj hxL hyK), fun _ => hxK⟩
  · have hyL : y ∈ jec_leftRegion Vc := by
      by_contra hyL; exact hxL (hbd.mpr hyL)
    have hyK : y ∈ K := hsub hyL
    have hxK : x ∉ K := fun hxK => hxL (hnoCross y x hadj.symm hyL hxK)
    exact ⟨fun hxK' => absurd hxK' hxK, fun hyK' => absurd hyK hyK'⟩

/-- If `K` lies inside the closed walk `Vc`, no lattice edge joins the inside of `Vc` to a site of
`K` outside it. -/
theorem owr_noCross_of_interior (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hKsub : K ⊆ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc :=
  fun _ _ _ _ hyK => hKsub hyK

/-- If `K` equals the inside of the closed walk `Vc`, every boundary edge of the inside is a
boundary edge of `K`. -/
theorem owr_revMatch_of_inclusions (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hsub : jec_leftRegion Vc ⊆ K) (hKsub : K ⊆ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) :=
  owr_revMatch_of_subset_and_noCross K Vc hsub (owr_noCross_of_interior K Vc hKsub)

/-- `OrbitWindingRevMatch` from the exterior hypothesis `hExt`, a site `z0 ∈ K` with odd ray count,
and lattice paths from every site of `K` to `z0` avoiding the orbit loop. The exterior hypothesis
`hExt` fails whenever the orbit of `e` contains the leftward dart out of a leftmost site of `K`
(`owr_exists_not_exteriorHyp`); no boundary dart is shown here to satisfy it. -/
theorem owr_revMatch_of_winding (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
    OrbitWindingRevMatch K hK e he :=
  ofw_revMatch_of_match K hK e he
    (pbs_bdEdgeMatch_of_winding K hK e he hExt hz0K hodd0 hInt)

/-- `OrbitWindingRevMatch` from the exterior hypothesis `hExt` and the inclusion of `K` in the
winding region. The exterior hypothesis `hExt` fails whenever the orbit of `e` contains the leftward
dart out of a leftmost site of `K` (`owr_exists_not_exteriorHyp`); no boundary dart is shown here to
satisfy it. -/
theorem owr_revMatch_of_interiorInclusion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    (hKsub : K ⊆ jec_leftRegion (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he :=
  fun x y hadj hbd =>
    owr_revMatch_of_inclusions K (olb_orbitLoop K hK e he)
      (owr_leftRegion_subset_of_exterior K hK e he hExt) hKsub x y hadj hbd

/-- Under the hypotheses of `owr_revMatch_of_winding` and `OrbitCoversBoundaryEdges K e`, the orbit
of `e` separates the tail of `e` from its head. The exterior hypothesis `hExt` fails whenever the
orbit of `e` contains the leftward dart out of a leftmost site of `K`
(`owr_exists_not_exteriorHyp`); no boundary dart is shown here to satisfy it. -/
theorem owr_orbitSeparates_of_winding (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  osp_orbitSeparates_of_match_cover K hK e he
    (pbs_bdEdgeMatch_of_winding K hK e he hExt hz0K hodd0 hInt) hcov

end Lattice

end StatMech
