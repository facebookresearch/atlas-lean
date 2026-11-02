/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeometricFaces
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanLeftRegionInterior

/-!
# The exit orbit winds around the origin

For a configuration `ω` with finite origin cluster, consider the face loop of the boundary orbit of
the exit dart (`exitBaseSub`). If the orbit turns by a full revolution and has no pinched face, the
loop is a cycle and so encloses a site. If moreover the origin lies inside the loop
(`wwc2_OriginInside`), the loop winds around the origin (`acc_ExitDartWinds`), which gives an
anchored cycle and, assumed for every configuration, `p_c(ℤ²) < 1`.

The file also derives `wwc2_OriginInside` from `wwc2_OriginReachesEnclosed`: the origin is joined,
avoiding the loop, to every site inside the loop. That hypothesis is very strong. Faces are
labelled by their lower left corners, so it asks the path to avoid every site whose upper right face
is on the loop; an inside site whose upper right face is on the loop (for instance the origin of the
unit cell) can never be reached. The results under `wwc2_OriginReachesEnclosed` are conditional on
a hypothesis that fails in the basic examples.

## Main definitions

* `StatMech.Lattice.wwc2_OriginInside ω hfin`: the origin lies inside the exit face loop.
* `StatMech.Lattice.wwc2_OriginReachesEnclosed ω hfin`: the origin is joined off the loop to every
  site inside the loop.

## Main results

* `StatMech.Lattice.wwc2_leftRegion_nonempty`: a closed walk that is a cycle has a nonempty inside.
* `StatMech.Lattice.wwc2_even_of_connected_to_far`: sites joined off a closed walk to a site right
  of the walk have even ray count.
* `StatMech.Lattice.wwc2_exitDartWinds_of_turning_originInside`: full turn, no pinched face and the
  origin inside give `acc_ExitDartWinds`.
* `StatMech.Lattice.wwc2_pc_lt_one_of_turning_originInside`: `p_c(ℤ²) < 1` under these three
  assumptions for every configuration.
* `StatMech.Lattice.wwc2_pc_lt_one_of_originReachesEnclosed`: `p_c(ℤ²) < 1` with
  `wwc2_OriginInside` replaced by `wwc2_OriginReachesEnclosed`.

## References

* R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936).
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- A site joined, by a path avoiding the closed walk `Vc`, to a site strictly right of every site
of `Vc` has even ray count. See also `StatMech.Lattice.ccs_closedLoop_outside_far`. -/
theorem wwc2_even_of_connected_to_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z q : Site 2} (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (p : (hypercubicLattice 2).Walk z q) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    Even (jec_rayCount z Vc) := by
  have hsame := jlri_sameRegion_along_offSupport_walk Vc p hp
  by_contra hodd
  have hzmem : z ∈ jec_leftRegion Vc := by rw [jec_mem_leftRegion]; exact hodd
  exact ccs_closedLoop_outside_far Vc hq (hsame.mp hzmem)

/-- A closed lattice walk that is a cycle has a site of odd ray count: its inside is nonempty. -/
theorem wwc2_leftRegion_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    (jec_leftRegion Vc).Nonempty := by
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell' Vc hcyc
  exact ⟨z, (jec_mem_leftRegion Vc z).mpr hz⟩

/-- The inside of a cycle contained in a box `[-R, R]²` is nonempty and finite. -/
theorem wwc2_leftRegion_nonempty_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Nonempty ∧ (jec_leftRegion Vc).Finite :=
  ⟨wwc2_leftRegion_nonempty Vc hcyc, egf_leftRegion_finite Vc R hsupp⟩

/-- The origin lies inside the face loop of the exit orbit of the origin cluster: it has odd ray
count. -/
def wwc2_OriginInside (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  origin 2 ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))

/-- `wwc2_OriginInside` restated as odd ray count of the origin. -/
theorem wwc2_oddOrigin_of_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : wwc2_OriginInside ω hfin) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) :=
  (jec_mem_leftRegion _ _).mp h

/-- If the exit orbit turns by a full revolution, has no pinched face, and the origin lies inside
its loop, then the loop is a cycle winding around the origin. -/
theorem wwc2_exitDartWinds_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp)

/-- The same as `wwc2_exitDartWinds_of_turning_originInside`, with the full turn replaced by period
at least three. -/
theorem wwc2_exitDartWinds_of_cycle_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp)

/-- Full turn, no pinched face and the origin inside the exit loop give an anchored cycle. -/
theorem wwc2_anchoredCycleExists_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp hinside)

/-- **Peierls bound for bond percolation on `ℤ²`**, conditional form: `p_c(ℤ²) < 1`, assuming for
every configuration with finite origin cluster that the exit orbit turns by a full revolution, has
no pinched face, and its loop contains the origin. These three geometric inputs are hypotheses,
not proved here; the literature result is unconditional (Peierls 1936). -/
theorem wwc2_pc_lt_one_of_turning_originInside
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
          wwc2_OriginInside ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)

/-- The origin lies inside the face loop of the unit cell. -/
theorem wwc2_unitCell_originInside :
    origin 2 ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
  rw [jec_mem_leftRegion]
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide

/-- The face loop of the unit cell, viewed in the square lattice, is a cycle. -/
theorem wwc2_unitCell_primalLoop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj

/-- The inside of the unit cell loop is nonempty. -/
theorem wwc2_unitCell_enclosesCell :
    (jec_leftRegion (mpl_orbitLoop unitCell ucBase)).Nonempty :=
  wwc2_leftRegion_nonempty (mpl_orbitLoop unitCell ucBase) wwc2_unitCell_primalLoop_isCycle

/-- If the exit orbit turns by a full revolution and has no pinched face, its face loop is a
cycle. -/
theorem wwc2_exitLoop_isCycle_of_turning (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle := by
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp)

/-- Under the same hypotheses, some site lies inside the exit loop. -/
theorem wwc2_turning_enclosesCell (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    ∃ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :=
  wwc2_leftRegion_nonempty _ (wwc2_exitLoop_isCycle_of_turning (ω := ω) hfin hturn hnp)

/-- If the exit loop is a cycle and the origin is joined off the loop to every site inside it, the
origin lies inside the loop. -/
theorem wwc2_originInside_of_reaches_enclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hreach : ∀ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) →
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support,
          w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support)) :
    wwc2_OriginInside ω hfin := by
  obtain ⟨z₀, hz₀⟩ := wwc2_turning_enclosesCell (ω := ω) hfin hturn hnp
  obtain ⟨p, hp⟩ := hreach z₀ hz₀
  have hodd0 : ¬ Even (jec_rayCount z₀
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) :=
    (jec_mem_leftRegion _ z₀).mp hz₀
  have hoddO : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) :=
    ooi_odd_of_connected_to_odd _ p hp hodd0
  exact (jec_mem_leftRegion _ (origin 2)).mpr hoddO

/-- The origin is joined, by a lattice path avoiding the exit face loop, to every site inside the
loop. Since faces are labelled by their lower left corners, this fails whenever some site inside
the loop has its upper right face on the loop (for the unit cell, the origin itself). -/
def wwc2_OriginReachesEnclosed (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∀ z₀ : Site 2,
    z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) →
    ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
      (∀ w ∈ p.support,
        w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support)

/-- Full turn, no pinched face and `wwc2_OriginReachesEnclosed` give `acc_ExitDartWinds`. -/
theorem wwc2_exitDartWinds_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    acc_ExitDartWinds ω hfin :=
  wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp
    (wwc2_originInside_of_reaches_enclosed (ω := ω) hfin hturn hnp hreach)

/-- Full turn, no pinched face and `wwc2_OriginReachesEnclosed` give an anchored cycle. -/
theorem wwc2_anchoredCycleExists_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin hturn hnp hreach)

/-- `p_c(ℤ²) < 1`, assuming for every configuration with finite origin cluster a full turn of the
exit orbit, no pinched face, and `wwc2_OriginReachesEnclosed`. The last hypothesis fails whenever a
site inside the exit loop has its upper right face on the loop, which happens for the all-closed
configuration (the unit cell), so this statement is expected to be vacuous; prefer
`wwc2_pc_lt_one_of_turning_originInside`. -/
theorem wwc2_pc_lt_one_of_originReachesEnclosed
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
          wwc2_OriginReachesEnclosed ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)

/-- If the origin is off the exit loop, the empty walk joins it to itself off the loop. -/
theorem wwc2_origin_reaches_self_offSupport (hfin : (cluster 2 ω (origin 2)).Finite)
    (hO : origin 2 ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support) :
    ∃ p : (hypercubicLattice 2).Walk (origin 2) (origin 2),
      (∀ w ∈ p.support,
        w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support) := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
  rw [hw]; exact hO

/-- For the unit cell, the origin lies inside the loop. The disjunct `z₀ = origin 2` makes this
weaker than `wwc2_OriginReachesEnclosed`, which fails for the unit cell. -/
theorem wwc2_unitCell_originReachesEnclosed_witness :
    ∃ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) ∧
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ z₀ = origin 2 := by
  exact ⟨origin 2, wwc2_unitCell_originInside, SimpleGraph.Walk.nil, Or.inr rfl⟩

end Lattice

end StatMech
