/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriangularSharpnessThreshold
import Code.FK.TriHexFKFiniteWiredCofinal
import Code.OSSS.BetaCMatch





open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS
open RevealmentTranslation



def triangularBoxToBuffered (k : Nat) :
    TriangularBoxVertex (2 * k) → triangular.BufferedVertex (2 * k) :=
  fun x => ⟨x.1, by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2 (triangular.id_le_bufferedRadius (2 * k)) x.2⟩

theorem triangularBoxToBuffered_injective (k : Nat) :
    Function.Injective (triangularBoxToBuffered k) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : triangular.BufferedVertex (2 * k) => (z : Site 2)) h

theorem triangularBoxToBuffered_adjMatch (k : Nat) :
    ocd_AdjMatch (triangularBoxGraph (2 * k))
      (triangular.bufferedGraph (2 * k)) (triangularBoxToBuffered k) := by
  intro x y
  rfl


def triangularBufferedInnerShellEvent (k : Nat) :
    Set (ConfigSpace (Sym2 (triangular.BufferedVertex (2 * k)))) :=
  ocd_innerRestrict (triangularBoxToBuffered k) ⁻¹'
    triangularCenteredShellFullEvent (2 * k) k

theorem triangularCenteredShellFullEvent_increasing (R k : Nat) :
    IsIncreasing (triangularCenteredShellFullEvent R k) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro x z hxz
  rw [FK.openSub_adj] at hxz ⊢
  refine ⟨hxz.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hxz.2] using home s(x, z)

theorem triangularBufferedInnerShellEvent_increasing (k : Nat) :
    IsIncreasing (triangularBufferedInnerShellEvent k) := by
  intro omega eta home hmem
  exact triangularCenteredShellFullEvent_increasing (2 * k) k
    (fun e => home _) hmem



def triangularBoxToBufferedAt (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    TriangularBoxVertex (2 * k) → triangular.BufferedVertex m :=
  fun x => ⟨x.1, by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2 hkm x.2⟩

theorem triangularBoxToBufferedAt_injective (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    Function.Injective (triangularBoxToBufferedAt k m hkm) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : triangular.BufferedVertex m => (z : Site 2)) h

theorem triangularBoxToBufferedAt_adjMatch (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    ocd_AdjMatch (triangularBoxGraph (2 * k))
      (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m hkm) := by
  intro x y
  rfl

theorem triangularBoxToBufferedAt_not_boundary
    (k m : Nat) (hkm : 2 * k < m)
    (x : TriangularBoxVertex (2 * k)) :
    ¬ triangular.bufferedBoundary m
      (triangularBoxToBufferedAt k m
        ((triangular.id_le_bufferedRadius (2 * k)).trans
          (triangular.bufferedRadius_strictMono.monotone hkm.le)) x) := by
  intro hx
  have hxEarlier : x.1 ∈
      triangular.orbitBox (triangular.bufferedRadius (2 * k)) := by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2 (triangular.id_le_bufferedRadius (2 * k)) x.2
  exact (triangular.bufferedBoundary_not_mem_of_lt hkm _ hx) hxEarlier

theorem triangularBoxToBufferedAt_boundary_of_adj_outside
    (k : Nat) (hk : 1 ≤ k)
    (x : TriangularBoxVertex (2 * k))
    (z : Site 2) (hxz : triangularGraph.Adj x.1 z)
    (hz : z ∉ box 2 (2 * k)) :
    x ∈ triangularBoxShell (2 * k) (2 * k) := by
  have hxtrans : x.1 ∈ triangularTransBox (2 * k) (0 : Site 2) := by
    simpa only [triangularTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using x.2
  have hztrans : z ∉ triangularTransBox (2 * k) (0 : Site 2) := by
    simpa only [triangularTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using hz
  have hboundary := triangularTransBox_boundary_of_adj_outside
    (x := (0 : Site 2)) (R := 2 * k) (by omega)
    ⟨x.1, hxtrans⟩ z hxz hztrans
  simp [triangularBoxShell, triangularTransBoxBoundary,
    vertexBoundary] at hboundary ⊢
  exact hboundary

theorem triangularBoxToBufferedAt_inducedWiring_le
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))) :
    ocd_inducedWiring (triangular.bufferedGraph m)
        (triangularBoxToBufferedAt k m
          ((triangular.id_le_bufferedRadius (2 * k)).trans
            (triangular.bufferedRadius_strictMono.monotone hkm.le)))
        (triangular.bufferedBoundary m) psi ≤
      boundaryCliqueGraph
        (fun x => x ∈ triangularBoxShell (2 * k) (2 * k)) := by
  let hrad : 2 * k ≤ triangular.bufferedRadius m :=
    (triangular.id_le_bufferedRadius (2 * k)).trans
      (triangular.bufferedRadius_strictMono.monotone hkm.le)
  let incl := triangularBoxToBufferedAt k m hrad
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl) (triangularBoxToBufferedAt_injective k m hrad)
    (triangular.bufferedBoundary m)
    (fun x => x ∈ triangularBoxShell (2 * k) (2 * k))
  · intro x
    exact triangularBoxToBufferedAt_not_boundary k m hkm x
  · intro x z hxz hz
    exact triangularBoxToBufferedAt_boundary_of_adj_outside
      k hk x z hxz hz

theorem triangularBufferedInnerShell_finite_le_theta
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hNm : 2 * k ≤ m := hkm.le
  let hrad : 2 * k ≤ triangular.bufferedRadius m :=
    (triangular.id_le_bufferedRadius (2 * k)).trans
      (triangular.bufferedRadius_strictMono.monotone hNm)
  let incl := triangularBoxToBufferedAt k m hrad
  have hcomp : ∀ omega : ConfigSpace (Sym2 (triangular.BufferedVertex m)),
      ocd_innerRestrict (triangularBoxToBuffered k)
          (triangular.bufferedRestrictLE hNm omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ x : TriangularBoxVertex (2 * k),
        triangular.bufferedVertexInclLE hNm (triangularBoxToBuffered k x) =
          incl x := by
      intro x
      apply Subtype.ext
      rfl
    induction e using Sym2.inductionOn with
    | _ x y =>
        change omega s(triangular.bufferedVertexInclLE hNm
            (triangularBoxToBuffered k x),
          triangular.bufferedVertexInclLE hNm
            (triangularBoxToBuffered k y)) =
          omega s(incl x, incl y)
        rw [hv x, hv y]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangularBoxGraph (2 * k))
    (Gout := triangular.bufferedGraph m)
    (ιV := incl)
    (bdryOut := triangular.bufferedBoundary m)
    (triangularBoxToBufferedAt_injective k m hrad)
    (triangularBoxToBufferedAt_adjMatch k m hrad)
    (fun x => x ∈ triangularBoxShell (2 * k) (2 * k))
    hp hp1 hq
    (triangularBoxToBufferedAt_inducedWiring_le k m hk hkm)
    (triangularCenteredShellFullEvent_increasing (2 * k) k)
  rw [triangular.wiredBufferedMeasure_real_cylinder hNm hp hp1
    (zero_lt_one.trans_le hq) (triangularBufferedInnerShellEvent k)]
  have heventEq :
      triangular.bufferedRestrictLE hNm ⁻¹'
          triangularBufferedInnerShellEvent k =
        ocd_innerRestrict incl ⁻¹'
          triangularCenteredShellFullEvent (2 * k) k := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedInnerShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          triangularCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangular.bufferedGraph m)
            (triangular.bufferedBoundary m) p q omega) ≤
      ∑ omega,
        (triangularCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph (2 * k))
            (fun x => x ∈ triangularBoxShell (2 * k) (2 * k)) p q omega := by
        simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = triangularOuterInnerTheta q beta k := by
      simpa [p] using triangularCenteredFullMass_eq_outerInnerTheta
        k hk q beta hq hbeta

theorem triangularBufferedInnerShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := triangular.wiredBufferedMeasure_tendsto_cylinder
    (2 * k) hp hp1 hq (triangularBufferedInnerShellEvent_increasing k)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop (2 * k + 1)] with m hm
  exact triangularBufferedInnerShell_finite_le_theta
    k m hk (by omega) q beta hq hbeta

theorem triangular_root_eq_zero : triangular.root = (0 : Site 2) := by
  have h := triangular.root_mem_fundamentalDomain
  simpa [triangular] using h

theorem triangular_percolationEvent_subset_innerShell
    (k : Nat) (hk : 1 ≤ k) :
    triangular.percolationEvent ⊆
      triangular.bufferedCylinder (2 * k)
        (triangularBufferedInnerShellEvent k) := by
  intro omega hperc
  have hall : ∀ n, omega ∈ triangular.bufferedCylinder n
      (triangular.bufferedRootBoundaryEvent n) := by
    have hinter : omega ∈ ⋂ n, triangular.bufferedCylinder n
        (triangular.bufferedRootBoundaryEvent n) := by
      rw [triangular.iInter_bufferedRootBoundaryCylinder]
      exact hperc
    exact Set.mem_iInter.mp hinter
  obtain ⟨v, hvBoundary, hreach⟩ := hall (2 * k)
  have hfull := triangular.bufferedReachable_full (2 * k) omega hreach
  change (triangular.openSubgraph omega).Reachable triangular.root v.1 at hfull
  rw [triangular_root_eq_zero] at hfull
  have hvOutside : v.1 ∉ box 2 k := by
    intro hvbox
    have hvEarlier : v.1 ∈
        triangular.orbitBox (triangular.bufferedRadius k) := by
      rw [triangular_mem_orbitBox_iff_box]
      exact box_mono 2 (triangular.id_le_bufferedRadius k) hvbox
    exact (triangular.bufferedBoundary_not_mem_of_lt
      (show k < 2 * k by omega) v hvBoundary) hvEarlier
  have hzero : (0 : Site 2) ∈ box 2 k := by simp
  obtain ⟨y, hyReach, w, hyw, hwOutside⟩ :=
    reachable_induce_innerBoundary (triangular.openSubgraph omega)
      (box 2 k) hzero hvOutside hfull
  have hyAdj : triangularGraph.Adj y.1 w := hyw.1
  have hyShell : y.1 ∈ vertexBoundary 2 k := by
    refine ⟨y.2, ?_⟩
    intro hySmall
    exact hwOutside (triangular_adj_mem_box_of_mem_pred hk hySmall hyAdj)
  let phi : ((triangular.openSubgraph omega).induce (box 2 k)) →g
      FK.openSub (triangularBoxGraph (2 * k))
        (ocd_innerRestrict (triangularBoxToBuffered k)
          (triangular.bufferedRestrict (2 * k) omega)) := {
    toFun := fun z => (⟨z.1,
      box_mono 2 (by omega : k ≤ 2 * k) z.2⟩ :
        TriangularBoxVertex (2 * k))
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1 b.1 ∧ omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularBoxToBuffered,
        PeriodicGraph.bufferedRestrict] using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨(0 : Site 2), hzero⟩ = triangularBoxRoot (2 * k) := by
    apply Subtype.ext
    rfl
  have hyMem : phi y ∈ triangularBoxShell (2 * k) k := by
    simp only [triangularBoxShell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hyShell
  change ocd_innerRestrict (triangularBoxToBuffered k)
      (triangular.bufferedRestrict (2 * k) omega) ∈
    triangularCenteredShellFullEvent (2 * k) k
  refine ⟨phi y, hyMem, ?_⟩
  rwa [hroot] at hmapped

theorem triangular_wiredPercolationProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q ≤
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := triangular.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
      triangular.percolationEvent ≤
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) :=
    measureReal_mono (triangular_percolationEvent_subset_innerShell k hk)
      (measure_ne_top _ _)
  rw [show triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q =
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        triangular.percolationEvent by
    simp [PeriodicGraph.wiredPercolationProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (triangularBufferedInnerShell_infinite_le_theta k hk q beta hq hbeta)


def triangularBufferedToBox (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    triangular.BufferedVertex j → TriangularBoxVertex (2 * N) :=
  fun x => ⟨x.1, by
    rw [← triangular_mem_orbitBox_iff_box]
    exact triangular.orbitBox_mono hjn x.2⟩

theorem triangularBufferedToBox_injective (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    Function.Injective (triangularBufferedToBox j N hjn) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : TriangularBoxVertex (2 * N) => (z : Site 2)) h

theorem triangularBufferedToBox_adjMatch (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    ocd_AdjMatch (triangular.bufferedGraph j)
      (triangularBoxGraph (2 * N)) (triangularBufferedToBox j N hjn) := by
  intro x y
  rfl

theorem triangularBufferedToBox_not_outerBoundary
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (x : triangular.BufferedVertex j) :
    triangularBufferedToBox j N (by omega) x ∉
      triangularBoxShell (2 * N) (2 * N) := by
  intro hx
  have hxSmall : x.1 ∈ box 2 (2 * N - 1) := by
    rw [← triangular_mem_orbitBox_iff_box]
    exact triangular.orbitBox_mono (by omega) x.2
  exact (Finset.mem_filter.mp hx).2.2 hxSmall

theorem triangularBufferedToBox_inducedWiring_le
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * N)))) :
    ocd_inducedWiring (triangularBoxGraph (2 * N))
        (triangularBufferedToBox j N (by omega))
        (fun y => y ∈ triangularBoxShell (2 * N) (2 * N)) psi ≤
      boundaryCliqueGraph (triangular.bufferedBoundary j) := by
  let incl := triangularBufferedToBox j N (by omega :
    triangular.bufferedRadius j ≤ 2 * N)
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl) (triangularBufferedToBox_injective j N (by omega))
    (fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    (triangular.bufferedBoundary j)
  · intro x
    exact triangularBufferedToBox_not_outerBoundary j N hjn x
  · intro x z hxz hz
    exact ⟨z, hxz, by
      intro hzOrbit
      exact hz hzOrbit⟩

theorem triangularCenteredShellFullEvent_subset_bufferedRestrict
    (j N : Nat) (hjn : triangular.bufferedRadius j < N) :
    triangularCenteredShellFullEvent (2 * N) N ⊆
      ocd_innerRestrict (triangularBufferedToBox j N (by omega)) ⁻¹'
        triangular.bufferedRootBoundaryEvent j := by
  intro omega hcross
  obtain ⟨v, hvShell, hreach⟩ := hcross
  let S : Set (TriangularBoxVertex (2 * N)) :=
    {x | x.1 ∈ triangular.orbitBox (triangular.bufferedRadius j)}
  have hrootS : triangularBoxRoot (2 * N) ∈ S := by
    change (0 : Site 2) ∈ triangular.orbitBox (triangular.bufferedRadius j)
    rw [triangular_mem_orbitBox_iff_box]
    simp
  have hvOutside : v ∉ S := by
    intro hvS
    have hvSmall : v.1 ∈ box 2 (N - 1) := by
      rw [← triangular_mem_orbitBox_iff_box]
      exact triangular.orbitBox_mono (by omega) hvS
    exact (Finset.mem_filter.mp hvShell).2.2 hvSmall
  obtain ⟨y, hyReach, z, hyz, hzOutside⟩ :=
    reachable_induce_innerBoundary
      (FK.openSub (triangularBoxGraph (2 * N)) omega) S
      hrootS hvOutside hreach
  let phi : ((FK.openSub (triangularBoxGraph (2 * N)) omega).induce S) →g
      FK.openSub (triangular.bufferedGraph j)
        (ocd_innerRestrict (triangularBufferedToBox j N (by omega)) omega) := {
    toFun := fun x => (⟨x.1.1, x.2⟩ : triangular.BufferedVertex j)
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1.1 b.1.1 ∧
        omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularBufferedToBox]
        using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨triangularBoxRoot (2 * N), hrootS⟩ =
      triangular.bufferedRoot j := by
    apply Subtype.ext
    simp [phi, triangularBoxRoot, PeriodicGraph.bufferedRoot_val,
      triangular_root_eq_zero]
  have hyBoundary : triangular.bufferedBoundary j (phi y) := by
    refine ⟨z.1, ?_, ?_⟩
    · exact hyz.1
    · intro hzOrbit
      exact hzOutside hzOrbit
  change ocd_innerRestrict (triangularBufferedToBox j N (by omega)) omega ∈
    triangular.bufferedRootBoundaryEvent j
  refine ⟨phi y, hyBoundary, ?_⟩
  rwa [hroot] at hmapped

noncomputable def triangularBufferedRootArmMass
    (j : Nat) (p q : Real) : Real :=
  finiteWiredEventMass (triangular.bufferedGraph j)
    (triangular.bufferedBoundary j) p q
    (triangular.bufferedRootBoundaryEvent j)

theorem triangularOuterInnerTheta_le_bufferedRootArmMass
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta N ≤
      triangularBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let incl := triangularBufferedToBox j N (by omega :
    triangular.bufferedRadius j ≤ 2 * N)
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangular.bufferedGraph j)
    (Gout := triangularBoxGraph (2 * N))
    (ιV := incl)
    (bdryOut := fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    (triangularBufferedToBox_injective j N (by omega))
    (triangularBufferedToBox_adjMatch j N (by omega))
    (triangular.bufferedBoundary j) hp hp1 hq
    (triangularBufferedToBox_inducedWiring_le j N hjn)
    (triangular.bufferedRootBoundaryEvent_isIncreasing j)
  have hmono := finiteWiredEventMass_mono
    (triangularBoxGraph (2 * N))
    (fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    hp hp1 (zero_lt_one.trans_le hq)
    (triangularCenteredShellFullEvent_subset_bufferedRestrict j N hjn)
  rw [← triangularCenteredFullMass_eq_outerInnerTheta
    N (by omega) q beta hq hbeta]
  unfold triangularBufferedRootArmMass finiteWiredEventMass
  exact hmono.trans (by
    simpa only [bcProb_clique_eq_wiredFkProb] using hdom)

theorem triangularBufferedRestrictLE_self
    (j : Nat) (omega : ConfigSpace (Sym2 (triangular.BufferedVertex j))) :
    triangular.bufferedRestrictLE (le_refl j) omega = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      change omega s(triangular.bufferedVertexInclLE (le_refl j) x,
          triangular.bufferedVertexInclLE (le_refl j) y) = omega s(x, y)
      have hx : triangular.bufferedVertexInclLE (le_refl j) x = x := by
        apply Subtype.ext
        rfl
      have hy : triangular.bufferedVertexInclLE (le_refl j) y = y := by
        apply Subtype.ext
        rfl
      rw [hx, hy]

theorem triangularBufferedRootArmMass_eq_measure
    (j : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triangularBufferedRootArmMass j p q =
      (triangular.wiredBufferedMeasure j hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder j
          (triangular.bufferedRootBoundaryEvent j)) := by
  rw [triangular.wiredBufferedMeasure_real_cylinder (le_refl j)
    hp hp1 hq (triangular.bufferedRootBoundaryEvent j)]
  have hpre : triangular.bufferedRestrictLE (le_refl j) ⁻¹'
      triangular.bufferedRootBoundaryEvent j =
      triangular.bufferedRootBoundaryEvent j := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedRestrictLE_self]
  rw [hpre]
  unfold triangularBufferedRootArmMass finiteWiredEventMass
  rfl

theorem triangularBufferedRootArmMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun j => triangularBufferedRootArmMass j p q) atTop
      (nhds (triangular.wiredPercolationProbability p q)) := by
  have hdiag := triangular.wiredBufferedRootBoundary_diag_tendsto
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with j
  exact (triangularBufferedRootArmMass_eq_measure j hp hp1
    (zero_lt_one.trans_le hq)).symm



theorem triangularOuterInnerTheta_tendsto_percolation
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => triangularOuterInnerTheta q beta n) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q)) := by
  let p := 1 - Real.exp (-beta)
  let thetaInf := triangular.wiredPercolationProbability p q
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have harm : Tendsto (fun j => triangularBufferedRootArmMass j p q)
      atTop (nhds thetaInf) := by
    simpa [thetaInf] using triangularBufferedRootArmMass_tendsto hp hp1 hq
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp harm) epsilon hepsilon
  refine ⟨max 1 (triangular.bufferedRadius J + 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (Nat.le_max_left _ _).trans hn
  have hJn : triangular.bufferedRadius J < n := by
    have := (Nat.le_max_right 1 (triangular.bufferedRadius J + 1)).trans hn
    omega
  have hlower : thetaInf ≤ triangularOuterInnerTheta q beta n := by
    simpa [thetaInf, p] using
      triangular_wiredPercolationProbability_le_theta n hn1 q beta hq hbeta
  have hupper : triangularOuterInnerTheta q beta n ≤
      triangularBufferedRootArmMass J p q :=
    triangularOuterInnerTheta_le_bufferedRootArmMass
      J n hJn q beta hq hbeta
  have hclose := hJ J le_rfl
  rw [Real.dist_eq] at hclose ⊢
  have hclose' := (abs_lt.mp hclose).2
  rw [show p = 1 - Real.exp (-beta) by rfl] at hupper
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

noncomputable def triangularBeta1 (q beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n => IntegrationSubcritical.Sig
    (triangularThresholdTheta q beta0) n b)

noncomputable def triangularCriticalBeta (q : Real) : Real :=
  -Real.log (1 - triangular.criticalPoint q)

theorem triangularCriticalBeta_pos
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 < triangularCriticalBeta q := by
  unfold triangularCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc.2) (by linarith [hpc.1]))

theorem triangularCriticalBeta_param
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    1 - Real.exp (-triangularCriticalBeta q) = triangular.criticalPoint q := by
  unfold triangularCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc.2)]
  ring

theorem betaToP_lt_triangularCritical_of_lt
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : beta < triangularCriticalBeta q) :
    1 - Real.exp (-beta) < triangular.criticalPoint q := by
  rw [← triangularCriticalBeta_param q hpc]
  have hexp : Real.exp (-triangularCriticalBeta q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem triangularCritical_lt_betaToP_of_lt
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : triangularCriticalBeta q < beta) :
    triangular.criticalPoint q < 1 - Real.exp (-beta) := by
  rw [← triangularCriticalBeta_param q hpc]
  have hexp : Real.exp (-beta) < Real.exp (-triangularCriticalBeta q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem triangularNormalizedTheta_tendsto_percolation_div
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => triangularNormalizedTheta q beta0 n beta) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / triangularSharpConstant beta0)) := by
  simpa [triangularNormalizedTheta] using
    (triangularOuterInnerTheta_tendsto_percolation q beta hq hbeta).div_const
      (triangularSharpConstant beta0)

theorem triangularThresholdSet_mem_of_percolation_pos
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hperc : 0 < triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b) := by
  let L := triangular.wiredPercolationProbability
    (1 - Real.exp (-beta)) q / triangularSharpConstant beta0
  have hL : 0 < L := div_pos hperc (triangularSharpConstant_pos beta0)
  have hconv : Tendsto
      (fun n => triangularThresholdTheta q beta0 n beta) atTop (nhds L) := by
    simpa [L, triangularThresholdTheta, not_le.mpr hbeta] using
      triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]

theorem triangularThresholdSet_nonempty
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n b)).Nonempty := by
  let beta := triangularCriticalBeta q + 1
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith [triangularCriticalBeta_pos q hpc]
  have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · rw [sub_pos]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · linarith [Real.exp_pos (-beta)]
  have hsuper : triangular.criticalPoint q < 1 - Real.exp (-beta) :=
    triangularCritical_lt_betaToP_of_lt q hpc (by simp [beta])
  have hsharp := triangular.offCriticalSharpness hq hpc
  have hperc : 0 < triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q := hsharp.2 _ hp hsuper
  exact ⟨beta, triangularThresholdSet_mem_of_percolation_pos
    q beta0 beta hq hbeta hperc⟩

theorem triangularBeta1_nonneg
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 ≤ triangularBeta1 q beta0 := by
  unfold triangularBeta1 BetaThresholdBound.beta1
  apply le_csInf (triangularThresholdSet_nonempty q beta0 hq hpc)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / triangularSharpConstant beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / triangularSharpConstant beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [triangularThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem triangularThresholdLogRatio_bddAbove
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) := by
  exact BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)
    (1 / triangularSharpConstant beta0)
    (one_le_inv_triangularSharpConstant beta0 hbeta0)
    (fun n hn => triangularThresholdSig_pos n (by omega) q beta0 beta hq)
    (fun n => triangularThresholdSig_le_linear n q beta0 beta hq)

theorem triangularThresholdLogRatio_cobounded
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) := by
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta))
    (x := 0) atTop ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig1 : 1 ≤ IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta := by
    have hzero : 1 ≤ triangularThresholdTheta q beta0 0 beta := by
      have hM := one_le_inv_triangularSharpConstant beta0 hbeta0
      by_cases hbeta : beta ≤ 0
      · simpa [triangularThresholdTheta, hbeta] using hM
      · rw [triangularThresholdTheta_of_pos 0 q beta0 beta (lt_of_not_ge hbeta)]
        simpa [triangularNormalizedTheta, triangularOuterInnerTheta] using hM
    exact hzero.trans (by
      unfold IntegrationSubcritical.Sig
      apply Finset.single_le_sum
        (fun k _ => triangularThresholdTheta_nonneg k q beta0 beta hq)
      exact Finset.mem_range.mpr (by omega))
  unfold BetaThresholdBound.logRatio
  exact div_nonneg (Real.log_nonneg hsig1) hlogn.le


theorem triangularPercolation_difference_lower
    (q beta0 beta' beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : triangularBeta1 q beta0 < beta') (hbeta : beta' ≤ beta)
    (hupper : beta ≤ beta0) :
    beta - beta' ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
          triangularSharpConstant beta0 -
        triangular.wiredPercolationProbability (1 - Real.exp (-beta')) q /
          triangularSharpConstant beta0 := by
  let f := triangularNormalizedTheta q beta0
  let fp := triangularNormalizedThetaPrime q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := triangularBeta1_nonneg q beta0 hq hpc
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : ∀ i x, x ∈ Set.Icc beta' beta →
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / triangularSharpConstant beta0 := by
        funext z
        simp [f, triangularNormalizedTheta, triangularOuterInnerTheta]
      rw [hconst]
      simpa [fp, triangularNormalizedThetaPrime,
        triangularOuterInnerThetaPrime, triangularOuterInnerTheta] using
        (hasDerivAt_const x (1 / triangularSharpConstant beta0))
    · exact hasDerivAt_triangularNormalizedTheta i
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 ≤ f i x := by
    intro i x hi hx
    exact triangularNormalizedTheta_nonneg i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 < Sig i x := by
    intro i x hi hx
    exact triangularNormalizedSig_pos i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : ∀ i : Nat, ∀ x, 1 ≤ i → x ∈ Set.Icc beta' beta →
      ((i : Real) / Sig i x) * f i x ≤ fp i x := by
    intro i x hi hx
    exact triangularNormalizedTheta_differential i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc beta' beta →
      Sig n beta' ≤ Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' ≤ Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        triangularNormalizedTheta_mono_beta k q beta0 beta' x hq
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : ∀ x, x ∈ Set.Icc beta' beta →
      Sig 1 x ≤ 1 / triangularSharpConstant beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, triangularNormalizedTheta,
      triangularOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / triangularSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta')) q / triangularSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta') := by
    funext n
    symm
    exact triangularThresholdSig_of_pos n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact triangularThresholdLogRatio_cobounded
      q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact triangularThresholdLogRatio_bddAbove
      q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 ≤ Filter.limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (triangularThresholdSet_nonempty q beta0 hq hpc)
      (fun hab n => triangularThresholdSig_mono_beta n q beta0 hq hab)
      (fun x n hn => triangularThresholdSig_pos n (by omega) q beta0 x hq)
      (fun x => triangularThresholdLogRatio_cobounded
        q beta0 x hq hbeta0pos.le)
      (fun x => triangularThresholdLogRatio_bddAbove
        q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
      triangularSharpConstant beta0)
    (triangular.wiredPercolationProbability (1 - Real.exp (-beta')) q /
      triangularSharpConstant beta0)
    (1 / triangularSharpConstant beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1

theorem triangularPercolation_meanField_lower
    (q beta0 beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : triangularBeta1 q beta0 < beta) (hupper : beta ≤ beta0) :
    triangularSharpConstant beta0 * (beta - triangularBeta1 q beta0) ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
  have hc := triangularSharpConstant_pos beta0
  have hnormalized : beta - triangularBeta1 q beta0 ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
        triangularSharpConstant beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => triangular.wiredPercolationProbability
        (1 - Real.exp (-x)) q / triangularSharpConstant beta0)
      (β₁ := triangularBeta1 q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg
        (triangular.wiredPercolationProbability_nonneg _ _) hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact triangularPercolation_difference_lower q beta0 beta' beta hq hpc
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith



theorem triangularBeta1_eq_criticalBeta_of_ge
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta0 : triangularCriticalBeta q ≤ beta0) :
    triangularBeta1 q beta0 = triangularCriticalBeta q := by
  let betaC := triangularCriticalBeta q
  let Sgf : Real → Nat → Real := fun b n => IntegrationSubcritical.Sig
    (triangularThresholdTheta q beta0) n b
  have hbetaCpos : 0 < betaC := triangularCriticalBeta_pos q hpc
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using triangularThresholdSet_bddBelow q beta0
  have hsharp := triangular.offCriticalSharpness hq hpc
  have hle : triangularBeta1 q beta0 ≤ betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hpcp : triangular.criticalPoint q < 1 - Real.exp (-beta) :=
      triangularCritical_lt_betaToP_of_lt q hpc hbetaCbeta
    have hperc : 0 < triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := hsharp.2 _ hp hpcp
    have hmem := triangularThresholdSet_mem_of_percolation_pos
      q beta0 beta hq hbetapos hperc
    unfold triangularBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC ≤ triangularBeta1 q beta0 := by
    by_contra hnot
    have hlt : triangularBeta1 q beta0 < betaC := lt_of_not_ge hnot
    let beta := (triangularBeta1 q beta0 + betaC) / 2
    have hcrit : triangularBeta1 q beta0 < beta := by
      dsimp [beta]
      linarith
    have hbetaC : beta < betaC := by
      dsimp [beta]
      linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (triangularBeta1_nonneg q beta0 hq hpc) hcrit
    have hmean := triangularPercolation_meanField_lower
      q beta0 beta hq hpc hcrit (hbetaC.le.trans hbeta0)
    have hpercPos : 0 < triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := by
      have hc := triangularSharpConstant_pos beta0
      have hgap : 0 < beta - triangularBeta1 q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hppc : 1 - Real.exp (-beta) < triangular.criticalPoint q :=
      betaToP_lt_triangularCritical_of_lt q hpc hbetaC
    have hnotperc := hsharp.1 _ hp hppc
    exact hnotperc hpercPos
  exact le_antisymm hle hge



theorem triangularOuterInner_exponential_decay_below_critical
    (q beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta : 0 < beta) (hsub : beta < triangularCriticalBeta q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n →
      triangularOuterInnerTheta q beta n ≤
        Real.exp (-((n : Real) / Q *
          ((triangularCriticalBeta q - beta) / 4))) := by
  let betaC := triangularCriticalBeta q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid ≤ betaC := by dsimp [betaMid]; linarith
  have hthreshold : triangularBeta1 q betaC = betaC :=
    triangularBeta1_eq_criticalBeta_of_ge q betaC hq hpc le_rfl
  have hmidThreshold : betaMid < triangularBeta1 q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    triangularOuterInner_subcritical_decay_of_threshold
      q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [triangularBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn

noncomputable def triangularTransBufferLevel (k : Nat) (x : Site 2) : Nat :=
  siteRadius x + 2 * k

theorem triangularTransBox_mem_bufferLevel
    (k : Nat) (x : Site 2) (y : TriangularTransBoxVertex (2 * k) x) :
    y.1 ∈ box 2 (triangularTransBufferLevel k x) := by
  rw [mem_box_iff_siteRadius_le]
  have hrad : centeredRadius x y.1 ≤ 2 * k := by
    rw [centeredRadius, siteRadius_le_iff]
    exact y.2
  exact (siteRadius_triangle y.1 x).trans (Nat.add_le_add_left hrad _)

def triangularTransBoxToBuffered (k : Nat) (x : Site 2) :
    TriangularTransBoxVertex (2 * k) x →
      triangular.BufferedVertex (triangularTransBufferLevel k x) :=
  fun y => ⟨y.1, by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2
      (triangular.id_le_bufferedRadius (triangularTransBufferLevel k x))
      (triangularTransBox_mem_bufferLevel k x y)⟩

theorem triangularTransBoxToBuffered_injective (k : Nat) (x : Site 2) :
    Function.Injective (triangularTransBoxToBuffered k x) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun w : triangular.BufferedVertex
    (triangularTransBufferLevel k x) => (w : Site 2)) h

noncomputable def triangularTransBoxToBufferedAt (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    TriangularTransBoxVertex (2 * k) x → triangular.BufferedVertex m :=
  fun y => triangular.bufferedVertexInclLE hm
    (triangularTransBoxToBuffered k x y)

theorem triangularTransBoxToBufferedAt_injective
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    Function.Injective (triangularTransBoxToBufferedAt k x m hm) :=
  (triangular.bufferedVertexInclLE hm).injective.comp
    (triangularTransBoxToBuffered_injective k x)

theorem triangularTransBoxToBufferedAt_adjMatch
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    ocd_AdjMatch (triangularTransBoxGraph (2 * k) x)
      (triangular.bufferedGraph m)
      (triangularTransBoxToBufferedAt k x m hm) := by
  intro y z
  rfl

theorem triangularTransBoxToBufferedAt_inducedWiring_le
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x < m)
    (psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))) :
    ocd_inducedWiring (triangular.bufferedGraph m)
        (triangularTransBoxToBufferedAt k x m hm.le)
        (triangular.bufferedBoundary m) psi ≤
      boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
  let incl := triangularTransBoxToBufferedAt k x m hm.le
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl)
    (triangularTransBoxToBufferedAt_injective k x m hm.le)
    (triangular.bufferedBoundary m)
    (triangularTransBoxBoundary (2 * k) x)
  · intro y hy
    have hyEarlier : y.1 ∈ triangular.orbitBox
        (triangular.bufferedRadius (triangularTransBufferLevel k x)) :=
      (triangularTransBoxToBuffered k x y).2
    exact (triangular.bufferedBoundary_not_mem_of_lt hm _ hy) hyEarlier
  · intro y z hyz hz
    exact triangularTransBox_boundary_of_adj_outside (by omega) y z hyz hz

def triangularBufferedTransShellEvent (k : Nat) (x : Site 2) :
    Set (ConfigSpace (Sym2
      (triangular.BufferedVertex (triangularTransBufferLevel k x)))) :=
  ocd_innerRestrict (triangularTransBoxToBuffered k x) ⁻¹'
    triangularTransShellFullEvent (2 * k) k x

theorem triangularTransShellFullEvent_increasing
    (R k : Nat) (x : Site 2) :
    IsIncreasing (triangularTransShellFullEvent R k x) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro a b hab
  rw [FK.openSub_adj] at hab ⊢
  refine ⟨hab.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hab.2] using home s(a, b)

theorem triangularBufferedTransShellEvent_increasing
    (k : Nat) (x : Site 2) :
    IsIncreasing (triangularBufferedTransShellEvent k x) := by
  intro omega eta home hmem
  exact triangularTransShellFullEvent_increasing (2 * k) k x
    (fun e => home _) hmem

theorem triangularTransFullMass_eq_outerInnerTheta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    finiteWiredEventMass (triangularTransBoxGraph (2 * k) x)
        (triangularTransBoxBoundary (2 * k) x)
        (1 - Real.exp (-beta)) q
        (triangularTransShellFullEvent (2 * k) k x) =
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have htrans := triangularTransShellEvent_betaMean_eq_centeredFullMass
    (2 * k) k x q beta (zero_lt_one.trans_le hq) hbeta
  have hparam : FK.betaParams
      (fun _ : Sym2 (TriangularTransBoxVertex (2 * k) x) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [FK.betaParams]
  rw [hparam] at htrans
  rw [FK.activeBCMean_boundaryClique_eq_wired
    (triangularTransBoxGraph (2 * k) x)
    (triangularTransBoxBoundary (2 * k) x)
    hp hp1 (zero_lt_one.trans_le hq)] at htrans
  rw [← triangularCenteredFullMass_eq_outerInnerTheta
    k hk q beta hq hbeta]
  unfold finiteWiredEventMass
  calc
    (∑ omega,
      (triangularTransShellFullEvent (2 * k) k x).indicator
          (fun _ => (1 : Real)) omega *
        wiredFkProb (triangularTransBoxGraph (2 * k) x)
          (triangularTransBoxBoundary (2 * k) x)
          (1 - Real.exp (-beta)) q omega) =
      ∑ omega,
        (triangularTransShellEvent (2 * k) k x).indicator
            (fun _ => (1 : Real))
            (restrictActive (triangularTransBoxGraph (2 * k) x) omega) *
          wiredFkProb (triangularTransBoxGraph (2 * k) x)
            (triangularTransBoxBoundary (2 * k) x)
            (1 - Real.exp (-beta)) q omega := by
        apply Finset.sum_congr rfl
        intro omega homega
        congr 1
        rw [Set.indicator_apply, Set.indicator_apply]
        have heq := Set.ext_iff.mp
          (restrictActive_preimage_triangularTransShellEvent (2 * k) k x) omega
        split_ifs with h h' <;> simp_all
    _ = _ := htrans

theorem triangularBufferedTransShell_finite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let L := triangularTransBufferLevel k x
  let incl := triangularTransBoxToBufferedAt k x m hm.le
  have hcomp : ∀ omega : ConfigSpace (Sym2 (triangular.BufferedVertex m)),
      ocd_innerRestrict (triangularTransBoxToBuffered k x)
          (triangular.bufferedRestrictLE hm.le omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ y : TriangularTransBoxVertex (2 * k) x,
        triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x y) = incl y := by
      intro y
      rfl
    induction e using Sym2.inductionOn with
    | _ y z =>
        change omega s(triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x y),
          triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x z)) =
          omega s(incl y, incl z)
        rw [hv y, hv z]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangularTransBoxGraph (2 * k) x)
    (Gout := triangular.bufferedGraph m)
    (ιV := incl)
    (bdryOut := triangular.bufferedBoundary m)
    (triangularTransBoxToBufferedAt_injective k x m hm.le)
    (triangularTransBoxToBufferedAt_adjMatch k x m hm.le)
    (triangularTransBoxBoundary (2 * k) x)
    hp hp1 hq
    (triangularTransBoxToBufferedAt_inducedWiring_le k hk x m hm)
    (triangularTransShellFullEvent_increasing (2 * k) k x)
  rw [triangular.wiredBufferedMeasure_real_cylinder hm.le hp hp1
    (zero_lt_one.trans_le hq) (triangularBufferedTransShellEvent k x)]
  have heventEq :
      triangular.bufferedRestrictLE hm.le ⁻¹'
          triangularBufferedTransShellEvent k x =
        ocd_innerRestrict incl ⁻¹'
          triangularTransShellFullEvent (2 * k) k x := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedTransShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          triangularTransShellFullEvent (2 * k) k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangular.bufferedGraph m)
            (triangular.bufferedBoundary m) p q omega) ≤
      finiteWiredEventMass (triangularTransBoxGraph (2 * k) x)
        (triangularTransBoxBoundary (2 * k) x) p q
        (triangularTransShellFullEvent (2 * k) k x) := by
      unfold finiteWiredEventMass
      simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = triangularOuterInnerTheta q beta k := by
      simpa [p] using triangularTransFullMass_eq_outerInnerTheta
        k hk x q beta hq hbeta

theorem triangularBufferedTransShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := triangular.wiredBufferedMeasure_tendsto_cylinder
    (triangularTransBufferLevel k x) hp hp1 hq
    (triangularBufferedTransShellEvent_increasing k x)
  apply le_of_tendsto htend
  filter_upwards [eventually_ge_atTop (triangularTransBufferLevel k x + 1)]
    with m hm
  exact triangularBufferedTransShell_finite_le_theta
    k hk x m (by omega) q beta hq hbeta

theorem triangular_twoPointEvent_subset_transShell
    (k : Nat) (hk : 1 ≤ k) (x y : Site 2)
    (hxy : k ≤ centeredRadius x y) :
    triangular.twoPointEvent x y ⊆
      triangular.bufferedCylinder (triangularTransBufferLevel k x)
        (triangularBufferedTransShellEvent k x) := by
  intro omega hconn
  have hxSmall : x ∈ triangularTransBox (k - 1) x := by
    simp [triangularTransBox, StatMech.FK.fvs_transBox]
  have hyOutside : y ∉ triangularTransBox (k - 1) x := by
    intro hy
    have hyrad : centeredRadius x y ≤ k - 1 := by
      rw [centeredRadius, siteRadius_le_iff]
      exact hy
    omega
  obtain ⟨a, haReach, z, haz, hzOutside⟩ :=
    reachable_induce_innerBoundary (triangular.openSubgraph omega)
      (triangularTransBox (k - 1) x) hxSmall hyOutside hconn
  have hazTri : triangularGraph.Adj a.1 z := haz.1
  have hzK : z - x ∈ box 2 k := by
    have hadj := triangular_adj_sub_right x hazTri
    simpa [Nat.sub_add_cancel hk] using
      triangular_adj_mem_box_succ a.2 hadj
  have hzBoundary : z - x ∈ vertexBoundary 2 k := ⟨hzK, hzOutside⟩
  have hz2k : z ∈ triangularTransBox (2 * k) x := by
    exact box_mono 2 (by omega : k ≤ 2 * k) hzK
  let phi : ((triangular.openSubgraph omega).induce
      (triangularTransBox (k - 1) x)) →g
      FK.openSub (triangularTransBoxGraph (2 * k) x)
        (ocd_innerRestrict (triangularTransBoxToBuffered k x)
          (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega)) := {
    toFun := fun a => (⟨a.1, box_mono 2 (by omega : k - 1 ≤ 2 * k) a.2⟩ :
      TriangularTransBoxVertex (2 * k) x)
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1 b.1 ∧ omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularTransBoxToBuffered,
        PeriodicGraph.bufferedRestrict] using hab.2 }
  let zi : TriangularTransBoxVertex (2 * k) x := ⟨z, hz2k⟩
  have hmapped := haReach.map phi
  have hroot : phi ⟨x, hxSmall⟩ = triangularTransBoxCenter (2 * k) x := by
    apply Subtype.ext
    rfl
  have hazInner : (FK.openSub (triangularTransBoxGraph (2 * k) x)
      (ocd_innerRestrict (triangularTransBoxToBuffered k x)
        (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega))).Adj
      (phi a) zi := by
    rw [FK.openSub_adj]
    refine ⟨hazTri, ?_⟩
    simpa [ocd_innerRestrict, ocd_innerEdge, triangularTransBoxToBuffered,
      PeriodicGraph.bufferedRestrict, phi, zi] using haz.2
  have hreachZ := hmapped.trans hazInner.reachable
  have hzShell : zi ∈ triangularTransBoxShell (2 * k) k x := by
    simp only [triangularTransBoxShell, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hzBoundary
  change ocd_innerRestrict (triangularTransBoxToBuffered k x)
      (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega) ∈
    triangularTransShellFullEvent (2 * k) k x
  refine ⟨zi, hzShell, ?_⟩
  rwa [hroot] at hreachZ

theorem triangular_wiredTwoPointProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (x y : Site 2)
    (hxy : k ≤ centeredRadius x y) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangular.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := triangular.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.twoPointEvent x y) ≤
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) :=
    measureReal_mono (triangular_twoPointEvent_subset_transShell k hk x y hxy)
      (measure_ne_top _ _)
  rw [show triangular.wiredTwoPointProbability
      (1 - Real.exp (-beta)) q x y =
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.twoPointEvent x y) by
    simp [PeriodicGraph.wiredTwoPointProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (triangularBufferedTransShell_infinite_le_theta
      k hk x q beta hq hbeta)

theorem betaOfP_pos {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    0 < -Real.log (1 - p) :=
  neg_pos.mpr (Real.log_neg (sub_pos.mpr hp1) (by linarith))

theorem betaOfP_param {p : Real} (hp1 : p < 1) :
    1 - Real.exp (-(-Real.log (1 - p))) = p := by
  rw [neg_neg, Real.exp_log (sub_pos.mpr hp1)]
  ring

theorem betaOfP_lt_criticalBeta
    (q p : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hp1 : p < 1) (hsub : p < triangular.criticalPoint q) :
    -Real.log (1 - p) < triangularCriticalBeta q := by
  by_contra hnot
  have hle : triangularCriticalBeta q ≤ -Real.log (1 - p) :=
    le_of_not_gt hnot
  have hexp : Real.exp (-(-Real.log (1 - p))) ≤
      Real.exp (-triangularCriticalBeta q) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  have hpEq := betaOfP_param hp1
  have hcEq := triangularCriticalBeta_param q hpc
  linarith

theorem centeredRadius_eq_zero_iff (x y : Site 2) :
    centeredRadius x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply funext
    intro i
    have hle : centeredRadius x y ≤ 0 := h.le
    rw [centeredRadius, siteRadius_le_iff] at hle
    have hi := hle i
    simp only at hi
    have : y i - x i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp hi)
    linarith
  · rintro rfl
    exact centeredRadius_self x



theorem triangular_subcritical_twoPoint_exponential_decay
    (q : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    SubcriticalTwoPointExponentialDecay
      triangular q (triangular.criticalPoint q) := by
  intro p hp
  have hp1 : p < 1 := hp.2.trans hpc.2
  let beta := -Real.log (1 - p)
  have hbeta : 0 < beta := betaOfP_pos hp.1 hp1
  have hsub : beta < triangularCriticalBeta q :=
    betaOfP_lt_criticalBeta q p hpc hp1 hp.2
  obtain ⟨Q, hQ, hdecay⟩ :=
    triangularOuterInner_exponential_decay_below_critical
      q beta hq hpc hbeta hsub
  let delta := (triangularCriticalBeta q - beta) / 4
  let c := delta / (2 * Q)
  refine ⟨c, 1, ?_, by norm_num, ?_⟩
  · have hdelta : 0 < delta := by dsimp [delta]; linarith
    dsimp [c]
    positivity
  intro x y
  by_cases hxy : x = y
  · subst y
    simpa using triangular.wiredTwoPointProbability_le_one p q x x
  let r := centeredRadius x y
  have hr : 1 ≤ r := by
    exact Nat.one_le_iff_ne_zero.mpr
      (fun h => hxy ((centeredRadius_eq_zero_iff x y).mp h))
  have hpEq : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    exact betaOfP_param hp1
  have hpoint := triangular_wiredTwoPointProbability_le_theta
    r hr x y le_rfl q beta hq hbeta
  rw [hpEq] at hpoint
  have harm := hdecay r hr
  have hrbox : y - x ∈ box 2 r := by
    rw [mem_box_iff_siteRadius_le]
    change centeredRadius x y ≤ r
    exact le_rfl
  have hdistNat := triangular_dist_le_two_mul_of_sub_mem_box hrbox
  have hdist : (triangularGraph.dist x y : Real) ≤ 2 * (r : Real) := by
    exact_mod_cast hdistNat
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hrate : c * (triangularGraph.dist x y : Real) ≤
      ((r : Real) / Q) * delta := by
    calc
      c * (triangularGraph.dist x y : Real) ≤ c * (2 * (r : Real)) :=
        mul_le_mul_of_nonneg_left hdist hc.le
      _ = ((r : Real) / Q) * delta := by
        dsimp [c]
        field_simp
  calc
    triangular.wiredTwoPointProbability p q x y ≤
        triangularOuterInnerTheta q beta r := hpoint
    _ ≤ Real.exp (-(((r : Real) / Q) * delta)) := by
      simpa [delta, mul_assoc] using harm
    _ ≤ 1 * Real.exp (-c * (triangularGraph.dist x y : Real)) := by
      rw [one_mul]
      simpa [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hrate)

end StatMech.FK.PeriodicPlanar
