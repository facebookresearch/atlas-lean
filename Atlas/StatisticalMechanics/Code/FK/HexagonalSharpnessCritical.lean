/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.HexagonalSharpnessThreshold
import Code.FK.HexagonalTranslatedArm
import Code.FK.TriHexFKFiniteWiredCofinal
import Code.OSSS.BetaCMatch





open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS
open RevealmentTranslation



def hexagonalBoxToBuffered (k : Nat) :
    HexagonalBoxVertex (2 * k) → hexagonal.BufferedVertex (2 * k) :=
  fun x => ⟨x.1, by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2 (hexagonal.id_le_bufferedRadius (2 * k)) x.2.1⟩

theorem hexagonalBoxToBuffered_injective (k : Nat) :
    Function.Injective (hexagonalBoxToBuffered k) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : hexagonal.BufferedVertex (2 * k) => (z : HexVertex)) h

theorem hexagonalBoxToBuffered_adjMatch (k : Nat) :
    ocd_AdjMatch (hexagonalBoxGraph (2 * k))
      (hexagonal.bufferedGraph (2 * k)) (hexagonalBoxToBuffered k) := by
  intro x y
  rfl


def hexagonalBufferedInnerShellEvent (k : Nat) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex (2 * k)))) :=
  ocd_innerRestrict (hexagonalBoxToBuffered k) ⁻¹'
    hexagonalCenteredShellFullEvent (2 * k) k

theorem hexagonalCenteredShellFullEvent_increasing (R k : Nat) :
    IsIncreasing (hexagonalCenteredShellFullEvent R k) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro x z hxz
  rw [FK.openSub_adj] at hxz ⊢
  refine ⟨hxz.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hxz.2] using home s(x, z)

theorem hexagonalBufferedInnerShellEvent_increasing (k : Nat) :
    IsIncreasing (hexagonalBufferedInnerShellEvent k) := by
  intro omega eta home hmem
  exact hexagonalCenteredShellFullEvent_increasing (2 * k) k
    (fun e => home _) hmem



def hexagonalBoxToBufferedAt (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    HexagonalBoxVertex (2 * k) → hexagonal.BufferedVertex m :=
  fun x => ⟨x.1, by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2 hkm x.2.1⟩

theorem hexagonalBoxToBufferedAt_injective (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    Function.Injective (hexagonalBoxToBufferedAt k m hkm) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : hexagonal.BufferedVertex m => (z : HexVertex)) h

theorem hexagonalBoxToBufferedAt_adjMatch (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    ocd_AdjMatch (hexagonalBoxGraph (2 * k))
      (hexagonal.bufferedGraph m) (hexagonalBoxToBufferedAt k m hkm) := by
  intro x y
  rfl

theorem hexagonalBoxToBufferedAt_not_boundary
    (k m : Nat) (hkm : 2 * k < m)
    (x : HexagonalBoxVertex (2 * k)) :
    ¬ hexagonal.bufferedBoundary m
      (hexagonalBoxToBufferedAt k m
        ((hexagonal.id_le_bufferedRadius (2 * k)).trans
          (hexagonal.bufferedRadius_strictMono.monotone hkm.le)) x) := by
  intro hx
  have hxEarlier : x.1 ∈
      hexagonal.orbitBox (hexagonal.bufferedRadius (2 * k)) := by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2 (hexagonal.id_le_bufferedRadius (2 * k)) x.2.1
  exact (hexagonal.bufferedBoundary_not_mem_of_lt hkm _ hx) hxEarlier

theorem hexagonalBoxToBufferedAt_boundary_of_adj_outside
    (k : Nat) (hk : 1 ≤ k)
    (x : HexagonalBoxVertex (2 * k))
    (z : HexVertex) (hxz : hexagonalGraph.Adj x.1 z)
    (hz : z.1 ∉ box 2 (2 * k)) :
    x ∈ hexagonalBoxShell (2 * k) (2 * k) := by
  have hxtrans : x.1.1 ∈ hexagonalTransBox (2 * k) (0 : Site 2) := by
    simpa only [hexagonalTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using x.2.1
  have hztrans : z.1 ∉ hexagonalTransBox (2 * k) (0 : Site 2) := by
    simpa only [hexagonalTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using hz
  have hboundary := hexagonalTransBox_boundary_of_adj_outside
    (x := (0 : Site 2)) (R := 2 * k) (by omega)
    ⟨x.1, ⟨hxtrans, Set.mem_univ _⟩⟩ z hxz hztrans
  simp [hexagonalBoxShell, hexagonalTransBoxBoundary,
    vertexBoundary] at hboundary ⊢
  exact hboundary

theorem hexagonalBoxToBufferedAt_inducedWiring_le
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))) :
    ocd_inducedWiring (hexagonal.bufferedGraph m)
        (hexagonalBoxToBufferedAt k m
          ((hexagonal.id_le_bufferedRadius (2 * k)).trans
            (hexagonal.bufferedRadius_strictMono.monotone hkm.le)))
        (hexagonal.bufferedBoundary m) psi ≤
      boundaryCliqueGraph
        (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k)) := by
  let hrad : 2 * k ≤ hexagonal.bufferedRadius m :=
    (hexagonal.id_le_bufferedRadius (2 * k)).trans
      (hexagonal.bufferedRadius_strictMono.monotone hkm.le)
  let incl := hexagonalBoxToBufferedAt k m hrad
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph incl
    (fun _ => rfl) (hexagonalBoxToBufferedAt_injective k m hrad)
    (hexagonal.bufferedBoundary m)
    (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k))
  · intro x
    exact hexagonalBoxToBufferedAt_not_boundary k m hkm x
  · intro x z hxz hz
    apply hexagonalBoxToBufferedAt_boundary_of_adj_outside k hk x z hxz
    intro hzbox
    exact hz ⟨hzbox, Set.mem_univ _⟩

theorem hexagonalBufferedInnerShell_finite_le_theta
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (2 * k)
          (hexagonalBufferedInnerShellEvent k)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hNm : 2 * k ≤ m := hkm.le
  let hrad : 2 * k ≤ hexagonal.bufferedRadius m :=
    (hexagonal.id_le_bufferedRadius (2 * k)).trans
      (hexagonal.bufferedRadius_strictMono.monotone hNm)
  let incl := hexagonalBoxToBufferedAt k m hrad
  have hcomp : ∀ omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex m)),
      ocd_innerRestrict (hexagonalBoxToBuffered k)
          (hexagonal.bufferedRestrictLE hNm omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ x : HexagonalBoxVertex (2 * k),
        hexagonal.bufferedVertexInclLE hNm (hexagonalBoxToBuffered k x) =
          incl x := by
      intro x
      apply Subtype.ext
      rfl
    induction e using Sym2.inductionOn with
    | _ x y =>
        change omega s(hexagonal.bufferedVertexInclLE hNm
            (hexagonalBoxToBuffered k x),
          hexagonal.bufferedVertexInclLE hNm
            (hexagonalBoxToBuffered k y)) =
          omega s(incl x, incl y)
        rw [hv x, hv y]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := hexagonalBoxGraph (2 * k))
    (Gout := hexagonal.bufferedGraph m)
    (ιV := incl)
    (bdryOut := hexagonal.bufferedBoundary m)
    (hexagonalBoxToBufferedAt_injective k m hrad)
    (hexagonalBoxToBufferedAt_adjMatch k m hrad)
    (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k))
    hp hp1 hq
    (hexagonalBoxToBufferedAt_inducedWiring_le k m hk hkm)
    (hexagonalCenteredShellFullEvent_increasing (2 * k) k)
  rw [hexagonal.wiredBufferedMeasure_real_cylinder hNm hp hp1
    (zero_lt_one.trans_le hq) (hexagonalBufferedInnerShellEvent k)]
  have heventEq :
      hexagonal.bufferedRestrictLE hNm ⁻¹'
          hexagonalBufferedInnerShellEvent k =
        ocd_innerRestrict incl ⁻¹'
          hexagonalCenteredShellFullEvent (2 * k) k := by
    ext omega
    simp only [Set.mem_preimage, hexagonalBufferedInnerShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          hexagonalCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonal.bufferedGraph m)
            (hexagonal.bufferedBoundary m) p q omega) ≤
      ∑ omega,
        (hexagonalCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph (2 * k))
            (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k)) p q omega := by
        simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = hexagonalOuterInnerTheta q beta k := by
      simpa [p] using hexagonalCenteredFullMass_eq_outerInnerTheta
        k hk q beta hq hbeta

theorem hexagonalBufferedInnerShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (2 * k)
          (hexagonalBufferedInnerShellEvent k)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := hexagonal.wiredBufferedMeasure_tendsto_cylinder
    (2 * k) hp hp1 hq (hexagonalBufferedInnerShellEvent_increasing k)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop (2 * k + 1)] with m hm
  exact hexagonalBufferedInnerShell_finite_le_theta
    k m hk (by omega) q beta hq hbeta

theorem hexagonal_root_coord_eq_zero : hexagonal.root.1 = (0 : Site 2) := by
  have h : hexagonal.root = ((0, false) : HexVertex) ∨
      hexagonal.root = ((0, true) : HexVertex) := by
    simpa [hexagonal] using hexagonal.root_mem_fundamentalDomain
  rcases h with h | h <;> simp [h]

theorem site_neg_mem_box {n : Nat} {x : Site 2} (hx : x ∈ box 2 n) :
    -x ∈ box 2 n := by
  intro i
  simpa using hx i




noncomputable def hexagonalRootFrame : HexVertex ≃ HexVertex where
  toFun v := if hexagonal.root.2 then hexagonalReflect v else v
  invFun v := if hexagonal.root.2 then hexagonalReflect v else v
  left_inv v := by
    by_cases h : hexagonal.root.2 <;>
      simp [h, hexagonalReflect]
  right_inv v := by
    by_cases h : hexagonal.root.2 <;>
      simp [h, hexagonalReflect]

theorem hexagonalRootFrame_adj (u v : HexVertex) :
    hexagonalGraph.Adj (hexagonalRootFrame u) (hexagonalRootFrame v) ↔
      hexagonalGraph.Adj u v := by
  by_cases h : hexagonal.root.2
  · simpa [hexagonalRootFrame, h] using (hexagonalReflect_adj u v).symm
  · simp [hexagonalRootFrame, h]

theorem hexagonalRootFrame_coord_mem_box_iff (n : Nat) (v : HexVertex) :
    (hexagonalRootFrame v).1 ∈ box 2 n ↔ v.1 ∈ box 2 n := by
  by_cases h : hexagonal.root.2
  · constructor <;> intro hv
    · have := site_neg_mem_box hv
      simpa [hexagonalRootFrame, h, hexagonalReflect] using this
    · simpa [hexagonalRootFrame, h, hexagonalReflect] using site_neg_mem_box hv
  · simp [hexagonalRootFrame, h]

theorem hexagonalRootFrame_mem_orbitBox_iff (n : Nat) (v : HexVertex) :
    hexagonalRootFrame v ∈ hexagonal.orbitBox n ↔
      v ∈ hexagonal.orbitBox n := by
  rw [hexagonal_mem_orbitBox_iff_box, hexagonal_mem_orbitBox_iff_box]
  exact hexagonalRootFrame_coord_mem_box_iff n v

theorem hexagonalRootFrame_root :
    hexagonalRootFrame hexagonal.root = ((0, false) : HexVertex) := by
  by_cases hcolor : hexagonal.root.2
  · simp [hexagonalRootFrame, hcolor, hexagonalReflect,
      hexagonal_root_coord_eq_zero]
  · rw [show hexagonalRootFrame hexagonal.root = hexagonal.root by
      simp [hexagonalRootFrame, hcolor]]
    apply Prod.ext
    · exact hexagonal_root_coord_eq_zero
    · exact Bool.eq_false_of_not_eq_true hcolor

theorem hexagonal_percolationEvent_subset_innerShell
    (k : Nat) (hk : 1 ≤ k) :
    hexagonal.percolationEvent ⊆
      hexagonal.bufferedCylinder
        (hexagonalTransBufferLevel k hexagonal.root.1)
        (hexagonalBufferedTransShellEvent k hexagonal.root) := by
  intro omega hperc
  have hall : ∀ n, omega ∈ hexagonal.bufferedCylinder n
      (hexagonal.bufferedRootBoundaryEvent n) := by
    have hinter : omega ∈ ⋂ n, hexagonal.bufferedCylinder n
        (hexagonal.bufferedRootBoundaryEvent n) := by
      rw [hexagonal.iInter_bufferedRootBoundaryCylinder]
      exact hperc
    exact Set.mem_iInter.mp hinter
  let L := hexagonalTransBufferLevel k hexagonal.root.1
  obtain ⟨v, hvBoundary, hreach⟩ := hall L
  have hfull := hexagonal.bufferedReachable_full L omega hreach
  change (hexagonal.openSubgraph omega).Reachable hexagonal.root v.1 at hfull
  have hvFar : k ≤ centeredRadius hexagonal.root.1 v.1.1 := by
    by_contra hnot
    have hrad : centeredRadius hexagonal.root.1 v.1.1 ≤ k - 1 := by omega
    have hvbox : v.1.1 ∈ box 2 k := by
      rw [mem_box_iff_siteRadius_le]
      have hvRad : siteRadius v.1.1 ≤ k - 1 := by
        simpa [centeredRadius, hexagonal_root_coord_eq_zero] using hrad
      exact hvRad.trans (Nat.sub_le k 1)
    have hvEarlier : v.1 ∈
        hexagonal.orbitBox (hexagonal.bufferedRadius k) := by
      rw [hexagonal_mem_orbitBox_iff_box]
      exact box_mono 2 (hexagonal.id_le_bufferedRadius k) hvbox
    have hkL : k < L := by
      dsimp [L, hexagonalTransBufferLevel]
      rw [hexagonal_root_coord_eq_zero]
      simp [siteRadius]
      omega
    exact (hexagonal.bufferedBoundary_not_mem_of_lt hkL v hvBoundary) hvEarlier
  exact hexagonal_twoPointEvent_subset_transShell
    k hk hexagonal.root v.1 hvFar hfull

theorem hexagonal_wiredPercolationProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q ≤
      hexagonalOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := hexagonal.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
      hexagonal.percolationEvent ≤
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder
          (hexagonalTransBufferLevel k hexagonal.root.1)
          (hexagonalBufferedTransShellEvent k hexagonal.root)) :=
    measureReal_mono (hexagonal_percolationEvent_subset_innerShell k hk)
      (measure_ne_top _ _)
  rw [show hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q =
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        hexagonal.percolationEvent by
    simp [PeriodicGraph.wiredPercolationProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (hexagonalBufferedTransShell_infinite_le_theta
      k hk hexagonal.root q beta hq hbeta)


noncomputable def hexagonalBufferedToBox (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    hexagonal.BufferedVertex j → HexagonalBoxVertex (2 * N) :=
  fun x => ⟨hexagonalRootFrame x.1, by
    refine ⟨?_, Set.mem_univ _⟩
    rw [hexagonalRootFrame_coord_mem_box_iff]
    rw [← hexagonal_mem_orbitBox_iff_box]
    exact hexagonal.orbitBox_mono hjn x.2⟩

theorem hexagonalBufferedToBox_injective (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    Function.Injective (hexagonalBufferedToBox j N hjn) := by
  intro x y h
  apply Subtype.ext
  apply hexagonalRootFrame.injective
  exact congrArg (fun z : HexagonalBoxVertex (2 * N) => (z : HexVertex)) h

theorem hexagonalBufferedToBox_adjMatch (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    ocd_AdjMatch (hexagonal.bufferedGraph j)
      (hexagonalBoxGraph (2 * N)) (hexagonalBufferedToBox j N hjn) := by
  intro x y
  exact (hexagonalRootFrame_adj x.1 y.1).symm

theorem hexagonalBufferedToBox_not_outerBoundary
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (x : hexagonal.BufferedVertex j) :
    hexagonalBufferedToBox j N (by omega) x ∉
      hexagonalBoxShell (2 * N) (2 * N) := by
  intro hx
  have hxSmall : (hexagonalRootFrame x.1).1 ∈ box 2 (2 * N - 1) := by
    rw [hexagonalRootFrame_coord_mem_box_iff]
    rw [← hexagonal_mem_orbitBox_iff_box]
    exact hexagonal.orbitBox_mono (by omega) x.2
  exact (Finset.mem_filter.mp hx).2.2 hxSmall

theorem hexagonalBufferedToBox_inducedWiring_le
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * N)))) :
    ocd_inducedWiring (hexagonalBoxGraph (2 * N))
        (hexagonalBufferedToBox j N (by omega))
        (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N)) psi ≤
      boundaryCliqueGraph (hexagonal.bufferedBoundary j) := by
  let incl := hexagonalBufferedToBox j N (by omega :
    hexagonal.bufferedRadius j ≤ 2 * N)
  apply StatMech.FK.ocd_comapInducedWiring_le_equiv hexagonalGraph
    hexagonalRootFrame hexagonalRootFrame_adj incl
    (fun _ => rfl) (hexagonalBufferedToBox_injective j N (by omega))
    (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    (hexagonal.bufferedBoundary j)
  · intro x
    exact hexagonalBufferedToBox_not_outerBoundary j N hjn x
  · intro x z hxz hz
    exact ⟨z, hxz, by
      intro hzOrbit
      exact hz hzOrbit⟩

theorem hexagonalCenteredShellFullEvent_subset_bufferedRestrict
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N) :
    hexagonalCenteredShellFullEvent (2 * N) N ⊆
      ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) ⁻¹'
        hexagonal.bufferedRootBoundaryEvent j := by
  intro omega hcross
  obtain ⟨v, hvShell, hreach⟩ := hcross
  let S : Set (HexagonalBoxVertex (2 * N)) :=
    {x | x.1 ∈ hexagonal.orbitBox (hexagonal.bufferedRadius j)}
  have hrootS : hexagonalBoxRoot (2 * N) ∈ S := by
    change ((0, false) : HexVertex) ∈
      hexagonal.orbitBox (hexagonal.bufferedRadius j)
    rw [hexagonal_mem_orbitBox_iff_box]
    simp
  have hvOutside : v ∉ S := by
    intro hvS
    have hvSmall : v.1.1 ∈ box 2 (N - 1) := by
      rw [← hexagonal_mem_orbitBox_iff_box]
      exact hexagonal.orbitBox_mono (by omega) hvS
    exact (Finset.mem_filter.mp hvShell).2.2 hvSmall
  obtain ⟨y, hyReach, z, hyz, hzOutside⟩ :=
    reachable_induce_innerBoundary
      (FK.openSub (hexagonalBoxGraph (2 * N)) omega) S
      hrootS hvOutside hreach
  let phi : ((FK.openSub (hexagonalBoxGraph (2 * N)) omega).induce S) →g
      FK.openSub (hexagonal.bufferedGraph j)
        (ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) omega) := {
    toFun := fun x => (⟨hexagonalRootFrame.symm x.1.1, by
      change hexagonalRootFrame x.1.1 ∈
        hexagonal.orbitBox (hexagonal.bufferedRadius j)
      exact (hexagonalRootFrame_mem_orbitBox_iff _ _).2 x.2⟩ :
        hexagonal.BufferedVertex j)
    map_rel' := by
      intro a b hab
      change hexagonalGraph.Adj a.1.1 b.1.1 ∧
        omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨?_, ?_⟩
      · change hexagonalGraph.Adj (hexagonalRootFrame a.1.1)
          (hexagonalRootFrame b.1.1)
        exact (hexagonalRootFrame_adj _ _).2 hab.1
      simpa [ocd_innerRestrict, ocd_innerEdge, hexagonalBufferedToBox]
        using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨hexagonalBoxRoot (2 * N), hrootS⟩ =
      hexagonal.bufferedRoot j := by
    apply Subtype.ext
    have h := congrArg hexagonalRootFrame.symm hexagonalRootFrame_root
    simpa [phi, hexagonalBoxRoot, PeriodicGraph.bufferedRoot_val] using h.symm
  have hyBoundary : hexagonal.bufferedBoundary j (phi y) := by
    refine ⟨hexagonalRootFrame.symm z.1, ?_, ?_⟩
    · change hexagonalGraph.Adj (hexagonalRootFrame y.1.1)
        (hexagonalRootFrame z.1)
      exact (hexagonalRootFrame_adj _ _).2 hyz.1
    · intro hzOrbit
      have hzOrbit' :=
        (hexagonalRootFrame_mem_orbitBox_iff
          (hexagonal.bufferedRadius j) (hexagonalRootFrame.symm z.1)).2 hzOrbit
      exact hzOutside (by simpa using hzOrbit')
  change ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) omega ∈
    hexagonal.bufferedRootBoundaryEvent j
  refine ⟨phi y, hyBoundary, ?_⟩
  rwa [hroot] at hmapped

noncomputable def hexagonalBufferedRootArmMass
    (j : Nat) (p q : Real) : Real :=
  finiteWiredEventMass (hexagonal.bufferedGraph j)
    (hexagonal.bufferedBoundary j) p q
    (hexagonal.bufferedRootBoundaryEvent j)

theorem hexagonalOuterInnerTheta_le_bufferedRootArmMass
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta N ≤
      hexagonalBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let incl := hexagonalBufferedToBox j N (by omega :
    hexagonal.bufferedRadius j ≤ 2 * N)
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := hexagonal.bufferedGraph j)
    (Gout := hexagonalBoxGraph (2 * N))
    (ιV := incl)
    (bdryOut := fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    (hexagonalBufferedToBox_injective j N (by omega))
    (hexagonalBufferedToBox_adjMatch j N (by omega))
    (hexagonal.bufferedBoundary j) hp hp1 hq
    (hexagonalBufferedToBox_inducedWiring_le j N hjn)
    (hexagonal.bufferedRootBoundaryEvent_isIncreasing j)
  have hmono := finiteWiredEventMass_mono
    (hexagonalBoxGraph (2 * N))
    (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    hp hp1 (zero_lt_one.trans_le hq)
    (hexagonalCenteredShellFullEvent_subset_bufferedRestrict j N hjn)
  rw [← hexagonalCenteredFullMass_eq_outerInnerTheta
    N (by omega) q beta hq hbeta]
  unfold hexagonalBufferedRootArmMass finiteWiredEventMass
  exact hmono.trans (by
    simpa only [bcProb_clique_eq_wiredFkProb] using hdom)

theorem hexagonalBufferedRestrictLE_self
    (j : Nat) (omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex j))) :
    hexagonal.bufferedRestrictLE (le_refl j) omega = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      change omega s(hexagonal.bufferedVertexInclLE (le_refl j) x,
          hexagonal.bufferedVertexInclLE (le_refl j) y) = omega s(x, y)
      have hx : hexagonal.bufferedVertexInclLE (le_refl j) x = x := by
        apply Subtype.ext
        rfl
      have hy : hexagonal.bufferedVertexInclLE (le_refl j) y = y := by
        apply Subtype.ext
        rfl
      rw [hx, hy]

theorem hexagonalBufferedRootArmMass_eq_measure
    (j : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    hexagonalBufferedRootArmMass j p q =
      (hexagonal.wiredBufferedMeasure j hp hp1 hq :
        Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder j
          (hexagonal.bufferedRootBoundaryEvent j)) := by
  rw [hexagonal.wiredBufferedMeasure_real_cylinder (le_refl j)
    hp hp1 hq (hexagonal.bufferedRootBoundaryEvent j)]
  have hpre : hexagonal.bufferedRestrictLE (le_refl j) ⁻¹'
      hexagonal.bufferedRootBoundaryEvent j =
      hexagonal.bufferedRootBoundaryEvent j := by
    ext omega
    simp only [Set.mem_preimage, hexagonalBufferedRestrictLE_self]
  rw [hpre]
  unfold hexagonalBufferedRootArmMass finiteWiredEventMass
  rfl

theorem hexagonalBufferedRootArmMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun j => hexagonalBufferedRootArmMass j p q) atTop
      (nhds (hexagonal.wiredPercolationProbability p q)) := by
  have hdiag := hexagonal.wiredBufferedRootBoundary_diag_tendsto
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with j
  exact (hexagonalBufferedRootArmMass_eq_measure j hp hp1
    (zero_lt_one.trans_le hq)).symm



theorem hexagonalOuterInnerTheta_tendsto_percolation
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => hexagonalOuterInnerTheta q beta n) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q)) := by
  let p := 1 - Real.exp (-beta)
  let thetaInf := hexagonal.wiredPercolationProbability p q
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have harm : Tendsto (fun j => hexagonalBufferedRootArmMass j p q)
      atTop (nhds thetaInf) := by
    simpa [thetaInf] using hexagonalBufferedRootArmMass_tendsto hp hp1 hq
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp harm) epsilon hepsilon
  refine ⟨max 1 (hexagonal.bufferedRadius J + 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (Nat.le_max_left _ _).trans hn
  have hJn : hexagonal.bufferedRadius J < n := by
    have := (Nat.le_max_right 1 (hexagonal.bufferedRadius J + 1)).trans hn
    omega
  have hlower : thetaInf ≤ hexagonalOuterInnerTheta q beta n := by
    simpa [thetaInf, p] using
      hexagonal_wiredPercolationProbability_le_theta n hn1 q beta hq hbeta
  have hupper : hexagonalOuterInnerTheta q beta n ≤
      hexagonalBufferedRootArmMass J p q :=
    hexagonalOuterInnerTheta_le_bufferedRootArmMass
      J n hJn q beta hq hbeta
  have hclose := hJ J le_rfl
  rw [Real.dist_eq] at hclose ⊢
  have hclose' := (abs_lt.mp hclose).2
  rw [show p = 1 - Real.exp (-beta) by rfl] at hupper
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

noncomputable def hexagonalBeta1 (q beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n => IntegrationSubcritical.Sig
    (hexagonalThresholdTheta q beta0) n b)

noncomputable def hexagonalCriticalBeta (q : Real) : Real :=
  -Real.log (1 - hexagonal.criticalPoint q)

theorem hexagonalCriticalBeta_pos
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 < hexagonalCriticalBeta q := by
  unfold hexagonalCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc.2) (by linarith [hpc.1]))

theorem hexagonalCriticalBeta_param
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    1 - Real.exp (-hexagonalCriticalBeta q) = hexagonal.criticalPoint q := by
  unfold hexagonalCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc.2)]
  ring

theorem betaToP_lt_hexagonalCritical_of_lt
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : beta < hexagonalCriticalBeta q) :
    1 - Real.exp (-beta) < hexagonal.criticalPoint q := by
  rw [← hexagonalCriticalBeta_param q hpc]
  have hexp : Real.exp (-hexagonalCriticalBeta q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem hexagonalCritical_lt_betaToP_of_lt
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : hexagonalCriticalBeta q < beta) :
    hexagonal.criticalPoint q < 1 - Real.exp (-beta) := by
  rw [← hexagonalCriticalBeta_param q hpc]
  have hexp : Real.exp (-beta) < Real.exp (-hexagonalCriticalBeta q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem hexagonalNormalizedTheta_tendsto_percolation_div
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => hexagonalNormalizedTheta q beta0 n beta) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0)) := by
  simpa [hexagonalNormalizedTheta] using
    (hexagonalOuterInnerTheta_tendsto_percolation q beta hq hbeta).div_const
      (hexagonalSharpConstant beta0)

theorem hexagonalThresholdSet_mem_of_percolation_pos
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hperc : 0 < hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b) := by
  let L := hexagonal.wiredPercolationProbability
    (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0
  have hL : 0 < L := div_pos hperc (hexagonalSharpConstant_pos beta0)
  have hconv : Tendsto
      (fun n => hexagonalThresholdTheta q beta0 n beta) atTop (nhds L) := by
    simpa [L, hexagonalThresholdTheta, not_le.mpr hbeta] using
      hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]

theorem hexagonalThresholdSet_nonempty
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n b)).Nonempty := by
  let beta := hexagonalCriticalBeta q + 1
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith [hexagonalCriticalBeta_pos q hpc]
  have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · rw [sub_pos]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · linarith [Real.exp_pos (-beta)]
  have hsuper : hexagonal.criticalPoint q < 1 - Real.exp (-beta) :=
    hexagonalCritical_lt_betaToP_of_lt q hpc (by simp [beta])
  have hsharp := hexagonal.offCriticalSharpness hq hpc
  have hperc : 0 < hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q := hsharp.2 _ hp hsuper
  exact ⟨beta, hexagonalThresholdSet_mem_of_percolation_pos
    q beta0 beta hq hbeta hperc⟩

theorem hexagonalBeta1_nonneg
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 ≤ hexagonalBeta1 q beta0 := by
  unfold hexagonalBeta1 BetaThresholdBound.beta1
  apply le_csInf (hexagonalThresholdSet_nonempty q beta0 hq hpc)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / hexagonalSharpConstant beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / hexagonalSharpConstant beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [hexagonalThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem hexagonalThresholdLogRatio_bddAbove
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) := by
  exact BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)
    (1 / hexagonalSharpConstant beta0)
    (one_le_inv_hexagonalSharpConstant beta0 hbeta0)
    (fun n hn => hexagonalThresholdSig_pos n (by omega) q beta0 beta hq)
    (fun n => hexagonalThresholdSig_le_linear n q beta0 beta hq)

theorem hexagonalThresholdLogRatio_cobounded
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) := by
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta))
    (x := 0) atTop ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig1 : 1 ≤ IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta := by
    have hzero : 1 ≤ hexagonalThresholdTheta q beta0 0 beta := by
      have hM := one_le_inv_hexagonalSharpConstant beta0 hbeta0
      by_cases hbeta : beta ≤ 0
      · simpa [hexagonalThresholdTheta, hbeta] using hM
      · rw [hexagonalThresholdTheta_of_pos 0 q beta0 beta (lt_of_not_ge hbeta)]
        simpa [hexagonalNormalizedTheta, hexagonalOuterInnerTheta] using hM
    exact hzero.trans (by
      unfold IntegrationSubcritical.Sig
      apply Finset.single_le_sum
        (fun k _ => hexagonalThresholdTheta_nonneg k q beta0 beta hq)
      exact Finset.mem_range.mpr (by omega))
  unfold BetaThresholdBound.logRatio
  exact div_nonneg (Real.log_nonneg hsig1) hlogn.le


theorem hexagonalPercolation_difference_lower
    (q beta0 beta' beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : hexagonalBeta1 q beta0 < beta') (hbeta : beta' ≤ beta)
    (hupper : beta ≤ beta0) :
    beta - beta' ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
          hexagonalSharpConstant beta0 -
        hexagonal.wiredPercolationProbability (1 - Real.exp (-beta')) q /
          hexagonalSharpConstant beta0 := by
  let f := hexagonalNormalizedTheta q beta0
  let fp := hexagonalNormalizedThetaPrime q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := hexagonalBeta1_nonneg q beta0 hq hpc
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : ∀ i x, x ∈ Set.Icc beta' beta →
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / hexagonalSharpConstant beta0 := by
        funext z
        simp [f, hexagonalNormalizedTheta, hexagonalOuterInnerTheta]
      rw [hconst]
      simpa [fp, hexagonalNormalizedThetaPrime,
        hexagonalOuterInnerThetaPrime, hexagonalOuterInnerTheta] using
        (hasDerivAt_const x (1 / hexagonalSharpConstant beta0))
    · exact hasDerivAt_hexagonalNormalizedTheta i
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 ≤ f i x := by
    intro i x hi hx
    exact hexagonalNormalizedTheta_nonneg i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 < Sig i x := by
    intro i x hi hx
    exact hexagonalNormalizedSig_pos i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : ∀ i : Nat, ∀ x, 1 ≤ i → x ∈ Set.Icc beta' beta →
      ((i : Real) / Sig i x) * f i x ≤ fp i x := by
    intro i x hi hx
    exact hexagonalNormalizedTheta_differential i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc beta' beta →
      Sig n beta' ≤ Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' ≤ Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        hexagonalNormalizedTheta_mono_beta k q beta0 beta' x hq
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : ∀ x, x ∈ Set.Icc beta' beta →
      Sig 1 x ≤ 1 / hexagonalSharpConstant beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, hexagonalNormalizedTheta,
      hexagonalOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta')) q / hexagonalSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta') := by
    funext n
    symm
    exact hexagonalThresholdSig_of_pos n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact hexagonalThresholdLogRatio_cobounded
      q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact hexagonalThresholdLogRatio_bddAbove
      q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 ≤ Filter.limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (hexagonalThresholdSet_nonempty q beta0 hq hpc)
      (fun hab n => hexagonalThresholdSig_mono_beta n q beta0 hq hab)
      (fun x n hn => hexagonalThresholdSig_pos n (by omega) q beta0 x hq)
      (fun x => hexagonalThresholdLogRatio_cobounded
        q beta0 x hq hbeta0pos.le)
      (fun x => hexagonalThresholdLogRatio_bddAbove
        q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
      hexagonalSharpConstant beta0)
    (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta')) q /
      hexagonalSharpConstant beta0)
    (1 / hexagonalSharpConstant beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1

theorem hexagonalPercolation_meanField_lower
    (q beta0 beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : hexagonalBeta1 q beta0 < beta) (hupper : beta ≤ beta0) :
    hexagonalSharpConstant beta0 * (beta - hexagonalBeta1 q beta0) ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
  have hc := hexagonalSharpConstant_pos beta0
  have hnormalized : beta - hexagonalBeta1 q beta0 ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
        hexagonalSharpConstant beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => hexagonal.wiredPercolationProbability
        (1 - Real.exp (-x)) q / hexagonalSharpConstant beta0)
      (β₁ := hexagonalBeta1 q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg
        (hexagonal.wiredPercolationProbability_nonneg _ _) hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact hexagonalPercolation_difference_lower q beta0 beta' beta hq hpc
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith



theorem hexagonalBeta1_eq_criticalBeta_of_ge
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta0 : hexagonalCriticalBeta q ≤ beta0) :
    hexagonalBeta1 q beta0 = hexagonalCriticalBeta q := by
  let betaC := hexagonalCriticalBeta q
  let Sgf : Real → Nat → Real := fun b n => IntegrationSubcritical.Sig
    (hexagonalThresholdTheta q beta0) n b
  have hbetaCpos : 0 < betaC := hexagonalCriticalBeta_pos q hpc
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using hexagonalThresholdSet_bddBelow q beta0
  have hsharp := hexagonal.offCriticalSharpness hq hpc
  have hle : hexagonalBeta1 q beta0 ≤ betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hpcp : hexagonal.criticalPoint q < 1 - Real.exp (-beta) :=
      hexagonalCritical_lt_betaToP_of_lt q hpc hbetaCbeta
    have hperc : 0 < hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := hsharp.2 _ hp hpcp
    have hmem := hexagonalThresholdSet_mem_of_percolation_pos
      q beta0 beta hq hbetapos hperc
    unfold hexagonalBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC ≤ hexagonalBeta1 q beta0 := by
    by_contra hnot
    have hlt : hexagonalBeta1 q beta0 < betaC := lt_of_not_ge hnot
    let beta := (hexagonalBeta1 q beta0 + betaC) / 2
    have hcrit : hexagonalBeta1 q beta0 < beta := by
      dsimp [beta]
      linarith
    have hbetaC : beta < betaC := by
      dsimp [beta]
      linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (hexagonalBeta1_nonneg q beta0 hq hpc) hcrit
    have hmean := hexagonalPercolation_meanField_lower
      q beta0 beta hq hpc hcrit (hbetaC.le.trans hbeta0)
    have hpercPos : 0 < hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := by
      have hc := hexagonalSharpConstant_pos beta0
      have hgap : 0 < beta - hexagonalBeta1 q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hppc : 1 - Real.exp (-beta) < hexagonal.criticalPoint q :=
      betaToP_lt_hexagonalCritical_of_lt q hpc hbetaC
    have hnotperc := hsharp.1 _ hp hppc
    exact hnotperc hpercPos
  exact le_antisymm hle hge



theorem hexagonalOuterInner_exponential_decay_below_critical
    (q beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta : 0 < beta) (hsub : beta < hexagonalCriticalBeta q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n →
      hexagonalOuterInnerTheta q beta n ≤
        Real.exp (-((n : Real) / Q *
          ((hexagonalCriticalBeta q - beta) / 4))) := by
  let betaC := hexagonalCriticalBeta q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid ≤ betaC := by dsimp [betaMid]; linarith
  have hthreshold : hexagonalBeta1 q betaC = betaC :=
    hexagonalBeta1_eq_criticalBeta_of_ge q betaC hq hpc le_rfl
  have hmidThreshold : betaMid < hexagonalBeta1 q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    hexagonalOuterInner_subcritical_decay_of_threshold
      q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [hexagonalBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn



theorem hexagonal_wiredTwoPointProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (x y : HexVertex)
    (hxy : k ≤ centeredRadius x.1 y.1) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonal.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤
      hexagonalOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := hexagonal.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.twoPointEvent x y) ≤
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1)
          (hexagonalBufferedTransShellEvent k x)) :=
    measureReal_mono (hexagonal_twoPointEvent_subset_transShell k hk x y hxy)
      (measure_ne_top _ _)
  rw [show hexagonal.wiredTwoPointProbability
      (1 - Real.exp (-beta)) q x y =
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.twoPointEvent x y) by
    simp [PeriodicGraph.wiredTwoPointProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (hexagonalBufferedTransShell_infinite_le_theta
      k hk x q beta hq hbeta)

theorem hexagonalBetaOfP_pos {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    0 < -Real.log (1 - p) :=
  neg_pos.mpr (Real.log_neg (sub_pos.mpr hp1) (by linarith))

theorem hexagonalBetaOfP_param {p : Real} (hp1 : p < 1) :
    1 - Real.exp (-(-Real.log (1 - p))) = p := by
  rw [neg_neg, Real.exp_log (sub_pos.mpr hp1)]
  ring

theorem hexagonalBetaOfP_lt_criticalBeta
    (q p : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hp1 : p < 1) (hsub : p < hexagonal.criticalPoint q) :
    -Real.log (1 - p) < hexagonalCriticalBeta q := by
  by_contra hnot
  have hle : hexagonalCriticalBeta q ≤ -Real.log (1 - p) :=
    le_of_not_gt hnot
  have hexp : Real.exp (-(-Real.log (1 - p))) ≤
      Real.exp (-hexagonalCriticalBeta q) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  have hpEq := hexagonalBetaOfP_param hp1
  have hcEq := hexagonalCriticalBeta_param q hpc
  linarith

theorem hexagonal_centeredRadius_eq_zero_iff (x y : Site 2) :
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

theorem hexToTriAnchor_sub_mem_box_add_two
    {x y : HexVertex} {r : Nat} (hxy : y.1 - x.1 ∈ box 2 r) :
    hexToTriAnchor y - hexToTriAnchor x ∈ box 2 (r + 2) := by
  have hx : x.1 - hexToTriAnchor x ∈ box 2 1 := by
    rcases x with ⟨x, bx⟩
    cases bx with
    | false => simp [hexToTriAnchor]
    | true =>
        have hx0 : Matrix.vecHead x = x 0 := rfl
        have hx1 : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
        intro i
        fin_cases i <;>
          simp [hexToTriAnchor, hexagonalStep, Matrix.cons_val_zero,
            Matrix.cons_val_one, hx0, hx1]
  have hy : hexToTriAnchor y - y.1 ∈ box 2 1 := by
    rcases y with ⟨y, cy⟩
    cases cy with
    | false => simp [hexToTriAnchor]
    | true =>
        have hy0 : Matrix.vecHead y = y 0 := rfl
        have hy1 : Matrix.vecHead (Matrix.vecTail y) = y 1 := rfl
        intro i
        fin_cases i <;>
          simp [hexToTriAnchor, hexagonalStep, Matrix.cons_val_zero,
            Matrix.cons_val_one, hy0, hy1]
  intro i
  have hxi := hx i
  have hxyi := hxy i
  have hyi := hy i
  change (x.1 i - hexToTriAnchor x i).natAbs ≤ 1 at hxi
  change (y.1 i - x.1 i).natAbs ≤ r at hxyi
  change (hexToTriAnchor y i - y.1 i).natAbs ≤ 1 at hyi
  change (hexToTriAnchor y i - hexToTriAnchor x i).natAbs ≤ r + 2
  calc
    (hexToTriAnchor y i - hexToTriAnchor x i).natAbs =
        ((hexToTriAnchor y i - y.1 i) +
          ((y.1 i - x.1 i) + (x.1 i - hexToTriAnchor x i))).natAbs := by
      congr 1
      ring
    _ ≤ (hexToTriAnchor y i - y.1 i).natAbs +
        ((y.1 i - x.1 i) + (x.1 i - hexToTriAnchor x i)).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ (hexToTriAnchor y i - y.1 i).natAbs +
        ((y.1 i - x.1 i).natAbs +
          (x.1 i - hexToTriAnchor x i).natAbs) := by
      gcongr
      exact Int.natAbs_add_le _ _
    _ ≤ 1 + (r + 1) := Nat.add_le_add hyi (Nat.add_le_add hxyi hxi)
    _ = r + 2 := by omega



theorem hexagonal_subcritical_twoPoint_exponential_decay
    (q : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    SubcriticalTwoPointExponentialDecay
      hexagonal q (hexagonal.criticalPoint q) := by
  intro p hp
  have hp1 : p < 1 := hp.2.trans hpc.2
  let beta := -Real.log (1 - p)
  have hbeta : 0 < beta := hexagonalBetaOfP_pos hp.1 hp1
  have hsub : beta < hexagonalCriticalBeta q :=
    hexagonalBetaOfP_lt_criticalBeta q p hpc hp1 hp.2
  obtain ⟨Q, hQ, hdecay⟩ :=
    hexagonalOuterInner_exponential_decay_below_critical
      q beta hq hpc hbeta hsub
  let delta := (hexagonalCriticalBeta q - beta) / 4
  let c := delta / (4 * Q)
  let C := Real.exp (10 * c)
  refine ⟨c, C, ?_, Real.exp_pos _, ?_⟩
  · have hdelta : 0 < delta := by dsimp [delta]; linarith
    dsimp [c]
    positivity
  intro x y
  let r := centeredRadius x.1 y.1
  have hpEq : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    exact hexagonalBetaOfP_param hp1
  have hrbox : y.1 - x.1 ∈ box 2 r := by
    rw [mem_box_iff_siteRadius_le]
    change centeredRadius x.1 y.1 ≤ r
    exact le_rfl
  have hanchor := hexToTriAnchor_sub_mem_box_add_two hrbox
  have hdistNat :=
    hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box hanchor
  have hdist : (hexagonalGraph.dist x y : Real) ≤ 4 * (r : Real) + 10 := by
    exact_mod_cast hdistNat
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hrate : c * (hexagonalGraph.dist x y : Real) ≤
      ((r : Real) / Q) * delta + 10 * c := by
    calc
      c * (hexagonalGraph.dist x y : Real) ≤
          c * (4 * (r : Real) + 10) :=
        mul_le_mul_of_nonneg_left hdist hc.le
      _ = ((r : Real) / Q) * delta + 10 * c := by
        dsimp [c]
        field_simp
  by_cases hrzero : r = 0
  · have hone := hexagonal.wiredTwoPointProbability_le_one p q x y
    calc
      hexagonal.wiredTwoPointProbability p q x y ≤ 1 := hone
      _ ≤ C * Real.exp (-c * (hexagonalGraph.dist x y : Real)) := by
        rw [show (1 : Real) = Real.exp 0 by simp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [C]
        have hrate0 : c * (hexagonalGraph.dist x y : Real) ≤ 10 * c := by
          simpa [hrzero] using hrate
        linarith
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrzero
    have hpoint := hexagonal_wiredTwoPointProbability_le_theta
      r hr x y le_rfl q beta hq hbeta
    rw [hpEq] at hpoint
    have harm := hdecay r hr
    calc
      hexagonal.wiredTwoPointProbability p q x y ≤
          hexagonalOuterInnerTheta q beta r := hpoint
      _ ≤ Real.exp (-(((r : Real) / Q) * delta)) := by
        simpa [delta, mul_assoc] using harm
      _ ≤ C * Real.exp (-c * (hexagonalGraph.dist x y : Real)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [C]
        linarith

end StatMech.FK.PeriodicPlanar
