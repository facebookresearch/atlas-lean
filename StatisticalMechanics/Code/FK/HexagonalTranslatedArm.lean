/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.HexagonalSharpnessThreshold
import Code.FK.TriHexFKFiniteWiredCofinal

open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS
open RevealmentTranslation

noncomputable def hexagonalTransBufferLevel (k : Nat) (x : Site 2) : Nat :=
  siteRadius x + 2 * k

theorem hexagonalTransBox_mem_bufferLevel
    (k : Nat) (x : Site 2) (y : HexagonalTransBoxVertex (2 * k) x) :
    y.1.1 ∈ box 2 (hexagonalTransBufferLevel k x) := by
  rw [mem_box_iff_siteRadius_le]
  have hrad : centeredRadius x y.1.1 ≤ 2 * k := by
    rw [centeredRadius, siteRadius_le_iff]
    exact y.2.1
  exact (siteRadius_triangle y.1.1 x).trans (Nat.add_le_add_left hrad _)

def hexagonalTransBoxToBuffered (k : Nat) (x : Site 2) :
    HexagonalTransBoxVertex (2 * k) x →
      hexagonal.BufferedVertex (hexagonalTransBufferLevel k x) :=
  fun y => ⟨y.1, by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2
      (hexagonal.id_le_bufferedRadius (hexagonalTransBufferLevel k x))
      (hexagonalTransBox_mem_bufferLevel k x y)⟩

theorem hexagonalTransBoxToBuffered_injective (k : Nat) (x : Site 2) :
    Function.Injective (hexagonalTransBoxToBuffered k x) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun w : hexagonal.BufferedVertex
    (hexagonalTransBufferLevel k x) => (w : HexVertex)) h

noncomputable def hexagonalTransBoxToBufferedAt (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    HexagonalTransBoxVertex (2 * k) x → hexagonal.BufferedVertex m :=
  fun y => hexagonal.bufferedVertexInclLE hm
    (hexagonalTransBoxToBuffered k x y)

theorem hexagonalTransBoxToBufferedAt_injective
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    Function.Injective (hexagonalTransBoxToBufferedAt k x m hm) :=
  (hexagonal.bufferedVertexInclLE hm).injective.comp
    (hexagonalTransBoxToBuffered_injective k x)

theorem hexagonalTransBoxToBufferedAt_adjMatch
    (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    ocd_AdjMatch (hexagonalTransBoxGraph (2 * k) x)
      (hexagonal.bufferedGraph m)
      (hexagonalTransBoxToBufferedAt k x m hm) := by
  intro y z
  rfl

theorem hexagonalTransBoxToBufferedAt_inducedWiring_le
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x < m)
    (psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))) :
    ocd_inducedWiring (hexagonal.bufferedGraph m)
        (hexagonalTransBoxToBufferedAt k x m hm.le)
        (hexagonal.bufferedBoundary m) psi ≤
      boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
  let incl := hexagonalTransBoxToBufferedAt k x m hm.le
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph incl
    (fun _ => rfl)
    (hexagonalTransBoxToBufferedAt_injective k x m hm.le)
    (hexagonal.bufferedBoundary m)
    (hexagonalTransBoxBoundary (2 * k) x)
  · intro y hy
    have hyEarlier : y.1 ∈ hexagonal.orbitBox
        (hexagonal.bufferedRadius (hexagonalTransBufferLevel k x)) :=
      (hexagonalTransBoxToBuffered k x y).2
    exact (hexagonal.bufferedBoundary_not_mem_of_lt hm _ hy) hyEarlier
  · intro y z hyz hz
    apply hexagonalTransBox_boundary_of_adj_outside (by omega) y z hyz
    intro hzcoord
    exact hz ⟨hzcoord, Set.mem_univ _⟩

def hexagonalBufferedTransShellEvent (k : Nat) (x : HexVertex) :
    Set (ConfigSpace (Sym2
      (hexagonal.BufferedVertex (hexagonalTransBufferLevel k x.1)))) :=
  ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1) ⁻¹'
    hexagonalTransShellFullEvent (2 * k) k x

theorem hexagonalTransShellFullEvent_increasing
    (R k : Nat) (x : HexVertex) :
    IsIncreasing (hexagonalTransShellFullEvent R k x) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro a b hab
  rw [FK.openSub_adj] at hab ⊢
  refine ⟨hab.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hab.2] using home s(a, b)

theorem hexagonalBufferedTransShellEvent_increasing
    (k : Nat) (x : HexVertex) :
    IsIncreasing (hexagonalBufferedTransShellEvent k x) := by
  intro omega eta home hmem
  exact hexagonalTransShellFullEvent_increasing (2 * k) k x
    (fun e => home _) hmem

theorem hexagonalTransFullMass_eq_outerInnerTheta
    (k : Nat) (hk : 1 ≤ k) (x : HexVertex) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    finiteWiredEventMass (hexagonalTransBoxGraph (2 * k) x.1)
        (hexagonalTransBoxBoundary (2 * k) x.1)
        (1 - Real.exp (-beta)) q
        (hexagonalTransShellFullEvent (2 * k) k x) =
      hexagonalOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have htrans := hexagonalTransShellEvent_betaMean_eq_centeredFullMass
    (2 * k) k x q beta (zero_lt_one.trans_le hq) hbeta
  have hparam : FK.betaParams
      (fun _ : Sym2 (HexagonalTransBoxVertex (2 * k) x.1) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [FK.betaParams]
  rw [hparam] at htrans
  rw [FK.activeBCMean_boundaryClique_eq_wired
    (hexagonalTransBoxGraph (2 * k) x.1)
    (hexagonalTransBoxBoundary (2 * k) x.1)
    hp hp1 (zero_lt_one.trans_le hq)] at htrans
  rw [← hexagonalCenteredFullMass_eq_outerInnerTheta
    k hk q beta hq hbeta]
  unfold finiteWiredEventMass
  calc
    (∑ omega,
      (hexagonalTransShellFullEvent (2 * k) k x).indicator
          (fun _ => (1 : Real)) omega *
        wiredFkProb (hexagonalTransBoxGraph (2 * k) x.1)
          (hexagonalTransBoxBoundary (2 * k) x.1)
          (1 - Real.exp (-beta)) q omega) =
      ∑ omega,
        (hexagonalTransShellEvent (2 * k) k x).indicator
            (fun _ => (1 : Real))
            (restrictActive (hexagonalTransBoxGraph (2 * k) x.1) omega) *
          wiredFkProb (hexagonalTransBoxGraph (2 * k) x.1)
            (hexagonalTransBoxBoundary (2 * k) x.1)
            (1 - Real.exp (-beta)) q omega := by
        apply Finset.sum_congr rfl
        intro omega homega
        congr 1
        rw [Set.indicator_apply, Set.indicator_apply]
        have heq := Set.ext_iff.mp
          (restrictActive_preimage_hexagonalTransShellEvent (2 * k) k x) omega
        split_ifs with h h' <;> simp_all
    _ = _ := htrans

theorem hexagonalBufferedTransShell_finite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : HexVertex) (m : Nat)
    (hm : hexagonalTransBufferLevel k x.1 < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1)
          (hexagonalBufferedTransShellEvent k x)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let L := hexagonalTransBufferLevel k x.1
  let incl := hexagonalTransBoxToBufferedAt k x.1 m hm.le
  have hcomp : ∀ omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex m)),
      ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1)
          (hexagonal.bufferedRestrictLE hm.le omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ y : HexagonalTransBoxVertex (2 * k) x.1,
        hexagonal.bufferedVertexInclLE hm.le
            (hexagonalTransBoxToBuffered k x.1 y) = incl y := by
      intro y
      rfl
    induction e using Sym2.inductionOn with
    | _ y z =>
        change omega s(hexagonal.bufferedVertexInclLE hm.le
            (hexagonalTransBoxToBuffered k x.1 y),
          hexagonal.bufferedVertexInclLE hm.le
            (hexagonalTransBoxToBuffered k x.1 z)) =
          omega s(incl y, incl z)
        rw [hv y, hv z]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := hexagonalTransBoxGraph (2 * k) x.1)
    (Gout := hexagonal.bufferedGraph m)
    (ιV := incl)
    (bdryOut := hexagonal.bufferedBoundary m)
    (hexagonalTransBoxToBufferedAt_injective k x.1 m hm.le)
    (hexagonalTransBoxToBufferedAt_adjMatch k x.1 m hm.le)
    (hexagonalTransBoxBoundary (2 * k) x.1)
    hp hp1 hq
    (hexagonalTransBoxToBufferedAt_inducedWiring_le k hk x.1 m hm)
    (hexagonalTransShellFullEvent_increasing (2 * k) k x)
  rw [hexagonal.wiredBufferedMeasure_real_cylinder hm.le hp hp1
    (zero_lt_one.trans_le hq) (hexagonalBufferedTransShellEvent k x)]
  have heventEq :
      hexagonal.bufferedRestrictLE hm.le ⁻¹'
          hexagonalBufferedTransShellEvent k x =
        ocd_innerRestrict incl ⁻¹'
          hexagonalTransShellFullEvent (2 * k) k x := by
    ext omega
    simp only [Set.mem_preimage, hexagonalBufferedTransShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          hexagonalTransShellFullEvent (2 * k) k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonal.bufferedGraph m)
            (hexagonal.bufferedBoundary m) p q omega) ≤
      finiteWiredEventMass (hexagonalTransBoxGraph (2 * k) x.1)
        (hexagonalTransBoxBoundary (2 * k) x.1) p q
        (hexagonalTransShellFullEvent (2 * k) k x) := by
      unfold finiteWiredEventMass
      simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = hexagonalOuterInnerTheta q beta k := by
      simpa [p] using hexagonalTransFullMass_eq_outerInnerTheta
        k hk x q beta hq hbeta

theorem hexagonalBufferedTransShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : HexVertex) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1)
          (hexagonalBufferedTransShellEvent k x)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := hexagonal.wiredBufferedMeasure_tendsto_cylinder
    (hexagonalTransBufferLevel k x.1) hp hp1 hq
    (hexagonalBufferedTransShellEvent_increasing k x)
  apply le_of_tendsto htend
  filter_upwards [eventually_ge_atTop (hexagonalTransBufferLevel k x.1 + 1)]
    with m hm
  exact hexagonalBufferedTransShell_finite_le_theta
    k hk x m (by omega) q beta hq hbeta

theorem hexagonal_twoPointEvent_subset_transShell
    (k : Nat) (hk : 1 ≤ k) (x y : HexVertex)
    (hxy : k ≤ centeredRadius x.1 y.1) :
    hexagonal.twoPointEvent x y ⊆
      hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1)
        (hexagonalBufferedTransShellEvent k x) := by
  intro omega hconn
  let S : Set HexVertex :=
    (hexagonalTransBox (k - 1) x.1) ×ˢ (Set.univ : Set Bool)
  have hxSmall : x ∈ S := by
    refine ⟨?_, Set.mem_univ _⟩
    simp [hexagonalTransBox, StatMech.FK.fvs_transBox]
  have hyOutside : y ∉ S := by
    intro hy
    have hyrad : centeredRadius x.1 y.1 ≤ k - 1 := by
      rw [centeredRadius, siteRadius_le_iff]
      exact hy.1
    omega
  obtain ⟨a, haReach, z, haz, hzOutside⟩ :=
    reachable_induce_innerBoundary (hexagonal.openSubgraph omega)
      S hxSmall hyOutside hconn
  have hazTri : hexagonalGraph.Adj a.1 z := haz.1
  have hzK : z.1 - x.1 ∈ box 2 k := by
    have hadj := hexagonal_adj_sub_right x.1 hazTri
    have haBox : a.1.1 - x.1 ∈ box 2 (k - 1) := a.2.1
    simpa [Nat.sub_add_cancel hk] using
      hexagonal_adj_mem_box_succ haBox hadj
  have hzBoundary : z.1 - x.1 ∈ vertexBoundary 2 k := by
    refine ⟨hzK, ?_⟩
    intro hzSmall
    exact hzOutside ⟨hzSmall, Set.mem_univ _⟩
  have hz2k : z.1 ∈ hexagonalTransBox (2 * k) x.1 := by
    exact box_mono 2 (by omega : k ≤ 2 * k) hzK
  let phi : ((hexagonal.openSubgraph omega).induce
      S) →g
      FK.openSub (hexagonalTransBoxGraph (2 * k) x.1)
        (ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1)
          (hexagonal.bufferedRestrict (hexagonalTransBufferLevel k x.1) omega)) := {
    toFun := fun a => (⟨a.1, ⟨
      box_mono 2 (by omega : k - 1 ≤ 2 * k) a.2.1,
      Set.mem_univ _⟩⟩ : HexagonalTransBoxVertex (2 * k) x.1)
    map_rel' := by
      intro a b hab
      change hexagonalGraph.Adj a.1 b.1 ∧ omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, hexagonalTransBoxToBuffered,
        PeriodicGraph.bufferedRestrict] using hab.2 }
  let zi : HexagonalTransBoxVertex (2 * k) x.1 :=
    ⟨z, ⟨hz2k, Set.mem_univ _⟩⟩
  have hmapped := haReach.map phi
  have hroot : phi ⟨x, hxSmall⟩ = hexagonalTransBoxCenter (2 * k) x := by
    apply Subtype.ext
    rfl
  have hazInner : (FK.openSub (hexagonalTransBoxGraph (2 * k) x.1)
      (ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1)
        (hexagonal.bufferedRestrict (hexagonalTransBufferLevel k x.1) omega))).Adj
      (phi a) zi := by
    rw [FK.openSub_adj]
    refine ⟨hazTri, ?_⟩
    simpa [ocd_innerRestrict, ocd_innerEdge, hexagonalTransBoxToBuffered,
      PeriodicGraph.bufferedRestrict, phi, zi] using haz.2
  have hreachZ := hmapped.trans hazInner.reachable
  have hzShell : zi ∈ hexagonalTransBoxShell (2 * k) k x.1 := by
    simp only [hexagonalTransBoxShell, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hzBoundary
  change ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1)
      (hexagonal.bufferedRestrict (hexagonalTransBufferLevel k x.1) omega) ∈
    hexagonalTransShellFullEvent (2 * k) k x
  refine ⟨zi, hzShell, ?_⟩
  rwa [hroot] at hreachZ

end StatMech.FK.PeriodicPlanar
