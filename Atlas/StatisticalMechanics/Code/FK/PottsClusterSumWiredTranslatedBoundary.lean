/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredTruncation
import Code.FK.FKGeneralQTranslation
import Code.IsingFK.PcUpperAllDimensions










open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators

namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section


def finiteConnToBdryEvent {V : Type*} (G : SimpleGraph V)
    (bdry : V -> Prop) (x : V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | ConnToBdry G bdry omega x}

theorem finiteConnToBdryEvent_isIncreasing {V : Type*}
    (G : SimpleGraph V) (bdry : V -> Prop) (x : V) :
    IsIncreasing (finiteConnToBdryEvent G bdry x) := by
  intro omega eta hle homega
  obtain ⟨y, hy, hxy⟩ := homega
  exact ⟨y, hy, hxy.mono (openSub_mono G hle)⟩


def wiredConnToBdryMass {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (p q : Real) (x : V) : Real :=
  ∑ omega,
    (finiteConnToBdryEvent G bdry x).indicator (fun _ => (1 : Real)) omega *
      wiredFkProb G bdry p q omega



theorem wiredConnToBdryMass_equiv
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hadj : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : ∀ x, bdryV x ↔ bdryW (sigma x))
    (p q : Real) (x : V) :
    wiredConnToBdryMass H bdryW p q (sigma x) =
      wiredConnToBdryMass G bdryV p q x := by
  classical
  unfold wiredConnToBdryMass
  rw [← Equiv.sum_comp (reCfgIsoEquiv sigma)]
  apply Finset.sum_congr rfl
  intro omega _
  have hconn :
      ConnToBdry G bdryV (reCfgIso sigma omega) x ↔
        ConnToBdry H bdryW omega (sigma x) := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨sigma y, (hbdry y).mp hy, ?_⟩
      exact (fvs_openSubIso G H sigma hadj omega).reachable_iff.mpr hxy
    · rintro ⟨y, hy, hxy⟩
      refine ⟨sigma.symm y, ?_, ?_⟩
      · simpa using (hbdry (sigma.symm y)).mpr (by simpa using hy)
      · have hout : (openSub H omega).Reachable
            ((fvs_openSubIso G H sigma hadj omega) x)
            ((fvs_openSubIso G H sigma hadj omega) (sigma.symm y)) := by
          simpa [fvs_openSubIso] using hxy
        exact (fvs_openSubIso G H sigma hadj omega).reachable_iff.mp hout
  rw [show (finiteConnToBdryEvent H bdryW (sigma x)).indicator
      (fun _ => (1 : Real)) omega =
      (finiteConnToBdryEvent G bdryV x).indicator
        (fun _ => (1 : Real)) (reCfgIso sigma omega) by
    by_cases h : ConnToBdry G bdryV (reCfgIso sigma omega) x
    · rw [Set.indicator_of_mem
          (show omega ∈ finiteConnToBdryEvent H bdryW (sigma x) from hconn.mp h),
        Set.indicator_of_mem
          (show reCfgIso sigma omega ∈ finiteConnToBdryEvent G bdryV x from h)]
    · rw [Set.indicator_of_notMem
          (show omega ∉ finiteConnToBdryEvent H bdryW (sigma x) from
            fun ht => h (hconn.mpr ht)),
        Set.indicator_of_notMem
          (show reCfgIso sigma omega ∉ finiteConnToBdryEvent G bdryV x from h)]]
  rw [← fvs_wiredFkProb_reCfgIso G H bdryV bdryW sigma hadj hbdry]
  rfl



theorem connToBdry_innerRestrict_of_connToBdry_outer
    {d : Nat} {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (hsub : Sin ⊆ Sout)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
    (hbdryIn : ∀ (x : Sin) (z : Site d),
      NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
    (rho : ConfigSpace (Sym2 Sout)) (x : Sin)
    (hout : ConnToBdry
      (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut rho
        (flc_incl hsub x)) :
    ConnToBdry (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn
      (ocd_innerRestrict (flc_incl hsub) rho) x := by
  let Gout : SimpleGraph Sout :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let Gin : SimpleGraph Sin :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let OS := openSub Gout rho
  let os := openSub Gin (ocd_innerRestrict (flc_incl hsub) rho)
  obtain ⟨z, hzbdry, hxz⟩ := hout
  have hzout : (z : Site d) ∉ Sin := by
    intro hz
    let zin : Sin := ⟨z, hz⟩
    have heq : flc_incl hsub zin = z := Subtype.ext rfl
    exact hmargin zin (heq ▸ hzbdry)
  change OS.Reachable (flc_incl hsub x) z at hxz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxz
  suffices H : ∀ w : Sout,
      Relation.ReflTransGen OS.Adj (flc_incl hsub x) w ->
        (ConnToBdry Gin bdryIn (ocd_innerRestrict (flc_incl hsub) rho) x ∨
          ∃ y : Sin, flc_incl hsub y = w ∧ os.Reachable x y) by
    rcases H z hxz with hdone | ⟨y, hy, hxy⟩
    · exact hdone
    · exact absurd (hy ▸ y.2) hzout
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w huw hadj ih =>
      rcases ih with hdone | ⟨y, hy, hxy⟩
      · exact Or.inl hdone
      · subst hy
        by_cases hwIn : (w : Site d) ∈ Sin
        · let win : Sin := ⟨w, hwIn⟩
          have hwEq : flc_incl hsub win = w := Subtype.ext rfl
          refine Or.inr ⟨win, hwEq, hxy.trans ?_⟩
          apply SimpleGraph.Adj.reachable
          rw [openSub_adj] at hadj ⊢
          constructor
          · simpa [Gin, Gout, flc_incl] using hadj.1
          · simpa [ocd_innerRestrict, ocd_innerEdge, hwEq] using hadj.2
        · left
          refine ⟨y, hbdryIn y (w : Site d) ?_ hwIn, hxy⟩
          rw [openSub_adj] at hadj
          simpa [Gout, flc_incl] using hadj.1



theorem wiredConnToBdryMass_outer_le_inner
    {d : Nat} {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (hsub : Sin ⊆ Sout)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
    (hbdryIn : ∀ (x : Sin) (z : Site d),
      NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : Sin) :
    wiredConnToBdryMass
        (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q
          (flc_incl hsub x) ≤
      wiredConnToBdryMass
        (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q x := by
  let Gout : SimpleGraph Sout :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let Gin : SimpleGraph Sin :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let A := finiteConnToBdryEvent Gin bdryIn x
  have hdom := ocd_latticeWired_inner_dominated
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    bdryOut bdryIn hmargin hbdryIn hp hp1 hq
    (finiteConnToBdryEvent_isIncreasing Gin bdryIn x)
  change (∑ rho,
      (finiteConnToBdryEvent Gout bdryOut (flc_incl hsub x)).indicator
          (fun _ => (1 : Real)) rho * wiredFkProb Gout bdryOut p q rho) ≤ _
  refine le_trans ?_ hdom
  apply Finset.sum_le_sum
  intro rho _
  apply mul_le_mul_of_nonneg_right _
    (wiredFkProb_nonneg Gout bdryOut hp hp1 (zero_lt_one.trans_le hq) rho)
  apply Set.indicator_le_indicator_of_subset
  · intro eta heta
    exact connToBdry_innerRestrict_of_connToBdry_outer hsub bdryOut bdryIn
      hmargin hbdryIn eta x heta
  · exact zero_le_one


def transBoxCenter (d n : Nat) (x : Site d) :
    fvs_transBoxVerts d n x :=
  fvs_transEquiv d n x (boxOrigin d n)

@[simp] theorem transBoxCenter_val (d n : Nat) (x : Site d) :
    (transBoxCenter d n x : Site d) = x := by
  funext i
  simp [transBoxCenter, boxOrigin, fvs_transEquiv_val, origin]



theorem translated_wiredConnToBdryMass_eq_centered
    {d : Nat} (x : Site d) (n : Nat) (p q : Real) :
    wiredConnToBdryMass (fvs_transBoxGraph d n x)
        (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) =
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        (boxOrigin d n) := by
  simpa [transBoxCenter] using
    (wiredConnToBdryMass_equiv
      (boxGraph d n) (fvs_transBoxGraph d n x)
      (boxBoundary d n) (fvs_transBoxBoundary d n x)
      (fvs_transEquiv d n x) (fvs_transEquiv_adj d n x)
      (fvs_transEquiv_boundary d n x) p q (boxOrigin d n))


theorem translated_outer_boundaryMass_le_centered_marked
    {d : Nat} (x : Site d) (n : Nat) (hn : 1 ≤ n)
    (hxn : flc_vrad x ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredConnToBdryMass
        (fvs_transBoxGraph d (n + flc_vrad x + 1) x)
        (fvs_transBoxBoundary d (n + flc_vrad x + 1) x) p q
        (transBoxCenter d (n + flc_vrad x + 1) x) ≤
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        ⟨x, by
          exact fun i => (flc_vrad_le x i).trans hxn⟩ := by
  have hsub : box d n ⊆ fvs_transBox d (n + flc_vrad x + 1) x :=
    flc_box_subset_transBox x (by omega)
  have hdom := wiredConnToBdryMass_outer_le_inner hsub
    (fvs_transBoxBoundary d (n + flc_vrad x + 1) x)
    (boxBoundary d n)
    (flc_hmargin_box_in_transBox x hsub (by omega))
    (flc_hbdryIn_box hn) hp hp1 hq
    (⟨x, fun i => (flc_vrad_le x i).trans hxn⟩ : boxVerts d n)
  have hcenter : flc_incl hsub
      (⟨x, fun i => (flc_vrad_le x i).trans hxn⟩ : boxVerts d n) =
      transBoxCenter d (n + flc_vrad x + 1) x := by
    apply Subtype.ext
    simp
  rw [hcenter] at hdom
  simpa only [boxGraph, fvs_transBoxGraph, transBoxCenter_val] using hdom


theorem centered_marked_boundaryMass_le_translated_inner
    {d : Nat} (x : Site d) (n : Nat) (hn : 1 ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredConnToBdryMass
        (boxGraph d (n + flc_vrad x + 1))
        (boxBoundary d (n + flc_vrad x + 1)) p q
        ⟨x, box_mono d (by omega) (fun i => flc_vrad_le x i)⟩ ≤
      wiredConnToBdryMass (fvs_transBoxGraph d n x)
        (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) := by
  have hsub : fvs_transBox d n x ⊆ box d (n + flc_vrad x + 1) :=
    (flc_transBox_subset_box x n).trans (box_mono d (by omega))
  have hdom := wiredConnToBdryMass_outer_le_inner hsub
    (boxBoundary d (n + flc_vrad x + 1))
    (fvs_transBoxBoundary d n x)
    (flc_hmargin_transBox_in_box x hsub)
    (flc_hbdryIn_transBox hn x) hp hp1 hq (transBoxCenter d n x)
  have hcenter : flc_incl hsub (transBoxCenter d n x) =
      (⟨x, box_mono d (by omega) (fun i => flc_vrad_le x i)⟩ :
        boxVerts d (n + flc_vrad x + 1)) := by
    apply Subtype.ext
    simp
  rw [hcenter] at hdom
  simpa only [boxGraph, fvs_transBoxGraph, transBoxCenter_val] using hdom



def boxMarkedVertex (d n : Nat) (x : Site d) : boxVerts d n :=
  if hx : x ∈ box d n then ⟨x, hx⟩ else boxOrigin d n

theorem boxMarkedVertex_eq_of_mem {d n : Nat} {x : Site d}
    (hx : x ∈ box d n) :
    boxMarkedVertex d n x = ⟨x, hx⟩ := by
  simp [boxMarkedVertex, hx]


def centeredMarkedBoundaryMass (d : Nat) (x : Site d) (n : Nat)
    (p q : Real) : Real :=
  wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
    (boxMarkedVertex d n x)

theorem centeredMarkedBoundaryMass_eq_of_mem
    {d n : Nat} {x : Site d} (hx : x ∈ box d n) (p q : Real) :
    centeredMarkedBoundaryMass d x n p q =
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q ⟨x, hx⟩ := by
  simp [centeredMarkedBoundaryMass, boxMarkedVertex_eq_of_mem hx]


theorem centered_origin_wiredConnToBdryMass_eq_measure
    {d n : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        (boxOrigin d n) =
      (wiredFiniteMeasure d n hp hp1 hq : Measure _).real
        (boxBdryConnEvent d n) := by
  have h := fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) n hp hp1 hq
    (finiteConnToBdryEvent (boxGraph d n) (boxBoundary d n) (boxOrigin d n))
    (measurableSet_boxBdryConnEvent d n)
  simpa [wiredConnToBdryMass, finiteConnToBdryEvent,
    boxBdryConnEvent] using h.symm



theorem centered_origin_wiredConnToBdryMass_tendsto
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n => wiredConnToBdryMass
        (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n))
      atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
  have h := fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp hp1 hq
  exact h.congr' (Filter.Eventually.of_forall fun n =>
    (centered_origin_wiredConnToBdryMass_eq_measure
      (d := d) (n := n) hp hp1 (zero_lt_one.trans_le hq)).symm)



theorem centeredMarkedBoundaryMass_tendsto
    {d : Nat} (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n => centeredMarkedBoundaryMass d x n p q) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
  let c := flc_vrad x
  let originMass := fun n => wiredConnToBdryMass
    (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n)
  have horigin : Tendsto originMass atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    simpa only [originMass] using
      centered_origin_wiredConnToBdryMass_tendsto hp hp1 hq
  have hlo : Tendsto (fun n => originMass (n + c + 1)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    exact horigin.comp (by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun n hn => by omega⟩)
  have hhi : Tendsto (fun n => originMass (n - c - 1)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    exact horigin.comp (by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b + c + 1, fun n hn => by omega⟩)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 c)] with n hn
    have hn1 : 1 ≤ n := le_max_left 1 c |>.trans hn
    have hcn : c ≤ n := le_max_right 1 c |>.trans hn
    have hx : x ∈ box d n := fun i => (flc_vrad_le x i).trans hcn
    rw [centeredMarkedBoundaryMass_eq_of_mem hx]
    rw [show originMass (n + c + 1) =
        wiredConnToBdryMass
          (fvs_transBoxGraph d (n + flc_vrad x + 1) x)
          (fvs_transBoxBoundary d (n + flc_vrad x + 1) x) p q
          (transBoxCenter d (n + flc_vrad x + 1) x) by
      rw [translated_wiredConnToBdryMass_eq_centered]]
    exact translated_outer_boundaryMass_le_centered_marked
      x n hn1 hcn hp hp1 hq
  · filter_upwards [eventually_ge_atTop (c + 2)] with n hn
    let k := n - c - 1
    have hk1 : 1 ≤ k := by omega
    have hkn : k + c + 1 = n := by omega
    have hx : x ∈ box d n := fun i =>
      (flc_vrad_le x i).trans (by omega)
    rw [show originMass (n - c - 1) =
        wiredConnToBdryMass (fvs_transBoxGraph d k x)
          (fvs_transBoxBoundary d k x) p q (transBoxCenter d k x) by
      rw [translated_wiredConnToBdryMass_eq_centered]]
    have hbound := centered_marked_boundaryMass_le_translated_inner
      x k hk1 hp hp1 hq
    have hkn' : k + flc_vrad x + 1 = n := by simpa only [c] using hkn
    have hxk : x ∈ box d (k + flc_vrad x + 1) := fun i =>
      (flc_vrad_le x i).trans (by omega)
    rw [← centeredMarkedBoundaryMass_eq_of_mem hxk p q] at hbound
    rw [hkn'] at hbound
    exact hbound


theorem shift_preimage_clusterInfiniteEvent_wired
    {d : Nat} (g : Multiplicative (Site d)) (x : Site d) :
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> _) ⁻¹'
        clusterInfiniteEvent d (g • x) =
      clusterInfiniteEvent d x := by
  ext omega
  change (cluster d (ConfigSpace.shift g omega) (g • x)).Infinite ↔
    (cluster d omega x).Infinite
  rw [cluster_shift]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))



theorem wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta
    {d : Nat} (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (clusterInfiniteEvent d x) =
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-x)
  have hg : g • x = origin d := by
    change (-x) + x = origin d
    rw [neg_add_cancel]
    rfl
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> _) ⁻¹'
          percolationEvent d = clusterInfiniteEvent d x := by
    have h := shift_preimage_clusterInfiniteEvent_wired (d := d) g x
    rw [hg] at h
    simpa [percolationEvent, clusterInfiniteEvent] using h
  have hpres := fkgqt_wiredIV_isTranslationInvariant hp hp1 hq g
  have hmeas : MeasurableSet (percolationEvent d) := by
    simpa [percolationEvent, clusterInfiniteEvent] using
      (measurableSet_clusterInfiniteEvent (d := d) (origin d))
  unfold fkTheta
  change mu.real (clusterInfiniteEvent d x) = mu.real (percolationEvent d)
  rw [← hpre]
  exact hpres.measureReal_preimage hmeas.nullMeasurableSet



theorem wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (x : Site d)
    (hx : x ∈ box d n) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (wiredOpenExteriorFiniteMeasure d n hp hp1 hq : Measure _).real
        (clusterInfiniteEvent d x) =
      centeredMarkedBoundaryMass d x n p q := by
  let xb : boxVerts d n := ⟨x, hx⟩
  have hpre : extendWiredEdge d n ⁻¹' clusterInfiniteEvent d x =
      finiteConnToBdryEvent (boxGraph d n) (boxBoundary d n) xb := by
    ext omega
    change (cluster d (extendWiredEdge d n omega) (xb : Site d)).Infinite ↔
      ConnToBdry (boxGraph d n) (boxBoundary d n) omega xb
    exact cluster_extendWiredEdge_infinite_iff_connToBdry hd hn omega xb
  have hmeas : MeasurableSet (clusterInfiniteEvent d x) :=
    measurableSet_clusterInfiniteEvent x
  unfold wiredOpenExteriorFiniteMeasure
  change (Measure.map (extendWiredEdge d n)
      (wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
        (clusterInfiniteEvent d x)).toReal = _
  rw [Measure.map_apply (measurable_extendWiredEdge d n) hmeas,
    hpre, wiredFkPMF_toMeasure_toReal]
  rw [centeredMarkedBoundaryMass_eq_of_mem hx]
  rfl



theorem wiredOpenExterior_clusterInfiniteEvent_real_tendsto
    {d : Nat} (hd : 2 ≤ d) (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n =>
        (wiredOpenExteriorFiniteMeasure d n hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (clusterInfiniteEvent d x)) atTop
      (nhds ((wiredInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (clusterInfiniteEvent d x))) := by
  have hmass := centeredMarkedBoundaryMass_tendsto x hp hp1 hq
  have heq : (λ n =>
      (wiredOpenExteriorFiniteMeasure d n hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (clusterInfiniteEvent d x)) =ᶠ[atTop]
      (λ n => centeredMarkedBoundaryMass d x n p q) := by
    filter_upwards [eventually_ge_atTop (max 1 (flc_vrad x))] with n hn
    have hn1 : 1 ≤ n := le_max_left 1 (flc_vrad x) |>.trans hn
    have hxn : flc_vrad x ≤ n :=
      le_max_right 1 (flc_vrad x) |>.trans hn
    have hx : x ∈ box d n := fun i => (flc_vrad_le x i).trans hxn
    exact wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass
      hd hn1 x hx hp hp1 (zero_lt_one.trans_le hq)
  rw [wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta x hp hp1 hq]
  exact hmass.congr' heq.symm



def wiredTruncatedInfiniteEvent (d R : Nat) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | (cluster d (wiredTruncationEdge d R omega) x).Infinite}

theorem wiredTruncatedInfiniteEvent_eq_preimage
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    wiredTruncatedInfiniteEvent d R x =
      boxRestrict d R ⁻¹'
        finiteConnToBdryEvent (boxGraph d R) (boxBoundary d R) ⟨x, hx⟩ := by
  ext omega
  change (cluster d (extendWiredEdge d R (boxRestrict d R omega)) x).Infinite ↔
    ConnToBdry (boxGraph d R) (boxBoundary d R)
      (boxRestrict d R omega) ⟨x, hx⟩
  exact cluster_extendWiredEdge_infinite_iff_connToBdry
    hd hR (boxRestrict d R omega) ⟨x, hx⟩

theorem isClopen_wiredTruncatedInfiniteEvent
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    IsClopen (wiredTruncatedInfiniteEvent d R x) := by
  rw [wiredTruncatedInfiniteEvent_eq_preimage hd hR x hx]
  exact (isClopen_discrete _).preimage (continuous_boxRestrict d R)

theorem measurableSet_wiredTruncatedInfiniteEvent
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    MeasurableSet (wiredTruncatedInfiniteEvent d R x) :=
  (isClopen_wiredTruncatedInfiniteEvent hd hR x hx).isOpen.measurableSet

end

end StatMech.FK
