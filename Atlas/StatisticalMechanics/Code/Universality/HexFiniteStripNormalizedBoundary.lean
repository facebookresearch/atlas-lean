/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexFiniteStripNormalization
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexInfraWinding
import Code.Universality.HexFiniteStripEnum
import Code.Universality.HexInfraHeading
import Code.Universality.HexStripInterior
import Code.Universality.HexReturnUniqueness

namespace StatMech.Universality

open Complex HexWalk



theorem hexLegalSAW_eq_nil_of_lastVertex_eq_first
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsLegalSAW)
    (hlast : hexInfra_midAccum a h0 ts
        + halfStep (hexInfra_headAccum h0 ts) = a + halfStep h0) :
    ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      exfalso
      have hnd : (verticesAux a h0 (t :: ts)).Nodup := hsaw.2
      rw [verticesAux_cons, List.nodup_cons] at hnd
      apply hnd.1
      have hmem := hexInfra_verticesAux_getLast_mem
        (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) ts
      rw [← hexInfra_midAccum_cons, ← hexInfra_headAccum_cons, hlast] at hmem
      exact hmem

namespace HexFiniteRegion



def StartInteriorUnique (R : HexFiniteRegion) (h0 : ℤ) : Prop :=
  ∀ h : ℤ, R.start + halfStep h ∈ R.verts →
    R.start + halfStep h = R.start + halfStep h0




theorem not_startInteriorUnique (R : HexFiniteRegion) (h0 : ℤ) :
    ¬R.StartInteriorUnique h0 := by
  intro hstart
  have hstay :
      (ofTurns R.start (h0 + 1) []).StaysIn R.inRegion := by
    intro m hm
    change m ∈ R.mids
    have hmids : (ofTurns R.start (h0 + 1) []).mids = [R.start] := by
      show (trivialWalk R.start (h0 + 1)).mids = [R.start]
      unfold HexWalk.mids
      simp [trivialWalk]
    rw [hmids] at hm
    have hma : m = R.start := List.mem_singleton.mp hm
    exact hma ▸ R.start_mem
  have hmem : R.start + halfStep (h0 + 1) ∈ R.verts := by
    apply R.vertices_mem R.start (h0 + 1) [] hstay
    change R.start + halfStep (h0 + 1) ∈
      [R.start + halfStep (h0 + 1)]
    exact List.mem_singleton.mpr rfl
  have heq := hstart (h0 + 1) hmem
  have hstep : halfStep (h0 + 1) = halfStep h0 := add_left_cancel heq
  have hdiv : (6 : ℤ) ∣ (h0 + 1 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
  norm_num at hdiv




theorem hexStrip_finiteRegion_not_startInteriorUnique
    (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (h0 : ℤ) :
    ¬(hexStrip_finiteRegion M a ha).StartInteriorUnique h0 := by
  intro hstart
  have hmem :
      a + halfStep (h0 + 1) ∈
        (hexStrip_finiteRegion M a ha).verts := by
    rw [hexStrip_finiteRegion_verts]
    exact hexStrip_mem_verts M ha (h0 + 1)
  have heq := hstart (h0 + 1) hmem
  have hstep : halfStep (h0 + 1) = halfStep h0 := by
    exact add_left_cancel heq
  have hdiv : (6 : ℤ) ∣ (h0 + 1 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
  norm_num at hdiv


















structure DirectedStartIncidence (R : HexFiniteRegion) (h0 : ℤ) where
  
  dregion : ℂ → ℤ → Prop
  
  project : ∀ m h, dregion m h → R.inRegion m
  
  walksInDirectedRegion : ∀ ts : List ℤ,
    (ofTurns R.start h0 ts).IsLegalSAW →
    (ofTurns R.start h0 ts).StaysIn R.inRegion →
    hexStripStaysInDir dregion R.start h0 ts
  
  start_exact : ∀ h : ℤ, dregion R.start h → halfStep h = halfStep h0


theorem hexStripDirMids_final_mem (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts, hexInfra_headAccum h ts) ∈
      hexStripDirMids m h ts := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
      rw [hexStripDirMids_cons]
      exact List.mem_cons_of_mem _
        (ih (m + halfStep h + halfStep (h + t)) (h + t))



theorem hexStart_midsAux_prefix (m : ℂ) (h : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) : midsAux m h s <+: midsAux m h ts := by
  obtain ⟨u, rfl⟩ := hst
  induction s generalizing m h with
  | nil =>
      cases u <;> simp [midsAux]
  | cons t s ih =>
      rw [List.cons_append, midsAux_cons, midsAux_cons]
      exact (List.prefix_cons_inj _).mpr
        (ih (m + halfStep h + halfStep (h + t)) (h + t))



theorem hexStart_verticesAux_prefix (m : ℂ) (h : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) : verticesAux m h s <+: verticesAux m h ts := by
  obtain ⟨u, rfl⟩ := hst
  induction s generalizing m h with
  | nil =>
      cases u <;> simp [verticesAux]
  | cons t s ih =>
      rw [List.cons_append, verticesAux_cons, verticesAux_cons]
      exact (List.prefix_cons_inj _).mpr
        (ih (m + halfStep h + halfStep (h + t)) (h + t))


theorem hexStart_isLegalSAW_of_prefix (a : ℂ) (h0 : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 s).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hlegal.1 t (hst.sublist.mem ht)
  · change (verticesAux a h0 s).Nodup
    have hsaw := hlegal.2
    change (verticesAux a h0 ts).Nodup at hsaw
    exact hsaw.sublist (hexStart_verticesAux_prefix a h0 hst).sublist


theorem hexStart_staysIn_of_prefix
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) (hstay : (ofTurns a h0 ts).StaysIn inRegion) :
    (ofTurns a h0 s).StaysIn inRegion := by
  intro m hm
  apply hstay m
  change m ∈ midsAux a h0 s at hm
  change m ∈ midsAux a h0 ts
  exact (hexStart_midsAux_prefix a h0 hst).sublist.mem hm




theorem hexStripDirMids_mem_prefix_state
    (m : ℂ) (h : ℤ) (ts : List ℤ) (p : ℂ × ℤ)
    (hp : p ∈ hexStripDirMids m h ts) :
    ∃ s : List ℤ, s <+: ts ∧
      p = (hexInfra_midAccum m h s, hexInfra_headAccum h s) := by
  induction ts generalizing m h with
  | nil =>
      simp only [hexStripDirMids_nil, List.mem_singleton] at hp
      subst p
      exact ⟨[], ⟨[], rfl⟩, rfl⟩
  | cons t ts ih =>
      rw [hexStripDirMids_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨[], ⟨t :: ts, rfl⟩, rfl⟩
      · obtain ⟨s, hs, rfl⟩ :=
          ih (m + halfStep h + halfStep (h + t)) (h + t) hp
        refine ⟨t :: s, ?_, ?_⟩
        · exact (List.prefix_cons_inj t).mpr hs
        · rfl





noncomputable def directedStartIncidence_of_returningUnique
    (R : HexFiniteRegion) (h0 : ℤ)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    R.DirectedStartIncidence h0 where
  dregion := fun m h => R.inRegion m ∧
    (m = R.start → halfStep h = halfStep h0)
  project := by
    intro m h hm
    exact hm.1
  walksInDirectedRegion := by
    intro ts hlegal hstay p hp
    obtain ⟨s, hs, rfl⟩ :=
      hexStripDirMids_mem_prefix_state R.start h0 ts p hp
    have hlegalS := hexStart_isLegalSAW_of_prefix R.start h0 hs hlegal
    have hstayS := hexStart_staysIn_of_prefix R.inRegion R.start h0 hs hstay
    refine ⟨?_, ?_⟩
    · have hm : (ofTurns R.start h0 s).endMid ∈
          (ofTurns R.start h0 s).mids := by
        unfold HexWalk.endMid
        exact List.getLast_mem _
      rw [hexInfra_endMid_eq_midAccum] at hm
      exact hstayS _ hm
    · intro hm
      have hend : (ofTurns R.start h0 s).EndsAt R.start := by
        rw [HexWalk.EndsAt, hexInfra_endMid_eq_midAccum]
        exact hm
      have hs0 := hunique s ⟨hlegalS, hstayS, hend⟩
      subst s
      rfl
  start_exact := by
    intro h hh
    exact hh.2 rfl






theorem returningSAW_eq_nil_of_straightStart_reverse
    (R : HexFiniteRegion) (h0 : ℤ) (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  cases ts with
  | nil => rfl
  | cons t ts =>
      have hdir := S.dir_eq t ts hts
      have hfinal : halfStep (hexInfra_headAccum h0 (t :: ts)) =
          -halfStep h0 := hdir.trans hreverse
      cases ts with
      | nil =>
          have ht : t = 1 ∨ t = -1 := hts.1.1 t (by simp)
          have hrev : halfStep (h0 + 3) = -halfStep h0 :=
            hexW1Exit_halfStep_add_three h0
          have heq : halfStep (h0 + t) = halfStep (h0 + 3) := by
            simpa only [hexInfra_headAccum_cons, hexInfra_headAccum_nil] using
              hfinal.trans hrev.symm
          have hdiv : (6 : ℤ) ∣ (h0 + t - (h0 + 3)) :=
            (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
          rcases ht with rfl | rfl <;> norm_num at hdiv
      | cons s ss =>
          have hend : hexInfra_midAccum R.start h0 (t :: s :: ss) =
              R.start := by
            rw [← hexInfra_endMid_eq_midAccum]
            exact hts.2.2
          have hpen := hexW1Exit_penult_mem
            (R.start + halfStep h0 + halfStep (h0 + t)) (h0 + t) s ss
          have hpen' :
              hexInfra_midAccum R.start h0 (t :: s :: ss)
                    - halfStep (hexInfra_headAccum h0 (t :: s :: ss)) ∈
                verticesAux
                  (R.start + halfStep h0 + halfStep (h0 + t))
                  (h0 + t) (s :: ss) := by
            simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons] using hpen
          have hfirst : R.start + halfStep h0 ∈
              verticesAux
                (R.start + halfStep h0 + halfStep (h0 + t))
                (h0 + t) (s :: ss) := by
            rw [hend, hfinal] at hpen'
            convert hpen' using 1
            all_goals ring
          have hnd := hts.1.2
          change (verticesAux R.start h0 (t :: s :: ss)).Nodup at hnd
          rw [verticesAux_cons, List.nodup_cons] at hnd
          exact (hnd.1 hfirst).elim




noncomputable def directedStartIncidence_of_straightStart_reverse
    (R : HexFiniteRegion) (h0 : ℤ) (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    R.DirectedStartIncidence h0 :=
  R.directedStartIncidence_of_returningUnique h0
    (R.returningSAW_eq_nil_of_straightStart_reverse h0 interior S hreverse)









noncomputable def directedStartIncidence_of_stripStartGeometry
    (R : HexFiniteRegion) (h0 : ℤ) (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    R.DirectedStartIncidence h0 := by
  let S : HexStraightSide R.inRegion (hexStripInterior dregion)
      R.start h0 R.start :=
    hexStrip_straightSide dregion R.inRegion R.start h0 R.start (h0 + 3)
      (by
        intro h hint
        calc
          halfStep h = halfStep h0 := huniq h hint
          _ = halfStep ((h0 + 3) + 3) := by
            rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring,
              hexStrip_halfStep_add6])
      hbridge
  exact R.directedStartIncidence_of_straightStart_reverse h0
    (hexStripInterior dregion) S (by
      change halfStep (h0 + 3) = -halfStep h0
      exact hexW1Exit_halfStep_add_three h0)



theorem returningSAW_eq_nil_of_directedStartIncidence
    (R : HexFiniteRegion) (h0 : ℤ) (S : R.DirectedStartIncidence h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  have hdir := S.walksInDirectedRegion ts hts.1 hts.2.1
  have hfinal : S.dregion
      (hexInfra_midAccum R.start h0 ts) (hexInfra_headAccum h0 ts) :=
    hdir _ (hexStripDirMids_final_mem R.start h0 ts)
  have hend : hexInfra_midAccum R.start h0 ts = R.start := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hts.2.2
  have hheading : halfStep (hexInfra_headAccum h0 ts) = halfStep h0 := by
    apply S.start_exact
    rwa [hend] at hfinal
  apply hexLegalSAW_eq_nil_of_lastVertex_eq_first R.start h0 ts hts.1
  rw [hend, hheading]




theorem hexStrip_singleRegion_legal_stays_eq_nil
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion) :
    ts = [] := by
  have hstayEq : (ofTurns a h0 ts).StaysIn (fun m => m = a) := by
    intro m hm
    have hm' := hstay m hm
    simpa [hexStrip_singleRegion, hexStrip_finiteRegion,
      HexFiniteRegion.inRegion] using hm'
  have hend : (ofTurns a h0 ts).EndsAt a := by
    rw [HexWalk.EndsAt]
    apply hstayEq
    unfold HexWalk.endMid
    exact List.getLast_mem _
  exact hexW1_singleton_admissible_nil a h0 ts ⟨hlegal, hstayEq, hend⟩




noncomputable def hexStrip_singleRegion_directedStartIncidence
    (a : ℂ) (h0 : ℤ) :
    (hexStrip_singleRegion a).DirectedStartIncidence h0 where
  dregion := fun m h => m = a ∧ halfStep h = halfStep h0
  project := by
    intro m h hm
    simp [hexStrip_singleRegion, hexStrip_finiteRegion,
      HexFiniteRegion.inRegion, hm.1]
  walksInDirectedRegion := by
    intro ts hlegal hstay
    have hnil := hexStrip_singleRegion_legal_stays_eq_nil a h0 ts hlegal hstay
    subst hnil
    intro p hp
    simp only [hexStripDirMids_nil, List.mem_singleton] at hp
    subst p
    exact ⟨rfl, rfl⟩
  start_exact := by
    intro h hh
    exact hh.2



theorem hexStrip_singleRegion_returningSAW_eq_nil
    (a : ℂ) (h0 : ℤ) :
    ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion
        ∧ (ofTurns a h0 ts).EndsAt a → ts = [] :=
  (hexStrip_singleRegion a).returningSAW_eq_nil_of_directedStartIncidence h0
    (hexStrip_singleRegion_directedStartIncidence a h0)



theorem hexStrip_singleRegion_directedStartIncidence_nonempty
    (a : ℂ) (h0 : ℤ) :
    Nonempty ((hexStrip_singleRegion a).DirectedStartIncidence h0) :=
  ⟨hexStrip_singleRegion_directedStartIncidence a h0⟩


theorem returningSAW_eq_nil_of_startInteriorUnique
    (R : HexFiniteRegion) (h0 : ℤ) (hstart : R.StartInteriorUnique h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  have hlastMemWalk := hexInfra_verticesAux_getLast_mem R.start h0 ts
  have hlastMemVerts :
      hexInfra_midAccum R.start h0 ts
          + halfStep (hexInfra_headAccum h0 ts) ∈ R.verts :=
    R.vertices_mem R.start h0 ts hts.2.1 _ hlastMemWalk
  have hend : hexInfra_midAccum R.start h0 ts = R.start := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hts.2.2
  have hlast : hexInfra_midAccum R.start h0 ts
      + halfStep (hexInfra_headAccum h0 ts) = R.start + halfStep h0 := by
    rw [hend] at hlastMemVerts
    rw [hend]
    exact hstart _ hlastMemVerts
  exact hexLegalSAW_eq_nil_of_lastVertex_eq_first
    R.start h0 ts hts.1 hlast




theorem returningSAW_eq_nil
    (R : HexFiniteRegion) (h0 : ℤ) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  exact hexReturningLegalSAW_eq_nil R.start h0 ts hts.1 hts.2.2

end HexFiniteRegion



theorem parafObservable_start_eq_weight_of_unique
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (sigma x : ℝ)
    (hreg : inRegion a)
    (hunique : ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt a → ts = []) :
    parafObservable inRegion a h0 a sigma x = (x : ℂ) := by
  unfold parafObservable
  calc
    (∑' ts : List ℤ, parafSummand inRegion a h0 a sigma x ts)
        = parafSummand inRegion a h0 a sigma x [] := by
          apply tsum_eq_single
          intro ts hts
          by_cases hguard :
              (ofTurns a h0 ts).IsLegalSAW
                ∧ (ofTurns a h0 ts).StaysIn inRegion
                ∧ (ofTurns a h0 ts).EndsAt a
          · exact (hts (hunique ts hguard)).elim
          · unfold parafSummand
            rw [if_neg hguard]
    _ = (x : ℂ) := parafSummand_self inRegion a h0 sigma x hreg




theorem parafObservable_start_eq_weight
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (sigma x : ℝ)
    (hreg : inRegion a) :
    parafObservable inRegion a h0 a sigma x = (x : ℂ) :=
  parafObservable_start_eq_weight_of_unique inRegion a h0 sigma x hreg
    (fun ts hts => hexReturningLegalSAW_eq_nil a h0 ts hts.1 hts.2.2)

namespace HexFObsBoundaryData

variable (B : HexFObsBoundaryData)


theorem boundaryIdentity_fa :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa := by
  have hraw := B.raw
  rw [B.alphaRest_eq, B.betaSum_eq, B.epsSum_eq, B.epsbarSum_eq] at hraw
  have hap := hbi_alphaPhase
  have hsp := hbi_slantPhase
  have hreal :
      (-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam))
          + B.ups + hexBdryCt * B.tau : ℝ) = 0 := by
    have hcast :
        ((-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam))
            + B.ups + hexBdryCt * B.tau : ℝ) : ℂ) = 0 := by
      push_cast
      push_cast at hraw hap hsp
      linear_combination hraw + (B.lam : ℂ) * hap - (B.tau : ℂ) * hsp
    exact_mod_cast hcast
  linarith

end HexFObsBoundaryData

variable {V : Type*} [DecidableEq V]

namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)



theorem boundary_identity_fa :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa :=
  B.toFObsBoundaryData.boundaryIdentity_fa



theorem normalized_boundary_identity (hFa : B.Fa = hexChi) :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := B.boundary_identity_fa
  rw [hFa] at h
  calc
    hexBdryCl * (hexChi⁻¹ * B.lam)
          + hexBdryCt * (hexChi⁻¹ * B.tau)
          + hexChi⁻¹ * B.ups
        = hexChi⁻¹ *
            (hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [h]
    _ = 1 := inv_mul_cancel₀ hchi


theorem normalized_contour_boundary_identity (hFa : B.Fa = hexChi) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
  rw [← B.lam_eq, ← B.tau_eq, ← B.ups_eq]
  exact B.normalized_boundary_identity hFa



theorem Fa_eq_hexChi_of_unique_start
    (hreg : R.inRegion R.start)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    B.Fa = hexChi := by
  apply Complex.ofReal_injective
  calc
    (B.Fa : ℂ) = D.obs R.start := B.Fa_eq
    _ = parafObservable R.inRegion R.start h0 R.start (5 / 8) hexChi :=
      B.obs_eq R.start
    _ = (hexChi : ℂ) :=
      parafObservable_start_eq_weight_of_unique
        R.inRegion R.start h0 (5 / 8) hexChi hreg hunique



theorem Fa_eq_hexChi : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil h0



theorem normalized_boundary_identity_closed :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 :=
  B.normalized_boundary_identity B.Fa_eq_hexChi



theorem normalized_contour_boundary_identity_closed :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity B.Fa_eq_hexChi



theorem normalized_contour_boundary_identity_of_unique_start
    (hreg : R.inRegion R.start)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_unique_start hreg hunique)



theorem Fa_eq_hexChi_of_directedStartIncidence
    (S : R.DirectedStartIncidence h0) : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil_of_directedStartIncidence h0 S



theorem normalized_contour_boundary_identity_of_directedStartIncidence
    (S : R.DirectedStartIncidence h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_directedStartIncidence S)




theorem Fa_eq_hexChi_of_straightStart_reverse
    (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) : B.Fa = hexChi :=
  B.Fa_eq_hexChi_of_directedStartIncidence
    (R.directedStartIncidence_of_straightStart_reverse
      h0 interior S hreverse)



theorem normalized_contour_boundary_identity_of_straightStart_reverse
    (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity_of_directedStartIncidence
    (R.directedStartIncidence_of_straightStart_reverse
      h0 interior S hreverse)




theorem Fa_eq_hexChi_of_stripStartGeometry
    (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    B.Fa = hexChi :=
  B.Fa_eq_hexChi_of_directedStartIncidence
    (R.directedStartIncidence_of_stripStartGeometry
      h0 dregion huniq hbridge)




theorem normalized_contour_boundary_identity_of_stripStartGeometry
    (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity_of_directedStartIncidence
    (R.directedStartIncidence_of_stripStartGeometry
      h0 dregion huniq hbridge)



theorem Fa_eq_hexChi_singleRegion
    {a : ℂ}
    (B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P) :
    B₁.Fa = hexChi :=
  B₁.Fa_eq_hexChi_of_directedStartIncidence
    (HexFiniteRegion.hexStrip_singleRegion_directedStartIncidence a h0)



theorem normalized_contour_boundary_identity_singleRegion
    {a : ℂ}
    (B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda (hexStrip_singleRegion a).inRegion
          a h0 B₁.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus (hexStrip_singleRegion a).inRegion
              a h0 B₁.sides hexChi
            + hexContourTauMinus (hexStrip_singleRegion a).inRegion
              a h0 B₁.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon (hexStrip_singleRegion a).inRegion
            a h0 B₁.sides hexChi = 1 :=
  B₁.normalized_contour_boundary_identity_of_directedStartIncidence
    (HexFiniteRegion.hexStrip_singleRegion_directedStartIncidence a h0)



theorem Fa_eq_hexChi_of_startInteriorUnique
    (hstart : R.StartInteriorUnique h0) : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil_of_startInteriorUnique h0 hstart


theorem normalized_contour_boundary_identity_of_startInteriorUnique
    (hstart : R.StartInteriorUnique h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_startInteriorUnique hstart)

end HexFiniteStripBoundaryData

end StatMech.Universality
