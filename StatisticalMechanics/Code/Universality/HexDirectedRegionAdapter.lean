/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.HexFiniteStripNormalizedBoundary
import Code.Universality.HexBoundaryAssign

namespace StatMech.Universality

open Complex HexWalk





def HexHeadingPeriodic (dregion : ℂ → ℤ → Prop) : Prop :=
  ∀ m h, dregion m h → dregion m (h + 6)





theorem hexStripInterior_of_headingPeriodic_edge
    (dregion : ℂ → ℤ → Prop) (hperiodic : HexHeadingPeriodic dregion)
    (m : ℂ) (h : ℤ) (hmh : dregion m h) :
    hexStripInterior dregion (m + halfStep h)
      ∧ hexStripInterior dregion (m + halfStep (h + 3)) := by
  have hmh6 : dregion m (h + 6) := hperiodic m h hmh
  have hpairs : (m, h) ≠ (m, h + 6) := by
    intro hp
    have := congrArg Prod.snd hp
    omega
  constructor
  · refine ⟨m, m, h, h + 6, hmh, hmh6, hpairs, Or.inl rfl, ?_⟩
    left
    rw [hexStrip_halfStep_add6]
  · refine ⟨m, m, h, h + 6, hmh, hmh6, hpairs, Or.inr rfl, ?_⟩
    right
    convert rfl using 1
    rw [show (h + 6 + 3 : ℤ) = (h + 3) + 6 by ring,
      hexStrip_halfStep_add6]





theorem not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ)
    (hperiodic : HexHeadingPeriodic dregion) (hstart : dregion a h0) :
    ¬(∀ h : ℤ, hexStripInterior dregion (a + halfStep h) →
        halfStep h = halfStep h0) := by
  intro huniq
  have hinterior : hexStripInterior dregion (a + halfStep (h0 + 3)) :=
    (hexStripInterior_of_headingPeriodic_edge dregion hperiodic a h0 hstart).2
  have heq := huniq (h0 + 3) hinterior
  have hdiv : (6 : ℤ) ∣ (h0 + 3 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
  norm_num at hdiv





def hexStripMembershipDRegion (M : Finset ℂ) : ℂ → ℤ → Prop :=
  fun m _ => m ∈ M



theorem hexStripDirMids_fst_mem_midsAux
    (m : ℂ) (h : ℤ) (ts : List ℤ) (p : ℂ × ℤ)
    (hp : p ∈ hexStripDirMids m h ts) : p.1 ∈ midsAux m h ts := by
  induction ts generalizing m h with
  | nil =>
      simp only [hexStripDirMids_nil, List.mem_singleton] at hp
      subst p
      simp [midsAux]
  | cons t ts ih =>
      rw [hexStripDirMids_cons, List.mem_cons] at hp
      rw [midsAux_cons, List.mem_cons]
      rcases hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr
          (ih (m + halfStep h + halfStep (h + t)) (h + t) hp)



theorem hexStripMembershipDRegion_staysInDir
    (M : Finset ℂ) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hstay : (ofTurns a h0 ts).StaysIn (fun m => m ∈ M)) :
    hexStripStaysInDir (hexStripMembershipDRegion M) a h0 ts := by
  intro p hp
  apply hstay p.1
  exact hexStripDirMids_fst_mem_midsAux a h0 ts p hp


theorem hexStripMembershipDRegion_headingPeriodic (M : Finset ℂ) :
    HexHeadingPeriodic (hexStripMembershipDRegion M) := by
  intro m h hm
  exact hm




theorem hexStripMembershipDRegion_not_uniqueInterior
    (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (h0 : ℤ) :
    ¬(∀ h : ℤ,
      hexStripInterior (hexStripMembershipDRegion M) (a + halfStep h) →
        halfStep h = halfStep h0) :=
  not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (hexStripMembershipDRegion M) a h0
    (hexStripMembershipDRegion_headingPeriodic M) ha







theorem hexReturning_staysInDir_of_launch
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ)
    (hlaunch : dregion a h0) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hend : (ofTurns a h0 ts).EndsAt a) :
    hexStripStaysInDir dregion a h0 ts := by
  have hnil := hexReturningLegalSAW_eq_nil a h0 ts hlegal hend
  rw [hnil]
  intro p hp
  simp only [hexStripDirMids_nil, List.mem_singleton] at hp
  subst p
  exact hlaunch







def hexStripInteriorDistinctMidpoint (dregion : ℂ → ℤ → Prop)
    (v : ℂ) : Prop :=
  ∃ (m1 m2 : ℂ) (d1 d2 : ℤ),
    dregion m1 d1 ∧ dregion m2 d2 ∧ m1 ≠ m2
      ∧ hexIncident v m1 d1 ∧ hexIncident v m2 d2


theorem hexStripInterior_of_distinctMidpoint
    (dregion : ℂ → ℤ → Prop) (v : ℂ)
    (hv : hexStripInteriorDistinctMidpoint dregion v) :
    hexStripInterior dregion v := by
  rcases hv with ⟨m1, m2, d1, d2, hm1, hm2, hne, hi1, hi2⟩
  exact ⟨m1, m2, d1, d2, hm1, hm2, fun hp => hne (congrArg Prod.fst hp),
    hi1, hi2⟩




theorem hexStrip_interiorVertices_distinctMidpoint_core
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : hexStripStaysInDir dregion a h0 ts)
    (v : ℂ) (hv : v ∈ (ofTurns a h0 ts).vertices)
    (hvne : v ≠ hexInfra_midAccum a h0 ts
      + halfStep (hexInfra_headAccum h0 ts)) :
    hexStripInteriorDistinctMidpoint dregion v := by
  have hvv : v ∈ verticesAux a h0 ts := hv
  obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ :=
    hexStrip_nonlast_dir a h0 ts v hvv hvne
  have hr1 : dregion m' h' := hstay (m', h') hm1
  have hr2 : dregion
      (m' + halfStep h' + halfStep (h' + t')) (h' + t') :=
    hstay _ hm2
  have htlegal : t' = 1 ∨ t' = -1 :=
    hlegal.1 t' (by unfold ofTurns; exact ht')
  refine ⟨m', m' + halfStep h' + halfStep (h' + t'),
    h', h' + t', hr1, hr2, ?_, ?_, ?_⟩
  · intro hc
    have hzero : halfStep h' + halfStep (h' + t') = 0 := by
      have heq : m' + (halfStep h' + halfStep (h' + t')) = m' + 0 := by
        rw [add_zero, ← add_assoc]
        exact hc.symm
      exact add_left_cancel heq
    exact hexW1_halfStep_add_ne_zero h' t' htlegal hzero
  · left
    exact hveq
  · right
    rw [hexW1Exit_halfStep_add_three, hveq]
    ring




noncomputable def hexStrip_straightSide_distinctMidpoint
    (dregion : ℂ → ℤ → Prop) (inRegion : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (z : ℂ) (Hd : ℤ)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint dregion (z + halfStep h) →
        halfStep h = halfStep (Hd + 3))
    (hbridge : ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z →
      hexStripStaysInDir dregion a h0 ts) :
    HexStraightSide inRegion
      (hexStripInteriorDistinctMidpoint dregion) a h0 z where
  H := Hd
  uniqueInterior := huniq
  interiorVertices := by
    intro ts hadm v hv hvne
    have hzm : hexInfra_midAccum a h0 ts = z := by
      rw [← hexInfra_endMid_eq_midAccum]
      exact hadm.2.2
    refine hexStrip_interiorVertices_distinctMidpoint_core
      dregion a h0 ts hadm.1 (hbridge ts hadm) v hv ?_
    rw [hzm]
    exact hvne

namespace HexFiniteRegion






noncomputable def directedStartIncidence_closed
    (R : HexFiniteRegion) (h0 : ℤ) : R.DirectedStartIncidence h0 :=
  R.directedStartIncidence_of_returningUnique h0 (R.returningSAW_eq_nil h0)





noncomputable def directedStartIncidence_of_distinctMidpointStripStartGeometry
    (R : HexFiniteRegion) (h0 : ℤ) (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hlaunch : dregion R.start h0) :
    R.DirectedStartIncidence h0 := by
  let S : HexStraightSide R.inRegion
      (hexStripInteriorDistinctMidpoint dregion) R.start h0 R.start :=
    hexStrip_straightSide_distinctMidpoint
      dregion R.inRegion R.start h0 R.start (h0 + 3)
      (by
        intro h hint
        calc
          halfStep h = halfStep h0 := huniq h hint
          _ = halfStep ((h0 + 3) + 3) := by
            rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring,
              hexStrip_halfStep_add6])
      (by
        intro ts hts
        exact hexReturning_staysInDir_of_launch
          dregion R.start h0 hlaunch ts hts.1 hts.2.2)
  exact R.directedStartIncidence_of_straightStart_reverse h0
    (hexStripInteriorDistinctMidpoint dregion) S (by
      change halfStep (h0 + 3) = -halfStep h0
      exact hexW1Exit_halfStep_add_three h0)

end HexFiniteRegion








structure HexStripDirectedStartData
    (M : Finset ℂ) (a : ℂ) (h0 : ℤ) where
  
  dregion : ℂ → ℤ → Prop
  
  project : ∀ m h, dregion m h → m ∈ M
  
  launch : dregion a h0
  
  uniqueInterior : ∀ h : ℤ,
    hexStripInteriorDistinctMidpoint dregion (a + halfStep h) →
      halfStep h = halfStep h0

namespace HexStripDirectedStartData



noncomputable def toDirectedStartIncidence
    {M : Finset ℂ} {a : ℂ} {h0 : ℤ}
    (G : HexStripDirectedStartData M a h0) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).DirectedStartIncidence h0 := by
  refine HexFiniteRegion.directedStartIncidence_of_distinctMidpointStripStartGeometry
      (hexStrip_finiteRegion M a ha) h0 G.dregion G.uniqueInterior G.launch




noncomputable def toRegionDirectedStartIncidence
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (G : HexStripDirectedStartData M R.start h0) :
    (hexStrip_region_finiteRegion R M ha).DirectedStartIncidence h0 := by
  simpa [hexStrip_region_finiteRegion] using G.toDirectedStartIncidence ha

end HexStripDirectedStartData






def hexDomainInwardDRegion {V : Type*} [DecidableEq V]
    (D : HexDomain V) (m : ℂ) (h : ℤ) : Prop :=
  ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m ∧ D.pos e.vtx = m + halfStep h


theorem hexDomainInwardDRegion_headingPeriodic
    {V : Type*} [DecidableEq V] (D : HexDomain V) :
    HexHeadingPeriodic (hexDomainInwardDRegion D) := by
  intro m h hm
  rcases hm with ⟨e, he, hmid, hpos⟩
  refine ⟨e, he, hmid, ?_⟩
  rw [hexStrip_halfStep_add6]
  exact hpos



theorem hexDomainInwardDRegion_project
    {V : Type*} [DecidableEq V] {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (m : ℂ) (h : ℤ) (hm : hexDomainInwardDRegion D m h) :
    R.inRegion m := by
  rcases hm with ⟨e, he, hmid, _⟩
  change m ∈ R.mids
  rw [← hmid]
  exact B.mid_mem e he




theorem hexDomainInwardDRegion_not_old_uniqueInterior
    {V : Type*} [DecidableEq V] (D : HexDomain V) (a : ℂ) (h0 : ℤ)
    (hstart : hexDomainInwardDRegion D a h0) :
    ¬(∀ h : ℤ, hexStripInterior (hexDomainInwardDRegion D)
        (a + halfStep h) → halfStep h = halfStep h0) :=
  not_hexStrip_uniqueInterior_of_headingPeriodic_start
    (hexDomainInwardDRegion D) a h0
    (hexDomainInwardDRegion_headingPeriodic D) hstart







noncomputable def hexDomainDirectedStartData_of_boundaryData
    {V : Type*} [DecidableEq V]
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData
      (hexStrip_region_finiteRegion R M ha) h0 D P)
    (hlaunch : hexDomainInwardDRegion D R.start h0)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint (hexDomainInwardDRegion D)
          (R.start + halfStep h) →
        halfStep h = halfStep h0) :
    HexStripDirectedStartData M R.start h0 where
  dregion := hexDomainInwardDRegion D
  project := by
    intro m h hm
    rcases hm with ⟨e, he, hmid, _⟩
    rw [← hmid]
    simpa only [hexStrip_region_finiteRegion_mids] using B.mid_mem e he
  launch := hlaunch
  uniqueInterior := huniq



noncomputable def hexDomainDirectedStartIncidence_of_boundaryData
    {V : Type*} [DecidableEq V]
    (R : HexRegion) (M : Finset ℂ) (ha : R.start ∈ M) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing)
    (B : HexFiniteStripBoundaryData
      (hexStrip_region_finiteRegion R M ha) h0 D P)
    (hlaunch : hexDomainInwardDRegion D R.start h0)
    (huniq : ∀ h : ℤ,
      hexStripInteriorDistinctMidpoint (hexDomainInwardDRegion D)
          (R.start + halfStep h) →
        halfStep h = halfStep h0) :
    (hexStrip_region_finiteRegion R M ha).DirectedStartIncidence h0 :=
  (hexDomainDirectedStartData_of_boundaryData
    R M ha h0 D P B hlaunch huniq).toRegionDirectedStartIncidence
      R M ha h0

end StatMech.Universality
