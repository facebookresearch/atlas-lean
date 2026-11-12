/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPairedRecurrence

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar





theorem exists_currentSuccessorMarginIndex
    (horizontal vertical : Nat -> Nat)
    (hhorizontal : Tendsto horizontal atTop atTop)
    (hvertical : Tendsto vertical atTop atTop)
    (horizontalRequirement verticalRequirement : Fin 8 -> Int) :
    exists k,
      (forall i, horizontalRequirement i <= horizontal k) /\
      (forall i, horizontalRequirement i <= horizontal (k + 1)) /\
      (forall i, verticalRequirement i <= vertical k) := by
  let horizontalTarget : Nat :=
    ∑ i : Fin 8, (horizontalRequirement i).natAbs
  let verticalTarget : Nat :=
    ∑ i : Fin 8, (verticalRequirement i).natAbs
  have hHorizontal : ∀ᶠ k in atTop, horizontalTarget <= horizontal k :=
    hhorizontal (eventually_ge_atTop horizontalTarget)
  have hVertical : ∀ᶠ k in atTop, verticalTarget <= vertical k :=
    hvertical (eventually_ge_atTop verticalTarget)
  obtain ⟨horizontalIndex, hHorizontalIndex⟩ :=
    eventually_atTop.1 hHorizontal
  obtain ⟨verticalIndex, hVerticalIndex⟩ :=
    eventually_atTop.1 hVertical
  let k := max horizontalIndex verticalIndex
  have hkHorizontal := hHorizontalIndex k (Nat.le_max_left _ _)
  have hkHorizontalSucc := hHorizontalIndex (k + 1)
    ((Nat.le_max_left horizontalIndex verticalIndex).trans
      (Nat.le_add_right k 1))
  have hkVertical := hVerticalIndex k (Nat.le_max_right _ _)
  have hHorizontalTerm (i : Fin 8) :
      (horizontalRequirement i).natAbs <= horizontalTarget := by
    dsimp only [horizontalTarget]
    exact Finset.single_le_sum
      (f := fun j : Fin 8 => (horizontalRequirement j).natAbs)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hVerticalTerm (i : Fin 8) :
      (verticalRequirement i).natAbs <= verticalTarget := by
    dsimp only [verticalTarget]
    exact Finset.single_le_sum
      (f := fun j : Fin 8 => (verticalRequirement j).natAbs)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  refine ⟨k, ?_, ?_, ?_⟩
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hHorizontalTerm i).trans hkHorizontal)
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hHorizontalTerm i).trans hkHorizontalSucc)
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hVerticalTerm i).trans hkVertical)

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

omit [Countable V] in

theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono
    (E : PeriodicPlaneEmbedding P) {n m : Nat} (hnm : n <= m)
    (i : Fin 2) :
    E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.sup'_mono (fun v => |E.vertexCoord v i|)
    (fun _ hv => P.orbitBox_mono hnm hv)
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n)
      P.root_mem_orbitBox_zero⟩

omit [Countable V] in

theorem PeriodicPlaneEmbedding.connectorMarginRequirement_mono
    (E : PeriodicPlaneEmbedding P) {radius radius' : Nat}
    (h : radius <= radius') :
    E.connectorMarginRequirement radius <=
      E.connectorMarginRequirement radius' := by
  unfold PeriodicPlaneEmbedding.connectorMarginRequirement
  apply Nat.ceil_mono
  apply max_le_max
  · apply E.orbitBoxCoordinateBound_mono
    exact P.bufferedRadius_strictMono.monotone h
  · apply E.orbitBoxCoordinateBound_mono
    exact P.bufferedRadius_strictMono.monotone h



theorem PeriodicPlaneEmbedding.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.horizontalCrossingEvent a b c d ⊆
      E.verticalCrossingEvent c d a b := by
  intro omega homega
  change E.axisSwap.rectRestrict a b c d omega ∈
    E.axisSwap.finiteHorizontalCrossing a b c d at homega
  obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using x.2.2.2.1, by simpa using x.2.2.2.2,
      by simpa using x.2.1, by simpa using x.2.2.1⟩
  have hy' : y.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using y.2.2.2.1, by simpa using y.2.2.2.2,
      by simpa using y.2.1, by simpa using y.2.2.1⟩
  have hxBottom : E.rectBottomBoundary c d a b ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxLeft
    refine ⟨z, hxz, ?_⟩
    simpa using hz
  have hyTop : E.rectTopBoundary c d a b ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyRight
    refine ⟨z, hyz, ?_⟩
    simpa using hz
  rw [E.axisSwap.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce
      (E.axisSwap.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices c d a b := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.axisSwap.rectVertices a b c d)).toHom).support := hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨w, _hw, rfl⟩ := hv'
    exact ⟨by simpa using w.2.2.2.1, by simpa using w.2.2.2.2,
      by simpa using w.2.1, by simpa using w.2.2.1⟩
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices c d a b)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices c d a b) hpAmbient⟩
  change E.rectRestrict c d a b omega ∈ E.finiteVerticalCrossing c d a b
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxBottom, hyTop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach



theorem PeriodicPlaneEmbedding.axisSwap_crossingMax_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (aH bH cH dH aV bV cV dV : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.axisSwap.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))
      (mu.real (E.axisSwap.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        (cH n) (dH n) (aH n) (bH n)))
      (mu.real (E.horizontalCrossingEvent
        (cV n) (dV n) (aV n) (bV n)))) atTop (nhds 1) := by
  apply hlimit.squeeze tendsto_const_nhds
  · intro n
    apply max_le_max
    · exact measureReal_mono
        (E.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent
          (aH n) (bH n) (cH n) (dH n))
    · exact measureReal_mono
        (E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
          (aV n) (bV n) (cV n) (dV n))
  · intro n
    exact max_le measureReal_le_one measureReal_le_one

omit [Countable V] [Countable W] in


theorem PairedAlignedConnectorSlack.of_le
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {radius radius' k : Nat} (h : radius <= radius')
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius' k) :
    PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k := by
  have hprimal := E.connectorMarginRequirement_mono h
  have hdual := Edual.connectorMarginRequirement_mono h
  have hprimalInt : (E.connectorMarginRequirement radius : Int) <=
      E.connectorMarginRequirement radius' := by
    exact_mod_cast hprimal
  have hdualInt : (Edual.connectorMarginRequirement radius : Int) <=
      Edual.connectorMarginRequirement radius' := by
    exact_mod_cast hdual
  exact {
    primalLeft := hprimalInt.trans slack.primalLeft
    primalRight := by
      have := slack.primalRight
      omega
    primalBottom := hprimalInt.trans slack.primalBottom
    primalTop := by
      have := slack.primalTop
      omega
    dualLeft := hdualInt.trans slack.dualLeft
    dualRight := by
      have := slack.dualRight
      omega
    dualBottom := hdualInt.trans slack.dualBottom
    dualTop := by
      have := slack.dualTop
      omega }




theorem tendsto_two_max_one_fixedBranches_subsequence
    (H0 V1 V0 H1 : Nat -> Real)
    (hnormal : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1))
    (hrotated : Tendsto (fun n => max (V0 n) (H1 n))
      atTop (nhds 1)) :
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) := by
  rcases tendsto_max_one_fixedBranch_subsequence H0 V1 hnormal with
    ⟨phi, hphi, _hphiBranch, hH0⟩ |
    ⟨phi, hphi, _hphiBranch, hV1⟩
  · have hrotated' := hrotated.comp hphi.tendsto_atTop
    rcases tendsto_max_one_fixedBranch_subsequence
        (fun n => V0 (phi n)) (fun n => H1 (phi n)) hrotated' with
      ⟨psi, hpsi, _hpsiBranch, hV0⟩ |
      ⟨psi, hpsi, _hpsiBranch, hH1⟩
    · left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hH0.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hV0
    · right
      left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hH0.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hH1
  · have hrotated' := hrotated.comp hphi.tendsto_atTop
    rcases tendsto_max_one_fixedBranch_subsequence
        (fun n => V0 (phi n)) (fun n => H1 (phi n)) hrotated' with
      ⟨psi, hpsi, _hpsiBranch, hV0⟩ |
      ⟨psi, hpsi, _hpsiBranch, hH1⟩
    · right
      right
      left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hV1.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hV0
    · right
      right
      right
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hV1.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hH1



theorem exists_pairedAlignedNormalRotatedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius radiusRotated : Nat) :
    exists k,
      PairedAlignedConnectorSlack E Edual family familyDual schedule
        radius k /\
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        family.axisSwap familyDual.axisSwap schedule.axisSwap
        radiusRotated k := by
  let MP : Int := E.connectorMarginRequirement radius
  let MD : Int := Edual.connectorMarginRequirement radius
  let MPR : Int := E.axisSwap.connectorMarginRequirement radiusRotated
  let MDR : Int :=
    Edual.axisSwap.connectorMarginRequirement radiusRotated
  let H : Fin 8 -> Int := ![
    MP - family.baseLeft 0,
    family.baseRight 0 + MP,
    MD - familyDual.baseLeft 0,
    familyDual.baseRight 0 + MD,
    MPR - family.baseLeft 0,
    family.baseRight 0 + MPR,
    MDR - familyDual.baseLeft 0,
    familyDual.baseRight 0 + MDR]
  let Vreq : Fin 8 -> Int := ![
    MP - family.baseBottom 1,
    family.baseTop 1 + MP,
    MD - familyDual.baseBottom 1,
    familyDual.baseTop 1 + MD,
    MPR - family.baseBottom 1,
    family.baseTop 1 + MPR,
    MDR - familyDual.baseBottom 1,
    familyDual.baseTop 1 + MDR]
  obtain ⟨k, hH, hHSucc, hV⟩ :=
    exists_currentSuccessorMarginIndex schedule.horizontal schedule.vertical
      schedule.horizontal_tendsto schedule.vertical_tendsto H Vreq
  have hH0 := hH (0 : Fin 8)
  have hH1 := hH (1 : Fin 8)
  have hH2 := hH (2 : Fin 8)
  have hH3 := hH (3 : Fin 8)
  have hHS4 := hHSucc (4 : Fin 8)
  have hHS5 := hHSucc (5 : Fin 8)
  have hHS6 := hHSucc (6 : Fin 8)
  have hHS7 := hHSucc (7 : Fin 8)
  have hV0 := hV (0 : Fin 8)
  have hV1 := hV (1 : Fin 8)
  have hV2 := hV (2 : Fin 8)
  have hV3 := hV (3 : Fin 8)
  have hV4 := hV (4 : Fin 8)
  have hV5 := hV (5 : Fin 8)
  have hV6 := hV (6 : Fin 8)
  have hV7 := hV (7 : Fin 8)
  simp [H, MP, MD, MPR, MDR] at hH0 hH1 hH2 hH3
  simp [H, MP, MD, MPR, MDR] at hHS4 hHS5 hHS6 hHS7
  simp [Vreq, MP, MD, MPR, MDR] at hV0 hV1 hV2 hV3
  simp [Vreq, MP, MD, MPR, MDR] at hV4 hV5 hV6 hV7
  refine ⟨k, {
    primalLeft := by omega
    primalRight := by omega
    primalBottom := by omega
    primalTop := by omega
    dualLeft := by omega
    dualRight := by omega
    dualBottom := by omega
    dualTop := by omega }, ?_⟩
  refine {
    primalLeft := ?_
    primalRight := ?_
    primalBottom := ?_
    primalTop := ?_
    dualLeft := ?_
    dualRight := ?_
    dualBottom := ?_
    dualTop := ?_ }
  · change E.axisSwap.connectorMarginRequirement radiusRotated <=
      family.baseBottom 1 + schedule.vertical k
    omega
  · change family.baseTop 1 - schedule.vertical k +
      E.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change E.axisSwap.connectorMarginRequirement radiusRotated <=
      family.baseLeft 0 + schedule.horizontal (k + 1)
    omega
  · change family.baseRight 0 - schedule.horizontal (k + 1) +
      E.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change Edual.axisSwap.connectorMarginRequirement radiusRotated <=
      familyDual.baseBottom 1 + schedule.vertical k
    omega
  · change familyDual.baseTop 1 - schedule.vertical k +
      Edual.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change Edual.axisSwap.connectorMarginRequirement radiusRotated <=
      familyDual.baseLeft 0 + schedule.horizontal (k + 1)
    omega
  · change familyDual.baseRight 0 - schedule.horizontal (k + 1) +
      Edual.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega




theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (p n) (pDual n) (family n) (familyDual n) (schedule n)
          (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (family n) (familyDual n) (schedule n)
          (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))
          (muDual.real (Edual.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            0 (extentY n)))) atTop (nhds 1) := by
  let template : Nat -> Finset W := fun n => Pdual.orbitBox n
  have hexists :
      muDual {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- huniqueDual]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      muDual.real (Pdual.setHitsInfinite (template n : Set W)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      Pdual.orbitBoxHitsInfinite_real_tendsto_one muDual hexists
  obtain ⟨radius, hcross⟩ :=
    Edual.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual template htemplateHit
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  apply hcross
      (fun n => (data n).raw.data.widthDual)
      (fun n => (data n).raw.data.heightDual)
      (fun n => (data n).raw.data.widthDual_pos)
      (fun n => (data n).raw.data.heightDual_pos)
      (fun n => (data n).raw.data.baseDual)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real)) pDual hpDual hpDual_le
  · intro n
    exact (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (Pdual.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply Pdual.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (data n).raw.shortTop_eq]
    apply (data n).dualConnector_subset_wide (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply Pdual.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.dual_bottom i)
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.dual_top i)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.dual_left j)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.dual_right j)



structure NormalRotatedInsetLimitData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W))) (padding : Nat) where
  score : Nat -> Real
  scoreDual : Nat -> Real
  family : forall n,
    E.NormalBoundaryBandFamily mu (P.orbitBox n) (score n)
  familyDual : forall n,
    Edual.NormalBoundaryBandFamily muDual
      (Pdual.orbitBox n) (scoreDual n)
  schedule : forall n, PairedAlignedMarginSchedule E Edual
    (family n) (familyDual n) (fun _ => 0) (fun _ => 0)
  index : Nat -> Nat
  level : forall n, AlignedNormalRotatedInsetPairedMixedBoundaryScores
    E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
    (score n) (scoreDual n) (family n) (familyDual n) (schedule n)
    (index n) padding
  familyRotated : forall n,
    E.axisSwap.NormalBoundaryBandFamily mu
      (P.axisSwap.orbitBox n) (score n)
  familyDualRotated : forall n,
    Edual.axisSwap.NormalBoundaryBandFamily muDual
      (Pdual.axisSwap.orbitBox n) (scoreDual n)
  scheduleRotated : forall n,
    PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
      (familyRotated n) (familyDualRotated n)
      (fun _ => 0) (fun _ => 0)
  rotatedLevel : forall n,
    AlignedExactExtentPairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
      (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
      (scheduleRotated n) (index n) (level n).rotatedX
      (level n).rotatedY
  rotatedLevel_heq : forall n, rotatedLevel n ≍ (level n).rotated
  normalLimit : Tendsto (fun n => max
    (mu.real (E.horizontalCrossingEvent
      0 (level n).normalX 0 (level n).normalY))
    (mu.real (E.verticalCrossingEvent
      (level n).normal.raw.data.wideLeft
      (level n).normal.raw.data.wideRight 0 (level n).normalY)))
    atTop (nhds 1)
  rotatedLimit : Tendsto (fun n => max
    (mu.real (E.axisSwap.horizontalCrossingEvent
      0 (level n).rotatedX 0 (level n).rotatedY))
    (mu.real (E.axisSwap.verticalCrossingEvent
      (rotatedLevel n).raw.data.wideLeft
      (rotatedLevel n).raw.data.wideRight 0 (level n).rotatedY)))
    atTop (nhds 1)
  dualNormalLimit : Tendsto (fun n => max
    (muDual.real (Edual.horizontalCrossingEvent
      0 (level n).normalX 0 (level n).normalY))
    (muDual.real (Edual.verticalCrossingEvent
      (level n).normal.raw.data.wideLeft
      (level n).normal.raw.data.wideRight 0 (level n).normalY)))
    atTop (nhds 1)
  dualRotatedLimit : Tendsto (fun n => max
    (muDual.real (Edual.axisSwap.horizontalCrossingEvent
      0 (level n).rotatedX 0 (level n).rotatedY))
    (muDual.real (Edual.axisSwap.verticalCrossingEvent
      (rotatedLevel n).raw.data.wideLeft
      (rotatedLevel n).raw.data.wideRight 0 (level n).rotatedY)))
    atTop (nhds 1)



theorem NormalRotatedInsetLimitData.normalWideInset_eq_rotatedY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).normal.raw.wideLeftInt + padding +
        (data.level n).rotatedY =
      (data.level n).normal.raw.wideRightInt - padding := by
  have hspan := (data.level n).normalSpan_eq
  omega


theorem NormalRotatedInsetLimitData.normalWideInset_real_eq_rotatedY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).normal.raw.data.wideLeft + padding +
        (data.level n).rotatedY =
      (data.level n).normal.raw.data.wideRight - padding := by
  rw [(data.level n).normal.raw.wideLeft_eq,
    (data.level n).normal.raw.wideRight_eq]
  exact_mod_cast data.normalWideInset_eq_rotatedY n


theorem NormalRotatedInsetLimitData.rotatedWideRight_eq_left_add_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).rotated.raw.wideRightInt =
      (data.level n).rotated.raw.wideLeftInt +
        (data.level n).normalY := by
  have hspan := (data.level n).rotatedSpan_eq
  omega


theorem NormalRotatedInsetLimitData.rotatedWide_real_eq_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).rotated.raw.data.wideRight =
      (data.level n).rotated.raw.data.wideLeft +
        (data.level n).normalY := by
  rw [(data.level n).rotated.raw.wideLeft_eq,
    (data.level n).rotated.raw.wideRight_eq]
  exact_mod_cast data.rotatedWideRight_eq_left_add_normalY n



theorem NormalRotatedInsetLimitData.rotatedX_le_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) : (data.level n).rotatedX <= (data.level n).normalY := by
  have hspan := (data.level n).rotated.raw.extentX_le_wideSpan
  have heq := data.rotatedWideRight_eq_left_add_normalY n
  rw [heq] at hspan
  norm_num at hspan
  exact_mod_cast hspan



theorem NormalRotatedInsetLimitData.rotatedOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX))
      (mu.real (E.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact E.axisSwap_crossingMax_tendsto_one mu
    (fun _ => 0) (fun n => (data.level n).rotatedX)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    (fun n => (data.rotatedLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    data.rotatedLimit



theorem NormalRotatedInsetLimitData.dualRotatedOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).rotatedX)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    (fun n => (data.rotatedLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    data.dualRotatedLimit



theorem NormalRotatedInsetLimitData.exists_primalDualFixedBranchesSubsequence
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    let H0 : Nat -> Real := fun n => mu.real
      (E.horizontalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY)
    let V1 : Nat -> Real := fun n => mu.real
      (E.verticalCrossingEvent
        (data.level n).normal.raw.data.wideLeft
        (data.level n).normal.raw.data.wideRight
        0 (data.level n).normalY)
    let V0 : Nat -> Real := fun n => muDual.real
      (Edual.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX)
    let H1 : Nat -> Real := fun n => muDual.real
      (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) := by
  dsimp only
  exact tendsto_two_max_one_fixedBranches_subsequence _ _ _ _
    data.normalLimit data.dualRotatedOriginalLimit




theorem nonempty_normalRotatedInsetLimitData_of_unique
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (padding : Nat) :
    Nonempty (NormalRotatedInsetLimitData
      E Edual mu muDual padding) := by
  obtain ⟨score, scoreDual, family, familyDual,
      hscore, hscore_le, hscoreDual, hscoreDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique
        hFKGDual hTIDual huniqueDual
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  let familyRotated : forall n,
      E.axisSwap.NormalBoundaryBandFamily mu
        (P.axisSwap.orbitBox n) (score n) := fun n => by
    simpa only [P.axisSwap_orbitBox] using (family n).axisSwap
  let familyDualRotated : forall n,
      Edual.axisSwap.NormalBoundaryBandFamily muDual
        (Pdual.axisSwap.orbitBox n) (scoreDual n) := fun n => by
    simpa only [Pdual.axisSwap_orbitBox] using (familyDual n).axisSwap
  let scheduleRotated : forall n,
      PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n)
        (fun _ => 0) (fun _ => 0) := fun n => by
    convert (schedule n).axisSwap using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals
      exact cast_heq _ _
  obtain ⟨radius, hnormal⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual mu muDual hFKG hTI hunique score scoreDual family familyDual
      schedule hscore hscore_le
  obtain ⟨radiusRotated, hrotated⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual.axisSwap mu muDual hFKG
      (P.axisSwap_isTranslationInvariant mu hTI) hunique score scoreDual
      familyRotated familyDualRotated scheduleRotated hscore hscore_le
  obtain ⟨radiusDual, hnormalDual⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual mu muDual hFKGDual hTIDual huniqueDual score scoreDual
      family familyDual schedule hscoreDual hscoreDual_le
  obtain ⟨radiusDualRotated, hrotatedDual⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual.axisSwap mu muDual hFKGDual
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual) huniqueDual
      score scoreDual familyRotated familyDualRotated scheduleRotated
      hscoreDual hscoreDual_le
  let radiusNormalShared : Nat -> Nat := fun n =>
    max (max (radius n) n) (max (radiusDual n) n)
  let radiusRotatedShared : Nat -> Nat := fun n =>
    max (max (radiusRotated n) n) (max (radiusDualRotated n) n)
  have hslack (n : Nat) :=
    exists_pairedAlignedNormalRotatedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (radiusNormalShared n) (radiusRotatedShared n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let normalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radius n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E Edual
      (Nat.le_max_left _ _) (Classical.choose_spec (hslack n)).1
  let normalSlackDual : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radiusDual n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E Edual
      (Nat.le_max_right _ _) (Classical.choose_spec (hslack n)).1
  let rotatedSlackShared : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (radiusRotatedShared n) (index n) := fun n =>
    by
      convert (Classical.choose_spec (hslack n)).2 using 1
      · exact P.axisSwap_orbitBox n
      · exact Pdual.axisSwap_orbitBox n
      all_goals exact cast_heq _ _
  let rotatedSlack : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusRotated n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E.axisSwap Edual.axisSwap
      (Nat.le_max_left _ _) (rotatedSlackShared n)
  let rotatedSlackDual : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusDualRotated n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E.axisSwap Edual.axisSwap
      (Nat.le_max_right _ _) (rotatedSlackShared n)
  let level : forall n,
      AlignedNormalRotatedInsetPairedMixedBoundaryScores E Edual mu muDual
        (P.orbitBox n) (Pdual.orbitBox n) (score n) (scoreDual n)
        (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choice
      (nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores
        E Edual mu muDual hTI hTIDual (family n) (familyDual n)
        (schedule n) (index n) padding)
  have hnormalLimit := hnormal index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlack
  let rotatedLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).rotatedX
        (level n).rotatedY := fun n => by
    convert (level n).rotated using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  have hrotatedLimit := hrotated index
    (fun n => (level n).rotatedX) (fun n => (level n).rotatedY)
    rotatedLevel rotatedSlack
  have hnormalDualLimit := hnormalDual index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlackDual
  have hrotatedDualLimit := hrotatedDual index
    (fun n => (level n).rotatedX) (fun n => (level n).rotatedY)
    rotatedLevel rotatedSlackDual
  have hrotatedLevelHeq (n : Nat) :
      rotatedLevel n ≍ (level n).rotated := by
    exact cast_heq _ _
  exact ⟨{
    score := score
    scoreDual := scoreDual
    family := family
    familyDual := familyDual
    schedule := schedule
    index := index
    level := level
    familyRotated := familyRotated
    familyDualRotated := familyDualRotated
    scheduleRotated := scheduleRotated
    rotatedLevel := rotatedLevel
    rotatedLevel_heq := hrotatedLevelHeq
    normalLimit := hnormalLimit
    rotatedLimit := hrotatedLimit
    dualNormalLimit := hnormalDualLimit
    dualRotatedLimit := hrotatedDualLimit }⟩





structure NormalTwoRotatedEndpointLimitData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W))) where
  score : Nat -> Real
  scoreDual : Nat -> Real
  family : forall n,
    E.NormalBoundaryBandFamily mu (P.orbitBox n) (score n)
  familyDual : forall n,
    Edual.NormalBoundaryBandFamily muDual
      (Pdual.orbitBox n) (scoreDual n)
  schedule : forall n, PairedAlignedMarginSchedule E Edual
    (family n) (familyDual n) (fun _ => 0) (fun _ => 0)
  index : Nat -> Nat
  level : forall n,
    AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (score n) (scoreDual n) (family n) (familyDual n)
      (schedule n) (index n)
  familyRotated : forall n,
    E.axisSwap.NormalBoundaryBandFamily mu
      (P.axisSwap.orbitBox n) (score n)
  familyDualRotated : forall n,
    Edual.axisSwap.NormalBoundaryBandFamily muDual
      (Pdual.axisSwap.orbitBox n) (scoreDual n)
  scheduleRotated : forall n,
    PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
      (familyRotated n) (familyDualRotated n)
      (fun _ => 0) (fun _ => 0)
  rotatedVerticalLevel : forall n,
    AlignedExactExtentPairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
      (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
      (scheduleRotated n) (index n) (level n).normalY
      (level n).normalX
  rotatedHorizontalLevel : forall n,
    AlignedExactExtentPairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
      (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
      (scheduleRotated n) (index n) (level n).rotatedHorizontalX
      (level n).rotatedHorizontalY
  rotatedVerticalLevel_heq : forall n,
    rotatedVerticalLevel n ≍ (level n).rotatedVertical
  rotatedHorizontalLevel_heq : forall n,
    rotatedHorizontalLevel n ≍ (level n).rotatedHorizontal
  normalLimit : Tendsto (fun n => max
    (mu.real (E.horizontalCrossingEvent
      0 (level n).normalX 0 (level n).normalY))
    (mu.real (E.verticalCrossingEvent
      (level n).normal.raw.data.wideLeft
      (level n).normal.raw.data.wideRight 0 (level n).normalY)))
    atTop (nhds 1)
  dualRotatedVerticalLimit : Tendsto (fun n => max
    (muDual.real (Edual.axisSwap.horizontalCrossingEvent
      0 (level n).normalY 0 (level n).normalX))
    (muDual.real (Edual.axisSwap.verticalCrossingEvent
      (rotatedVerticalLevel n).raw.data.wideLeft
      (rotatedVerticalLevel n).raw.data.wideRight 0 (level n).normalX)))
    atTop (nhds 1)
  dualRotatedHorizontalLimit : Tendsto (fun n => max
    (muDual.real (Edual.axisSwap.horizontalCrossingEvent
      0 (level n).rotatedHorizontalX 0
        (level n).rotatedHorizontalY))
    (muDual.real (Edual.axisSwap.verticalCrossingEvent
      (rotatedHorizontalLevel n).raw.data.wideLeft
      (rotatedHorizontalLevel n).raw.data.wideRight 0
        (level n).rotatedHorizontalY))) atTop (nhds 1)



theorem NormalTwoRotatedEndpointLimitData.normalWide_real_span_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual)
    (n : Nat) :
    (data.level n).normal.raw.data.wideRight -
        (data.level n).normal.raw.data.wideLeft =
      (data.level n).rotatedHorizontalY := by
  rw [(data.level n).normal.raw.wideLeft_eq,
    (data.level n).normal.raw.wideRight_eq]
  exact_mod_cast (data.level n).normalSpan_eq



theorem NormalTwoRotatedEndpointLimitData.rotatedHorizontalWide_real_span_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual)
    (n : Nat) :
    (data.level n).rotatedHorizontal.raw.data.wideRight -
        (data.level n).rotatedHorizontal.raw.data.wideLeft =
      (data.level n).normalY := by
  have hspan := (data.level n).rotatedHorizontalSpan_eq
  rw [(data.level n).rotatedHorizontal.raw.wideLeft_eq,
    (data.level n).rotatedHorizontal.raw.wideRight_eq]
  exact_mod_cast hspan



theorem NormalTwoRotatedEndpointLimitData.dualRotatedVerticalOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).normalX
        (data.rotatedVerticalLevel n).raw.data.wideLeft
        (data.rotatedVerticalLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).normalY)
    (fun _ => 0) (fun n => (data.level n).normalX)
    (fun n => (data.rotatedVerticalLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedVerticalLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).normalX)
    data.dualRotatedVerticalLimit



theorem NormalTwoRotatedEndpointLimitData.dualRotatedHorizontalOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).rotatedHorizontalY 0
        (data.level n).rotatedHorizontalX))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedHorizontalY
        (data.rotatedHorizontalLevel n).raw.data.wideLeft
        (data.rotatedHorizontalLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalX)
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalY)
    (fun n => (data.rotatedHorizontalLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedHorizontalLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalY)
    data.dualRotatedHorizontalLimit



theorem nonempty_normalTwoRotatedEndpointLimitData_of_unique
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    Nonempty (NormalTwoRotatedEndpointLimitData E Edual mu muDual) := by
  obtain ⟨score, scoreDual, family, familyDual,
      hscore, hscore_le, hscoreDual, hscoreDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique
        hFKGDual hTIDual huniqueDual
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  let familyRotated : forall n,
      E.axisSwap.NormalBoundaryBandFamily mu
        (P.axisSwap.orbitBox n) (score n) := fun n => by
    simpa only [P.axisSwap_orbitBox] using (family n).axisSwap
  let familyDualRotated : forall n,
      Edual.axisSwap.NormalBoundaryBandFamily muDual
        (Pdual.axisSwap.orbitBox n) (scoreDual n) := fun n => by
    simpa only [Pdual.axisSwap_orbitBox] using (familyDual n).axisSwap
  let scheduleRotated : forall n,
      PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n)
        (fun _ => 0) (fun _ => 0) := fun n => by
    convert (schedule n).axisSwap using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  obtain ⟨radiusNormal, hnormal⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual mu muDual hFKG hTI hunique score scoreDual family familyDual
      schedule hscore hscore_le
  obtain ⟨radiusDualRotated, hrotatedDual⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual.axisSwap mu muDual hFKGDual
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual) huniqueDual
      score scoreDual familyRotated familyDualRotated scheduleRotated
      hscoreDual hscoreDual_le
  let normalRadius : Nat -> Nat := fun n => max (radiusNormal n) n
  let rotatedRadius : Nat -> Nat := fun n =>
    max (radiusDualRotated n) n
  have hslack (n : Nat) :=
    exists_pairedAlignedNormalRotatedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (normalRadius n) (rotatedRadius n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let normalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radiusNormal n) n) (index n) := fun n =>
    (Classical.choose_spec (hslack n)).1
  let rotatedSlack : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusDualRotated n) n) (index n) := fun n => by
    convert (Classical.choose_spec (hslack n)).2 using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  let level : forall n,
      AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
        E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
        (score n) (scoreDual n) (family n) (familyDual n)
        (schedule n) (index n) := fun n => Classical.choice
    (nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual hTI hTIDual (family n) (familyDual n)
      (schedule n) (index n))
  let rotatedVerticalLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).normalY
        (level n).normalX := fun n => by
    convert (level n).rotatedVertical using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  let rotatedHorizontalLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).rotatedHorizontalX
        (level n).rotatedHorizontalY := fun n => by
    convert (level n).rotatedHorizontal using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  have hnormalLimit := hnormal index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlack
  have hrotatedVerticalLimit := hrotatedDual index
    (fun n => (level n).normalY) (fun n => (level n).normalX)
    rotatedVerticalLevel rotatedSlack
  have hrotatedHorizontalLimit := hrotatedDual index
    (fun n => (level n).rotatedHorizontalX)
    (fun n => (level n).rotatedHorizontalY)
    rotatedHorizontalLevel rotatedSlack
  exact ⟨{
    score := score
    scoreDual := scoreDual
    family := family
    familyDual := familyDual
    schedule := schedule
    index := index
    level := level
    familyRotated := familyRotated
    familyDualRotated := familyDualRotated
    scheduleRotated := scheduleRotated
    rotatedVerticalLevel := rotatedVerticalLevel
    rotatedHorizontalLevel := rotatedHorizontalLevel
    rotatedVerticalLevel_heq := fun n => cast_heq _ _
    rotatedHorizontalLevel_heq := fun n => cast_heq _ _
    normalLimit := hnormalLimit
    dualRotatedVerticalLimit := hrotatedVerticalLimit
    dualRotatedHorizontalLimit := hrotatedHorizontalLimit }⟩

end StatMech.FK.PeriodicPlanar
