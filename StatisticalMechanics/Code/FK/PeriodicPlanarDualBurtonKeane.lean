/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarBurtonKeaneUniqueness











open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



theorem PeriodicGraph.hasInfiniteCluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.HasInfiniteCluster (P.configTranslate z omega) ↔
      P.HasInfiniteCluster omega := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨P.shift (-z) x, ?_⟩
    exact (P.cluster_infinite_configTranslate z omega
      (P.shift (-z) x)).mp (by simpa using hx)
  · rintro ⟨x, hx⟩
    exact ⟨P.shift z x, (P.cluster_infinite_configTranslate z omega x).2 hx⟩



theorem PeriodicGraph.hasInfiniteCluster_measure_eq_one_of_percolation_pos
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu)
    (hpos : 0 < mu P.percolationEvent) :
    mu {omega | P.HasInfiniteCluster omega} = 1 := by
  have hinv : ∀ z : Site 2,
      P.configTranslate z ⁻¹' {omega | P.HasInfiniteCluster omega} =
        {omega | P.HasInfiniteCluster omega} := by
    intro z
    ext omega
    exact P.hasInfiniteCluster_configTranslate z omega
  have hsub : P.percolationEvent ⊆
      {omega | P.HasInfiniteCluster omega} := by
    intro omega hroot
    exact ⟨P.root, hroot⟩
  have hhasPos : 0 < mu {omega | P.HasInfiniteCluster omega} :=
    hpos.trans_le (measure_mono hsub)
  rcases herg.2 _ P.measurableSet_hasInfiniteCluster hinv with hzero | hone
  · rw [hzero] at hhasPos
    exact False.elim (lt_irrefl 0 hhasPos)
  · exact hone



theorem PeriodicGraph.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hzeroOne : ∃ k : ℕ∞,
      mu {omega | P.numInfiniteClusters omega = k} = 1 ∧
        (k = 0 ∨ k = 1))
    (hinfinite : mu {omega | P.HasInfiniteCluster omega} = 1) :
    mu {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
  obtain ⟨k, hk, hk0 | hk1⟩ := hzeroOne
  · subst k
    have hcomp : mu {omega | P.HasInfiniteCluster omega}ᶜ = 0 :=
      (prob_compl_eq_zero_iff P.measurableSet_hasInfiniteCluster).2 hinfinite
    have hsub : {omega | P.numInfiniteClusters omega = 0} ⊆
        {omega | P.HasInfiniteCluster omega}ᶜ := by
      intro omega hzero hinf
      obtain ⟨x, hx⟩ := hinf
      have hnonempty : (P.infiniteClusters omega).Nonempty :=
        ⟨P.cluster omega x, hx, x, rfl⟩
      have hne : (P.infiniteClusters omega).encard ≠ 0 :=
        Set.encard_ne_zero.mpr hnonempty
      exact hne (by simpa [PeriodicGraph.numInfiniteClusters] using hzero)
    have hzero := measure_mono_null hsub hcomp
    rw [hk] at hzero
    exact False.elim (one_ne_zero hzero)
  · subst k
    rwa [P.numInfiniteClusters_eq_one_event] at hk



theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one
    (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hperc : 0 <
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        P.percolationEvent) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have herg := E.freeBufferedInfiniteVolume_isErgodic hp hp1 hq
  have hpercMeasure : 0 < mu P.percolationEvent :=
    (ENNReal.toReal_pos_iff.mp hperc).1
  have hinfinite := P.hasInfiniteCluster_measure_eq_one_of_percolation_pos
    mu herg hpercMeasure
  exact P.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one mu
    (E.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one
      hconn hp hp1 hq) hinfinite

namespace PeriodicPlanarDualPair



def dualPatternPullback (D : PeriodicPlanarDualPair P Pdual)
    (I : Finset (Sym2 W)) (eta : ConfigSpace ↥I) :
    ConfigSpace ↥(I.map D.edgeDual.symm.toEmbedding) :=
  fun e => !eta ⟨D.edgeDual e.1, by simpa using e.2⟩



theorem dualConfigEquiv_setPattern
    (D : PeriodicPlanarDualPair P Pdual)
    (I : Finset (Sym2 W)) (eta : ConfigSpace ↥I)
    (omega : ConfigSpace (Sym2 V)) :
    setPattern I eta (dualConfigEquiv D.edgeDual omega) =
      dualConfigEquiv D.edgeDual
        (setPattern (I.map D.edgeDual.symm.toEmbedding)
          (D.dualPatternPullback I eta) omega) := by
  funext e
  by_cases he : e ∈ I
  · have hePre : D.edgeDual.symm e ∈
        I.map D.edgeDual.symm.toEmbedding := by
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    rw [setPattern_of_mem eta he, dualConfigEquiv_apply,
      setPattern_of_mem (D.dualPatternPullback I eta) hePre]
    simp [dualPatternPullback]
  · have hePre : D.edgeDual.symm e ∉
        I.map D.edgeDual.symm.toEmbedding := by
      simpa using he
    rw [setPattern_of_not_mem eta he]
    change (!omega (D.edgeDual.symm e)) =
      !(setPattern (I.map D.edgeDual.symm.toEmbedding)
        (D.dualPatternPullback I eta) omega (D.edgeDual.symm e))
    rw [setPattern_of_not_mem (D.dualPatternPullback I eta) hePre]



theorem dualMeasure_setPattern_absolutelyContinuous
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (I : Finset (Sym2 W)) (eta : ConfigSpace ↥I) :
    (D.dualMeasure mu).map (setPattern I eta) ≪ D.dualMeasure mu := by
  let Ipre := I.map D.edgeDual.symm.toEmbedding
  let etaPre := D.dualPatternPullback I eta
  have hfun : setPattern I eta ∘ dualConfigEquiv D.edgeDual =
      dualConfigEquiv D.edgeDual ∘ setPattern Ipre etaPre := by
    funext omega
    exact D.dualConfigEquiv_setPattern I eta omega
  have hac := (hpattern Ipre etaPre).map
    (continuous_dualConfigEquiv D.edgeDual).measurable
  unfold dualMeasure
  rw [Measure.map_map (measurable_setPattern I eta)
      (continuous_dualConfigEquiv D.edgeDual).measurable,
    hfun,
    ← Measure.map_map (continuous_dualConfigEquiv D.edgeDual).measurable
      (measurable_setPattern Ipre etaPre)]
  exact hac



theorem dualMeasure_isErgodic
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (herg : P.IsErgodic mu) :
    Pdual.IsErgodic (D.dualMeasure mu) := by
  refine ⟨D.dualMeasure_isTranslationInvariant mu herg.1, ?_⟩
  intro s hs hinv
  let A := (dualConfigEquiv D.edgeDual) ⁻¹' s
  have hAmeas : MeasurableSet A :=
    hs.preimage (continuous_dualConfigEquiv D.edgeDual).measurable
  have hAinv : ∀ z : Site 2, P.configTranslate z ⁻¹' A = A := by
    intro z
    ext omega
    change dualConfigEquiv D.edgeDual (P.configTranslate z omega) ∈ s ↔
      dualConfigEquiv D.edgeDual omega ∈ s
    rw [D.dualConfigEquiv_configTranslate]
    have hz := Set.ext_iff.mp (hinv z) (dualConfigEquiv D.edgeDual omega)
    simpa using hz
  have hzeroOne := herg.2 A hAmeas hAinv
  unfold dualMeasure
  rw [Measure.map_apply
    (continuous_dualConfigEquiv D.edgeDual).measurable hs]
  exact hzeroOne



theorem dualMeasure_hasFiniteEnergy
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu) :
    HasFiniteEnergy (D.dualMeasure mu) := by
  apply hasFiniteEnergy_of_singleOpen (D.dualMeasure mu)
  intro e
  let eta : ConfigSpace ↥({e} : Finset (Sym2 W)) := fun _ => true
  have hac := D.dualMeasure_setPattern_absolutelyContinuous
    mu hpattern ({e} : Finset (Sym2 W)) eta
  have heq : setPattern ({e} : Finset (Sym2 W)) eta = setOpen e := by
    funext omega f
    by_cases hfe : f = e
    · subst f
      simp [eta, setOpen]
    · rw [setPattern_of_not_mem eta (by simpa using hfe)]
      simp [setOpen, hfe]
  rwa [heq] at hac



theorem dualMeasure_numInfiniteClusters_zero_or_one
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : Pdual.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu)
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu) :
    ∃ k : ℕ∞,
      D.dualMeasure mu {omega | Pdual.numInfiniteClusters omega = k} = 1 ∧
        (k = 0 ∨ k = 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  exact D.dualEmbedding.numInfiniteClusters_zero_or_one hconn
    (D.dualMeasure mu) (D.dualMeasure_isErgodic mu herg)
      (D.dualMeasure_hasFiniteEnergy mu hpattern)
      (D.dualMeasure_setPattern_absolutelyContinuous mu hpattern)



theorem dualMeasure_hasUniqueInfiniteCluster_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : Pdual.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu)
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (hinfinite : D.dualMeasure mu
      {omega | Pdual.HasInfiniteCluster omega} = 1) :
    D.dualMeasure mu
      {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  exact Pdual.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one
    (D.dualMeasure mu)
      (D.dualMeasure_numInfiniteClusters_zero_or_one hconn mu herg hpattern)
      hinfinite



theorem freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    (hconnDual : Pdual.graph.Connected)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hdualPerc : 0 < (D.dualMeasure
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _)).real Pdual.percolationEvent) :
    D.dualMeasure
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have herg := D.primalEmbedding.freeBufferedInfiniteVolume_isErgodic hp hp1 hq
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdualPercMeasure : 0 < D.dualMeasure mu Pdual.percolationEvent :=
    (ENNReal.toReal_pos_iff.mp hdualPerc).1
  have hinfinite :=
    Pdual.hasInfiniteCluster_measure_eq_one_of_percolation_pos
      (D.dualMeasure mu) (D.dualMeasure_isErgodic mu herg) hdualPercMeasure
  exact D.dualMeasure_hasUniqueInfiniteCluster_measure_eq_one
    hconnDual mu herg
      (P.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous hp hp1 hq)
      hinfinite




theorem freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_of_freeDualPercolates
    (D : PeriodicPlanarDualPair P Pdual)
    (hconnDual : Pdual.graph.Connected)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hdual : D.FreeDualPercolates p q) :
    D.dualMeasure
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
  apply D.freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one
    hconnDual hp hp1 hq
  unfold FreeDualPercolates freeDualPercolationProbability at hdual
  rw [dif_pos ⟨⟨hp, hp1⟩, zero_lt_one.trans_le hq⟩] at hdual
  unfold dualMeasure Measure.real
  rw [Measure.map_apply
    (continuous_dualConfigEquiv D.edgeDual).measurable
    (percolationEvent_measurableSet Pdual)]
  exact hdual




theorem freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hprimalPerc : 0 <
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        P.percolationEvent)
    (hdualPerc : 0 < (D.dualMeasure
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _)).real Pdual.percolationEvent) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      D.commonUniqueInfiniteClusterEvent = 1 := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have hprimal :=
    D.primalEmbedding.freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one
      hconn hp hp1 hq hprimalPerc
  have hdualMap :=
    D.freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one
      hconnDual hp hp1 hq hdualPerc
  have hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1 := by
    rw [← hdualMap]
    simpa only [dualMeasure, mu] using (Measure.map_apply
      (continuous_dualConfigEquiv D.edgeDual).measurable
      Pdual.measurableSet_hasUniqueInfiniteCluster).symm
  exact D.commonUniqueInfiniteClusterEvent_measure_eq_one mu hprimal hdual

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
