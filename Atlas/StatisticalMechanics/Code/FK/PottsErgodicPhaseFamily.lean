/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredOrder
import Code.FK.PottsClusterSumWiredErgodicity
import Code.FK.PottsClusterSumProductErgodicity
import Code.FK.PottsClusterSumContinuity
import Code.FK.PottsClusterSumWeakLimitIdentification
import Code.FK.OrderTransition










open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

noncomputable section


theorem pottsClusterSumJointMeasure_otherColor_real
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q)
    (hba : boundaryColor ≠ a)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] (x : Site d) :
    (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
        (pottsColorEvent d q x a) =
      (1 / (q : Real)) *
        edgeMeasure.real {omega | (cluster d omega x).Finite} := by
  have h := congrArg ENNReal.toReal
    (pottsClusterSumJointMeasure_otherColor_apply
      boundaryColor a hba edgeMeasure x)
  have htop : edgeMeasure {omega | (cluster d omega x).Finite} ≠ ⊤ :=
    measure_ne_top edgeMeasure _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at h
  simpa only [Measure.real, ENNReal.toReal_natCast, one_div] using h



def freePottsClusterSumSpinProbabilityMeasure
    (d q : Nat) [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ProbabilityMeasure (PottsConfig d q) :=
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  (pottsClusterSumJointProbabilityMeasure boundaryColor
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR))).map
      continuous_fst.measurable.aemeasurable



def wiredPottsClusterSumSpinProbabilityMeasure
    (d q : Nat) [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ProbabilityMeasure (PottsConfig d q) :=
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  (pottsClusterSumJointProbabilityMeasure boundaryColor
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR))).map
      continuous_fst.measurable.aemeasurable




theorem freePottsClusterSumSpinProbabilityMeasure_isWeakLimit
    (d q : Nat) [NeZero q] (hq : 2 <= q) (boundaryColor : Fin q)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (hfree : ((freeInfiniteVolume d
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        exact neg_neg_of_pos (mul_pos hbeta hJ))
      (by linarith [Real.exp_pos (-(beta * J))])
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
          {omega | (cluster d omega (origin d)).Infinite} = 0) :
    let hp : 0 < 1 - Real.exp (-(beta * J)) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (mul_pos hbeta hJ)
    let hp1 : 1 - Real.exp (-(beta * J)) < 1 := by
      linarith [Real.exp_pos (-(beta * J))]
    exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
        atTop (nhds (freePottsClusterSumSpinProbabilityMeasure
          d q boundaryColor hp hp1)) := by
  dsimp only
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : Real) < q := by
    exact_mod_cast (show 0 < q by omega)
  have hqR1 : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rcases freePottsInfiniteVolume_exists d q hq beta J hbeta hJ with
    ⟨Xi, mu, phi, hphi, hjoint, hspin, hmapSpin, hmapEdge⟩
  let edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 hqR
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi (by simpa [p] using hjoint) continuous_snd
  have hedge : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds edgeLimit) := by
    have h := hedge0
    rw [hmapEdge] at h
    simpa only [freePottsJointFiniteMeasure_map_snd] using h
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d))
      (edgeLimit : Measure (ConfigSpace (Sym2 (Site d)))) := by
    exact fkgqt_freeIV_isTranslationInvariant hp hp1 hqR1
  have horigin : (edgeLimit : Measure _)
      {omega | (cluster d omega (origin d)).Infinite} = 0 := by
    apply (measureReal_eq_zero_iff
      (measure_ne_top (edgeLimit : Measure (ConfigSpace (Sym2 (Site d)))) _)).1
    simpa [edgeLimit, p] using hfree
  have hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d :=
    ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero
      (d := d) (edgeLimit : Measure _) htrans horigin
  have hXi : Xi =
      pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
    apply freePottsJointWeakLimit_eq_clusterSum boundaryColor beta J
      (by simpa [p] using hp) (by simpa [p] using hp1) hqR
      phi hphi Xi edgeLimit
    · simpa [p] using hjoint
    · exact hedge
    · exact hfinite
  have hmu : mu = freePottsClusterSumSpinProbabilityMeasure
      d q boundaryColor hp hp1 := by
    rw [← hmapSpin, hXi]
    rfl
  refine ⟨phi, hphi, ?_⟩
  rw [← hmu]
  exact hspin

theorem freePottsClusterSumSpinProbabilityMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    IsErgodicFor (pottsSpinShift (d := d) (q := q))
      (freePottsClusterSumSpinProbabilityMeasure
        d q boundaryColor hp hp1 : Measure _) := by
  simpa [freePottsClusterSumSpinProbabilityMeasure,
    pottsClusterSumJointProbabilityMeasure,
    pottsClusterFactorInputProbabilityMeasure,
    pottsIIDLabelProbabilityMeasure, pottsClusterSumJointMeasure] using
      (freePottsClusterSumSpinMarginal_isErgodicFor
        (d := d) (q := q) hd hp hp1 boundaryColor)

theorem wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    IsErgodicFor (pottsSpinShift (d := d) (q := q))
      (wiredPottsClusterSumSpinProbabilityMeasure
        d q boundaryColor hp hp1 : Measure _) := by
  simpa [wiredPottsClusterSumSpinProbabilityMeasure,
    pottsClusterSumJointProbabilityMeasure,
    pottsClusterFactorInputProbabilityMeasure,
    pottsIIDLabelProbabilityMeasure, pottsClusterSumJointMeasure] using
      (wiredPottsClusterSumSpinMarginal_isErgodicFor
        (d := d) (q := q) hd hp hp1 boundaryColor)



theorem freePottsClusterSumSpin_colorProbability_eq_inv
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (hfinite : ((freeInfiniteVolume d hp hp1
      (by
        have hqR : (1 : Real) <= q := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
        exact zero_lt_one.trans_le hqR) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
          {omega | (cluster d omega (origin d)).Infinite} = 0) :
    ((freePottsClusterSumSpinProbabilityMeasure
        d q boundaryColor hp hp1 : Measure _).real
      (pottsColorEvent d q (origin d) a)) = 1 / (q : Real) := by
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  by_cases hba : boundaryColor = a
  · subst a
    have hlaw' := pottsClusterSumJointMeasure_boundaryColor_real
      boundaryColor edgeMeasure (origin d)
    have hI : MeasurableSet
        {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega (origin d)).Infinite} :=
      measurableSet_clusterInfinite (origin d)
    have hcomp : edgeMeasure.real
        {omega | (cluster d omega (origin d)).Finite} = 1 := by
      have hset : {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega (origin d)).Finite} =
          {omega | (cluster d omega (origin d)).Infinite}ᶜ := by
        ext omega
        exact not_infinite.symm
      rw [hset, measureReal_compl hI, probReal_univ]
      dsimp only [edgeMeasure]
      rw [hfinite]
      ring
    change (Measure.map Prod.fst
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
        (pottsColorEvent d q (origin d) boundaryColor) = _
    rw [hlaw', hcomp]
    rw [hfinite]
    ring
  · have hcomp : edgeMeasure.real
        {omega | (cluster d omega (origin d)).Finite} = 1 := by
      have hI : MeasurableSet
          {omega : ConfigSpace (Sym2 (Site d)) |
            (cluster d omega (origin d)).Infinite} :=
        measurableSet_clusterInfinite (origin d)
      have hset : {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega (origin d)).Finite} =
          {omega | (cluster d omega (origin d)).Infinite}ᶜ := by
        ext omega
        exact not_infinite.symm
      rw [hset, measureReal_compl hI, probReal_univ]
      dsimp only [edgeMeasure]
      rw [hfinite]
      ring
    change (Measure.map Prod.fst
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
        (pottsColorEvent d q (origin d) a) = _
    rw [pottsClusterSumJointMeasure_otherColor_real
      boundaryColor a hba edgeMeasure (origin d), hcomp]
    field_simp


theorem wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ((wiredPottsClusterSumSpinProbabilityMeasure
        d q boundaryColor hp hp1 : Measure _).real
      (pottsColorEvent d q (origin d) boundaryColor)) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        fkTheta d hp hp1
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
          (q := q) := by
  simpa [wiredPottsClusterSumSpinProbabilityMeasure,
    pottsClusterSumJointProbabilityMeasure,
    pottsClusterFactorInputProbabilityMeasure,
    pottsIIDLabelProbabilityMeasure, pottsClusterSumJointMeasure] using
      (wiredPottsClusterSum_boundaryColorBias_eq_fkTheta
        (d := d) boundaryColor hp hp1)



theorem wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q)
    (hba : boundaryColor ≠ a)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ((wiredPottsClusterSumSpinProbabilityMeasure
        d q boundaryColor hp hp1 : Measure _).real
      (pottsColorEvent d q (origin d) a)) - 1 / (q : Real) =
      -(1 / (q : Real)) *
        fkTheta d hp hp1
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
          (q := q) := by
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  let I : Set (ConfigSpace (Sym2 (Site d))) :=
    {omega | (cluster d omega (origin d)).Infinite}
  have hI : MeasurableSet I := measurableSet_clusterInfinite (origin d)
  have hfinite : edgeMeasure.real
      {omega | (cluster d omega (origin d)).Finite} =
        1 - fkTheta d hp hp1 (zero_lt_one.trans_le hqR) (q := q) := by
    have hset : {omega : ConfigSpace (Sym2 (Site d)) |
        (cluster d omega (origin d)).Finite} = Iᶜ := by
      ext omega
      exact not_infinite.symm
    rw [hset, measureReal_compl hI, probReal_univ]
    rfl
  change (Measure.map Prod.fst
    (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
      (pottsColorEvent d q (origin d) a) - 1 / (q : Real) = _
  rw [pottsClusterSumJointMeasure_otherColor_real
    boundaryColor a hba edgeMeasure (origin d), hfinite]
  ring





theorem exists_ergodic_potts_cluster_phase_candidate_family_with_exact_wired_bias
    (d q : Nat) [NeZero q] (hd : 1 <= d)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig d q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)),
      IsErgodicFor (pottsSpinShift (d := d) (q := q))
          (muFree : Measure _) ∧
      (∀ b, IsErgodicFor (pottsSpinShift (d := d) (q := q))
        (muWired b : Measure _)) ∧
      (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig d q)) :
          Measure (PottsConfig d q)).real
            (pottsColorEvent d q (origin d) b) - 1 / (q : Real) =
          ((q : Real) - 1) / q *
            fkTheta d hp hp1
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
              (q := q)) ∧
      ∀ b a, b ≠ a ->
        ((muWired b : ProbabilityMeasure (PottsConfig d q)) :
          Measure (PottsConfig d q)).real
            (pottsColorEvent d q (origin d) a) - 1 / (q : Real) =
          -(1 / (q : Real)) *
            fkTheta d hp hp1
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
              (q := q) := by
  let boundaryColor : Fin q := ⟨0, Nat.pos_of_neZero q⟩
  let muFree := freePottsClusterSumSpinProbabilityMeasure
    d q boundaryColor hp hp1
  let muWired : Fin q -> ProbabilityMeasure (PottsConfig d q) := fun b =>
    wiredPottsClusterSumSpinProbabilityMeasure d q b hp hp1
  refine ⟨muFree, muWired,
    freePottsClusterSumSpinProbabilityMeasure_isErgodicFor
      hd boundaryColor hp hp1,
    fun b => wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor
      hd b hp hp1, fun b => ?_, fun b a hba => ?_⟩
  · exact wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta b hp hp1
  · exact wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta b a hba hp hp1




theorem exists_ergodic_critical_potts_cluster_phase_candidate_family_with_exact_wired_bias
    (q : Nat) [NeZero q] (hq : 4 < q) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)),
      IsErgodicFor (pottsSpinShift (d := 2) (q := q))
          (muFree : Measure _) ∧
      (∀ b, IsErgodicFor (pottsSpinShift (d := 2) (q := q))
        (muWired b : Measure _)) ∧
      (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) :
          Measure (PottsConfig 2 q)).real
            (pottsColorEvent 2 q (origin 2) b) - 1 / (q : Real) =
          ((q : Real) - 1) / q *
            fkTheta 2
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q)) ∧
      ∀ b a, b ≠ a ->
        ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) :
          Measure (PottsConfig 2 q)).real
            (pottsColorEvent 2 q (origin 2) a) - 1 / (q : Real) =
          -(1 / (q : Real)) *
            fkTheta 2
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q) := by
  exact
    exists_ergodic_potts_cluster_phase_candidate_family_with_exact_wired_bias
      2 q (by norm_num)
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2




theorem exists_pairwise_distinct_ergodic_potts_cluster_phase_family
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (hfree : ((freeInfiniteVolume d hp hp1
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
          {omega | (cluster d omega (origin d)).Infinite} = 0)
    (hwired : 0 < fkTheta d hp hp1
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
      (q := q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig d q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)),
      IsErgodicFor (pottsSpinShift (d := d) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := d) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  let boundaryColor : Fin q := ⟨0, by omega⟩
  let muFree := freePottsClusterSumSpinProbabilityMeasure
    d q boundaryColor hp hp1
  let muWired : Fin q -> ProbabilityMeasure (PottsConfig d q) := fun b =>
    wiredPottsClusterSumSpinProbabilityMeasure d q b hp hp1
  have hcoef : 0 < ((q : Real) - 1) / q := by
    have hqR : (1 : Real) < q := by exact_mod_cast hq
    positivity
  refine ⟨muFree, muWired,
    freePottsClusterSumSpinProbabilityMeasure_isErgodicFor
      hd boundaryColor hp hp1,
    fun b => wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor
      hd b hp hp1, ?_, ?_⟩
  · intro b heq
    have hfreeColor := freePottsClusterSumSpin_colorProbability_eq_inv
      boundaryColor b hp hp1 hfree
    have hwiredColor := wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta
      (d := d) b hp hp1
    have hmass := congrArg (fun rho : ProbabilityMeasure (PottsConfig d q) =>
      (rho : Measure _).real (pottsColorEvent d q (origin d) b)) heq
    change (muFree : Measure _).real
      (pottsColorEvent d q (origin d) b) =
        (muWired b : Measure _).real
          (pottsColorEvent d q (origin d) b) at hmass
    dsimp only [muFree, muWired] at hmass
    rw [hfreeColor] at hmass
    linarith [mul_pos hcoef hwired]
  · intro b c hbc heq
    have hb := wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta
      (d := d) b hp hp1
    have hc := wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta
      (d := d) c b (Ne.symm hbc) hp hp1
    have hmass := congrArg (fun rho : ProbabilityMeasure (PottsConfig d q) =>
      (rho : Measure _).real (pottsColorEvent d q (origin d) b)) heq
    change (muWired b : Measure _).real
      (pottsColorEvent d q (origin d) b) =
        (muWired c : Measure _).real
          (pottsColorEvent d q (origin d) b) at hmass
    dsimp only [muWired] at hmass
    linarith [mul_pos hcoef hwired,
      mul_pos (by positivity : 0 < (1 / (q : Real))) hwired]



theorem exists_pairwise_distinct_ergodic_potts_cluster_phase_family_of_firstOrder
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (hfirst : IsFirstOrderTransition d hp hp1
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig d q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)),
      IsErgodicFor (pottsSpinShift (d := d) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := d) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  apply exists_pairwise_distinct_ergodic_potts_cluster_phase_family
    d q hd hq hp hp1
  · simpa [fkThetaFree] using hfirst.1
  · exact hfirst.2



theorem exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family
    (q : Nat) [NeZero q] (hq : 4 < q)
    (hfirst : IsFirstOrderTransition 2
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)),
      IsErgodicFor (pottsSpinShift (d := 2) (q := q))
          (muFree : Measure _) ∧
      (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q))
        (muWired b : Measure _)) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  exact exists_pairwise_distinct_ergodic_potts_cluster_phase_family_of_firstOrder
    2 q (by norm_num) (by omega)
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
      hfirst

end

end StatMech.FK
