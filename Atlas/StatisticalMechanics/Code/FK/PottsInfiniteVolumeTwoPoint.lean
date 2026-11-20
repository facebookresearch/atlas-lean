/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsInfiniteVolumePhaseTransport
import Code.FK.EdwardsSokalFull
import Code.FrontierB.FreeInfiniteMultipointES











open MeasureTheory Filter Topology

namespace StatMech.FK

open Lattice Percolation

noncomputable section


def pottsAgreementEvent (d q : Nat) (x y : Site d) :
    Set (PottsConfig d q) :=
  {sigma | sigma x = sigma y}

theorem pottsAgreementEvent_isClopen (d q : Nat) (x y : Site d) :
    IsClopen (pottsAgreementEvent d q x y) := by
  change IsClopen ((fun sigma : PottsConfig d q => (sigma x, sigma y)) ⁻¹'
    {z : Fin q × Fin q | z.1 = z.2})
  exact IsClopen.preimage (isClopen_discrete _)
    ((continuous_apply x).prodMk (continuous_apply y))



theorem freePottsFiniteMeasure_real_pottsAgreementEvent
    (d n q : Nat) [NeZero q] (beta J : Real)
    (x y : Site d) (hx : x ∈ box d n) (hy : y ∈ box d n) :
    ((freePottsFiniteMeasure d n q beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real (pottsAgreementEvent d q x y) =
      pottsAgreeProb (boxGraph d n) q beta J
        (⟨x, hx⟩ : boxVerts d n) (⟨y, hy⟩ : boxVerts d n) := by
  classical
  let xb : boxVerts d n := ⟨x, hx⟩
  let yb : boxVerts d n := ⟨y, hy⟩
  let E : Set (boxVerts d n -> Fin q) := {sigma | sigma xb = sigma yb}
  have hpre : ivp_extendSpin d n q ⁻¹' pottsAgreementEvent d q x y = E := by
    ext sigma
    simp only [Set.mem_preimage, pottsAgreementEvent, Set.mem_setOf_eq, E]
    unfold ivp_extendSpin
    rw [dif_pos hx, dif_pos hy]
  have hmeas : MeasurableSet (pottsAgreementEvent d q x y) :=
    (pottsAgreementEvent_isClopen d q x y).2.measurableSet
  change ((Measure.map (ivp_extendSpin d n q)
    (Potts.pottsPMF (boxGraph d n) q beta J).toMeasure)
      (pottsAgreementEvent d q x y)).toReal = _
  rw [Measure.map_apply (ivp_measurable_extendSpin d n q) hmeas, hpre]
  unfold pottsAgreeProb
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun sigma _ => ?_)]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : sigma xb = sigma yb
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, Potts.pottsPMF_apply,
        ENNReal.toReal_ofReal (Potts.pottsProb_nonneg
          (boxGraph d n) q beta J sigma)]
      simp [hsigma, xb, yb]
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp [hsigma, xb, yb]
  · by_cases hsigma : sigma xb = sigma yb
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, Potts.pottsPMF_apply]
      exact ENNReal.ofReal_ne_top
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp



theorem freeFiniteMeasure_real_connectedEvent
    (d n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : Site d) (hx : x ∈ box d n) (hy : y ∈ box d n) :
    (freeFiniteMeasure d n hp hp1 hq :
      Measure (ConfigSpace (Sym2 (Site d)))).real
        {omega | Lattice.Connected d omega x y} =
      connProb (boxGraph d n) p q
        (⟨x, hx⟩ : boxVerts d n) (⟨y, hy⟩ : boxVerts d n) := by
  let xb : boxVerts d n := ⟨x, hx⟩
  let yb : boxVerts d n := ⟨y, hy⟩
  have hpre : extendEdge d n ⁻¹'
      {omega | Lattice.Connected d omega x y} =
      connEvent (boxGraph d n) xb yb := by
    ext omega
    exact StatMech.FrontierB.openSub_extendEdge_reachable_iff
      n omega xb yb |>.symm
  have hmeas : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        Lattice.Connected d omega x y} :=
    measurableSet_connected x y
  change ((Measure.map (extendEdge d n)
    (fkPMF (boxGraph d n) hp hp1 hq).toMeasure)
      {omega | Lattice.Connected d omega x y}).toReal = _
  rw [Measure.map_apply (measurable_extendEdge d n) hmeas, hpre,
    fkPMF_toMeasure_toReal]
  unfold connProb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hconn : Connected (boxGraph d n) omega
      (⟨x, hx⟩ : boxVerts d n) (⟨y, hy⟩ : boxVerts d n)
  · have hmem : omega ∈ connEvent (boxGraph d n) xb yb := by
      simpa [connEvent, xb, yb] using hconn
    rw [Set.indicator_of_mem hmem]
    simp [hconn]
  · have hmem : omega ∉ connEvent (boxGraph d n) xb yb := by
      simpa [connEvent, xb, yb] using hconn
    rw [Set.indicator_of_notMem hmem]
    simp [hconn]



theorem measure_frontier_connectedEvent_eq_zero
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (x y : Site d) :
    (mu : Measure _) (frontier
      {omega : ConfigSpace (Sym2 (Site d)) |
        Lattice.Connected d omega x y}) = 0 := by
  apply measure_mono_null
    (StatMech.FrontierB.frontier_connectedEvent_subset_distinctInfiniteClusterEvent
      x y |>.trans
      (StatMech.FrontierB.distinctInfiniteClusterEvent_subset_atLeastTwoInfinite
        x y))
  exact hunique




theorem freePottsJointLimit_agreement_eq_fkTwoPoint
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat)
    (hphi : StrictMono phi)
    (hjoint : Tendsto
      (fun n => freePottsJointFiniteMeasure d (phi n) q beta J
        (by
          apply sub_pos.mpr
          rw [Real.exp_lt_one_iff]
          exact neg_neg_of_pos (mul_pos hbeta hJ))
        (by linarith [Real.exp_pos (-(beta * J))]))
      atTop (nhds Xi))
    (hmu : Xi.map continuous_fst.measurable.aemeasurable = mu)
    (hfk : Xi.map continuous_snd.measurable.aemeasurable =
      freeInfiniteVolume d
        (by
          apply sub_pos.mpr
          rw [Real.exp_lt_one_iff]
          exact neg_neg_of_pos (mul_pos hbeta hJ))
        (by linarith [Real.exp_pos (-(beta * J))])
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
    forall x y : Site d,
      ((mu : Measure (PottsConfig d q)).real
          (pottsAgreementEvent d q x y)) - 1 / (q : Real) =
        ((q : Real) - 1) / q *
          infiniteTwoPointReal
            (freeInfiniteVolume d
              (by
                apply sub_pos.mpr
                rw [Real.exp_lt_one_iff]
                exact neg_neg_of_pos (mul_pos hbeta hJ))
              (by linarith [Real.exp_pos (-(beta * J))])
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
                Measure (ConfigSpace (Sym2 (Site d)))) x y := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hq0 : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : Real) <= q := by exact_mod_cast (show 1 <= q by omega)
  have hspin0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi (by simpa [p] using hjoint) continuous_fst
  have hspin : Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
      atTop (nhds mu) := by
    rw [<- hmu]
    simpa only [freePottsJointFiniteMeasure_map_fst] using hspin0
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi (by simpa [p] using hjoint) continuous_snd
  have hedge : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hq0)
      atTop (nhds (freeInfiniteVolume d hp hp1 hq0)) := by
    rw [<- hfk]
    simpa only [freePottsJointFiniteMeasure_map_snd] using hedge0
  have hunique :
      (freeInfiniteVolume d hp hp1 hq0 : Measure _)
        (atLeastTwoInfinite d) = 0 :=
    (freeInfinite_canonical_uniqueness_all_parameters hd hp hp1 hq1).2.1
  intro x y
  obtain ⟨N, hxyN⟩ := Lattice.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite {x, y})
  have hxN : x ∈ box d N := hxyN (by simp)
  have hyN : y ∈ box d N := hxyN (by simp)
  have hspinMass :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hspin
      (pottsAgreementEvent_isClopen d q x y)
  have hspinReal : Tendsto
      (fun n => ((freePottsFiniteMeasure d (phi n) q beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real
          (pottsAgreementEvent d q x y)) atTop
      (nhds ((mu : Measure _).real (pottsAgreementEvent d q x y))) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hspinMass
  have hedgeWeak : WeakConvergesTo
      (fun n => freeFiniteMeasure d (phi n) hp hp1 hq0)
      (freeInfiniteVolume d hp hp1 hq0) := hedge
  have hedgeReal : Tendsto
      (fun n => (freeFiniteMeasure d (phi n) hp hp1 hq0 : Measure _).real
        {omega | Lattice.Connected d omega x y}) atTop
      (nhds ((freeInfiniteVolume d hp hp1 hq0 : Measure _).real
        {omega | Lattice.Connected d omega x y})) := by
    apply StatMech.FrontierB.WeakConvergesTo.tendsto_real_of_null_frontier
      hedgeWeak
    exact measure_frontier_connectedEvent_eq_zero
      (freeInfiniteVolume d hp hp1 hq0) hunique x y
  have hfinite : forall k, N <= phi k ->
      ((freePottsFiniteMeasure d (phi k) q beta J :
          ProbabilityMeasure (PottsConfig d q)) : Measure _).real
            (pottsAgreementEvent d q x y) - 1 / (q : Real) =
        ((q : Real) - 1) / q *
          (freeFiniteMeasure d (phi k) hp hp1 hq0 : Measure _).real
            {omega | Lattice.Connected d omega x y} := by
    intro k hk
    have hxk : x ∈ box d (phi k) := box_mono d hk hxN
    have hyk : y ∈ box d (phi k) := box_mono d hk hyN
    rw [freePottsFiniteMeasure_real_pottsAgreementEvent
      d (phi k) q beta J x y hxk hyk,
      freeFiniteMeasure_real_connectedEvent
        d (phi k) hp hp1 hq0 x y hxk hyk]
    exact edwards_sokal_correlation'
      (boxGraph d (phi k)) q beta J
        (⟨x, hxk⟩ : boxVerts d (phi k))
        (⟨y, hyk⟩ : boxVerts d (phi k))
        (by simpa [p] using hp) (by simpa [p] using hp1) hq0
  have heq :
      (fun k => ((freePottsFiniteMeasure d (phi k) q beta J :
          ProbabilityMeasure (PottsConfig d q)) : Measure _).real
            (pottsAgreementEvent d q x y) - 1 / (q : Real)) =ᶠ[atTop]
        (fun k => ((q : Real) - 1) / q *
          (freeFiniteMeasure d (phi k) hp hp1 hq0 : Measure _).real
            {omega | Lattice.Connected d omega x y}) := by
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)]
      with k hk
    exact hfinite k hk
  have hconst : Tendsto (fun _ : Nat => 1 / (q : Real)) atTop
      (nhds (1 / (q : Real))) := tendsto_const_nhds
  have hcoef : Tendsto (fun _ : Nat => ((q : Real) - 1) / q) atTop
      (nhds (((q : Real) - 1) / q)) := tendsto_const_nhds
  have hleft := hspinReal.sub hconst
  have hright := hcoef.mul hedgeReal
  have hlimit := tendsto_nhds_unique hleft (hright.congr' heq.symm)
  simpa only [infiniteTwoPointReal] using hlimit



theorem freePottsInfiniteVolume_twoPoint_exists
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ mu : ProbabilityMeasure (PottsConfig d q),
      forall x y : Site d,
        ((mu : Measure (PottsConfig d q)).real
            (pottsAgreementEvent d q x y)) - 1 / (q : Real) =
          ((q : Real) - 1) / q *
            infiniteTwoPointReal
              (freeInfiniteVolume d
                (by
                  apply sub_pos.mpr
                  rw [Real.exp_lt_one_iff]
                  exact neg_neg_of_pos (mul_pos hbeta hJ))
                (by linarith [Real.exp_pos (-(beta * J))])
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
                  Measure (ConfigSpace (Sym2 (Site d)))) x y := by
  rcases freePottsInfiniteVolume_exists d q hq beta J hbeta hJ with
    ⟨Xi, mu, phi, hphi, hjoint, _, hmu, hfk⟩
  refine ⟨mu, ?_⟩
  exact freePottsJointLimit_agreement_eq_fkTwoPoint
    d q hd hq beta J hbeta hJ Xi mu phi hphi hjoint hmu hfk

end

end StatMech.FK
