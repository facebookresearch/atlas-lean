/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsInfiniteVolumePhaseTransport









open Filter MeasureTheory Topology

namespace StatMech.FK

noncomputable section



def pottsSelfDualInverseTemperature (q : Nat) (J : Real) : Real :=
  Real.log (1 + Real.sqrt q) / J

theorem pottsSelfDualInverseTemperature_pos
    {q : Nat} (hq : 0 < q) {J : Real} (hJ : 0 < J) :
    0 < pottsSelfDualInverseTemperature q J := by
  unfold pottsSelfDualInverseTemperature
  apply div_pos _ hJ
  have hsqrt : 0 < Real.sqrt (q : Real) := Real.sqrt_pos.2 (by exact_mod_cast hq)
  exact Real.log_pos (by linarith)



theorem one_sub_exp_neg_pottsSelfDualInverseTemperature_mul
    {q : Nat} (hq : 0 < q) {J : Real} (hJ : 0 < J) :
    1 - Real.exp (-(pottsSelfDualInverseTemperature q J * J)) =
      BeffaraDC.selfDualPoint q := by
  have hJ0 : J ≠ 0 := hJ.ne'
  have hbase : 0 < 1 + Real.sqrt (q : Real) := by positivity
  rw [pottsSelfDualInverseTemperature, div_mul_cancel₀ _ hJ0,
    Real.exp_neg, Real.exp_log hbase]
  rw [BeffaraDC.selfDualPoint]
  field_simp
  ring






theorem exists_potts_phase_candidate_family_with_exact_oneSite_bias
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig d q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      StrictMono phiFree ∧
      Tendsto (fun n => freePottsFiniteMeasure d (phiFree n) q beta J)
          atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure d (phiWired b n) q b beta J)
          atTop (nhds (muWired b))) ∧
      (∀ b, (muFree : Measure (PottsConfig d q)).real
          (pottsColorEvent d q (StatMech.Percolation.origin d) b) = 1 / (q : Real)) ∧
      (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig d q)) :
          Measure (PottsConfig d q)).real
            (pottsColorEvent d q (StatMech.Percolation.origin d) b) - 1 / (q : Real) =
          ((q : Real) - 1) / q *
            fkTheta d
              (by
                apply sub_pos.mpr
                rw [Real.exp_lt_one_iff]
                exact neg_neg_of_pos (mul_pos hbeta hJ))
              (by linarith [Real.exp_pos (-(beta * J))])
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q)) ∧
      ∀ b a, a ≠ b ->
        ((muWired b : ProbabilityMeasure (PottsConfig d q)) :
          Measure (PottsConfig d q)).real
            (pottsColorEvent d q (StatMech.Percolation.origin d) a) - 1 / (q : Real) =
          -(1 / (q : Real)) *
            fkTheta d
              (by
                apply sub_pos.mpr
                rw [Real.exp_lt_one_iff]
                exact neg_neg_of_pos (mul_pos hbeta hJ))
              (by linarith [Real.exp_pos (-(beta * J))])
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q) := by
  obtain ⟨_XiFree, muFree, phiFree, hphiFree, _hjointFree,
      hmuFree, _hfstFree, _hsndFree⟩ :=
    freePottsInfiniteVolume_exists d q hq beta J hbeta hJ
  have hwired (b : Fin q) :
      ∃ (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat),
        StrictMono phi ∧
        Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
          atTop (nhds mu) := by
    obtain ⟨_Xi, mu, phi, hphi, _hjoint, hmu, _hfst, _hsnd, _hbias⟩ :=
      wiredPottsOrderedInfiniteVolume_exists
        d q hd hq b beta J hbeta hJ
    exact ⟨mu, phi, hphi, hmu⟩
  choose muWired phiWired hwiredSpec using hwired
  refine ⟨muFree, muWired, phiFree, phiWired, hphiFree, hmuFree,
    hwiredSpec, fun b => ?_, fun b => ?_, fun b a ha => ?_⟩
  · exact freePottsLimit_colorProbability_eq_inv
      d q b beta J muFree phiFree hmuFree
  · exact wiredPottsLimit_colorBias_eq_fkTheta
      d q hd hq b beta J hbeta hJ (muWired b) (phiWired b)
        (hwiredSpec b).1 (hwiredSpec b).2
  · exact wiredPottsLimit_otherColorBias_eq_fkTheta
      d q hd hq b a ha beta J hbeta hJ (muWired b) (phiWired b)
        (hwiredSpec b).1 (hwiredSpec b).2




theorem exists_critical_potts_phase_candidate_family_with_exact_oneSite_bias
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      StrictMono phiFree ∧
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (∀ b, (muFree : Measure (PottsConfig 2 q)).real
          (pottsColorEvent 2 q (StatMech.Percolation.origin 2) b) =
            1 / (q : Real)) ∧
      (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) :
          Measure (PottsConfig 2 q)).real
            (pottsColorEvent 2 q (StatMech.Percolation.origin 2) b) -
              1 / (q : Real) =
          ((q : Real) - 1) / q *
            fkTheta 2
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q)) ∧
      ∀ b a, a ≠ b ->
        ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) :
          Measure (PottsConfig 2 q)).real
            (pottsColorEvent 2 q (StatMech.Percolation.origin 2) a) -
              1 / (q : Real) =
          -(1 / (q : Real)) *
            fkTheta 2
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
              (BeffaraDC.selfDualPoint_mem_Ioo
                (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
              (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
              (q := q) := by
  have hq0 : 0 < q := by omega
  have hbeta := pottsSelfDualInverseTemperature_pos hq0 hJ
  have hdata := exists_potts_phase_candidate_family_with_exact_oneSite_bias
    2 q (by norm_num) (by omega) (pottsSelfDualInverseTemperature q J) J
      hbeta hJ
  simpa only [one_sub_exp_neg_pottsSelfDualInverseTemperature_mul hq0 hJ]
    using hdata




theorem exists_pairwise_distinct_potts_phase_family_of_fkTheta_pos
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (htheta : 0 < fkTheta d
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        exact neg_neg_of_pos (mul_pos hbeta hJ))
      (by linarith [Real.exp_pos (-(beta * J))])
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
      (q := q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig d q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      Tendsto (fun n => freePottsFiniteMeasure d (phiFree n) q beta J)
          atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure d (phiWired b n) q b beta J)
          atTop (nhds (muWired b))) ∧
      (∀ b, muFree ≠ muWired b) ∧
      ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
  obtain ⟨muFree, muWired, phiFree, phiWired, _hphiFree, hmuFree,
      hwiredSpec, _hfreeBias, _hownBias, _hotherBias⟩ :=
    exists_potts_phase_candidate_family_with_exact_oneSite_bias
      d q hd hq beta J hbeta hJ
  refine ⟨muFree, muWired, phiFree, phiWired, hmuFree, hwiredSpec,
    fun b => ?_, fun b c hbc => ?_⟩
  · exact freePottsLimit_ne_wiredPottsLimit_of_fkTheta_pos
      d q hd hq b beta J hbeta hJ muFree (muWired b)
      phiFree (phiWired b) (hwiredSpec b).1 hmuFree
      (hwiredSpec b).2 htheta
  · exact wiredPottsLimits_ne_of_boundary_ne_of_fkTheta_pos
      d q hd hq b c hbc beta J hbeta hJ (muWired b) (muWired c)
      (phiWired b) (phiWired c) (hwiredSpec b).1 (hwiredSpec c).1
      (hwiredSpec b).2 (hwiredSpec c).2 htheta



theorem exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    (htheta : 0 < fkTheta 2
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
      (q := q)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (∀ b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (∀ b, muFree ≠ muWired b) ∧
      ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
  have hq0 : 0 < q := by omega
  have hbeta := pottsSelfDualInverseTemperature_pos hq0 hJ
  apply exists_pairwise_distinct_potts_phase_family_of_fkTheta_pos
    2 q (by norm_num) (by omega) (pottsSelfDualInverseTemperature q J) J
    hbeta hJ
  simpa [one_sub_exp_neg_pottsSelfDualInverseTemperature_mul hq0 hJ] using htheta

end

end StatMech.FK
