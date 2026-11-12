/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalUnequalBridgeGeometry










open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section




theorem unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hmean : forall t, 0 <= t -> t <= r ->
      unequalReplicaBridgeMean G H K J hf hg t +
          unequalReplicaBridgeMean G H K J hf hg (-t) <=
        2 * unequalReplicaBridgeMean G H K J hf hg 0) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  have hcont : ContinuousOn
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) (Icc 0 r) :=
    hdiffAll.continuous.continuousOn
  have hdiff : DifferentiableOn Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) (Ioo 0 r) :=
    hdiffAll.differentiableOn
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos hcont hdiff
  have hderiv : deriv
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) c <=
        2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    rw [(hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg c).deriv]
    exact hmean c hc.1.le hc.2.le
  have hzero : unequalReplicaBridgeFreeEnergy G H K J hf hg 0 = 0 := by
    simp [unequalReplicaBridgeFreeEnergy]
  have hmul := mul_le_mul_of_nonneg_right hderiv hrpos.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hrpos.ne'] at hmul
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul




def OddPrismUnequalBridgeSymmetricMeanOrder
    (beta : Real) (n : Nat) : Prop :=
  forall t, 0 <= t -> t <= beta ->
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t +
      unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) (-t) <=
      2 * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0



theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder
    {beta : Real} {n : Nat}
    (hvar : OddPrismUnequalBridgeVarianceOrder beta n) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t +
      unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) (-t)
  have hdiff : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta _ _ t).differentiableAt
  have hanti : AntitoneOn D (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real))
    · exact hdiff.continuous.continuousOn
    · intro t _
      exact hdiff t |>.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta _ _ t).deriv]
      exact sub_nonpos.mpr (hvar t ht.le)
  intro t ht _
  have hle := hanti (by simp) ht ht
  dsimp only [D] at hle
  rw [neg_zero] at hle
  linarith



theorem oddPrismUnequalBridgeFreeEnergy_le_of_symmetricMeanOrder
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (hmean : OddPrismUnequalBridgeSymmetricMeanOrder beta n) :
    oddPrismUnequalBridgeFreeEnergy beta n <=
      2 * beta * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) beta hbeta hmean



theorem standardCubicInterfaceDensity_critical_le_unequalMeanDensity_of_symmetricMeanOrder
    (n : Nat) (hn : 0 < n)
    (hmean : OddPrismUnequalBridgeSymmetricMeanOrder
      (Ising.betaC 3) n) :
    standardCubicInterfaceDensity (Ising.betaC 3) n <=
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n := by
  rw [standardCubicInterfaceDensity_eq_oddPrismUnequalBridge
    (Ising.betaC 3) n hn]
  unfold oddPrismCriticalUnequalBridgeMeanDensity
  calc
    oddPrismUnequalBridgeFreeEnergy (Ising.betaC 3) n /
        (((2 * n + 1 : Nat) : Real) ^ 2) <=
      (2 * Ising.betaC 3 * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0) /
          (((2 * n + 1 : Nat) : Real) ^ 2) :=
      div_le_div_of_nonneg_right
        (oddPrismUnequalBridgeFreeEnergy_le_of_symmetricMeanOrder
          (Ising.betaC 3) isingBetaC_three_pos.le n hmean) (sq_nonneg _)
    _ = 2 * Ising.betaC 3 *
        (unequalReplicaBridgeMean
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0 /
            (((2 * n + 1 : Nat) : Real) ^ 2)) := by ring



theorem standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder
    (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder
      (Ising.betaC 3) n) :
    Tendsto (standardCubicInterfaceDensity (Ising.betaC 3))
      atTop (nhds 0) := by
  have hu : Tendsto (fun n =>
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact standardCubicInterfaceDensity_nonneg
      isingBetaC_three_pos.le n (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact
      standardCubicInterfaceDensity_critical_le_unequalMeanDensity_of_symmetricMeanOrder
        n (by omega) (hmean n)
  · exact hu



theorem rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder
    (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
    (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder
      (Ising.betaC 3) n) :
    rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
  apply tendsto_nhds_unique
    (standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      isingBetaC_three_pos hprism
      (hasStandardPrismSurfaceComparison (Ising.betaC 3)))
  exact standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder
    hmean

end

end StatMech.FrontierA
