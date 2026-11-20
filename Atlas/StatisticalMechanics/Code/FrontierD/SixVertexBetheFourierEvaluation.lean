/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheBulkReduction
import Code.FrontierD.SixVertexFreeEnergyReduction


















open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexFreeEnergyKernelFourierCoeff (lam : Real) : Nat -> Real
  | 0 => lam
  | m + 1 =>
      (1 - Real.exp (-2 * (m + 1 : Real) * lam)) / (2 * (m + 1 : Real))



def sixVertexRootDensityFourierCoeff (lam : Real) : Nat -> Real
  | 0 => 1 / 2
  | m + 1 => 1 / (2 * Real.cosh ((m + 1 : Real) * lam))


def sixVertexFreeEnergyPairedFourierTerm (lam : Real) (n : Nat) : Real :=
  2 * sixVertexFreeEnergyKernelFourierCoeff lam (n + 1) *
    sixVertexRootDensityFourierCoeff lam (n + 1)



theorem sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm
    (lam : Real) (n : Nat) :
    sixVertexFreeEnergyPairedFourierTerm lam n =
      sixVertexFreeEnergySeriesTerm lam n := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hexp : Real.exp (m * lam) ≠ 0 := Real.exp_ne_zero _
  unfold sixVertexFreeEnergyPairedFourierTerm
    sixVertexFreeEnergyKernelFourierCoeff
    sixVertexRootDensityFourierCoeff
    sixVertexFreeEnergySeriesTerm
  change 2 * ((1 - Real.exp (-2 * m * lam)) / (2 * m)) *
      (1 / (2 * Real.cosh (m * lam))) =
    Real.exp (-(m * lam)) * Real.tanh (m * lam) / m
  rw [Real.cosh_eq, Real.tanh_eq]
  rw [show Real.exp (-2 * m * lam) =
      Real.exp (-(m * lam)) * Real.exp (-(m * lam)) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp (-(m * lam)) = (Real.exp (m * lam))⁻¹ by
    rw [← Real.exp_neg]]
  field_simp [hm, hexp]


def sixVertexFreeEnergyFourierPartialSum (lam : Real) (N : Nat) : Real :=
  sixVertexFreeEnergyKernelFourierCoeff lam 0 *
      sixVertexRootDensityFourierCoeff lam 0 +
    ∑ n ∈ range N, sixVertexFreeEnergyPairedFourierTerm lam n

theorem sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum
    (lam : Real) (N : Nat) :
    sixVertexFreeEnergyFourierPartialSum lam N =
      lam / 2 + ∑ n ∈ range N, sixVertexFreeEnergySeriesTerm lam n := by
  unfold sixVertexFreeEnergyFourierPartialSum
  simp only [sixVertexFreeEnergyKernelFourierCoeff,
    sixVertexRootDensityFourierCoeff]
  rw [Finset.sum_congr rfl (fun n _ =>
    sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm lam n)]
  ring



theorem sixVertexFreeEnergyFourierPartialSum_tendsto
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexFreeEnergyFourierPartialSum lam) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  have hsum := (summable_sixVertexFreeEnergySeriesTerm hlam).hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : Nat => lam / 2) atTop (nhds (lam / 2)) :=
    tendsto_const_nhds
  have hadd := hconst.add hsum
  apply hadd.congr'
  filter_upwards [] with N
  exact (sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum lam N).symm




def sixVertexOffsetFourierPartialSum (lam : Real) (N : Nat) : Real :=
  lam - ∑ n ∈ range N,
      (-1 : Real) ^ (n + 1) *
        (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) -
    ∑ n ∈ range N,
      (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
        (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)

private theorem one_add_tanh_mul_exp_neg_two_sub_one (x : Real) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) =
      -2 * Real.tanh x := by
  let a := Real.exp x
  let b := Real.exp (-x)
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [← Real.exp_add]
    simp
  have hab' : b * a = 1 := by rw [mul_comm, hab]
  have hsum : a + b ≠ 0 := by
    dsimp [a, b]
    positivity
  rw [Real.tanh_eq]
  rw [show Real.exp (-2 * x) = b * b by
    dsimp [b]
    rw [← Real.exp_add]
    congr 1
    ring]
  change (1 + (a - b) / (a + b)) * (b * b - 1) =
    -2 * ((a - b) / (a + b))
  field_simp [hsum]
  have habb : a * b ^ 2 = b := by
    rw [pow_two, ← mul_assoc, hab, one_mul]
  nlinarith [habb]



theorem sixVertexOffsetFourierPartialSum_eq_gapPartialSum
    (lam : Real) (N : Nat) :
    sixVertexOffsetFourierPartialSum lam N =
      lam + 2 * ∑ n ∈ range N, sixVertexGapSeriesTerm lam n := by
  unfold sixVertexOffsetFourierPartialSum
  let f : Nat → Real := fun n =>
    (-1 : Real) ^ (n + 1) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)
  let g : Nat → Real := fun n =>
    (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)
  change lam - (∑ n ∈ range N, f n) - (∑ n ∈ range N, g n) = _
  have hcombine :
      lam - (∑ n ∈ range N, f n) - (∑ n ∈ range N, g n) =
        lam + ∑ n ∈ range N, (-f n - g n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [hcombine, Finset.mul_sum]
  apply congrArg (fun t : Real => lam + t)
  apply Finset.sum_congr rfl
  intro n hn
  let x : Real := (n + 1 : Real) * lam
  let a : Real := (-1 : Real) ^ (n + 1) / (n + 1 : Real)
  have hcore := one_add_tanh_mul_exp_neg_two_sub_one x
  dsimp [f, g]
  have hf :
      (-1 : Real) ^ (n + 1) *
          (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) =
        a * (Real.exp (-2 * x) - 1) := by
    dsimp [a, x]
    ring
  have hg :
      (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
          (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) =
        a * Real.tanh x * (Real.exp (-2 * x) - 1) := by
    dsimp [a, x]
    ring
  rw [hf, hg]
  have hleft :
      -(a * (Real.exp (-2 * x) - 1)) -
          a * Real.tanh x * (Real.exp (-2 * x) - 1) =
        -a * ((1 + Real.tanh x) * (Real.exp (-2 * x) - 1)) := by
    ring
  rw [hleft, hcore]
  unfold sixVertexGapSeriesTerm
  dsimp [a, x]
  ring




theorem sixVertexOffsetFourierPartialSum_tendsto
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexOffsetFourierPartialSum lam) atTop
      (nhds (sixVertexAntiferroelectricGapRate lam)) := by
  have hsum := sixVertexGapSeries_partialSum_tendsto hlam
  have hconst : Tendsto (fun _ : Nat => lam) atTop (nhds lam) :=
    tendsto_const_nhds
  have hlim := hconst.add (hsum.const_mul 2)
  apply hlim.congr'
  filter_upwards [] with N
  exact (sixVertexOffsetFourierPartialSum_eq_gapPartialSum lam N).symm




def SixVertexSelectedBulkMatchesRootDensityFourier
    {c : Real} (hc : 2 < c) : Prop :=
  Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)



theorem sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier
    {c : Real} (hc : 2 < c) :
    SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔
      SixVertexSelectedBulkMatchesRootDensityFourier hc := by
  let lam := sixVertexAntiferroelectricLambda c
  have hFourier :
      Tendsto (sixVertexFreeEnergyFourierPartialSum lam) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) :=
    sixVertexFreeEnergyFourierPartialSum_tendsto
      (sixVertexAntiferroelectricLambda_pos hc)
  constructor
  · intro hbulk
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k)
      atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) at hbulk
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0)
    simpa [lam] using hbulk.sub hFourier
  · intro hmatch
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0) at hmatch
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k)
      atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)))
    have hadd := hmatch.add hFourier
    convert hadd using 1
    · funext k
      dsimp [lam]
      ring
    · dsimp [lam]
      ring




def SixVertexFixedChargeMatchesOffsetFourier
    (c : Real) (r : Nat) : Prop :=
  Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)



theorem sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) :
    Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : Real) * sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c))) ↔
      SixVertexFixedChargeMatchesOffsetFourier c r := by
  let lam := sixVertexAntiferroelectricLambda c
  let gap := sixVertexAntiferroelectricGapRate lam
  have hOffset :
      Tendsto (fun k => (r : Real) * sixVertexOffsetFourierPartialSum lam k)
        atTop (nhds ((r : Real) * gap)) :=
    (sixVertexOffsetFourierPartialSum_tendsto
      (sixVertexAntiferroelectricLambda_pos hc)).const_mul (r : Real)
  constructor
  · intro hratio
    have hadd := hratio.add hOffset
    change Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0)
    simpa [lam, gap] using hadd
  · intro hmatch
    change Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0) at hmatch
    have hsub := hmatch.sub hOffset
    convert hsub using 1
    · funext k
      dsimp [lam]
      ring
    · dsimp [gap, lam]
      ring


theorem sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : Real) *
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))) ↔
      SixVertexFixedChargeMatchesOffsetFourier c r :=
  (sixVertexFixedChargeRatio_tendsto_iff_logRatio (by linarith) r).trans
    (sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier hc r)




theorem sixVertexAntiferroelectricTransferConclusion_of_rootDensityFourier
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
    (hbulk : SixVertexSelectedBulkMatchesRootDensityFourier hc)
    (hoffset : ∀ r : Nat, 1 ≤ r →
      SixVertexFixedChargeMatchesOffsetFourier c r) :
    SixVertexAntiferroelectricTransferConclusion c
      (sixVertexAntiferroelectricLambda c) := by
  refine ⟨?_, ?_⟩
  · exact sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy
      hc hphase
      ((sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier
        hc).2 hbulk)
  · intro r hr
    exact (sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier hc r).2
      (hoffset r hr)

end

end StatMech.FrontierD
