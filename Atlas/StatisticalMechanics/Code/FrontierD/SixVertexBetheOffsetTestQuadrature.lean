/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature








namespace StatMech.FrontierD

open Finset
open Filter Topology

noncomputable section

def sixVertexFixedChargeOffsetTestError
    (c : Real) (N r : Nat) (lower G : Real) (D : NNReal) : Real :=
  (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * G / lower)

theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz
    {c : Real} (hc : 2 < c) {N m r : Nat} (hN : 0 < N) (hm : 0 < m)
    (hcharge : N = 2 * m + 2 * r) {p : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N m p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N m p y)
    (x : Real) {tau : Real → Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauPeriodic : Function.Periodic tau (2 * Real.pi))
    (htauBound : ∀ y, |tau y| ≤ G) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) /
          sixVertexFiniteRootDensity c N m p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y| ≤
      sixVertexFixedChargeOffsetTestError c N r lower G D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz
      hc hN hcharge hopen hsol hlower hdensity x
      htauLip htauPeriodic htauBound
  simpa [sixVertexFixedChargeOffsetTestError] using h

theorem tendsto_sixVertexFixedChargeOffsetTestError
    (c : Real) (r : Nat) {lower : Real} (hlower : 0 < lower)
    (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexFixedChargeOffsetTestError c
      (sixVertexFourWidth r k) r lower G D) atTop (nhds 0) := by
  let C := (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) *
        sixVertexFiniteRootDensityUniformBound c *
        ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
      2 * (r : Real) *
        ((sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) * G / lower)
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  convert hzero using 1
  funext k
  dsimp [C]
  unfold sixVertexFixedChargeOffsetTestError
  field_simp [hlower.ne']

end

end StatMech.FrontierD
