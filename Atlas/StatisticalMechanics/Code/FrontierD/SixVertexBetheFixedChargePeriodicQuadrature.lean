/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFixedChargeStability
import Code.FrontierD.SixVertexBetheTailConvolution









open scoped BigOperators
open Filter Finset

namespace StatMech.FrontierD



theorem abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x,
      lower <= sixVertexFiniteRootDensity c N (n + 1) p x)
    {f : Real -> Real} {C : NNReal} {F : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi))
    (hfBound : forall x, |f x| <= F) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N (n + 1) p y| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) * F := by
  have hmesh := sixVertexCyclicRootPartition_mesh_fixedCharge
    hc hN hcharge hopen hsol hlower hdensity
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge
      hc hN hcharge hopen hsol hmesh hf hlip hfBound
  have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p hperiodic
  have hsumScaled :
      ∑ k ∈ range (n + 1),
          (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) =
        (∑ j, f (p j)) / N := by
    rw [← Finset.mul_sum, hsum]
    ring
  have hint := intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle
    (N := N) c p hperiodic
  rw [hsumScaled, hint] at hquad
  exact hquad

end StatMech.FrontierD
