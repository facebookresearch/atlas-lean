/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCyclicQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic








namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheIntegratingFactor_add_two_pi
    (c x : Real) :
    sixVertexBetheIntegratingFactor c (x + 2 * Real.pi) =
      sixVertexBetheIntegratingFactor c x := by
  unfold sixVertexBetheIntegratingFactor
  rw [Real.cos_add_two_pi]

theorem sixVertexThetaDerivativeDenominator_add_two_pi_left
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c (x + 2 * Real.pi) y =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem sixVertexThetaDerivativeDenominator_add_two_pi_right
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c x (y + 2 * Real.pi) =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem sixVertexRootDensityKernel_add_two_pi_left
    (c x y : Real) :
    sixVertexRootDensityKernel c (x + 2 * Real.pi) y =
      sixVertexRootDensityKernel c x y := by
  unfold sixVertexRootDensityKernel
  rw [sixVertexBetheIntegratingFactor_add_two_pi,
    sixVertexThetaDerivativeDenominator_add_two_pi_left]

theorem sixVertexRootDensityKernel_add_two_pi_right
    (c x y : Real) :
    sixVertexRootDensityKernel c x (y + 2 * Real.pi) =
      sixVertexRootDensityKernel c x y := by
  unfold sixVertexRootDensityKernel
  rw [sixVertexBetheIntegratingFactor_add_two_pi,
    sixVertexThetaDerivativeDenominator_add_two_pi_right]

theorem periodic_sixVertexRootDensityKernel_right (c x : Real) :
    Function.Periodic (sixVertexRootDensityKernel c x) (2 * Real.pi) :=
  fun y => sixVertexRootDensityKernel_add_two_pi_right c x y

theorem sixVertexFiniteRootDensity_add_two_pi
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) :
    sixVertexFiniteRootDensity c N n p (x + 2 * Real.pi) =
      sixVertexFiniteRootDensity c N n p x := by
  unfold sixVertexFiniteRootDensity
  congr 3
  apply Finset.sum_congr rfl
  intro k _
  rw [sixVertexThetaDerivativeDenominator_add_two_pi_left]

theorem periodic_sixVertexFiniteRootDensity
    (c : Real) (N n : Nat) (p : Fin n → Real) :
    Function.Periodic (sixVertexFiniteRootDensity c N n p)
      (2 * Real.pi) :=
  sixVertexFiniteRootDensity_add_two_pi c N n p

def sixVertexRootDensityKernelLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexRootDensityKernelLipschitzBound c)

theorem lipschitzWith_sixVertexRootDensityKernel_right
    {c : Real} (hc : 2 < c) (x : Real) :
    LipschitzWith (sixVertexRootDensityKernelLipschitzNNReal c)
      (sixVertexRootDensityKernel c x) := by
  have hbound : 0 <= sixVertexRootDensityKernelLipschitzBound c :=
    (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  have hcoe : (sixVertexRootDensityKernelLipschitzNNReal c : Real) =
      sixVertexRootDensityKernelLipschitzBound c := by
    exact Real.coe_toNNReal _ hbound
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  exact sixVertexRootDensityKernel_lipschitz_right hc x y z

theorem sum_cyclicRootPartition_eq_sum_roots_of_periodic
    {n : Nat} (p : Fin (n + 1) → Real) {f : Real → Real}
    (hf : Function.Periodic f (2 * Real.pi)) :
    ∑ k ∈ Finset.range (n + 1), f (sixVertexCyclicRootPartition p k) =
      ∑ j, f (p j) := by
  rw [Finset.sum_range_succ']
  have hshift : f (p (Fin.last n) - 2 * Real.pi) =
      f (p (Fin.last n)) := by
    have h := hf (p (Fin.last n) - 2 * Real.pi)
    have harg : p (Fin.last n) - 2 * Real.pi + 2 * Real.pi =
        p (Fin.last n) := by ring
    rw [harg] at h
    exact h.symm
  rw [sixVertexCyclicRootPartition_zero, hshift,
    Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_bij
      (fun k hk => ⟨k, Finset.mem_range.mp hk⟩ :
        (k : Nat) → k ∈ Finset.range n → Fin n)
  · intro k hk
    exact Finset.mem_univ _
  · intro a ha b hb hab
    exact congrArg Fin.val hab
  · intro j _
    refine ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
    exact Fin.ext rfl
  · intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [sixVertexCyclicRootPartition_succ p hklt.le]
    rfl

theorem intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle
    (c : Real) {N n : Nat} (p : Fin (n + 1) → Real) (x : Real) :
    ∫ y in sixVertexCyclicRootPartition p 0..
        sixVertexCyclicRootPartition p (n + 1),
        sixVertexRootDensityKernel c x y *
          sixVertexFiniteRootDensity c N (n + 1) p y =
      ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y *
          sixVertexFiniteRootDensity c N (n + 1) p y := by
  let f : Real → Real := fun y =>
    sixVertexRootDensityKernel c x y *
      sixVertexFiniteRootDensity c N (n + 1) p y
  have hf : Function.Periodic f (2 * Real.pi) :=
    (periodic_sixVertexRootDensityKernel_right c x).mul
      (periodic_sixVertexFiniteRootDensity c N (n + 1) p)
  have hperiod := hf.intervalIntegral_add_eq
    (sixVertexCyclicRootPartition p 0) (-Real.pi)
  have hleft : sixVertexCyclicRootPartition p 0 + 2 * Real.pi =
      sixVertexCyclicRootPartition p (n + 1) := by
    rw [sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_end]
    ring
  have hright : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hleft, hright] at hperiod
  exact hperiod



theorem intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle
    (c : Real) {N n : Nat} (p : Fin (n + 1) -> Real)
    {f : Real -> Real} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ y in sixVertexCyclicRootPartition p 0..
        sixVertexCyclicRootPartition p (n + 1),
        f y * sixVertexFiniteRootDensity c N (n + 1) p y =
      ∫ y in -Real.pi..Real.pi,
        f y * sixVertexFiniteRootDensity c N (n + 1) p y := by
  let g : Real -> Real := fun y =>
    f y * sixVertexFiniteRootDensity c N (n + 1) p y
  have hg : Function.Periodic g (2 * Real.pi) :=
    hf.mul (periodic_sixVertexFiniteRootDensity c N (n + 1) p)
  have hperiod := hg.intervalIntegral_add_eq
    (sixVertexCyclicRootPartition p 0) (-Real.pi)
  have hleft : sixVertexCyclicRootPartition p 0 + 2 * Real.pi =
      sixVertexCyclicRootPartition p (n + 1) := by
    rw [sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_end]
    ring
  have hright : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hleft, hright] at hperiod
  exact hperiod

theorem abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {mesh : Real}
    (hmesh : ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤ mesh)
    (x : Real) :
    |(∑ j, sixVertexRootDensityKernel c x (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N (n + 1) p y| ≤
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c * mesh *
          (2 * Real.pi) := by
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh
      hc hN hcount hhalf hopen hsol hmesh
      (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
      (lipschitzWith_sixVertexRootDensityKernel_right hc x)
  have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p
    (periodic_sixVertexRootDensityKernel_right c x)
  have hsumScaled :
      ∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) *
            sixVertexRootDensityKernel c x
              (sixVertexCyclicRootPartition p k) =
        (∑ j, sixVertexRootDensityKernel c x (p j)) / N := by
    rw [← Finset.mul_sum, hsum]
    ring
  have hint := intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle
    (N := N) c p x
  rw [hsumScaled, hint] at hquad
  have hcoe : (sixVertexRootDensityKernelLipschitzNNReal c : Real) =
      sixVertexRootDensityKernelLipschitzBound c := by
    exact Real.coe_toNNReal _
      (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  rw [hcoe] at hquad
  exact hquad


theorem abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {f : Real -> Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N (n + 1) p y| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
          (2 * Real.pi) := by
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail
      hc htail hN hhalf hopen hsol hf hlip
  have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p hperiodic
  have hsumScaled :
      ∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) =
        (∑ j, f (p j)) / N := by
    rw [← Finset.mul_sum, hsum]
    ring
  have hint := intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle
    (N := N) c p hperiodic
  rw [hsumScaled, hint] at hquad
  exact hquad


theorem abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_pos_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hn : 0 < n) (hhalf : N = 2 * n)
    {p : Fin n -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {f : Real -> Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N n p y| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
          (2 * Real.pi) := by
  cases n with
  | zero => omega
  | succ n =>
      exact abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_le_tail
        hc htail hN hhalf hopen hsol hf hlip hperiodic



theorem abs_empiricalKernel_sub_finiteDensityIntegral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) :
    |(∑ j, sixVertexRootDensityKernel c x (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N (n + 1) p y| <=
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c *
          (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
            (2 * Real.pi) := by
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail
      hc htail hN hhalf hopen hsol
      (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
      (lipschitzWith_sixVertexRootDensityKernel_right hc x)
  have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p
    (periodic_sixVertexRootDensityKernel_right c x)
  have hsumScaled :
      ∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) *
            sixVertexRootDensityKernel c x
              (sixVertexCyclicRootPartition p k) =
        (∑ j, sixVertexRootDensityKernel c x (p j)) / N := by
    rw [← Finset.mul_sum, hsum]
    ring
  have hint := intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle
    (N := N) c p x
  rw [hsumScaled, hint] at hquad
  have hcoe : (sixVertexRootDensityKernelLipschitzNNReal c : Real) =
      sixVertexRootDensityKernelLipschitzBound c := by
    exact Real.coe_toNNReal _
      (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  rw [hcoe] at hquad
  exact hquad

end

end StatMech.FrontierD
