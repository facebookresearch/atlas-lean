/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootDensityKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









open Finset

namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheCountingFunction
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (x + (∑ k, sixVertexTheta c x (p k)) / N) / (2 * Real.pi)

def sixVertexFiniteRootDensity
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (1 + (∑ k,
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)) / N) /
    (2 * Real.pi)

theorem hasDerivAt_sixVertexBetheCountingFunction
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) (x : Real) :
    HasDerivAt (sixVertexBetheCountingFunction c N n p)
      (sixVertexFiniteRootDensity c N n p x) x := by
  have hsum : HasDerivAt (fun y : Real =>
      ∑ k, sixVertexTheta c y (p k))
      (∑ k, 4 * sixVertexDelta c *
        sixVertexBetheIntegratingFactor c (p k) /
          sixVertexThetaDerivativeDenominator c x (p k)) x := by
    simpa using HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      hasDerivAt_sixVertexTheta_left hc x (p k)
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexBetheCountingFunction sixVertexFiniteRootDensity
  convert ((hasDerivAt_id x).add (hsum.div_const N)).div_const
    (2 * Real.pi) using 1 <;> field_simp <;> ring

theorem continuous_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) (N n : Nat) (p : Fin n → Real) :
    Continuous (sixVertexFiniteRootDensity c N n p) := by
  unfold sixVertexFiniteRootDensity
  apply Continuous.div_const
  apply Continuous.add continuous_const
  apply Continuous.div_const
  apply continuous_finsetSum
  intro k _
  apply Continuous.div continuous_const
  · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    fun_prop
  · intro x
    exact (sixVertexThetaDerivativeDenominator_pos hc x (p k)).ne'


theorem sixVertexRootDensityWeight_mul_finiteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) (x : Real) :
    sixVertexRootDensityWeight c x *
        sixVertexFiniteRootDensity c N n p x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (∑ k, sixVertexRootDensityKernel c x (p k)) /
          ((2 * Real.pi) * N) := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi : Real) ≠ 0 := by positivity
  have hsum :
      (∑ k, sixVertexRootDensityKernel c x (p k)) =
        -sixVertexRootDensityWeight c x *
          ∑ k, (4 * sixVertexDelta c *
            sixVertexBetheIntegratingFactor c (p k) /
              sixVertexThetaDerivativeDenominator c x (p k)) := by
    simp_rw [sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
      hc x]
    rw [← Finset.mul_sum]
  unfold sixVertexFiniteRootDensity
  rw [hsum]
  field_simp
  ring

theorem sixVertexBetheCountingFunction_at_root
    {c : Real} {N n : Nat} (hN : 0 < N) {p : Fin n → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N n p) (j : Fin n) :
    sixVertexBetheCountingFunction c N n p (p j) =
      sixVertexCentralQuantumNumber j / N := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hj := hsol j
  unfold sixVertexBetheCountingFunction
  field_simp
  linarith

theorem intervalIntegral_sixVertexFiniteRootDensity_adjacent
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    ∫ x in p j.castSucc..p j.succ,
        sixVertexFiniteRootDensity c N (n + 1) p x = 1 / N := by
  let f := sixVertexBetheCountingFunction c N (n + 1) p
  let f' := sixVertexFiniteRootDensity c N (n + 1) p
  have hderiv : deriv f = f' := by
    funext x
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).deriv
  have hdiff : ∀ x ∈ Set.uIcc (p j.castSucc) (p j.succ),
      DifferentiableAt Real f x := by
    intro x _
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).differentiableAt
  have hcont : ContinuousOn f'
      (Set.uIcc (p j.castSucc) (p j.succ)) :=
    (continuous_sixVertexFiniteRootDensity hc N (n + 1) p).continuousOn
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := p j.castSucc) (b := p j.succ) f hderiv hdiff hcont
  have hleft := sixVertexBetheCountingFunction_at_root hN hsol j.castSucc
  have hright := sixVertexBetheCountingFunction_at_root hN hsol j.succ
  have hquantum : sixVertexCentralQuantumNumber j.succ -
      sixVertexCentralQuantumNumber j.castSucc = 1 := by
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp
  dsimp [f, f'] at hFTC hleft hright
  rw [hleft, hright] at hFTC
  rw [hFTC]
  rw [← sub_div]
  rw [hquantum]

theorem sixVertexBetheCountingFunction_add_two_pi
    {N n : Nat} (hN : 0 < N) (c : Real) (p : Fin n → Real) (x : Real) :
    sixVertexBetheCountingFunction c N n p (x + 2 * Real.pi) =
      sixVertexBetheCountingFunction c N n p x +
        1 - (n : Real) / N := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : (∑ k, sixVertexTheta c (x + 2 * Real.pi) (p k)) =
      (∑ k, sixVertexTheta c x (p k)) -
        (n : Real) * (2 * Real.pi) := by
    simp_rw [sixVertexTheta_add_two_pi_left]
    rw [Finset.sum_sub_distrib]
    simp
  unfold sixVertexBetheCountingFunction
  rw [hsum]
  field_simp
  ring


theorem intervalIntegral_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) :
    ∫ x in -Real.pi..Real.pi,
        sixVertexFiniteRootDensity c N n p x =
      1 - (n : Real) / N := by
  let f := sixVertexBetheCountingFunction c N n p
  let f' := sixVertexFiniteRootDensity c N n p
  have hderiv : deriv f = f' := by
    funext x
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).deriv
  have hdiff : ∀ x ∈ Set.uIcc (-Real.pi) Real.pi,
      DifferentiableAt Real f x := by
    intro x _
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc (-Real.pi) Real.pi) :=
    (continuous_sixVertexFiniteRootDensity hc N n p).continuousOn
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := -Real.pi) (b := Real.pi) f hderiv hdiff hcont
  have hperiod := sixVertexBetheCountingFunction_add_two_pi
    hN c p (-Real.pi)
  have harg : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [harg] at hperiod
  dsimp [f, f'] at hFTC hperiod
  rw [hFTC]
  linarith

end

end StatMech.FrontierD
