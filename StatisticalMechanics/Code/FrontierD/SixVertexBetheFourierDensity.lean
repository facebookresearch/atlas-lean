/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierEvaluation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact













open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFourierRootDensityTerm (lam : Real) (n : Nat) (alpha : Real) : Real :=
  Real.cos ((n + 1 : Real) * alpha) /
    Real.cosh ((n + 1 : Real) * lam)


def sixVertexFourierRootDensityMajorant (lam : Real) (n : Nat) : Real :=
  2 * Real.exp (-lam) ^ (n + 1)

theorem summable_sixVertexFourierRootDensityMajorant
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexFourierRootDensityMajorant lam) := by
  have hq0 : 0 <= Real.exp (-lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : Nat => Real.exp (-lam) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  simpa [sixVertexFourierRootDensityMajorant] using Summable.mul_left 2 hgeom

theorem norm_sixVertexFourierRootDensityTerm_le
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    ‖sixVertexFourierRootDensityTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant lam n := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hx : 0 < x := mul_pos hm hlam
  have hcos : |Real.cos (m * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcosh : Real.exp x <= 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-x)]
  have hinv : 1 / Real.cosh x <= 2 * Real.exp (-x) := by
    have hhalf : 1 / (2 * Real.cosh x) <= 1 / Real.exp x :=
      one_div_le_one_div_of_le (Real.exp_pos x) hcosh
    calc
      1 / Real.cosh x = 2 * (1 / (2 * Real.cosh x)) := by
        field_simp [(Real.cosh_pos x).ne']
      _ <= 2 * (1 / Real.exp x) := by gcongr
      _ = 2 * Real.exp (-x) := by
        simp [div_eq_mul_inv, Real.exp_neg]
  have hterm :
      |Real.cos (m * alpha)| / Real.cosh x <= 2 * Real.exp (-x) :=
    (div_le_div_of_nonneg_right hcos (Real.cosh_pos x).le).trans hinv
  rw [sixVertexFourierRootDensityTerm, Real.norm_eq_abs, abs_div,
    abs_of_pos (Real.cosh_pos _)]
  change |Real.cos (m * alpha)| / Real.cosh x <= _
  calc
    |Real.cos (m * alpha)| / Real.cosh x <= 2 * Real.exp (-x) := hterm
    _ = sixVertexFourierRootDensityMajorant lam n := by
      rw [sixVertexFourierRootDensityMajorant]
      dsimp [x, m]
      rw [<- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexFourierRootDensityTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexFourierRootDensityTerm lam n alpha) :=
  (summable_sixVertexFourierRootDensityMajorant hlam).of_norm_bounded
    (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha)



def sixVertexFourierRootDensity (lam alpha : Real) : Real :=
  1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha

theorem continuous_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexFourierRootDensity lam) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexFourierRootDensityTerm
    fun_prop
  · exact summable_sixVertexFourierRootDensityMajorant hlam
  · intro n alpha
    exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha

private def sixVertexFourierRootDensityTermContinuous
    (lam : Real) (n : Nat) : C(Real, Real) :=
  ⟨sixVertexFourierRootDensityTerm lam n, by
    unfold sixVertexFourierRootDensityTerm
    fun_prop⟩

theorem intervalIntegral_sixVertexFourierRootDensityTerm
    (lam : Real) (n : Nat) :
    ∫ alpha in -Real.pi..Real.pi,
      sixVertexFourierRootDensityTerm lam n alpha = 0 := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hscaled := intervalIntegral.mul_integral_comp_mul_left
    (a := -Real.pi) (b := Real.pi) (f := Real.cos) m
  have hrhs :
      (∫ x in m * (-Real.pi)..m * Real.pi, Real.cos x) = 0 := by
    rw [integral_cos]
    have hpos : Real.sin (m * Real.pi) = 0 := by
      dsimp [m]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.sin_nat_mul_pi (n + 1)
    have hneg : Real.sin (m * (-Real.pi)) = 0 := by
      rw [show m * (-Real.pi) = -(m * Real.pi) by ring, Real.sin_neg, hpos, neg_zero]
    rw [hpos, hneg, sub_zero]
  rw [hrhs] at hscaled
  have hcoszero :
      (∫ alpha in -Real.pi..Real.pi, Real.cos (m * alpha)) = 0 := by
    exact (mul_eq_zero.mp hscaled).resolve_left hm
  unfold sixVertexFourierRootDensityTerm
  change (∫ alpha in -Real.pi..Real.pi,
    Real.cos (m * alpha) / Real.cosh (m * lam)) = 0
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, hcoszero,
    zero_mul]

theorem intervalIntegral_tsum_sixVertexFourierRootDensityTerm
    {lam : Real} (hlam : 0 < lam) :
    ∫ alpha in -Real.pi..Real.pi,
      (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha) = 0 := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun n : Nat =>
      ‖(sixVertexFourierRootDensityTermContinuous lam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam n)]
    intro alpha
    exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  rw [show (fun alpha => ∑' n : Nat,
      (sixVertexFourierRootDensityTermContinuous lam n) alpha) =
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha) by rfl] at hswap
  rw [<- hswap]
  rw [show (fun i : Nat => ∫ x in -Real.pi..Real.pi,
      (sixVertexFourierRootDensityTermContinuous lam i) x) =
      (fun _ : Nat => 0) by
        funext i
        change (∫ x in -Real.pi..Real.pi,
          sixVertexFourierRootDensityTerm lam i x) = 0
        exact intervalIntegral_sixVertexFourierRootDensityTerm lam i]
  exact tsum_zero



theorem intervalIntegral_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) :
    ∫ alpha in -Real.pi..Real.pi,
      sixVertexFourierRootDensity lam alpha = Real.pi := by
  have hseriesContinuous : Continuous
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexFourierRootDensityTerm
      fun_prop
    · exact summable_sixVertexFourierRootDensityMajorant hlam
    · intro n alpha
      exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha
  have hseries : IntervalIntegrable
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    hseriesContinuous.intervalIntegrable _ _
  simp_rw [sixVertexFourierRootDensity]
  rw [intervalIntegral.integral_add intervalIntegrable_const hseries,
    intervalIntegral_tsum_sixVertexFourierRootDensityTerm hlam,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end

end StatMech.FrontierD
