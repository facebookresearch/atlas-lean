/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville









open Set Bornology

namespace StatMech.FrontierA

noncomputable section



theorem exists_affine_of_entire_exp_growth
    (g : Complex -> Complex) (hg : Differentiable Complex g)
    (A B : Real) (hA : 0 < A) (hB : 0 <= B)
    (hgrowth : forall z,
      ‖Complex.exp (g z)‖ <= A * Real.exp (B * ‖z‖)) :
    exists a b : Complex, forall z, g z = a * z + b := by
  have hre : forall z, (g z).re <= Real.log A + B * ‖z‖ := by
    intro z
    apply Real.exp_le_exp.mp
    calc
      Real.exp (g z).re = ‖Complex.exp (g z)‖ := by
        rw [Complex.norm_exp]
      _ <= A * Real.exp (B * ‖z‖) := hgrowth z
      _ = Real.exp (Real.log A + B * ‖z‖) := by
        rw [Real.exp_add, Real.exp_log hA]
  have hderivBound : forall c, ‖deriv g c‖ <= 4 * (1 + B) := by
    intro c
    let C : Real := |Real.log A| + B * ‖c‖ + ‖g c‖ + 1
    have hC : 0 < C := by
      dsimp [C]
      positivity
    let M : Real := C + B * C
    have hM : 0 < M := by
      dsimp [M]
      positivity
    let h : Complex -> Complex := fun z => g (z + c) - g c
    have hhDiff : Differentiable Complex h := by
      dsimp [h]
      fun_prop
    have hhMaps : MapsTo h (Metric.ball 0 C) {z | z.re <= M} := by
      intro z hz
      have hzC : ‖z‖ < C := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      have hnorm : ‖z + c‖ <= ‖z‖ + ‖c‖ := norm_add_le z c
      have hgRe := hre (z + c)
      have hlog : Real.log A <= |Real.log A| := le_abs_self _
      have hnegRe : -(g c).re <= ‖g c‖ :=
        (neg_le_abs (g c).re).trans (Complex.abs_re_le_norm (g c))
      have hBnorm : B * ‖z + c‖ <= B * (‖z‖ + ‖c‖) :=
        mul_le_mul_of_nonneg_left hnorm hB
      have hBz : B * ‖z‖ <= B * C :=
        mul_le_mul_of_nonneg_left hzC.le hB
      change (g (z + c)).re - (g c).re <= M
      calc
        (g (z + c)).re - (g c).re <=
            Real.log A + B * ‖z + c‖ - (g c).re := by
              linarith
        _ <= |Real.log A| + B * (‖z‖ + ‖c‖) + ‖g c‖ := by
              linarith
        _ <= |Real.log A| + B * C + B * ‖c‖ + ‖g c‖ := by
              linarith
        _ <= M := by
              dsimp [M, C]
              ring_nf
              linarith
    have hh0 : h 0 = 0 := by simp [h]
    have hhalf : 0 < C / 2 := by positivity
    have hsphere : forall (z : Complex), z ∈ Metric.sphere (0 : Complex) (C / 2) ->
        ‖h z‖ <= 2 * M := by
      intro z hz
      have hnorm : ‖z‖ = C / 2 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hzball : z ∈ Metric.ball (0 : Complex) C := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]
        linarith
      have hbc := Complex.borelCaratheodory_zero hM
        hhDiff.differentiableOn hhMaps hC hzball hh0
      rw [hnorm] at hbc
      calc
        ‖h z‖ <= 2 * M * (C / 2) / (C - C / 2) := hbc
        _ = 2 * M := by field_simp; ring
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      hhalf hhDiff.diffContOnCl hsphere
    have hhDeriv : deriv h 0 = deriv g c := by
      dsimp [h]
      rw [deriv_sub_const, deriv_comp_add_const, zero_add]
    rw [hhDeriv] at hcauchy
    calc
      ‖deriv g c‖ <= (2 * M) / (C / 2) := hcauchy
      _ = 4 * (1 + B) := by
        dsimp [M]
        field_simp
        ring
  have hderivDiff : Differentiable Complex (deriv g) :=
    differentiableOn_univ.mp (hg.differentiableOn.deriv isOpen_univ)
  have hderivBounded : IsBounded (Set.range (deriv g)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨4 * (1 + B), ?_⟩
    rintro y ⟨c, rfl⟩
    exact hderivBound c
  have hderivConst : forall z, deriv g z = deriv g 0 := by
    intro z
    exact hderivDiff.apply_eq_apply_of_bounded hderivBounded z 0
  let a : Complex := deriv g 0
  let b : Complex := g 0
  let p : Complex -> Complex := fun z => g z - (a * z + b)
  have hpDiff : Differentiable Complex p := by
    dsimp [p]
    fun_prop
  have hpDeriv : forall z, deriv p z = 0 := by
    intro z
    have hlin : HasDerivAt (fun w : Complex => a * w + b) a z := by
      convert ((hasDerivAt_id z).const_mul a).add_const b using 1 <;> ring
    have hpAt := (hg z).hasDerivAt.sub hlin
    change HasDerivAt p (deriv g z - a) z at hpAt
    rw [hpAt.deriv, hderivConst z]
    simp [a]
  refine ⟨a, b, fun z => ?_⟩
  have hpConst := is_const_of_deriv_eq_zero hpDiff hpDeriv z 0
  change g z - (a * z + b) = g 0 - (a * 0 + b) at hpConst
  have hpZero : g z - (a * z + b) = 0 := by
    calc
      g z - (a * z + b) = g 0 - (a * 0 + b) := hpConst
      _ = 0 := by simp [b]
  exact sub_eq_zero.mp hpZero

end

end StatMech.FrontierA
