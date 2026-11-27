/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ConstrainedTwoLink
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two-link pendulum checks

Concrete consumers of `PhyslibExt.Mechanics.ConstrainedTwoLink`: noncollinear links with nonzero
angular velocities, stretched and folded collinear links, the zero-length boundary, and the main
lemmas applied to those parameters and to a uniformly rotating trajectory; the tangent-space and
rod-reaction lemmas on collinear, noncollinear and hanging configurations, and a closed chain that
loses rank; the reduced dynamics on nonzero initial data, the zero-length boundary where the
Euler-Lagrange equation leaves the acceleration free, and the hanging pendulum at rest.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Fixtures
- B. The main lemmas on the fixture parameters
- C. Tangent space and constraint forces: fixtures
- D. Tangent space and constraint forces: consumers
- E. Reduced dynamics: fixtures
- F. Reduced dynamics: consumers

## iv. References

None.
-/

namespace PhyslibExtTest.Mechanics.ConstrainedTwoLink

open PhyslibExt.Mechanics.ConstrainedTwoLink
open scoped Matrix

/-! ## A. Fixtures -/

/-- Noncollinear links and nonzero angular velocities: `m₁ = 2`, `m₂ = 1`, `l₁ = 1`, `l₂ = 2`,
`q = (π / 3, 0)`, `w = (1, 1)`. The Cartesian velocities are `(1 / 2, √3 / 2)` and
`(5 / 2, √3 / 2)`, the kinetic energy is `9 / 2` and the determinant is `11`. -/
example :
    vel₁ 1 (Real.pi / 3) 1 = !₂[1 / 2, Real.sqrt 3 / 2] ∧
      vel₂ 1 2 (Real.pi / 3) 0 1 1 = !₂[5 / 2, Real.sqrt 3 / 2] ∧
      kineticEnergy 2 1 1 2 (Real.pi / 3) 0 1 1 = 9 / 2 ∧
      (massMatrix 2 1 1 2 (Real.pi / 3) 0).det = 11 := by
  have c3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have s3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [vel₁, c3, s3]
  · simp only [vel₂, vel₁, c3, s3, Real.cos_zero, Real.sin_zero]
    ext i; fin_cases i <;> simp; ring
  · rw [kineticEnergy_eq_massMatrix]
    simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp [massMatrix, Real.cos_pi_div_three]
    norm_num
  · have hs : Real.sin (Real.pi / 3 - 0) ^ 2 = 3 / 4 := by
      rw [sub_zero]
      exact Real.sq_sin_pi_div_three
    rw [massMatrix_det, hs]
    norm_num

/-- Collinear links stay regular: hanging straight (`q = (0, 0)`) and folded (`q = (0, π)`) the
determinant is `m₁ m₂ l₁² l₂² = 8`, and the counter-rotating velocity `w = (1, -1)` of the
stretched pendulum has kinetic energy `3 / 2`. -/
example :
    (massMatrix 2 1 1 2 0 0).det = 8 ∧ (massMatrix 2 1 1 2 0 Real.pi).det = 8 ∧
      kineticEnergy 2 1 1 2 0 0 1 (-1) = 3 / 2 := by
  have h00 : Real.sin ((0 : ℝ) - 0) = 0 := by rw [sub_self, Real.sin_zero]
  have h0pi : Real.sin ((0 : ℝ) - Real.pi) = 0 := by
    rw [zero_sub, Real.sin_neg, Real.sin_pi, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [massMatrix_det_of_collinear h00]
    norm_num
  · rw [massMatrix_det_of_collinear h0pi]
    norm_num
  · rw [kineticEnergy_eq_massMatrix]
    simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp [massMatrix]
    norm_num

/-- Zero length is the invalid boundary: with `l₂ = 0` the determinant vanishes and the nonzero
angular velocity `w = (0, 1)` carries no kinetic energy. -/
example :
    (massMatrix 2 1 1 0 (Real.pi / 3) 0).det = 0 ∧
      kineticEnergy 2 1 1 0 (Real.pi / 3) 0 0 1 = 0 := by
  refine ⟨?_, ?_⟩
  · exact massMatrix_det_eq_zero_of_length_eq_zero (Or.inr rfl) 2 1 _ _
  · have hv₁ : vel₁ 1 (Real.pi / 3) 0 = 0 := by simp [vel₁]
    have hv₂ : vel₂ 1 0 (Real.pi / 3) 0 0 1 = 0 := by simp [vel₂, hv₁]
    simp [kineticEnergy, hv₁, hv₂]

/-! ## B. The main lemmas on the fixture parameters -/

/-- The rod constraints on the noncollinear fixture configuration. -/
example : ‖pos₁ 1 (Real.pi / 3)‖ = 1 ∧ ‖pos₂ 1 2 (Real.pi / 3) 0 - pos₁ 1 (Real.pi / 3)‖ = 2 :=
  pos_rod_constraints (by norm_num) (by norm_num) _ _

/-- The fixture masses and lengths give a positive determinant and a positive kinetic energy for
the counter-rotating velocity of the stretched pendulum. -/
example : 0 < (massMatrix 2 1 1 2 (Real.pi / 3) 0).det ∧ 0 < kineticEnergy 2 1 1 2 0 0 1 (-1) :=
  ⟨massMatrix_det_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _,
    kineticEnergy_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _
      (Or.inl one_ne_zero)⟩

/-- The uniformly rotating trajectory `q₁ s = π / 3 + s`, `q₂ s = s` meets the hypotheses of
`kineticEnergy_actual` at `t = 0`; its actual kinetic energy is `9 / 2`. -/
example : 2 * ‖deriv (fun s => pos₁ 1 (Real.pi / 3 + s)) 0‖ ^ 2 / 2 +
    1 * ‖deriv (fun s => pos₂ 1 2 (Real.pi / 3 + s) s) 0‖ ^ 2 / 2 = 9 / 2 := by
  have h₁ : HasDerivAt (fun s : ℝ => Real.pi / 3 + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (Real.pi / 3)
  have h := kineticEnergy_actual 2 1 1 2 h₁ (hasDerivAt_id' 0)
  simp only [add_zero] at h
  rw [h]
  simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp [massMatrix, Real.cos_pi_div_three]
  norm_num

/-! ## C. Tangent space and constraint forces: fixtures -/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Collinear links are not rank loss: with `l = (1, 2)` the stretched configuration `q = (0, 0)`
and the folded configuration `q = (0, π)` keep rank two, and the nonzero angular velocity
`w = (1, -1)` gives the nonzero kernel velocity `((1, 0), (-1, 0))` at the stretched one. -/
example :
    Module.finrank ℝ (LinearMap.range (rodJacobian (posMap 1 2 (0, 0))).toLinearMap) = 2 ∧
      Module.finrank ℝ (LinearMap.range (rodJacobian (posMap 1 2 (0, Real.pi))).toLinearMap) = 2 ∧
      angleJacobian 1 2 (0, 0) (1, -1) = (!₂[1, 0], !₂[-1, 0]) ∧
      rodJacobian (posMap 1 2 (0, 0)) (!₂[1, 0], !₂[-1, 0]) = 0 := by
  refine ⟨rodJacobian_rank_two (by norm_num) (by norm_num) _,
    rodJacobian_rank_two (by norm_num) (by norm_num) _, ?_, ?_⟩
  · rw [angleJacobian_apply]
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> norm_num [vel₁, vel₂]
  · rw [rodJacobian_apply]
    simp [posMap, pos₁, pos₂, PiLp.inner_apply, Fin.sum_univ_two]

/-- Noncollinear links, `l = (1, 2)` and `q = (π / 2, 0)`: the angular velocity `w = (1, 1)` gives
the kernel velocity `((0, 1), (2, 1))`; the reaction with multipliers `(1, 1)` is
`((1, 2), (0, -2))` and does no virtual work along it, while a vertical load `(0, -1)` on the
first mass does the virtual work `-1`. -/
example :
    angleJacobian 1 2 (Real.pi / 2, 0) (1, 1) = (!₂[0, 1], !₂[2, 1]) ∧
      rodJacobian (posMap 1 2 (Real.pi / 2, 0)) (!₂[0, 1], !₂[2, 1]) = 0 ∧
      rodReaction 1 1 (posMap 1 2 (Real.pi / 2, 0)) = (!₂[1, 2], !₂[0, -2]) ∧
      virtualWork (!₂[1, 2], !₂[0, -2]) (!₂[0, 1], !₂[2, 1]) = 0 ∧
      virtualWork (!₂[0, -1], 0) (!₂[0, 1], !₂[2, 1]) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [angleJacobian_apply]
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> norm_num [vel₁, vel₂]
  · rw [rodJacobian_apply]
    simp [posMap, pos₁, pos₂, PiLp.inner_apply, Fin.sum_univ_two]
  · refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [rodReaction, posMap, pos₁, pos₂]
  · simp [virtualWork, PiLp.inner_apply, Fin.sum_univ_two]
  · simp [virtualWork, PiLp.inner_apply, Fin.sum_univ_two]

/-- Genuine rank loss in a closed chain: one point on the unit circles about `(0, 0)` and
`(2, 0)`, which are tangent at `(1, 0)`. The constraint map is differentiable there with a
derivative of rank one whose kernel contains the vertical direction `(0, 1)`, although `(1, 0)`
is the only point satisfying both constraints. -/
example :
    ∃ J : ℝ² →L[ℝ] ℝ × ℝ,
      HasFDerivAt (fun p : ℝ² => (‖p‖ ^ 2 - 1, ‖p - !₂[2, 0]‖ ^ 2 - 1)) J !₂[1, 0] ∧
        Module.finrank ℝ (LinearMap.range J.toLinearMap) = 1 ∧ J !₂[0, 1] = 0 ∧
        ∀ p : ℝ², ‖p‖ ^ 2 - 1 = 0 → ‖p - !₂[2, 0]‖ ^ 2 - 1 = 0 → p = !₂[1, 0] := by
  set p₀ : EuclideanSpace ℝ (Fin 2) := !₂[1, 0] with hp₀
  set c : EuclideanSpace ℝ (Fin 2) := !₂[2, 0] with hc
  set J : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
    ((2 : ℝ) • (innerSL ℝ p₀).comp (ContinuousLinearMap.id ℝ _)).prod
      ((2 : ℝ) • (innerSL ℝ (p₀ - c)).comp (ContinuousLinearMap.id ℝ _)) with hJ
  have hJv : ∀ v : EuclideanSpace ℝ (Fin 2), J v = v 0 • ((2 : ℝ), (-2 : ℝ)) := by
    intro v
    refine Prod.ext ?_ ?_ <;> simp [hJ, hp₀, hc, PiLp.inner_apply, Fin.sum_univ_two] <;> ring
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · have h1 := (hasFDerivAt_id (𝕜 := ℝ) p₀).norm_sq
    have h2 := ((hasFDerivAt_id (𝕜 := ℝ) p₀).sub_const c).norm_sq
    exact ((h1.sub_const (1 : ℝ)).prodMk (h2.sub_const (1 : ℝ))).congr_fderiv (by
      refine ContinuousLinearMap.ext fun v => ?_
      refine Prod.ext ?_ ?_ <;> simp [hJ, nsmul_eq_mul])
  · have hrange : LinearMap.range J.toLinearMap = Submodule.span ℝ {((2 : ℝ), (-2 : ℝ))} := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        rw [Submodule.mem_span_singleton]
        exact ⟨v 0, (hJv v).symm⟩
      · intro hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        refine ⟨a • !₂[1, 0], ?_⟩
        change J (a • !₂[1, 0]) = _
        rw [hJv]
        simp
    rw [hrange, finrank_span_singleton]
    simp
  · rw [hJv]
    simp
  · intro p h1 h2
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at h1 h2
    simp only [PiLp.sub_apply, hc] at h2
    simp at h2
    have hx : p 0 = 1 := by nlinarith
    have hy2 : p 1 ^ 2 = 0 := by nlinarith
    have hy : p 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
    ext i
    fin_cases i <;> simp [hx, hy, hp₀]

/-! ## D. Tangent space and constraint forces: consumers -/

/-- The uniformly rotating trajectory `s ↦ posMap 1 2 (π / 3 + s, s)` satisfies both rod
constraints at every time, so its velocity at `s = 0` lies in the kernel of the constraint
Jacobian. -/
example : rodJacobian (posMap 1 2 (Real.pi / 3, 0))
    (angleJacobian 1 2 (Real.pi / 3, 0) (1, 1)) = 0 := by
  have hline : HasDerivAt (fun s : ℝ => ((Real.pi / 3, 0) : ℝ × ℝ) + s • ((1, 1) : ℝ × ℝ))
      (1, 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((1, 1) : ℝ × ℝ)).const_add
      ((Real.pi / 3, 0) : ℝ × ℝ)
  have hv := (hasFDerivAt_posMap 1 2
    (((Real.pi / 3, 0) : ℝ × ℝ) + (0 : ℝ) • ((1, 1) : ℝ × ℝ))).comp_hasDerivAt (0 : ℝ) hline
  simp only [zero_smul, add_zero] at hv
  have h := rodJacobian_velocity_eq_zero (l₁ := 1) (l₂ := 2)
    (Filter.Eventually.of_forall fun s => rodConstraint_posMap 1 2 _) hv
  simpa using h

/-- At the stretched configuration the kernel velocity `((1, 0), (-1, 0))` is the velocity of the
constrained curve `s ↦ posMap 1 2 (s, -s)` and of no other straight angle curve: its angular
velocity is `(1, -1)`. -/
example (w : ℝ × ℝ)
    (hw : HasDerivAt (fun s : ℝ => posMap 1 2 ((0, 0) + s • w)) (!₂[1, 0], !₂[-1, 0]) 0) :
    w = (1, -1) := by
  have hker : rodJacobian (posMap 1 2 (0, 0)) (!₂[1, 0], !₂[-1, 0]) = 0 := by
    rw [rodJacobian_apply]
    simp [posMap, pos₁, pos₂, PiLp.inner_apply, Fin.sum_univ_two]
  have hline : HasDerivAt (fun s : ℝ => ((0, 0) : ℝ × ℝ) + s • ((1, -1) : ℝ × ℝ)) (1, -1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((1, -1) : ℝ × ℝ)).const_add
      ((0, 0) : ℝ × ℝ)
  have h1 := (hasFDerivAt_posMap 1 2
    (((0, 0) : ℝ × ℝ) + (0 : ℝ) • ((1, -1) : ℝ × ℝ))).comp_hasDerivAt (0 : ℝ) hline
  simp only [zero_smul, add_zero] at h1
  have hval : angleJacobian 1 2 (0, 0) (1, -1) = (!₂[1, 0], !₂[-1, 0]) := by
    rw [angleJacobian_apply]
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> norm_num [vel₁, vel₂]
  rw [hval] at h1
  exact (existsUnique_hasDerivAt_posMap (by norm_num) (by norm_num) (0, 0) hker).unique
    (y₂ := ((1, -1) : ℝ × ℝ)) hw h1

/-- Hanging at rest, `q = (0, 0)` and `l = (1, 2)`, under the weights `(0, -20)` and `(0, -10)`
(`m = (2, 1)`, `g = 10`), the rods supply the forces `(0, 20)` and `(0, 10)`. These do no virtual
work along the kernel of the constraint Jacobian, and they are the rod reaction with the unique
multipliers `(-30, -5)`: rod tensions `30` and `10`. -/
example :
    (∀ v, rodJacobian (posMap 1 2 (0, 0)) v = 0 →
        virtualWork (!₂[0, 20], !₂[0, 10]) v = 0) ∧
      ∀ c : ℝ × ℝ, (!₂[0, 20], !₂[0, 10]) = rodReaction c.1 c.2 (posMap 1 2 (0, 0)) →
        c = (-30, -5) := by
  have hF : ((!₂[0, 20], !₂[0, 10]) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) =
      rodReaction (-30) (-5) (posMap 1 2 (0, 0)) := by
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
      simp [rodReaction, posMap, pos₁, pos₂] <;> norm_num
  have hw : ∀ v, rodJacobian (posMap 1 2 (0, 0)) v = 0 →
      virtualWork (!₂[0, 20], !₂[0, 10]) v = 0 := by
    intro v hv
    rw [hF]
    exact virtualWork_rodReaction_eq_zero _ _ hv
  exact ⟨hw, fun c hc => (existsUnique_rodReaction (by norm_num) (by norm_num) (0, 0) hw).unique
    (y₂ := ((-30, -5) : ℝ × ℝ)) hc hF⟩

/-! ## E. Reduced dynamics: fixtures -/

open scoped ContDiff Time
open ClassicalMechanics (eulerLagrangeOp)

/-- Nonzero initial data: `m = (2, 1)`, `l = (1, 2)`, `g = 10`, initial angles `(π / 3, 0)` and
angular velocities `(1, 1)` at time `0`. The solution starts with the angular acceleration
`(-65 √3 / 11, 19 √3 / 11)`, and along it Newton's equations hold with unique rod multipliers. -/
example :
    ∃ ε > (0 : ℝ), ∃ q : Time → ℝ², q 0 = !₂[Real.pi / 3, 0] ∧ ∂ₜ q 0 = !₂[1, 1] ∧
      ∂ₜ (∂ₜ q) 0 = !₂[-(65 * Real.sqrt 3) / 11, 19 * Real.sqrt 3 / 11] ∧
      ∀ t : Time, t.val ∈ Set.Ioo (-ε) ε →
        ContDiffAt ℝ 2 q t ∧ eulerLagrangeOp (angleLagrangian 2 1 1 2 10) q t = 0 ∧
          ∃! c : ℝ × ℝ, ((2 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 q)) t).1,
            (1 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 q)) t).2) =
            gravityForce 2 1 10 + rodReaction c.1 c.2 (cartesianMotion 1 2 q t) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h1 : (0 : ℝ) < 1 := by norm_num
  obtain ⟨ε, hε, q, hq₀, hw₀, hq⟩ :=
    exists_eulerLagrangeOp_angleLagrangian_eq_zero h2 h1 h1 h2 10 0 !₂[Real.pi / 3, 0] !₂[1, 1]
  have hI : ∀ t : Time, t.val ∈ Set.Ioo (-ε) ε →
      t.val ∈ Set.Ioo ((0 : Time).val - ε) ((0 : Time).val + ε) := by
    intro t ht; simpa [Time.zero_val] using ht
  refine ⟨ε, hε, q, hq₀, hw₀, ?_, fun t ht => ?_⟩
  · obtain ⟨hC, hE⟩ := hq 0 (hI 0 (by simp [Time.zero_val, hε]))
    rw [(eulerLagrangeOp_angleLagrangian_eq_zero_iff h2 h1 h1 h2 10 hC).mp hE, hq₀, hw₀]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    ext i
    fin_cases i
    · simp [reducedAccel, generalizedForce, Real.sin_pi_div_three, Real.cos_pi_div_three]
      field_simp
      linear_combination 65 * h3
    · simp [reducedAccel, generalizedForce, Real.sin_pi_div_three, Real.cos_pi_div_three]
      field_simp
      linear_combination (-38) * h3
  · obtain ⟨hC, hE⟩ := hq t (hI t ht)
    exact ⟨hC, hE, (existsUnique_rodReaction_newton_iff h2 h1 h1 h2 10 hC).mpr
      ((eulerLagrangeOp_angleLagrangian_eq_zero_iff h2 h1 h1 h2 10 hC).mp hE)⟩

/-- The zero-length boundary: with `l₂ = 0` the Euler-Lagrange equation does not determine the
angular acceleration. The trajectory `(0, t² / 2)` and the rest trajectory `(0, 0)` have the same
angles and angular velocities at time `0`, and the Euler-Lagrange operator vanishes along both at
every instant, but their angular accelerations at `0` differ: no reduced ODE exists there. -/
example :
    (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²)) 0 = 0 ∧
      ∂ₜ (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²)) 0 = ∂ₜ (fun _ : Time => (0 : ℝ²)) 0 ∧
      ∂ₜ (∂ₜ (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²))) 0 ≠
        ∂ₜ (∂ₜ (fun _ : Time => (0 : ℝ²))) 0 ∧
      ∀ t : Time,
        eulerLagrangeOp (angleLagrangian 1 1 1 0 10) (fun s => !₂[0, s.val ^ 2 / 2]) t = 0 ∧
          eulerLagrangeOp (angleLagrangian 1 1 1 0 10) (fun _ => 0) t = 0 := by
  have hcomp : ∀ {γ : ℝ → ℝ²} {v : ℝ²} {s : Time}, HasDerivAt γ v s.val →
      ∂ₜ (fun s : Time => γ s.val) s = v :=
    fun {γ v s} h => Time.deriv_comp_toRealCLE_of_hasDerivAt γ s v h
  have hγ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => (!₂[0, τ ^ 2 / 2] : ℝ²)) !₂[0, τ] τ := by
    intro τ
    have h := ((hasDerivAt_pow 2 τ).div_const 2).smul_const (!₂[0, 1] : ℝ²)
    convert h using 1
    · funext x; ext i; fin_cases i <;> simp
    · ext i; fin_cases i <;> simp
  have hδ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => (!₂[0, τ] : ℝ²)) !₂[0, 1] τ := by
    intro τ
    have h := (hasDerivAt_id τ).smul_const (!₂[0, 1] : ℝ²)
    convert h using 1
    · funext x; ext i; fin_cases i <;> simp
    · ext i; fin_cases i <;> simp
  have hd : ∂ₜ (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²)) = fun s => !₂[0, s.val] :=
    funext fun s => hcomp (hγ s.val)
  have hdd : ∀ t : Time, ∂ₜ (∂ₜ (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²))) t = !₂[0, 1] := by
    intro t; rw [hd]; exact hcomp (hδ t.val)
  have h0 : ∂ₜ (fun _ : Time => (0 : ℝ²)) = fun _ => 0 := funext fun s => Time.deriv_const 0
  have hc : ContDiff ℝ 2 (fun τ : ℝ => (!₂[0, τ ^ 2 / 2] : ℝ²)) := by
    refine contDiff_euclidean.mpr fun i => ?_
    fin_cases i
    · simpa using contDiff_const
    · simpa using (contDiff_id.pow 2).div_const 2
  refine ⟨?_, ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · ext i; fin_cases i <;> simp [Time.zero_val]
  · rw [hd, h0]; ext i; fin_cases i <;> simp [Time.zero_val]
  · rw [hdd, h0, Time.deriv_const]
    intro h
    have := congrArg (fun v : ℝ² => v 1) h
    simp at this
  · have hC : ContDiffAt ℝ 2 (fun s : Time => (!₂[0, s.val ^ 2 / 2] : ℝ²)) t :=
      (hc.comp (Time.val_contDiff (n := 2))).contDiffAt
    rw [eulerLagrangeOp_angleLagrangian 1 1 1 0 10 hC, hdd, hd]
    ext i; fin_cases i <;> simp [generalizedForce, massMatrix]
  · rw [eulerLagrangeOp_angleLagrangian 1 1 1 0 10 contDiffAt_const, h0, Time.deriv_const]
    ext i; fin_cases i <;> simp [generalizedForce, massMatrix]

/-! ## F. Reduced dynamics: consumers -/

/-- At the fixture state the reduced acceleration is `M(q₀)⁻¹ f(q₀, w₀)` for the invertible reduced
mass matrix. -/
example : (reducedAccel 2 1 1 2 10 !₂[Real.pi / 3, 0] !₂[1, 1]).ofLp =
    (massMatrix 2 1 1 2 (!₂[Real.pi / 3, 0] 0) (!₂[Real.pi / 3, 0] 1))⁻¹ *ᵥ
      (generalizedForce 2 1 1 2 10 !₂[Real.pi / 3, 0] !₂[1, 1]).ofLp :=
  reducedAccel_eq_inv_mulVec (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10 _ _

/-- The fixture parameters give a smooth and locally Lipschitz reduced field. -/
example : ContDiff ℝ ∞ (reducedField 2 1 1 2 10) ∧ LocallyLipschitz (reducedField 2 1 1 2 10) :=
  ⟨contDiff_reducedField (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10,
    locallyLipschitz_reducedField (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10⟩

/-- Local Picard existence from the fixture state `((π / 3, 0), (1, 1))` at time `0`. -/
example : ∃ ε > (0 : ℝ), ∃ α : ℝ → ℝ² × ℝ², α 0 = (!₂[Real.pi / 3, 0], !₂[1, 1]) ∧
    ∀ t ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt α (reducedField 2 1 1 2 10 (α t)) t :=
  exists_forall_mem_Ioo_hasDerivAt_reducedField (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 10 0 _

/-- Hanging at rest, `q ≡ (0, 0)` with `m = (2, 1)`, `l = (1, 2)` and `g = 10`: Newton's equations
with the rod multipliers `(-30, -5)` (tensions `30` and `10`) give the reduced ODE, and the reduced
ODE pins the multipliers to exactly `(-30, -5)`. -/
example (t : Time) :
    ∂ₜ (∂ₜ fun _ : Time => (0 : ℝ²)) t =
        reducedAccel 2 1 1 2 10 ((fun _ : Time => (0 : ℝ²)) t) (∂ₜ (fun _ : Time => (0 : ℝ²)) t) ∧
      ∀ c : ℝ × ℝ, ((2 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 fun _ => 0)) t).1,
          (1 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 fun _ => 0)) t).2) =
          gravityForce 2 1 10 + rodReaction c.1 c.2 (cartesianMotion 1 2 (fun _ => 0) t) ↔
        c = (-30, -5) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hC : ContDiffAt ℝ 2 (fun _ : Time => (0 : ℝ²)) t := contDiffAt_const
  have hP : cartesianMotion 1 2 (fun _ => 0) = fun _ => posMap 1 2 (0, 0) := by
    funext s; simp [cartesianMotion]
  have hA : ∂ₜ (∂ₜ (cartesianMotion 1 2 fun _ => 0)) t = 0 := by
    have h : ∂ₜ (fun _ : Time => posMap 1 2 (0, 0)) = fun _ => 0 :=
      funext fun s => Time.deriv_const _
    rw [hP, h, Time.deriv_const]
  have hN : ((2 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 fun _ => 0)) t).1,
      (1 : ℝ) • (∂ₜ (∂ₜ (cartesianMotion 1 2 fun _ => 0)) t).2) =
      gravityForce 2 1 10 + rodReaction (-30, -5).1 (-30, -5).2
        (cartesianMotion 1 2 (fun _ => 0) t) := by
    rw [hA, hP]
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
      simp [gravityForce, rodReaction, posMap, pos₁, pos₂] <;> norm_num
  have hode := (exists_rodReaction_newton_iff h2 h1 h1 h2 10 hC).mp ⟨(-30, -5), hN⟩
  refine ⟨hode, fun c => ⟨fun hc => ?_, fun hc => hc ▸ hN⟩⟩
  exact ((existsUnique_rodReaction_newton_iff h2 h1 h1 h2 10 hC).mpr hode).unique hc hN

end PhyslibExtTest.Mechanics.ConstrainedTwoLink
