/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.MrcaAge

/-! Tests for Patterson's MRCA-age functions: Appendix values and junk endpoint
values, the two branches of the killed Green's function at concrete frequencies,
the generator equations, the derivative jump, the dilog values, the integral
identities behind his Theorems 5(2) and 6(2), Corollary 1, the mixture, the
Taylor steps, and the eigen-instances. -/

open Real Set Filter
open scoped Topology

namespace DomainsTest.Biology.PopulationGenetics.Diffusion.MrcaAge

open MathlibExt.Biology.PopulationGenetics.Diffusion
open Domains.Biology.PopulationGenetics.Diffusion

/-- `a₂(1/2) = 1`. -/
example : pattersonAux2 (1 / 2) = 1 := by norm_num [pattersonAux2]

/-- Endpoint `a₁(1) = 1` by computation (Equation A6). -/
example : pattersonAux1 1 = 1 := by norm_num [pattersonAux1]

/-- Endpoint `a₂(1) = 0` by computation (Equation A8). -/
example : pattersonAux2 1 = 0 := by norm_num [pattersonAux2]

/-- Junk endpoint value: `a₁(0) = 2` in Lean, not the limit `0`. -/
example : pattersonAux1 0 = 2 := by simp [pattersonAux1]

/-- The limits at the two endpoints. -/
example : Tendsto pattersonAux1 (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_pattersonAux1_nhdsGT_zero

example : Tendsto pattersonAux1 (𝓝[<] (1 : ℝ)) (𝓝 1) :=
  tendsto_pattersonAux1_nhdsLT_one

/-- `a₁` is positive at an interior point. -/
example : 0 < pattersonAux1 (1 / 2) :=
  pattersonAux1_pos ⟨by norm_num, by norm_num⟩

/-- Equation A2 in generator form at `x = 1/2`, for both Appendix solutions. -/
example : generator 0 pattersonAux2 (1 / 2) = pattersonAux2 (1 / 2) / (1 / 2) :=
  pattersonAux2_ode ⟨by norm_num, by norm_num⟩

example : generator 0 pattersonAux1 (1 / 2) = pattersonAux1 (1 / 2) / (1 / 2) :=
  pattersonAux1_ode ⟨by norm_num, by norm_num⟩

/-- Below the diagonal the killed Green function is `2 a₁(x) / y²`. -/
example : killedGreen (1 / 4) (1 / 2) = (2 / (1 / 2) ^ 2) * pattersonAux1 (1 / 4) :=
  killedGreen_eq_aux_left (by norm_num) (by norm_num) (by norm_num)

/-- Above the diagonal it is `(2 a₁(y) / ((1 - y) y)) a₂(x)`. -/
example : killedGreen (3 / 4) (1 / 2) =
    (2 * pattersonAux1 (1 / 2) / ((1 - 1 / 2) * (1 / 2))) * pattersonAux2 (3 / 4) :=
  killedGreen_eq_aux_right (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The two Appendix solutions have Wronskian `-1` at an interior point. -/
example : GreenKernel.wronskian pattersonAux1 pattersonAux2 (1 / 2) = -1 :=
  pattersonAux_wronskian ⟨by norm_num, by norm_num⟩

/-- Patterson's kernel is the generic two-solution Green kernel below the diagonal. -/
example : killedGreen (1 / 4) (1 / 2) =
    GreenKernel.kernel pattersonAux1 pattersonAux2 (fun y => 2 / y ^ 2) (1 / 4) (1 / 2) :=
  killedGreen_eq_greenKernel ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- Patterson's kernel is the generic two-solution Green kernel above the diagonal. -/
example : killedGreen (3 / 4) (1 / 2) =
    GreenKernel.kernel pattersonAux1 pattersonAux2 (fun y => 2 / y ^ 2) (3 / 4) (1 / 2) :=
  killedGreen_eq_greenKernel ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- The killed Green function is positive at an interior point. -/
example : 0 < killedGreen (1 / 4) (1 / 2) :=
  killedGreen_pos ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- The killed backward equation off the diagonal, in generator form. -/
example : generator 0 (fun x => killedGreen x (1 / 2)) (1 / 4) =
    killedGreen (1 / 4) (1 / 2) / (1 / 4) :=
  killedGreen_ode_lt ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num)

example : generator 0 (fun x => killedGreen x (1 / 2)) (3 / 4) =
    killedGreen (3 / 4) (1 / 2) / (3 / 4) :=
  killedGreen_ode_gt ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num)

/-- One-sided derivative at the diagonal from the left. -/
example : HasDerivWithinAt (fun x => killedGreen x (1 / 2))
    ((2 / (1 / 2) ^ 2) * (-1 - 2 * (log (1 - 1 / 2) + 1 / 2) / (1 / 2) ^ 2))
    (Iic (1 / 2)) (1 / 2) :=
  hasDerivWithinAt_killedGreen_Iic ⟨by norm_num, by norm_num⟩

/-- One-sided derivative at the diagonal from the right. -/
example : HasDerivWithinAt (fun x => killedGreen x (1 / 2))
    ((2 * pattersonAux1 (1 / 2) / ((1 - 1 / 2) * (1 / 2))) * (-1 / (1 / 2) ^ 2))
    (Ici (1 / 2)) (1 / 2) :=
  hasDerivWithinAt_killedGreen_Ici ⟨by norm_num, by norm_num⟩

/-- The derivative jump at the diagonal `y = 1 / 2` is `-2 / (y (1 - y)) = -8`. -/
example : derivWithin (fun x => killedGreen x (1 / 2)) (Ici (1 / 2)) (1 / 2) -
      derivWithin (fun x => killedGreen x (1 / 2)) (Iic (1 / 2)) (1 / 2) = -8 := by
  rw [killedGreen_deriv_jump (y := 1 / 2) ⟨by norm_num, by norm_num⟩]
  norm_num

/-- Continuity across the diagonal and the two boundary values. -/
example : ContinuousAt (fun x => killedGreen x (1 / 2)) (1 / 2) :=
  continuousAt_killedGreen_diagonal ⟨by norm_num, by norm_num⟩

example : Tendsto (fun x => killedGreen x (1 / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_killedGreen_zero ⟨by norm_num, by norm_num⟩

example : Tendsto (fun x => killedGreen x (1 / 2)) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
  tendsto_killedGreen_one ⟨by norm_num, by norm_num⟩

/-- The boundary ratio of Equation 14: `G_C(1 - ε, 1/2) / (2ε)` has the stated
limit in terms of `a₁(1/2)`. -/
example : Tendsto (fun ε => killedGreen (1 - ε) (1 / 2) / (2 * ε)) (𝓝[>] (0 : ℝ))
    (𝓝 (pattersonAux1 (1 / 2) / ((1 - 1 / 2) * (1 / 2)))) :=
  tendsto_killedGreen_one_sub_div ⟨by norm_num, by norm_num⟩

/-- Theorem 5(2)'s analytic identity at `y = 1/2`. -/
example : (1 / 2) * (1 - 1 / 2) *
      (∫ x in (0 : ℝ)..1, killedGreen x (1 / 2) / (x * (1 - x))) +
    pattersonAux1 (1 / 2) = 1 / 2 :=
  killedGreen_weighted_integral_add_pattersonAux1 ⟨by norm_num, by norm_num⟩

/-- Patterson's `dilog 1 = 0`. -/
example : pattersonDilog 1 = 0 := pattersonDilog_one

/-- The dilog derivative at an interior point. -/
example : HasDerivAt pattersonDilog (log (1 / 2) / (1 - 1 / 2)) (1 / 2) :=
  hasDerivAt_pattersonDilog ⟨by norm_num, by norm_num⟩

/-- The dilog limit at `1` from below. -/
example : Tendsto pattersonDilog (𝓝[<] (1 : ℝ)) (𝓝 0) :=
  tendsto_pattersonDilog_nhdsLT_one

/-- On `(0, 1)`, the `Real.li2PowerSeries` definition agrees with Patterson's integral
definition, here at `1 / 2`. -/
example : pattersonDilog (1 / 2) =
    ∫ t in (1 : ℝ)..(1 / 2), log t / (1 - t) :=
  pattersonDilog_eq_integral ⟨by norm_num, by norm_num⟩

/-- The Basel value `dilog 0 = π² / 6`. -/
example : pattersonDilog 0 = π ^ 2 / 6 := pattersonDilog_zero

/-- The Euler reflection identity at `y = 1/2`. -/
example : pattersonDilog (1 / 2) + pattersonDilog (1 - 1 / 2) +
    log (1 / 2) * log (1 - 1 / 2) = π ^ 2 / 6 :=
  pattersonDilog_reflection ⟨by norm_num, by norm_num⟩

/-- Corollary 1 at frequency `1 / 2` with `ε = 1 / 4`: the old-allele posterior is
`1 / 2`. -/
example : neutralGreen (1 - 1 / 4) (1 / 2) /
      (neutralGreen (1 / 4) (1 / 2) + neutralGreen (1 - 1 / 4) (1 / 2)) = 1 / 2 :=
  neutralGreen_old_ratio_eq (by norm_num) (by norm_num) (by norm_num)

/-- Equation 16 at `y = 1/2`, as the integral of Theorem 4's Green function. -/
example : meanMrcaNew (1 / 2) =
    (1 / 2) * ∫ x in (0 : ℝ)..1, killedGreen x (1 / 2) / x :=
  meanMrcaNew_eq_integral ⟨by norm_num, by norm_num⟩

/-- The mixture identity (Equation 17 rearranged) at frequency `1 / 2`. -/
example : (1 - 1 / 2) * meanMrcaNew (1 / 2) + (1 / 2) * meanMrcaOld (1 / 2) =
    1 / 2 :=
  meanMrca_mixture ⟨by norm_num, by norm_num⟩

/-- The limit of `M₁` at frequency `1` (p. 1094, item 6). -/
example : Tendsto meanMrcaNew (𝓝[<] (1 : ℝ)) (𝓝 (2 * (π ^ 2 - 9) / 3)) :=
  tendsto_meanMrcaNew_one

/-- Junk endpoint value: `M₁(1) = 2π² / 3 - 4` in Lean, which is `2` more than
the limit above (the term `2 log 1 / (1 - 1)` totalizes to `0`, not `-2`). -/
example : meanMrcaNew 1 = 2 * π ^ 2 / 3 - 4 := by
  simp [meanMrcaNew, pattersonDilog_one]
  ring

/-- Endpoint `M₂(1) = 1` by computation. -/
example : meanMrcaOld 1 = 1 := by simp [meanMrcaOld]

/-- Patterson's Corollary 3 one-step computation at `x = 1 / 2`. -/
example : pattersonTaylorStep (fun x => (1 / 3) / x ^ 2) (1 / 2) = 0 :=
  pattersonTaylorStep_new ⟨by norm_num, by norm_num⟩

/-- Patterson's Corollary 4 one-step computation at `x = 1 / 2`, `y = 1 / 3`. -/
example : pattersonTaylorStep
      (fun x => (1 / 3) * (1 - 1 / 3) / (x ^ 2 * (1 - x))) (1 / 2) =
    -((1 / 3) * (1 - 1 / 3) / ((1 / 2) ^ 2 * (1 - 1 / 2))) :=
  pattersonTaylorStep_unknown ⟨by norm_num, by norm_num⟩

/-- The `k = 2`, `n = 0` eigen-instance of Theorem 1 at `x = 1/2`. -/
example : ((1 : ℝ) - 3 * (1 / 2)) * ((1 / 2) ^ 2 * (1 - 1 / 2)) =
    (1 / 2) ^ 2 * (1 - 1 / 2) / 2 *
      deriv (deriv (fun x => x ^ 2 * (1 - x))) (1 / 2) :=
  eigeninstance_two_zero (1 / 2)

/-- The `k = 2`, `n = 1` eigen-instance at `x = 1/2`. -/
example : ((1 : ℝ) - 6 * (1 / 2)) * ((1 / 2) ^ 2 * (1 - 1 / 2) * (6 * (1 / 2) - 4)) =
    (1 / 2) ^ 2 * (1 - 1 / 2) / 2 *
      deriv (deriv (fun x => x ^ 2 * (1 - x) * (6 * x - 4))) (1 / 2) :=
  eigeninstance_two_one (1 / 2)

/-- The `k = 2`, `n = 2` eigen-instance at `x = 1/2`. -/
example : ((1 : ℝ) - 10 * (1 / 2)) *
      ((1 / 2) ^ 2 * (1 - 1 / 2) * (28 * (1 / 2) ^ 2 - 35 * (1 / 2) + 10)) =
    (1 / 2) ^ 2 * (1 - 1 / 2) / 2 * deriv
      (deriv (fun x => x ^ 2 * (1 - x) * (28 * x ^ 2 - 35 * x + 10))) (1 / 2) :=
  eigeninstance_two_two (1 / 2)

end DomainsTest.Biology.PopulationGenetics.Diffusion.MrcaAge
