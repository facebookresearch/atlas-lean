/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.ODE.CompactSublevel

open Set MathlibExt.Analysis.ODE

-- Cubic growth near zero is allowed: only the outer level needs strict decay.
example : ∃ x : ℝ → ℝ, x 0 = 1 / 2 ∧
    (∀ t ∈ Ici 0, x t ^ 2 ≤ 4) ∧
    ∀ t ∈ Ici 0, HasDerivAt x (x t - x t ^ 3) t := by
  have hcompact : IsCompact {x : ℝ | x ^ 2 ≤ 4} := by
    have heq : {x : ℝ | x ^ 2 ≤ 4} = Icc (-2) 2 := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc]
      constructor
      · intro h
        constructor <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2)]
      · rintro ⟨hl, hu⟩
        nlinarith
    rw [heq]
    exact isCompact_Icc
  have hF : ContDiff ℝ 1 (fun x : ℝ => x - x ^ 3) := by fun_prop
  apply exists_forward_solution_of_compact_sublevel
    hF.locallyLipschitz (V := fun x : ℝ => x ^ 2)
    (by fun_prop) hcompact (a := 0) (x₀ := 1 / 2) (by norm_num)
  intro x hx
  rw [(hasDerivAt_pow 2 x).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_eq_mul]
  rw [show x ^ 3 = x * x ^ 2 by ring, hx]
  nlinarith [hx]

-- The strict-boundary example really has positive orbital derivative inside.
example : 0 < fderiv ℝ (fun x : ℝ => x ^ 2) (1 / 2)
    ((1 / 2 : ℝ) - (1 / 2 : ℝ) ^ 3) := by
  rw [(hasDerivAt_pow 2 (1 / 2 : ℝ)).hasFDerivAt.fderiv]
  norm_num

-- Nonpositive decay permits a zero-width sublevel and a conserved energy.
example (a : ℝ) : ∃ x : ℝ → ℝ, x a = 0 ∧
    (∀ t ∈ Ici a, x t ^ 2 ≤ 0) ∧
    ∀ t ∈ Ici a, HasDerivAt x 0 t := by
  have hF : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) := contDiff_const
  have hK : IsCompact {y : ℝ | y ^ 2 ≤ 0} := by
    have heq : {y : ℝ | y ^ 2 ≤ 0} = {0} := by
      ext y
      simp [sq_nonpos_iff]
    rw [heq]
    exact isCompact_singleton
  exact exists_forward_solution_of_compact_sublevel_nonpos
    hF.locallyLipschitz (by fun_prop) hK a (by norm_num)
    (by intro y; simp)

#print axioms MathlibExt.Analysis.ODE.mapsTo_sublevel_of_boundary_deriv_neg
#print axioms MathlibExt.Analysis.ODE.exists_forward_solution_of_compact_sublevel
#print axioms MathlibExt.Analysis.ODE.exists_forward_solution_of_compact_sublevel_nonpos
