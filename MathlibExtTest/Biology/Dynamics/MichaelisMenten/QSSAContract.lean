/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.MichaelisMenten.QSSAContract
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Tests for the Michaelis–Menten QSSA contract: concrete values of the small parameter `ε`
(small and not small), the time-scale separation, the algebraic QSSA relation, the initial-layer
gap, and a non-vacuity check showing that every premise of `QSSAContract` can be met on a
concrete parameter set. -/

open Set

namespace MathlibExtTest.Biology.Dynamics.MichaelisMenten.QSSAContract

open MathlibExt.Biology.Dynamics.MichaelisMenten

/-! ### Smoke test and the small parameter -/

/-- Smoke test: `k₁ = kb = k₂ = 1`, so `K_M = 2`; with `s₀ = 98`, `e₀ = 1` we get `ε = 1/100`.
Small. -/
example : qssaEpsilon 1 1 1 98 1 = 1 / 100 := by
  norm_num [qssaEpsilon, michaelisConstant]

/-- Not small: `s₀ = 1`, `e₀ = 3`, `K_M = 2` give `ε = 1`. -/
example : qssaEpsilon 1 1 1 1 3 = 1 := by
  norm_num [qssaEpsilon, michaelisConstant]

/-- Not small: `e₀ = s₀ = 1`, `K_M = 2` give `ε = 1/3`. -/
example : 1 / 4 < qssaEpsilon 1 1 1 1 1 := by
  norm_num [qssaEpsilon, michaelisConstant]

/-- The Segel–Slemrod parameter can be small when the Heineken–Tsuchiya–Aris parameter `e₀/s₀`
is not: `e₀ = s₀ = 1`, `kb = 999`, so `K_M = 1000` and `ε = 1/1001`, while `e₀ / s₀ = 1`. -/
example : qssaEpsilon 1 999 1 1 1 = 1 / 1001 := by
  norm_num [qssaEpsilon, michaelisConstant]

example : qssaEpsilon 1 1 1 98 1 < 1 / 98 :=
  qssaEpsilon_lt_div one_pos zero_le_one one_pos (by norm_num) one_pos

/-- Dimensionless: rescaling all concentrations (`s₀`, `e₀`, and `K_M` through `k₁`) by `10`
leaves `ε` unchanged. -/
example : qssaEpsilon (1 / 10) 1 1 980 10 = qssaEpsilon 1 1 1 98 1 := by
  norm_num [qssaEpsilon, michaelisConstant]

/-! ### Time scales -/

/-- With `s₀ = 98`, `e₀ = 1`: `t_C = 1/100` and `t_S = 100`. -/
example : fastTimeScale 1 1 1 98 = 1 / 100 ∧ slowTimeScale 1 1 1 98 1 = 100 := by
  norm_num [fastTimeScale, slowTimeScale, michaelisConstant]

example : fastTimeScale 1 1 1 98 / slowTimeScale 1 1 1 98 1 < qssaEpsilon 1 1 1 98 1 :=
  fastTimeScale_div_slowTimeScale_lt one_pos zero_le_one one_pos (by norm_num) one_pos

/-! ### The algebraic QSSA relation -/

/-- `κ = K_M / s₀ = 2`, so `du/dθ = -3 u / (2 + u)`, which is `-1` at `u = 1`. -/
example : reducedField 1 1 1 1 1 = -1 := by
  norm_num [reducedField, mmRate, qssaKappa, michaelisConstant]

example : slowManifold 1 1 1 1 1 = 1 / 3 := by
  norm_num [slowManifold, qssaKappa, michaelisConstant]

/-- The reduced field is what substituting the slow manifold into `s'` gives. -/
example : slowTimeScale 1 1 1 1 (1 / 100) / 1 *
    substrateRate 1 1 (1 * 1) (qssComplex 1 1 1 (1 / 100) (1 * 1))
      (1 / 100 - qssComplex 1 1 1 (1 / 100) (1 * 1)) = -1 := by
  rw [slowTimeScale_mul_substrateRate_qss one_pos one_ne_zero one_ne_zero (by norm_num)
    (by norm_num [michaelisConstant])]
  norm_num [reducedField, mmRate, qssaKappa, michaelisConstant]

/-- The full solution starts off the manifold: `c'(0) = k₁ e₀ s₀ = 1/100`. -/
example : complexRate 1 1 1 1 0 (1 / 100 - 0) = 1 / 100 := by
  norm_num [complexRate]

/-! ### Initial layer -/

/-- At `θ = 0` the outer complex error is `1/(1 + κ) = 1/3`, independent of `e₀`. -/
example (e₀ : ℝ) (c u : ℝ → ℝ) (hc : c 0 = 0) (hu : u 0 = 1) :
    |c (slowTimeScale 1 1 1 1 e₀ * 0) / e₀ - slowManifold 1 1 1 1 (u 0)| = 1 / 3 := by
  rw [initialLayer_gap hc hu (qssaKappa_pos one_pos zero_le_one one_pos one_pos)]
  norm_num [qssaKappa, michaelisConstant]

/-- With `C = 1` and `e₀ = 1/100` (`ε = 1/300`) the outer complex bound fails at `θ = 0`. -/
example (c u : ℝ → ℝ) (hc : c 0 = 0) (hu : u 0 = 1) :
    ¬ |c (slowTimeScale 1 1 1 1 (1 / 100) * 0) / (1 / 100) - slowManifold 1 1 1 1 (u 0)| ≤
      1 * qssaEpsilon 1 1 1 1 (1 / 100) :=
  not_complex_le_at_zero hc hu (qssaKappa_pos one_pos zero_le_one one_pos one_pos)
    (by norm_num [qssaEpsilon, qssaKappa, michaelisConstant])

/-! ### Non-vacuity of the contract's premises -/

/-- The full Michaelis–Menten vector field in `(s, c)` with `k₁ = kb = k₂ = 1`, total enzyme
`e₀ = 1/100`. -/
noncomputable def fullField (x : ℝ × ℝ) : ℝ × ℝ :=
  (substrateRate 1 1 x.1 x.2 (1 / 100 - x.2), complexRate 1 1 1 x.1 x.2 (1 / 100 - x.2))

lemma contDiff_fullField : ContDiff ℝ 1 fullField := by
  unfold fullField substrateRate complexRate
  fun_prop

lemma contDiffAt_reducedField : ContDiffAt ℝ 1 (reducedField 1 1 1 1) 1 := by
  have h : qssaKappa 1 1 1 1 = 2 := by norm_num [qssaKappa, michaelisConstant]
  unfold reducedField mmRate
  rw [h]
  fun_prop (disch := norm_num)

/-- **Non-vacuity.** On the parameter set `k₁ = kb = k₂ = 1`, `s₀ = 1`, `e₀ = 1/100`
(`ε = 1/300`), there is a slow-time horizon `T > 0` for which every premise of
`QSSAContract 1 1 1 1 T` holds: the parameters are admissible, a reduced solution exists on
`[0, T]`, and a full solution with `s(0) = 1`, `c(0) = 0` exists on `[0, t_S T]`.

The horizon `T` comes from local Picard–Lindelöf and is short. For a given `T` (say `T = 1`)
this file exhibits no reduced or full solution on the window; that would need global existence
of ODE solutions, which Mathlib does not provide. Until then `QSSAContract 1 1 1 1 1` is not
shown to be non-vacuous. -/
theorem contract_premises_satisfiable :
    (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
      qssaEpsilon 1 1 1 1 (1 / 100) = 1 / 300 ∧
      ∃ T > 0, (∃ u, IsReducedSolutionOn 1 1 1 1 T u) ∧
        ∃ s c : ℝ → ℝ, IsSolutionOn 1 1 1 (1 / 100) (slowTimeScale 1 1 1 1 (1 / 100) * T) s c ∧
          s 0 = 1 ∧ c 0 = 0 := by
  refine ⟨one_pos, zero_le_one, one_pos, one_pos,
    by norm_num [qssaEpsilon, michaelisConstant], ?_⟩
  obtain ⟨u, hu0, η₁, hη₁, hu⟩ :=
    contDiffAt_reducedField.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  obtain ⟨α, hα0, η₂, hη₂, hα⟩ :=
    (contDiff_fullField.contDiffAt (x := ((1 : ℝ), (0 : ℝ)))
      ).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have htS : slowTimeScale 1 1 1 1 (1 / 100) = 300 := by
    norm_num [slowTimeScale, michaelisConstant]
  set T := min η₁ (η₂ / 300) / 2 with hT
  have hT0 : 0 < T := by positivity
  have hT1 : T < η₁ := by
    have := min_le_left η₁ (η₂ / 300); linarith
  have hT2 : 300 * T < η₂ := by
    have := min_le_right η₁ (η₂ / 300); linarith
  refine ⟨T, hT0, ⟨u, hu0, fun θ hθ ↦ hu θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩,
    fun t ↦ (α t).1, fun t ↦ (α t).2, ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩, by simp [hα0],
    by simp [hα0]⟩
  all_goals
    rw [htS] at ht
    have hd := hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact (hasFDerivAt_fst.comp_hasDerivAt t hd :)
  · exact (hasFDerivAt_snd.comp_hasDerivAt t hd :)

end MathlibExtTest.Biology.Dynamics.MichaelisMenten.QSSAContract
