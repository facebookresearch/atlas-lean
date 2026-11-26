/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.HyperbolicShadowing
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace MathlibExtTest.Dynamics.HyperbolicShadowing

open MathlibExt.Dynamics.HyperbolicShadowingWanted.Dynamics.HyperbolicShadowingProblem

private noncomputable def doubling : E 1 ≃ₜ E 1 :=
  Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num)

-- The fixed point is purely expanding. Its inverse contracts every vector by one half.
private theorem doubling_hyperbolic : IsHyperbolic doubling {0} := by
  have hD (r : ℝ) (x : E 1) :
      fderiv ℝ (fun y : E 1 => r • y) x = r • ContinuousLinearMap.id ℝ (E 1) :=
    ((hasFDerivAt_id x).const_smul r).fderiv
  refine ⟨{
    contDiff_fwd := contDiff_id.const_smul (2 : ℝ)
    contDiff_bwd := contDiff_id.const_smul (2 : ℝ)⁻¹
    invariant := by simp [doubling]
    stable := fun _ => ⊥
    unstable := fun _ => ⊤
    isCompl_stable_unstable := fun _ _ => isCompl_bot_top
    stable_invariant := fun _ _ => Submodule.map_bot _
    unstable_invariant := ?_
    rate := (2 : ℝ)⁻¹
    rate_pos := by norm_num
    rate_lt_one := by norm_num
    const := 1
    const_pos := one_pos
    contract_stable := ?_
    contract_unstable := ?_
  }⟩
  · intro x _
    change (⊤ : Submodule ℝ (E 1)).map (fderiv ℝ (fun y : E 1 => (2 : ℝ) • y) x).toLinearMap = ⊤
    rw [hD, Submodule.map_top, LinearMap.range_eq_top]
    intro v
    exact ⟨(2 : ℝ)⁻¹ • v, by simp [smul_smul]⟩
  · intro x _ v hv n
    obtain rfl : v = 0 := by simpa using hv
    simp
  · intro x _ v _ n
    change ‖fderiv ℝ ((fun y : E 1 => (2 : ℝ)⁻¹ • y)^[n]) x v‖ ≤ _
    rw [smul_iterate, hD]
    simp [norm_smul]

example : HasShadowing doubling ({0} : Set (E 1)) :=
  hyperbolic_has_shadowing doubling {0} isCompact_singleton doubling_hyperbolic

-- A constant sequence has jump size exactly ‖v‖, including at the fixed point v = 0.
example (v : E 1) (ε : ℝ) : IsPseudoOrbit doubling ε (fun _ => v) ↔ ‖v‖ < ε := by
  simp [IsPseudoOrbit, doubling, two_smul]

end MathlibExtTest.Dynamics.HyperbolicShadowing
