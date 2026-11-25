/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjoint

/-! # Tests for `MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjoint` -/

namespace MathlibExtTest.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjoint

open Filter Topology
open MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted

section General

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

-- A constant sequence converges strongly, hence in both weak senses.
example (T : H →L[𝕜] H) (x y : H) :
    Tendsto (fun _ : ℕ => inner 𝕜 y ((T.adjoint.comp T) x)) atTop
      (𝓝 (inner 𝕜 y ((T.adjoint.comp T) x))) :=
  ((tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp (fun _ => T) T).1
    fun _ => tendsto_const_nhds).2 x y

-- The multiples `cₙ • T`, with `cₙ = 1 + 1 / (n + 1)`, tend to `T` strongly, so
-- `(cₙ • T)† (cₙ • T)` tends to `T† T` weakly.
example (T : H →L[𝕜] H) (x y : H) :
    Tendsto (fun n : ℕ => inner 𝕜 y
        ((((1 + 1 / ((n : 𝕜) + 1)) • T).adjoint.comp ((1 + 1 / ((n : 𝕜) + 1)) • T)) x))
      atTop (𝓝 (inner 𝕜 y ((T.adjoint.comp T) x))) := by
  refine ((tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp _ T).1
    fun x => ?_).2 x y
  have hc : Tendsto (fun n : ℕ => 1 + 1 / ((n : 𝕜) + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : 𝕜)
  simpa using hc.smul_const (T x)

-- The identity: weak convergence of the constant sequence `1` gives strong convergence.
example (x : H) : Tendsto (fun _ : ℕ => (1 : H →L[𝕜] H) x) atTop (𝓝 ((1 : H →L[𝕜] H) x)) :=
  (tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp _ _).2
    ⟨fun _ _ => tendsto_const_nhds, fun _ _ => tendsto_const_nhds⟩ x

-- For isometries, `Tn n† Tn n = 1 = T† T`, so weak convergence alone gives strong convergence.
example (Tn : ℕ → H →L[𝕜] H) (T : H →L[𝕜] H) (hTn : ∀ n, (Tn n).adjoint.comp (Tn n) = 1)
    (hT : T.adjoint.comp T = 1)
    (hw : ∀ x y : H, Tendsto (fun n => inner 𝕜 y (Tn n x)) atTop (𝓝 (inner 𝕜 y (T x))))
    (x : H) : Tendsto (fun n => Tn n x) atTop (𝓝 (T x)) :=
  (tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp Tn T).2
    ⟨hw, fun x y => by simp only [hTn, hT]; exact tendsto_const_nhds⟩ x

end General

-- On `ℂ` over `ℂ`, multiplication by `(n + 1)⁻¹` tends to `0` strongly, so
-- `⟪y, Tn n† (Tn n x)⟫` tends to `⟪y, 0† (0 x)⟫ = 0`.
example (x y : ℂ) :
    Tendsto (fun n : ℕ => inner ℂ y
        (((((n : ℂ) + 1)⁻¹ • (1 : ℂ →L[ℂ] ℂ)).adjoint.comp
          (((n : ℂ) + 1)⁻¹ • (1 : ℂ →L[ℂ] ℂ))) x))
      atTop (𝓝 0) := by
  have h := ((tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp
    (fun n : ℕ => ((n : ℂ) + 1)⁻¹ • (1 : ℂ →L[ℂ] ℂ)) 0).1 fun x => ?_).2 x y
  · simpa using h
  · simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).mul_const x

-- Over `ℝ`, on `ℝ`: the operators `cₙ • 1`, with `cₙ = 1 + 1 / (n + 1)`, tend to `1` strongly,
-- so `⟪y, (cₙ • 1)† ((cₙ • 1) x)⟫` tends to `⟪y, 1† (1 x)⟫ = y * x`.
example (x y : ℝ) :
    Tendsto (fun n : ℕ => inner ℝ y
        ((((1 + 1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)).adjoint.comp
          ((1 + 1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ))) x))
      atTop (𝓝 (y * x)) := by
  have h := ((tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp
    (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) 1).1 fun x => ?_).2 x y
  · simpa [ContinuousLinearMap.adjoint_one, mul_comm] using h
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)).mul_const x

end MathlibExtTest.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjoint
