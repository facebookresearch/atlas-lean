/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.RoughPath

@[expose] public section

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.RoughPath

/-- Non-vacuity: the signature of the unit-speed path in `ℝ²` along `e₀ + e₁` is a multiplicative
functional of degree `3` on `[0, 1]` with finite `1`-variation in degree `3`. -/
example : IsMultiplicativeFunctional 3 (signature fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ))
      (Set.Icc 0 1) ∧
    HasFinitePVariation 1 3 (signature fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ)) (Set.Icc 0 1) :=
  ⟨isMultiplicativeFunctional_signature (fun _ _ _ => intervalIntegrable_const) 3 _,
    hasFinitePVariation_signature (fun _ => continuous_const) 3 _⟩

/-- The factorial bound at level `2` for that path: `‖S²_{0,t}‖₁ ≤ (2t)² / 2!`. -/
example (t : ℝ) (ht : 0 ≤ t) :
    levelNorm (signature (fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ)) 0 t) 2 ≤ (2 * t) ^ 2 / 2 := by
  have h := levelNorm_signature_le (v := fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ))
    (fun _ => continuous_const) ht 2
  simpa [mul_comm] using h

/-- The time increment `ω(s, t) = t − s` is a control. -/
example : IsControl (fun s t => t - s) Set.univ := by
  refine ⟨(continuous_snd.sub continuous_fst).continuousOn, fun t _ => sub_self t,
    fun s _ t _ h => sub_nonneg.mpr h, fun s _ t _ u _ _ _ => ?_⟩
  linarith

end MathlibExtTest.Analysis.PathSignature.RoughPath
