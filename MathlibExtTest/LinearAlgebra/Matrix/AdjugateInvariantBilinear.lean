/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.AdjugateInvariantBilinear

@[expose] public section

open Matrix

universe u

/-- Source consumer (with the original trace hypothesis), derived from
the stronger theorem without that hypothesis; generalized to a higher
universe. -/
example {k : Type u} [Field k] (μ : Matrix (Fin 2) (Fin 2) k)
    (htr : μ.trace = 0) (hdet : μ.det ≠ 0)
    (b : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k)
    (hb : ∀ (x : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k),
      b (x.mulVec v) w = b v ((μ⁻¹ * x.adjugate * μ).mulVec w)) :
    ∃ c : k, ∀ v w : Fin 2 → k,
      b v w = c * dotProduct v ((!![0, 1; -1, 0] * μ).mulVec w) :=
  exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq μ
    hdet b hb

/-- Boundary: the zero bilinear form satisfies the invariance hypothesis
with scalar `0`. -/
example (μ : Matrix (Fin 2) (Fin 2) ℚ) (htr : μ.trace = 0) (hdet : μ.det ≠ 0) :
    ∃ c : ℚ, ∀ v w : Fin 2 → ℚ,
      (0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ) v w =
        c * dotProduct v ((!![0, 1; -1, 0] * μ).mulVec w) :=
  exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq μ
    hdet 0 (by simp)
