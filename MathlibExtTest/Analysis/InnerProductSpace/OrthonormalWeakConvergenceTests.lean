/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.OrthonormalWeakConvergence
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

open Filter Topology
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.OrthonormalWeakConvergence

namespace MathlibExtTest.Analysis.InnerProductSpace.OrthonormalWeakConvergence

/-!
# Tests for weak convergence of orthonormal sequences

The abstract examples check the theorems on a hypothetical orthonormal
family. The final example is the vacuity check: the canonical Hilbert basis
of `ℓ²(ℕ, ℂ)` is a concrete orthonormal sequence, it converges weakly to `0`
but not strongly, and its Fourier coefficients against any fixed vector
tend to `0`.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Fourier coefficients along an orthonormal family tend to `0` along the
cofinite filter (general index type). -/
example {ι : Type*} {v : ι → H} (hv : Orthonormal 𝕜 v) (x : H) :
    Tendsto (fun i => ⟪v i, x⟫_𝕜) cofinite (𝓝 0) :=
  tendsto_inner_cofinite_zero hv x

/-- Fourier coefficients along an orthonormal sequence tend to `0`. -/
example {v : ℕ → H} (hv : Orthonormal 𝕜 v) (x : H) :
    Tendsto (fun n => ⟪v n, x⟫_𝕜) atTop (𝓝 0) :=
  tendsto_inner_atTop_zero hv x

/-- Every continuous linear functional kills an orthonormal sequence in the
limit. -/
example [CompleteSpace H] {v : ℕ → H} (hv : Orthonormal 𝕜 v)
    (f : H →L[𝕜] 𝕜) :
    Tendsto (fun n => f (v n)) atTop (𝓝 0) :=
  tendsto_apply_atTop_zero hv f

/-- An orthonormal sequence does not converge to `0` in norm. -/
example {v : ℕ → H} (hv : Orthonormal 𝕜 v) : ¬ Tendsto v atTop (𝓝 0) :=
  not_tendsto_atTop_zero hv

/-- The canonical Hilbert basis of `ℓ²(ℕ, ℂ)` is a concrete orthonormal
sequence converging weakly, but not strongly, to `0`. -/
example :
    ∃ v : ℕ → lp (fun _ : ℕ => ℂ) 2,
      Orthonormal ℂ v ∧
        (∀ x : lp (fun _ : ℕ => ℂ) 2,
          Tendsto (fun n => ⟪v n, x⟫_ℂ) atTop (𝓝 0)) ∧
        (∀ f : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ,
          Tendsto (fun n => f (v n)) atTop (𝓝 0)) ∧
        ¬ Tendsto v atTop (𝓝 0) := by
  let b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) := default
  have hb : Orthonormal ℂ (⇑b : ℕ → lp (fun _ : ℕ => ℂ) 2) :=
    HilbertBasis.orthonormal b
  exact ⟨⇑b, hb, fun x => tendsto_inner_atTop_zero hb x,
    fun f => tendsto_apply_atTop_zero hb f, not_tendsto_atTop_zero hb⟩
