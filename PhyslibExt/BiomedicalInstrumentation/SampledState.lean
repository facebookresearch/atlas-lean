/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix

/-!
# Sampled-state observability

For known homogeneous dynamics `x(t) = exp (tA) x0` and known output
`H`, initial-state information in noiseless samples is exactly
injectivity of the stacked finite map at the sampling times.
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExt.BiomedicalInstrumentation.SampledState

/-- **Sampled-state observability criterion.** For known dynamics
`A`, output matrix `H`, and fixed sampling times `t j`, the stacked
sampled map `x ↦ (H *ᵥ (exp (t j • A) *ᵥ x))_j` is injective exactly
when the only state producing zero at every sample is zero: initial
state information in noiseless samples is exactly injectivity of
the stacked finite map. This contrasts with the jet stack
`H, H A, ...`: instantaneous noninjectivity of `H` does not by
itself rule out dynamical recovery. -/
lemma sampled_injective_iff {n m k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin k) (Fin n) ℝ) (t : Fin m → ℝ) :
    Function.Injective
      (fun x => fun j => H *ᵥ ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) ↔
    ∀ x : Fin n → ℝ, (∀ j, H *ᵥ ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = 0) →
      x = 0 := by
  constructor
  · intro hinj x hx
    have hf0 : (fun x : Fin n → ℝ => fun j => H *ᵥ
        ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) 0 = 0 := by
      funext j
      simp only [Matrix.mulVec_zero, Pi.zero_apply]
    have hfx : (fun x : Fin n → ℝ => fun j => H *ᵥ
        ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) x = 0 := by
      funext j
      exact hx j
    exact hinj (hfx.trans hf0.symm)
  · intro hker x y hxy
    have hsub : x - y = 0 := by
      apply hker
      intro j
      have hj : H *ᵥ ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)
          = H *ᵥ ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) :=
        congrFun hxy j
      simp only [Matrix.mulVec_sub, hj, sub_self]
    exact sub_eq_zero.mp hsub

end PhyslibExt.BiomedicalInstrumentation.SampledState
