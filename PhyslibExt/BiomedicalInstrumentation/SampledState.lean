/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

/-!
# Sampled-state observability

## i. Overview

For known homogeneous dynamics `x(t) = exp (tA) x0` and known output `H`, initial-state information in noiseless samples is exactly injectivity of the stacked finite map at the sampling times. Dynamic observability does not ensure every finite sample design has full rank; the jet stack `H, HA, ...` is a different object.

## ii. Key results

* `sampled_injective_iff`: the stacked sampled map is injective exactly when only the zero state produces zero at every sample.

## iii. Table of contents

* A. Sampled-state criterion.

## iv. References

* The declared dynamics are local to this module; no literature result is claimed, so the declaration is a `lemma`.

-/

@[expose] public section

open scoped Matrix

/-! ## A. Sampled-state criterion. -/

namespace PhyslibExt.BiomedicalInstrumentation.SampledState

/-- The bundled sampled-state operator: the stacked output map as
a linear map via `Matrix.mulVecLin`. -/
noncomputable def sampledMap {n m k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin k) (Fin n) ℝ) (t : Fin m → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → Fin k → ℝ) :=
  LinearMap.pi (fun j => (Matrix.mulVecLin H).comp
    (Matrix.mulVecLin
      (NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ)))

/-- The bundled operator applied. -/
lemma sampledMap_apply {n m k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin k) (Fin n) ℝ) (t : Fin m → ℝ) (x : Fin n → ℝ) :
    sampledMap A H t x = fun j => H *ᵥ
      ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) := by
  funext j
  simp [sampledMap, Matrix.mulVecLin_apply]

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
    Function.Injective (sampledMap A H t) ↔
    ∀ x : Fin n → ℝ, (∀ j, H *ᵥ
      ((NormedSpace.exp (t j • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = 0) →
      x = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx
    have : sampledMap A H t x = 0 := by
      funext j
      rw [sampledMap_apply]
      exact hx j
    exact h x this
  · intro h x hx
    apply h
    intro j
    have := congrFun hx j
    rwa [sampledMap_apply] at this

end PhyslibExt.BiomedicalInstrumentation.SampledState
