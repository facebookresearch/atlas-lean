/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.BehaviorTree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Finite-time success for a sampled tree

The attraction region consists of running states. There is one finite bound for the whole
region, though the hitting tick may depend on the initial state. The trajectory is required
to remain in the region only at the samples *strictly before* success. No continuous
interpolation or post-success invariance is assumed.

## Reference

Michele Colledanchise and Petter Ögren, *Behavior Trees in Robotics and AI: An Introduction*
(2018), [arXiv:1709.00084v6](https://arxiv.org/abs/1709.00084), 25 October 2022,
§5.2, Definition 5.5, p. 66, with time sampled according to §5.1, equations (5.5)–(5.6).
-/

@[expose] public section

namespace Cslib.Planning.BehaviorTree.Tree

variable {X : Type*} {δ : TimeStep}

/-- A tree is finite-time successful on `A` if `A` lies in its running region and a *single*
elapsed-time bound suffices for all starts there. Every start reaches success at a sample
within the bound and stays in `A` at all earlier samples. -/
def FiniteTimeSuccessful (T : Tree X δ) (A : Set X) : Prop :=
  A ⊆ T.region .running ∧ ∃ τ : ℝ, ∀ x ∈ A, ∃ k : ℕ,
    sampleTime δ 0 k ≤ τ ∧ T.stateAt x k ∈ T.region .success ∧ ∀ j < k, T.stateAt x j ∈ A

/-- A common physical-time bound is equivalent to a common tick bound when the step is
fixed and positive. The tick bound, like the physical horizon, is independent of the start. -/
theorem finiteTimeSuccessful_iff_tickBound (T : Tree X δ) (A : Set X) :
    T.FiniteTimeSuccessful A ↔ A ⊆ T.region .running ∧ ∃ N : ℕ, ∀ x ∈ A, ∃ k ≤ N,
      T.stateAt x k ∈ T.region .success ∧ ∀ j < k, T.stateAt x j ∈ A := by
  constructor
  · rintro ⟨hA, τ, hτ⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (τ / δ.val)
    refine ⟨hA, N, fun x hx => ?_⟩
    obtain ⟨k, hk, hs, hpre⟩ := hτ x hx
    have hle : (k : ℝ) ≤ τ / δ.val := (le_div_iff₀ δ.property).mpr (by simpa [sampleTime] using hk)
    exact ⟨k, by exact_mod_cast hle.trans hN, hs, hpre⟩
  · rintro ⟨hA, N, hN⟩
    refine ⟨hA, sampleTime δ 0 N, fun x hx => ?_⟩
    obtain ⟨k, hk, hs, hpre⟩ := hN x hx
    refine ⟨k, ?_, hs, hpre⟩
    simpa [sampleTime] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk : (k : ℝ) ≤ N) δ.property.le

end Cslib.Planning.BehaviorTree.Tree
