/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UrysohnsLemma

/-! # One support-bearing scalar C0 cutoff factory on regular locally compact spaces -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ZeroAtInfty

namespace ZeroAtInftyContinuousMap
universe uX

/-- Let `X` be a regular locally compact topological space and let `K ⊆ X` be compact. The cutoff is
complex-valued and continuous, with compact support.

A single cutoff retains compact support, all one-on-K values and both norm bounds. -/
theorem exists_compact_one_on_of_regularSpace
    {X : Type uX} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) :
    ∃ φ : C₀(X, ℂ), HasCompactSupport φ ∧ EqOn φ 1 K ∧ ‖φ‖ ≤ 1 ∧ ∀ x : X, ‖φ x‖ ≤ 1 := by
  obtain ⟨u, hu, _hu0, hcompact, hinterval⟩ :=
    exists_continuous_one_zero_of_isCompact (s := K) (t := (∅ : Set X))
      hK isClosed_empty (by simp)
  let φ : C₀(X, ℂ) :=
    { toFun := fun x => (u x : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp u.continuous
      zero_at_infty' := by
        have ht : Tendsto (u : X → ℝ) (cocompact X) (𝓝 (0 : ℝ)) := hcompact.is_zero_at_infty
        simpa only [Function.comp_def, Complex.ofReal_zero] using
          (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp ht }
  have hpoint (x : X) : ‖φ x‖ ≤ 1 := by
    change ‖(u x : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (hinterval x).1]
    exact (hinterval x).2
  have hnorm : ‖φ.toBCF‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le (f := φ.toBCF) zero_le_one).2 hpoint
  refine ⟨φ, ?_, ?_, ?_, hpoint⟩
  · exact hcompact.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  · intro x hx
    change (u x : ℂ) = 1
    rw [hu hx, Pi.one_apply, Complex.ofReal_one]
  · simpa only [norm_toBCF_eq_norm] using hnorm

end ZeroAtInftyContinuousMap
