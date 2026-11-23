/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
extract finite rectangle-kernel sum expansion over the canonical grid evaluator.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Grid

/-! # Finite grid expansion over local kernel sums

This module distributes a finite kernel sum at each active grid rectangle through the grid
evaluation. Choices are indexed only by the active-rectangle subtype; the resulting kernel family
is extended to all raw rectangle indices by retaining the original kernel outside that subtype.

Adapted from `Groundwork.Grid.Expand.ZG_cross_eq_sum` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {ρ γ A : Type*}

/-- If every active rectangle kernel is a finite sum, the grid value is the sum over one kernel
choice for each active rectangle. Raw rectangle indices outside `gridRectangles` retain the
original kernel, which does not affect `gridValue`. -/
theorem gridValue_eq_sum_choices [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {κ : {ω // ω ∈ gridRectangles ρ γ} → Type*}
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (choices : (ω : {ω // ω ∈ gridRectangles ρ γ}) → Finset (κ ω))
    (K : (ω : {ω // ω ∈ gridRectangles ρ γ}) → κ ω → A → A → A → A → ℤ)
    (hG : ∀ (ω : {ω // ω ∈ gridRectangles ρ γ}) x y u v,
      G ω x y u v = ∑ k ∈ choices ω, K ω k x y u v) :
    gridValue labels diagonalLabels R G =
      ∑ choice ∈ Fintype.piFinset choices,
        gridValue labels diagonalLabels R fun ω =>
          if hω : ω ∈ gridRectangles ρ γ then K ⟨ω, hω⟩ (choice ⟨ω, hω⟩) else G ω := by
  classical
  unfold gridValue
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← mul_sum, ← mul_sum]
  congr 2
  calc
    (∏ ω ∈ gridRectangles ρ γ, rectangleApply (G ω) ℓ ω) =
        ∏ ω : {ω // ω ∈ gridRectangles ρ γ}, rectangleApply (G ω) ℓ ω :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ ω : {ω // ω ∈ gridRectangles ρ γ},
          ∑ k ∈ choices ω, rectangleApply (K ω k) ℓ ω := by
      apply Fintype.prod_congr
      intro ω
      simpa [rectangleApply] using hG ω
        (ℓ (ω.1.1.1, ω.1.2.1) (ω.1.1.2, ω.1.2.2))
        (ℓ (ω.1.1.1, ω.1.2.2) (ω.1.1.2, ω.1.2.1))
        (ℓ (ω.1.1.2, ω.1.2.1) (ω.1.1.1, ω.1.2.2))
        (ℓ (ω.1.1.2, ω.1.2.2) (ω.1.1.1, ω.1.2.1))
    _ = ∑ choice ∈ Fintype.piFinset choices,
          ∏ ω : {ω // ω ∈ gridRectangles ρ γ}, rectangleApply (K ω (choice ω)) ℓ ω :=
      Finset.prod_univ_sum choices fun ω k => rectangleApply (K ω k) ℓ ω
    _ = ∑ choice ∈ Fintype.piFinset choices,
          ∏ ω ∈ gridRectangles ρ γ,
            rectangleApply
              (if hω : ω ∈ gridRectangles ρ γ then K ⟨ω, hω⟩ (choice ⟨ω, hω⟩)
              else G ω) ℓ ω := by
      refine sum_congr rfl fun choice _ => ?_
      rw [Finset.prod_subtype (gridRectangles ρ γ) (fun _ => Iff.rfl)]
      apply Fintype.prod_congr
      intro ω
      simp [ω.property]

end TensorNetwork
