/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical product equivalences to transpose finite grid labelings while retaining independent
finite edge and diagonal label sets over an unrestricted label carrier.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Grid

/-! # Transposition of finite grid tensor evaluations

Swapping the row and column coordinates of every vertex and both endpoints of every directed
label preserves the grid value. Rectangle kernels exchange their top-right and bottom-left ends
under this coordinate swap.

Adapted from `Groundwork.Grid.{trInst,trG,trHalf,ZG_tr}` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

variable {ρ γ A : Type*}

namespace Instance

/-- Swap the row and column coordinates of a grid tensor instance. -/
def transpose (R : Instance (ρ × γ) A) : Instance (γ × ρ) A :=
  fun w h => R w.swap fun w' => h w'.swap

@[simp] theorem transpose_apply (R : Instance (ρ × γ) A) (w : γ × ρ)
    (h : γ × ρ → A) :
    R.transpose w h = R w.swap (fun w' => h w'.swap) := rfl

/-- Transposing a grid tensor instance twice recovers the original instance. -/
@[simp] theorem transpose_transpose (R : Instance (ρ × γ) A) : R.transpose.transpose = R := by
  funext w h
  rfl

end Instance

/-- Transpose a rectangle kernel, exchanging the `y` and `u` directed diagonal ends. -/
def transposeRectangleKernel
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    ((γ × γ) × (ρ × ρ)) → A → A → A → A → ℤ :=
  fun ω x y u v => G (ω.2, ω.1) x u y v

@[simp] theorem transposeRectangleKernel_apply
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (ω : (γ × γ) × (ρ × ρ)) (x y u v : A) :
    transposeRectangleKernel G ω x y u v = G (ω.2, ω.1) x u y v := rfl

/-- Transposing a rectangle kernel twice recovers the original kernel. -/
@[simp] theorem transposeRectangleKernel_transposeRectangleKernel
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    transposeRectangleKernel (transposeRectangleKernel G) = G := by
  funext ω x y u v
  rfl

/-- Transposing the grid coordinates, local tensors, and rectangle kernels preserves the finite
grid evaluation. Edge and diagonal label choices remain independent. -/
theorem gridValue_transpose [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [DecidableEq A] (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    gridValue labels diagonalLabels R.transpose (transposeRectangleKernel G) =
      gridValue labels diagonalLabels R G := by
  classical
  unfold gridValue
  let vertexEquiv := Equiv.prodComm γ ρ
  let labelingEquiv : Matrix (γ × ρ) (γ × ρ) A ≃ Matrix (ρ × γ) (ρ × γ) A :=
    vertexEquiv.arrowCongr (vertexEquiv.arrowCongr (Equiv.refl A))
  have labelingEquiv_apply (ℓ : Matrix (γ × ρ) (γ × ρ) A) (w w' : ρ × γ) :
      labelingEquiv ℓ w w' = ℓ w.swap w'.swap := rfl
  refine Finset.sum_equiv labelingEquiv ?_ ?_
  · intro ℓ
    rw [mem_gridLabelings, mem_gridLabelings]
    constructor
    · intro h w w'
      rw [labelingEquiv_apply]
      have hs := h w.swap w'.swap
      exact ⟨fun heq => hs.1 (congrArg Prod.swap heq),
        fun hne => hs.2 (fun heq => hne (Prod.swap_injective heq))⟩
    · intro h w w'
      have hs := h w.swap w'.swap
      simp only [labelingEquiv_apply, Prod.swap_swap] at hs
      exact ⟨fun heq => hs.1 (congrArg Prod.swap heq),
        fun hne => hs.2 (fun heq => hne (Prod.swap_injective heq))⟩
  · intro ℓ _
    have hvertex :
        (∏ w, R.transpose w (ℓ w)) = ∏ w, R w (labelingEquiv ℓ w) := by
      refine Fintype.prod_equiv vertexEquiv _ _ fun w => ?_
      rfl
    have hrow :
        (∏ a, ∏ q ∈ orderedPairs ρ,
            if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then (1 : ℤ) else 0) =
          ∏ i, ∏ p ∈ orderedPairs ρ,
            if labelingEquiv ℓ (p.1, i) (p.2, i) =
                labelingEquiv ℓ (p.2, i) (p.1, i) then 1 else 0 := by
      rfl
    have hcolumn :
        (∏ i, ∏ p ∈ orderedPairs γ,
            if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then (1 : ℤ) else 0) =
          ∏ a, ∏ q ∈ orderedPairs γ,
            if labelingEquiv ℓ (a, q.1) (a, q.2) =
                labelingEquiv ℓ (a, q.2) (a, q.1) then 1 else 0 := by
      rfl
    have hrectangle :
        (∏ ω ∈ gridRectangles γ ρ,
            rectangleApply (transposeRectangleKernel G ω) ℓ ω) =
          ∏ ω ∈ gridRectangles ρ γ, rectangleApply (G ω) (labelingEquiv ℓ) ω := by
      refine Finset.prod_equiv (Equiv.prodComm (γ × γ) (ρ × ρ)) ?_ ?_
      · intro ω
        simp [gridRectangles, and_comm]
      · intro ω _
        rfl
    rw [hvertex, hrow, hcolumn, hrectangle]
    ac_rfl

end TensorNetwork
