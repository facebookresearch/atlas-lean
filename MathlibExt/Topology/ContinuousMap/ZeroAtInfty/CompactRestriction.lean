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

public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.ExtendByZero

/-!
# Restricting compact-space functions supported in a subspace

On a compact topological space `X`, let `f : C(X,Y)` take value zero
outside an arbitrary subset `s`, where `Y` is a topological space with
zero. Its restriction defines a function in `C₀(s,Y)`, with exactly the
same values on `s`. The restriction constructor requires no openness of
`s`, Hausdorff property of `X`, norm or target completeness.

When `X` is also Hausdorff and `s` is open, restriction and zero extension
are inverse on these functions. The subset may be empty and the domain
and target universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

universe uX uY

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [Zero Y]

/-- The restriction to `s` of a continuous compact-space function that is zero on the complement,
with its resulting vanishing-at-infinity property.

`X` is compact, `Y` is topological with zero, and the original function is zero outside `s`. -/
def restrictZeroOutside (s : Set X) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) : C₀(s, Y) where
  toFun x := f x
  continuous_toFun := f.continuous.comp continuous_subtype_val
  zero_at_infty' := by
    apply Filter.tendsto_def.2
    intro V hV
    obtain ⟨U, hUV, hU, h0U⟩ := mem_nhds_iff.1 hV
    let K : Set X := f ⁻¹' Uᶜ
    have hK : IsCompact K := (hU.isClosed_compl.preimage f.continuous).isCompact
    have hKs : K ⊆ s := by
      intro x hx
      by_contra hxs
      have hfx : f x = 0 := hzero x hxs
      exact hx (hfx.symm ▸ h0U)
    have hKr : K ⊆ Set.range (Subtype.val : s → X) := by
      intro x hx
      exact ⟨⟨x, hKs hx⟩, rfl⟩
    have hKsub : IsCompact ((Subtype.val : s → X) ⁻¹' K) :=
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKr
    apply Filter.mem_cocompact.2
    refine ⟨(Subtype.val : s → X) ⁻¹' K, hKsub, ?_⟩
    intro x hx
    apply hUV
    by_contra hxU
    exact hx hxU

/-- The restricted function retains the original value at every subspace point.

`X` is compact, `Y` is topological with zero, and the original function is zero outside `s`.

```lean
theorem restrictZeroOutside_apply (s : Set X) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) (x : s) :
    restrictZeroOutside s f hzero x = f x
``` -/
@[simp]
theorem restrictZeroOutside_apply (s : Set X) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) (x : s) :
    restrictZeroOutside s f hzero x = f x := rfl

section OpenSubspace

variable [T2Space X] {s : Set X}

/-- On an open subspace of a compact Hausdorff space, zero extension after restriction recovers a
function supported there.

`X` is compact and Hausdorff, `s` is open, and `Y` is topological with zero.

```lean
theorem extendByZero_restrictZeroOutside (hs : IsOpen s) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) :
    extendByZero hs (restrictZeroOutside s f hzero) = f
``` -/
theorem extendByZero_restrictZeroOutside (hs : IsOpen s) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) :
    extendByZero hs (restrictZeroOutside s f hzero) = f := by
  apply ContinuousMap.ext
  intro x
  by_cases hx : x ∈ s
  · exact extendByZero_apply hs (restrictZeroOutside s f hzero) ⟨x, hx⟩
  · exact (extendByZero_apply_of_not_mem hs _ hx).trans (hzero x hx).symm

/-- On an open subspace of a compact Hausdorff space, restricting the zero extension recovers the
original C0 function.

`X` is compact and Hausdorff, `s` is open, and `Y` is topological with zero.

```lean
theorem restrictZeroOutside_extendByZero (hs : IsOpen s) (f : C₀(s, Y)) :
    restrictZeroOutside s (extendByZero hs f)
      (fun _x hx => extendByZero_apply_of_not_mem hs f hx) = f
``` -/
theorem restrictZeroOutside_extendByZero (hs : IsOpen s) (f : C₀(s, Y)) :
    restrictZeroOutside s (extendByZero hs f)
      (fun _x hx => extendByZero_apply_of_not_mem hs f hx) = f := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  exact extendByZero_apply hs f x

end OpenSubspace
end ZeroAtInftyContinuousMap
