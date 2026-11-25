/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Zero extension from an open subspace

Let `X` be a Hausdorff topological space, `s ⊆ X` open, and `Y` a
topological space with a specified zero. A continuous function on `s`
vanishing at infinity extends to a continuous function on `X` by retaining
its value on `s` and assigning zero at every point outside `s`, including
the boundary. This construction returns `C(X,Y)`.

The domain and target universes are independent. No norm, vector-space,
local-compactness or target completeness hypothesis is added. Empty open
subspaces are included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set Topology
open scoped ZeroAtInfty

noncomputable section

namespace ZeroAtInftyContinuousMap

universe uX uY

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [Zero Y]
variable {s : Set X}

private theorem continuous_extendByZero (hs : IsOpen s) (f : C₀(s, Y)) :
    Continuous (Function.extend (Subtype.val : s → X) f (0 : X → Y)) := by
  classical
  let g : X → Y := Function.extend (Subtype.val : s → X) f (0 : X → Y)
  have hzero (y : X) (hy : y ∉ s) : g y = 0 := by
    exact Function.extend_apply' (f := (Subtype.val : s → X))
      f (0 : X → Y) y (by
        rintro ⟨z, hz⟩
        exact hy (hz ▸ z.property))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ s
  · let z : s := ⟨x, hx⟩
    have hcomp : ContinuousAt (g ∘ (Subtype.val : s → X)) z := by
      change ContinuousAt (fun y : s => g y) z
      have heq : (fun y : s => g y) = (f : s → Y) := by
        funext y
        exact Subtype.val_injective.extend_apply f (0 : X → Y) y
      rw [heq]
      exact f.continuous_toFun.continuousAt
    exact (hs.isOpenEmbedding_subtypeVal.continuousAt_iff (g := g) (x := z)).mp hcomp
  · change Tendsto g (𝓝 x) (𝓝 (g x))
    rw [hzero x hx]
    refine Filter.tendsto_def.2 ?_
    intro V hV
    have hfV : f ⁻¹' V ∈ cocompact s := (zero_at_infty f) hV
    obtain ⟨K, hK, hKV⟩ := Filter.mem_cocompact.mp hfV
    have hclosed : IsClosed ((Subtype.val : s → X) '' K) :=
      (hK.image continuous_subtype_val).isClosed
    have hxK : x ∉ (Subtype.val : s → X) '' K := by
      rintro ⟨z, _, hz⟩
      exact hx (hz ▸ z.property)
    refine Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxK) ?_
    intro y hy
    change g y ∈ V
    by_cases hys : y ∈ s
    · have hyK : (⟨y, hys⟩ : s) ∉ K := by
        intro hyK
        exact hy ⟨⟨y, hys⟩, hyK, rfl⟩
      have hval : g y = f ⟨y, hys⟩ :=
        Subtype.val_injective.extend_apply f (0 : X → Y) ⟨y, hys⟩
      rw [hval]
      exact hKV hyK
    · rw [hzero y hys]
      exact mem_of_mem_nhds hV

/-- The continuous function on `X` equal to the given vanishing-at-infinity function on the open
subspace and zero on its complement.

The ambient space is Hausdorff, the subspace is open, and the target is an arbitrary topological
space with zero. -/
@[no_expose]
def extendByZero (hs : IsOpen s) (f : C₀(s, Y)) : C(X, Y) where
  toFun := Function.extend (Subtype.val : s → X) f (0 : X → Y)
  continuous_toFun := continuous_extendByZero hs f

/-- Zero extension retains every value at a point of the original open subspace.

The ambient space is Hausdorff, the subspace is open, and the target is an arbitrary topological
space with zero.

```lean
theorem extendByZero_apply (hs : IsOpen s) (f : C₀(s, Y)) (x : s) :
    extendByZero hs f (x : X) = f x
``` -/
@[simp]
theorem extendByZero_apply (hs : IsOpen s) (f : C₀(s, Y)) (x : s) :
    extendByZero hs f (x : X) = f x := by
  change Function.extend (Subtype.val : s → X) f (0 : X → Y) (x : X) = f x
  exact Subtype.val_injective.extend_apply f (0 : X → Y) x

/-- Zero extension has value zero at every point outside the open subspace.

The ambient space is Hausdorff, the subspace is open, and the target is an arbitrary topological
space with zero.

```lean
theorem extendByZero_apply_of_not_mem (hs : IsOpen s) (f : C₀(s, Y))
    {x : X} (hx : x ∉ s) : extendByZero hs f x = 0
``` -/
@[simp]
theorem extendByZero_apply_of_not_mem (hs : IsOpen s) (f : C₀(s, Y))
    {x : X} (hx : x ∉ s) : extendByZero hs f x = 0 := by
  change Function.extend (Subtype.val : s → X) f (0 : X → Y) x = 0
  exact Function.extend_apply' (f := (Subtype.val : s → X))
    f (0 : X → Y) x (by
      rintro ⟨z, hz⟩
      exact hx (hz ▸ z.property))

end ZeroAtInftyContinuousMap
