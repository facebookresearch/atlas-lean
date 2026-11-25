/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kernels of surjections between flat modules

The kernel of a surjective linear map between flat modules is flat. The proof uses the
tensor-kernel injection for a flat quotient and retains the submodule action. The scalar ring,
middle module, and quotient may lie in independent universes.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w

namespace Module.Flat

variable {R : Type u} [CommRing R]
  {N : Type v} {Q : Type w} [AddCommGroup N] [AddCommGroup Q]
  [Module R N] [Module R Q]

/--
The kernel of a surjective map between flat modules is flat. The ring, middle module and quotient
universes are independent.
-/
theorem kernel_of_surjective [Module.Flat R N] [Module.Flat R Q]
    (f : N →ₗ[R] Q) (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ g hg
  let i := (LinearMap.ker f).subtype
  have hgn : Function.Injective (g.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap g hg
  have hmap : Function.Injective ((i.lTensor B).comp (g.rTensor (LinearMap.ker f))) := by
    rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
    exact hgn.comp (LinearMap.lTensor_injective_of_exact_of_flat f hf i
      (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) A)
  intro x y hxy
  apply hmap
  exact congrArg (i.lTensor B) hxy

end Module.Flat
