/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.Basic.Countable.Basic

/-!
# Countable unions of simplicial subcomplexes

The component nondegenerate simplices cover those of the actual supremum.
The inclusion maps are monic and preserve nondegeneracy. The same argument
applies to an empty index, with no condition on the ambient simplicial set.

This is the countable counterpart of the direct nondegenerate-surjection
proof of `SSet.finite_iSup_iff`, used in the project support-size argument.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v

namespace SSet.Subcomplex

/-- A countable family of subcomplexes with countable total nondegenerate
sets has a countable actual supremum, including an empty family. -/
theorem countable_N_iSup {Y : SSet.{u}} {I : Type v} [Countable I]
    (V : I → Y.Subcomplex) [∀ i, Countable (V i).toSSet.N] :
    Countable (iSup V).toSSet.N := by
  refine Function.Surjective.countable
    (f := fun (⟨i, s⟩ : Σ i : I, (V i).toSSet.N) ↦
      N.mk ((homOfLE (le_iSup V i)).app _ s.simplex)
        (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenerate)) ?_
  intro s
  obtain ⟨d, ⟨⟨s, h₁⟩, h₂⟩, rfl⟩ := s.mk_surjective
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at h₁
  obtain ⟨i, hi⟩ := h₁
  rw [mem_nonDegenerate_iff] at h₂
  exact ⟨⟨i, N.mk ⟨s, hi⟩ (by rwa [mem_nonDegenerate_iff])⟩, rfl⟩

end SSet.Subcomplex
