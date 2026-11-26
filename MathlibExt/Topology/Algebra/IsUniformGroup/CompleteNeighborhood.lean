/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

public section

open Filter
open scoped Topology

namespace IsUniformAddGroup

/-- **Uniform group completeness from a complete neighborhood.** Let `G` be an additive group
with a compatible uniform group structure (`IsUniformAddGroup G`). If a complete subset
`S⊆G` is a neighborhood of zero, then `G` is complete. Commutativity, a norm and a
separation assumption are not required. -/
theorem completeSpace_of_isComplete_mem_nhds_zero
    {G : Type*} [AddGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {S : Set G} (hS : IsComplete S) (hS0 : S ∈ 𝓝 (0 : G)) :
    CompleteSpace G where
  complete {f} hf := by
    have : f.NeBot := hf.1
    obtain ⟨x, hx⟩ : ∃ x : G, ∀ᶠ y in f, y - x ∈ S := by
      have h := (IsUniformAddGroup.cauchy_iff_tendsto_swapped f).mp hf
      exact (h.2.eventually_mem hS0).curry.exists
    have htranslated : IsComplete ((fun y : G => y + x) '' S) :=
      (isUniformEmbedding_translate_add x).isComplete_iff.mpr hS
    obtain ⟨l, _, hl⟩ := htranslated f hf (by
      apply le_principal_iff.mpr
      filter_upwards [hx] with y hy
      exact ⟨y - x, hy, sub_add_cancel y x⟩)
    exact ⟨l, hl⟩

end IsUniformAddGroup
