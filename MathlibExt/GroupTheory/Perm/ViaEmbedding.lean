/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Adam Kiezun, Tsutomu Okano <toskua@meta.com>
-/

module

public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Canonical permutation-extension laws

The whole permutation-extension homomorphism carries an actual swap to
its swap on the two embedded points, on every ambient type.

Adam Kiezun first formalized the same extension law as
`FormalizedPapers.CaputoLiggettRichthammer2009.GapProof.extend_swap`
in commit `ff15005c93bc98006cfa88870ec09fda1174010d`. This shared proof also
retains the finite-embedding development's application of `map_swap`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Equiv.Perm

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- The canonical extension homomorphism takes a complete swap to the embedded swap. -/
theorem viaEmbeddingHom_swap (ι : α ↪ β) (x y : α) :
    viaEmbeddingHom ι (Equiv.swap x y) = Equiv.swap (ι x) (ι y) := by
  change (Equiv.swap x y).viaEmbedding ι = Equiv.swap (ι x) (ι y)
  ext z
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hz
    rw [viaEmbedding_apply]
    exact Function.Injective.map_swap ι.injective x y a
  · rw [viaEmbedding_apply_of_notMem _ _ _ hz]
    have hzx : z ≠ ι x := by
      intro he
      exact hz ⟨x, he.symm⟩
    have hzy : z ≠ ι y := by
      intro he
      exact hz ⟨y, he.symm⟩
    exact (Equiv.swap_apply_of_ne_of_ne hzx hzy).symm

end Equiv.Perm
