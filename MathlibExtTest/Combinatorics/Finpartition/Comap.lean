/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Finpartition.Comap

/-!
# Tests for pulling back partitions along maps

Pulling back the discrete partition `⊥` along a permutation keeps all `n` singletons; pulling
back along a constant map sends everything to one block; pulling back the one-block partition
of a nonempty type keeps one block; relabeling twice by a permutation and its inverse is the
identity.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Combinatorics.Finpartition.Comap

/-- Relabeling the discrete partition of `Fin 3` by a swap keeps three blocks. -/
example : #((⊥ : Finpartition (univ : Finset (Fin 3))).comap (Equiv.swap 0 1)).parts = 3 := by
  rw [Finpartition.card_parts_comap_equiv, Finpartition.card_bot]
  simp

/-- Relabeling by a permutation and back is the identity. -/
example (P : Finpartition (univ : Finset (Fin 4))) :
    (P.comap (Equiv.swap 1 3)).comap (Equiv.swap 1 3).symm = P :=
  Finpartition.comap_symm_comap _ P

/-- Along a constant map every point lands in the block of the image point: the pull-back of
any partition of `Fin 2` along `fun _ : Fin 3 ↦ 0` has the single block `univ`. -/
example (P : Finpartition (univ : Finset (Fin 2))) :
    (P.comap fun _ : Fin 3 ↦ (0 : Fin 2)).parts = {univ} := by
  ext C
  rw [Finpartition.mem_comap_parts, mem_singleton]
  constructor
  · rintro ⟨⟨a, ha⟩, B, hB, rfl⟩
    ext x
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    simpa using ha
  · rintro rfl
    obtain ⟨B, ⟨hB, h0⟩, -⟩ := P.existsUnique_mem (mem_univ (0 : Fin 2))
    exact ⟨univ_nonempty, B, hB, by ext; simp [h0]⟩

/-- Pulling back along the identity is the identity. -/
example (P : Finpartition (univ : Finset (Fin 5))) : P.comap id = P :=
  Finpartition.comap_refl P

end MathlibExtTest.Combinatorics.Finpartition.Comap
