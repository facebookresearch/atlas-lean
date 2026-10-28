/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact identifications of successive coordinate stabilizers in the independent diagonal group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalChain

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The prior coordinate stabilizer is the next one fixing its last free column. -/
theorem y322Orthogonal3DiagonalChain_step_mem (i : Fin 7)
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    g ∈ y322Orthogonal3DiagonalChain i.val ↔
      g ∈ y322Orthogonal3DiagonalChain (i.val + 1) ∧
        g • y322Orthogonal3DiagonalUnit i = y322Orthogonal3DiagonalUnit i := by
  rw [y322Orthogonal3DiagonalChain_mem, y322Orthogonal3DiagonalChain_mem]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨⟨hg, fun j hj => hf j (by omega)⟩, hf i (le_refl _)⟩
  · rintro ⟨⟨hg, hf⟩, hi⟩
    refine ⟨hg, fun j hj => ?_⟩
    by_cases heq : j = i
    · simpa only [heq] using hi
    · exact hf j (by have hji : j.val ≠ i.val := Fin.val_ne_of_ne heq; omega)

/-- The actual single-column stabilizer equals the preceding subgroup viewed in the next one. -/
theorem y322Orthogonal3DiagonalChain_stabilizer (i : Fin 7) :
    MulAction.stabilizer (y322Orthogonal3DiagonalChain (i.val + 1))
      (y322Orthogonal3DiagonalUnit i) =
        (y322Orthogonal3DiagonalChain i.val).subgroupOf
          (y322Orthogonal3DiagonalChain (i.val + 1)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change g.val • y322Orthogonal3DiagonalUnit i = y322Orthogonal3DiagonalUnit i ↔
    g.val ∈ y322Orthogonal3DiagonalChain i.val
  rw [y322Orthogonal3DiagonalChain_step_mem]
  simp only [g.property, true_and]

/-- Successive single-column stabilizers have exactly the preceding subgroup cardinality. -/
theorem y322Orthogonal3DiagonalChain_stabilizer_card (i : Fin 7) :
    Nat.card (MulAction.stabilizer (y322Orthogonal3DiagonalChain (i.val + 1))
      (y322Orthogonal3DiagonalUnit i)) = Nat.card (y322Orthogonal3DiagonalChain i.val) := by
  rw [y322Orthogonal3DiagonalChain_stabilizer]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (y322Orthogonal3DiagonalChain_mono (Nat.le_succ i.val))).toEquiv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
