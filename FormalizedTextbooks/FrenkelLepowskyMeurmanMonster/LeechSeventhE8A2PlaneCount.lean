/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneMembership
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SpanPairs

/-! Exact intrinsic A2-plane enumeration in the original selected E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The checked finite catalogue is equivalent to all intrinsic actual section A2 planes. -/
def leechSeventhE8A2PlaneEquiv : Fin 1120 ≃ leechSeventhE8A2Planes :=
  Equiv.ofBijective
    (fun p => ⟨leechSeventhE8A2Plane p, leechSeventhE8A2Plane_intrinsic p⟩)
    ⟨by
      intro p q h
      exact leechSeventhE8A2Plane_injective (congrArg Subtype.val h), by
      intro W
      have hW : W.val ∈ Set.range leechSeventhE8A2Plane :=
        Eq.mp (congrArg (fun S : Set (Submodule ℝ (Fin 24 → ℝ)) => W.val ∈ S)
          leechSeventhE8A2Planes_eq_range) W.property
      obtain ⟨p, hp⟩ := hW
      exact ⟨p, Subtype.ext hp⟩⟩

/-- There are exactly 1120 intrinsic actual A2 planes in the selected physical E8 section. -/
theorem leechSeventhE8A2Planes_card : Nat.card leechSeventhE8A2Planes = 1120 := by
  rw [← Nat.card_congr leechSeventhE8A2PlaneEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
