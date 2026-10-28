/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMembership

/-! The actual counted monomial subgroup injects into the genuine frame stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Membership of the original fourteen monomial generators includes the counted subgroup. -/
theorem sixthFrameOrbit_monomial_le (K : Subgroup Co1)
    (h : ∀ k : Fin 14, sixthFrameOrbitOriginalGenerator (Fin.castAdd 1 k) ∈ K) :
    leechRootedA2SixthMonomialCo1Subgroup ≤ K := by
  apply leechRootedA2SixthMonomialCo1_le_of_generators K
  · intro j
    have hm := h (Fin.castAdd 4 j)
    change sixthFrameOrbitOriginalGenerator (Fin.castAdd 5 j) ∈ K at hm
    rw [sixthFrameOrbitOriginalGenerator_sign] at hm
    exact hm
  · intro j
    have hm := h ⟨10 + j.val, by omega⟩
    have he : Fin.castAdd 1 (⟨10 + j.val, by omega⟩ : Fin 14) =
        Fin.natAdd 10 (Fin.castAdd 2 j) := by apply Fin.ext; simp
    rw [he, sixthFrameOrbitOriginalGenerator_raw, sixthFrameOrbit_raw_spatial] at hm
    exact hm
  · have hm := h 13
    change sixthFrameOrbitOriginalGenerator (Fin.natAdd 10 (3 : Fin 5)) ∈ K at hm
    rw [sixthFrameOrbitOriginalGenerator_raw, sixthFrameOrbit_swap_spatial] at hm
    exact hm

/-- The first fourteen genuine source actions fix the original starting frame class. -/
theorem sixthFrameOrbit_monomial_generator_fixes (k : Fin 14) :
    sixthFrameOrbitOriginalGenerator (Fin.castAdd 1 k) • sixthFrameOrbitBase =
      sixthFrameOrbitBase := by
  change co1BinaryAction (sixthFrameOrbitOriginalGenerator (Fin.castAdd 1 k))
    sixthFrameOrbitBase = sixthFrameOrbitBase
  rw [sixthFrameOrbitOriginalGenerator_binary]
  change sixthFrameOrbitColumnMatrix (sixthFrameOrbitColumns (Fin.castAdd 1 k)) *ᵥ
    monsterCo1GeometryBinaryMaskDecode 2048 = monsterCo1GeometryBinaryMaskDecode 2048
  rw [← sixthFrameOrbitMaskApply_decode, sixthFrameOrbit_monomial_frame_check]

/-- The entire actual counted monomial subgroup fixes the original frame. -/
theorem sixthFrameOrbit_monomial_le_base_stabilizer :
    leechRootedA2SixthMonomialCo1Subgroup ≤ MulAction.stabilizer Co1 sixthFrameOrbitBase := by
  apply sixthFrameOrbit_monomial_le
  intro k
  exact sixthFrameOrbit_monomial_generator_fixes k

/-- The counted monomial subgroup gives a genuine lower bound for the restricted stabilizer. -/
theorem sixthFrameOrbit_stabilizer_card_lower (K : Subgroup Co1)
    (h : ∀ k : Fin 14, sixthFrameOrbitOriginalGenerator (Fin.castAdd 1 k) ∈ K) :
    20643840 ≤ Nat.card (MulAction.stabilizer K sixthFrameOrbitBase) := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have hm := sixthFrameOrbit_monomial_le K h
  let f : leechRootedA2SixthMonomialCo1Subgroup → MulAction.stabilizer K sixthFrameOrbitBase :=
    fun x => ⟨⟨x.val, hm x.property⟩, sixthFrameOrbit_monomial_le_base_stabilizer x.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hab
  have hc := Nat.card_le_card_of_injective f hf
  rw [leechRootedA2SixthMonomialCo1Subgroup_card] at hc
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
