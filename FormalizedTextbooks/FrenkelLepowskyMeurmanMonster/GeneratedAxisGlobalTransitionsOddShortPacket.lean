/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates

/-! The complete odd-axis short constituent and its genuine finite source-word transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem oddPacket_sum_at {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ι → ℝ) (j : ι) :
    (∑ i, c i • Pi.single (f i) (1 : ℝ)) (f j) = c j := by
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm (fun h => hij (hf h))),
      mul_zero]
  · simp

private theorem oddPacket_sum_outside {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (c : ι → ℝ) (r : κ) (hr : ∀ i, f i ≠ r) :
    (∑ i, c i • Pi.single (f i) (1 : ℝ)) r = 0 := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm (hr i)), mul_zero]

/-- All 552 original pair-short coordinates, with both preferred signs. -/
abbrev GeneratedAxisGlobalOddShortPacketIndex := Fin 2 × Fin 276

/-- The actual preferred label carried by each original pair packet entry. -/
def generatedAxisGlobalOddShortPacketLabel (p : GeneratedAxisGlobalOddShortPacketIndex) :
    GriessShortIndex := Sum.inl p

/-- Original coefficients from the actual odd vector, with the pair's preferred sign. -/
def generatedAxisGlobalOddShortPacketCoefficient (p : GeneratedAxisGlobalOddShortPacketIndex) :
    ℝ :=
  (if p.1 = 0 then 1 else -1) *
    (2 * griessShortVector (Sum.inr (Sum.inr (0, 0))) (griessCoordinatePair p.2).1 *
      griessShortVector (Sum.inr (Sum.inr (0, 0))) (griessCoordinatePair p.2).2)

/-- A finite preferred-basis packet representing the entire actual odd-axis short constituent. -/
def generatedAxisGlobalOddShortPacket : GriessShortIndex → ℝ :=
  ∑ i : GeneratedAxisGlobalOddShortPacketIndex,
    generatedAxisGlobalOddShortPacketCoefficient i •
      Pi.single (generatedAxisGlobalOddShortPacketLabel i) (1 : ℝ)

/-- Every short coordinate equals the displayed packet, including all zero octad and odd rows. -/
theorem generatedAxisGlobalOddShortPacket_eq :
    generatedAxisGlobalOddShortPacket = (griessConwayEncode generatedOddAxis).2.1 := by
  have hi : Function.Injective generatedAxisGlobalOddShortPacketLabel := by
    intro i j h
    exact Sum.inl.inj h
  funext r
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · change generatedAxisGlobalOddShortPacket
      (generatedAxisGlobalOddShortPacketLabel (s, p)) = _
    rw [generatedAxisGlobalOddShortPacket,
      oddPacket_sum_at generatedAxisGlobalOddShortPacketLabel hi]
    exact (generatedAxis_triality_odd_pair_coordinate 0 0 0 s p).symm
  · rw [show generatedAxisGlobalOddShortPacket (Sum.inr (Sum.inl (o, e))) = 0 from
      oddPacket_sum_outside generatedAxisGlobalOddShortPacketLabel
        generatedAxisGlobalOddShortPacketCoefficient _ (fun i h => by
        change (Sum.inl i : GriessShortIndex) = _ at h
        cases h)]
    exact (generatedAxis_triality_odd_octad_coordinate 0 0 0 o e).symm
  · rw [show generatedAxisGlobalOddShortPacket (Sum.inr (Sum.inr (d, i))) = 0 from
      oddPacket_sum_outside generatedAxisGlobalOddShortPacketLabel
        generatedAxisGlobalOddShortPacketCoefficient _ (fun i h => by
        change (Sum.inl i : GriessShortIndex) = _ at h
        cases h)]
    exact (generatedAxis_triality_odd_odd_coordinate 0 d 0 i 0).symm

/-- A complete extraspecial source certificate gives the entire signed short-unit image. -/
theorem generatedAxisGlobalOddSourceRoot_short_basis (k : Fin 9)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalOddSourceWordQImage (generatedAxisGlobalOddSourceRootWords k)
        (griessShortQ r) = qCentral c * griessShortQ s) :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber k) (Pi.single r 1) =
      qSign c • Pi.single s (1 : ℝ) := by
  apply monsterNortonShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalOddSourceRoot_QImage]
  exact hc

/-- Only 552 full preferred-Q images suffice for the complete actual short-word constituent. -/
theorem generatedAxisGlobalOddShortPacket_transport (k : Fin 9)
    (s : GeneratedAxisGlobalOddShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalOddShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalOddSourceWordQImage (generatedAxisGlobalOddSourceRootWords k)
        (griessShortQ (generatedAxisGlobalOddShortPacketLabel i)) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber k)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ i, (generatedAxisGlobalOddShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) := by
  rw [← generatedAxisGlobalOddShortPacket_eq, generatedAxisGlobalOddShortPacket, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, generatedAxisGlobalOddSourceRoot_short_basis k _ _ _ (hc i), smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
