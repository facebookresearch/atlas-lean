/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRawPacket
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortQTransport

/-! The entire actual fifth short constituent is a finite preferred-basis packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem packet_sum_at {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ι → ℝ) (j : ι) :
    (∑ i, c i • Pi.single (f i) (1 : ℝ)) (f j) = c j := by
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm (fun h => hij (hf h))),
      mul_zero]
  · simp

private theorem packet_sum_outside {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (c : ι → ℝ) (r : κ) (hr : ∀ i, f i ≠ r) :
    (∑ i, c i • Pi.single (f i) (1 : ℝ)) r = 0 := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm (hr i)), mul_zero]

/-- All pair rows and all sixty-four Fourier rows of each of the fifty-six actual octads. -/
abbrev GeneratedAxisGlobalFifthShortPacketIndex := Sum (Fin 2 × Fin 276) (Fin 56 × Fin 64)

/-- The actual preferred-short coordinate carried by each packet entry. -/
def generatedAxisGlobalFifthShortPacketLabel :
    GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex
  | Sum.inl p => Sum.inl p
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))

/-- The packet has no duplicate actual preferred-short coordinates. -/
theorem generatedAxisGlobalFifthShortPacketLabel_injective :
    Function.Injective generatedAxisGlobalFifthShortPacketLabel := by
  intro i j h
  rcases i with p | ⟨a, e⟩ <;> rcases j with q | ⟨b, f⟩
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · have hp := Sum.inl.inj (Sum.inr.inj h)
    have hab := generatedFifth_even_octads_injective (congrArg Prod.fst hp)
    have hef := congrArg Prod.snd hp
    exact congrArg Sum.inr (Prod.ext hab hef)

/-- Exact original coefficients, including the preferred-Q and Fourier phases. -/
def generatedAxisGlobalFifthShortPacketCoefficient :
    GeneratedAxisGlobalFifthShortPacketIndex → ℝ
  | Sum.inl (s, p) => if s = 0 then
      (generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ)
    else -(generatedAxisGlobalFifthMiddleMatrixQ
      (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ)
  | Sum.inr (j, e) => trialityRealMatrix e (generatedFifthEvenRootSign j) *
      qSign (generatedFifthEvenCoefficientPhase j)

/-- A finite sum representing every short coordinate of the genuine fifth prototype. -/
def generatedAxisGlobalFifthShortPacket : GriessShortIndex → ℝ :=
  ∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
    generatedAxisGlobalFifthShortPacketCoefficient i •
      Pi.single (generatedAxisGlobalFifthShortPacketLabel i) (1 : ℝ)

/-- The packet equals the full actual short constituent, including all zero coordinates. -/
theorem generatedAxisGlobalFifthShortPacket_eq :
    generatedAxisGlobalFifthShortPacket = (griessConwayEncode generatedFifthAxis).2.1 := by
  rw [generatedAxisGlobalFifthRawShort_eq]
  funext r
  rcases r with p | (⟨o, e⟩ | d)
  · exact packet_sum_at _ generatedAxisGlobalFifthShortPacketLabel_injective _ (Sum.inl p)
  · by_cases ho : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o
    · obtain ⟨j, rfl⟩ := ho
      change generatedAxisGlobalFifthShortPacket
        (generatedAxisGlobalFifthShortPacketLabel (Sum.inr (j, e))) = _
      rw [generatedAxisGlobalFifthShortPacket, packet_sum_at _
        generatedAxisGlobalFifthShortPacketLabel_injective]
      change _ = ∑ k : Fin 56, if generatedFifthEvenRootOctad k =
        generatedFifthEvenRootOctad j then _ else 0
      rw [Finset.sum_eq_single j]
      · simp only [↓reduceIte]
        rfl
      · intro k _ hkj
        have hn : generatedFifthEvenRootOctad k ≠ generatedFifthEvenRootOctad j :=
          fun h => hkj (generatedFifth_even_octads_injective h)
        simp only [hn, ↓reduceIte]
      · simp
    · have hz : generatedAxisGlobalFifthShortPacket (Sum.inr (Sum.inl (o, e))) = 0 := by
        apply packet_sum_outside
        intro i hi
        rcases i with p | ⟨j, f⟩
        · cases hi
        · exact ho ⟨j, congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj hi))⟩
      rw [hz]
      change 0 = ∑ j : Fin 56, if generatedFifthEvenRootOctad j = o then _ else 0
      symm
      apply Finset.sum_eq_zero
      intro j _
      simp only [show generatedFifthEvenRootOctad j ≠ o from fun h => ho ⟨j, h⟩,
        ↓reduceIte]
  · apply packet_sum_outside
    intro i hi
    rcases i with p | ⟨j, e⟩ <;> cases hi

/-- Complete preferred-Q image certificates transport the entire genuine fifth short component. -/
theorem generatedAxisGlobalFifthShortPacket_transport (k : Fin 14)
    (s : GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalFifthShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalFifthChainQImage k 7
        (griessShortQ (generatedAxisGlobalFifthShortPacketLabel i)) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber k)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) := by
  rw [← generatedAxisGlobalFifthShortPacket_eq]
  exact generatedAxisGlobalFifthShortWord_short_sum k _ s p _ hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
