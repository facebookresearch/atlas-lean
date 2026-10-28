/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! Complete rational short outputs evaluate Fourier signs only on genuine nonzero inputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- All original forward Fourier inputs are retained, with their true zero guard. -/
def generatedAxisGlobalSparseTrialityShortQ (A : GeneratedAxisGlobalRationalPacket) : GriessShortIndex → ℚ
  | Sum.inr (Sum.inl (o,e)) => ∑ f : Fin 64,
      if A.2.1 (Sum.inr (Sum.inl (o,f))) = 0 then 0 else
        (trialityIntegerMatrix e f : ℚ) / 8 * A.2.1 (Sum.inr (Sum.inl (o,f)))
  | r => generatedAxisGlobalTrialityShortQ A r

/-- Every guarded forward coordinate equals the entire original forward short operator. -/
theorem generatedAxisGlobalSparseTrialityShortQ_eq (A : GeneratedAxisGlobalRationalPacket)
    (r : GriessShortIndex) :
    generatedAxisGlobalSparseTrialityShortQ A r = generatedAxisGlobalTrialityShortQ A r := by
  rcases r with p | (⟨o,e⟩ | p)
  · rfl
  · unfold generatedAxisGlobalSparseTrialityShortQ generatedAxisGlobalTrialityShortQ
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : A.2.1 (Sum.inr (Sum.inl (o,f))) = 0
    · simp only [h, ↓reduceIte, mul_zero]
    · simp only [h, ↓reduceIte]
  · rfl

/-- All original inverse transpose-Fourier inputs are retained, with their true zero guard. -/
def generatedAxisGlobalSparseInverseShortQ (A : GeneratedAxisGlobalRationalPacket) : GriessShortIndex → ℚ
  | Sum.inr (Sum.inl (o,e)) => ∑ f : Fin 64,
      if A.2.1 (Sum.inr (Sum.inl (o,f))) = 0 then 0 else
        (trialityIntegerMatrix f e : ℚ) / 8 * A.2.1 (Sum.inr (Sum.inl (o,f)))
  | r => generatedAxisGlobalInverseShortQ A r

/-- Every guarded inverse coordinate equals the entire original inverse short operator. -/
theorem generatedAxisGlobalSparseInverseShortQ_eq (A : GeneratedAxisGlobalRationalPacket)
    (r : GriessShortIndex) :
    generatedAxisGlobalSparseInverseShortQ A r = generatedAxisGlobalInverseShortQ A r := by
  rcases r with p | (⟨o,e⟩ | p)
  · rfl
  · unfold generatedAxisGlobalSparseInverseShortQ generatedAxisGlobalInverseShortQ
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : A.2.1 (Sum.inr (Sum.inl (o,f))) = 0
    · simp only [h, ↓reduceIte, mul_zero]
    · simp only [h, ↓reduceIte]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
