/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortSparseFixation

/-! Genuine preferred labels and the exact mask contract for the complete canonical short packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Every packet position is a genuine preferred pair, signed-octad or odd short label. -/
def generatedSeventhXiShortPacketLabel (k : Fin 27624) : GriessShortIndex :=
  if h : k.val < 552 then
    generatedSeventhXiShortInputLabel ⟨k.val / 276, by omega⟩
      ⟨k.val % 276, Nat.mod_lt _ (by decide)⟩
  else if h : k.val < 15336 then
    Sum.inr (Sum.inl (generatedSeventhXiOctadFamily ⟨(k.val - 552) / 64, by omega⟩,
      ⟨(k.val - 552) % 64, Nat.mod_lt _ (by decide)⟩))
  else
    Sum.inr (Sum.inr (generatedSeventhXiShortPackedOddCode ⟨(k.val - 15336) / 24, by omega⟩,
      ⟨(k.val - 15336) % 24, Nat.mod_lt _ (by decide)⟩))

/-- The labelled full short packet uses the genuine signed numerators and denominator thirty-two. -/
def generatedSeventhXiShortPacketVector : GriessShortIndex → ℝ :=
  ∑ k : Fin 27624, ((generatedSeventhXiShortPacketCoefficient k : ℝ) / 32) •
    Pi.single (generatedSeventhXiShortPacketLabel k) 1

/-- Exact original family mask bindings give the entire preferred-Q mask at each packet position. -/
theorem generatedSeventhXiShortPacketLabel_mask
    (ho : ∀ g : Fin 231, ∀ e : Fin 64,
      griessShortQ (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily g, e))) =
        generatedSeventhXiShortQMask (generatedSeventhXiShortPackedOctadMask g e))
    (hd : ∀ g : Fin 512, ∀ j : Fin 24,
      griessShortQ (Sum.inr (Sum.inr (generatedSeventhXiShortPackedOddCode g, j))) =
        generatedSeventhXiShortQMask (generatedSeventhXiShortPackedOddPreferredMask g j))
    (k : Fin 27624) :
    griessShortQ (generatedSeventhXiShortPacketLabel k) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortPacketMask k) := by
  by_cases h1 : k.val < 552
  · simp only [generatedSeventhXiShortPacketLabel, generatedSeventhXiShortPacketMask,
      h1, dite_true]
    rw [generatedSeventhXiShortInputLabel, generatedSeventhXiShortPairMask_actual,
      generatedSeventhXiShortInputIndex_coordinates]
  · by_cases h2 : k.val < 15336
    · simp only [generatedSeventhXiShortPacketLabel, generatedSeventhXiShortPacketMask,
        h1, h2, dite_false, dite_true]
      exact ho _ _
    · simp only [generatedSeventhXiShortPacketLabel, generatedSeventhXiShortPacketMask,
        h1, h2, dite_false]
      exact hd _ _

/-- Exact inverse-index certificates define the packet permutation without assuming bijectivity. -/
def generatedSeventhXiShortPacketPermutation
    (hleft : ∀ k : Fin 27624,
      generatedSeventhXiShortPacketInverseIndex (generatedSeventhXiShortPacketImageIndex k) = k)
    (hright : ∀ k : Fin 27624,
      generatedSeventhXiShortPacketImageIndex (generatedSeventhXiShortPacketInverseIndex k) = k) :
    Equiv.Perm (Fin 27624) where
  toFun := generatedSeventhXiShortPacketImageIndex
  invFun := generatedSeventhXiShortPacketInverseIndex
  left_inv := hleft
  right_inv := hright

private theorem sign_bool (b : Bool) :
    qSign (golayBooleanCast b) = ((if b then (-1 : ℤ) else 1) : ℝ) := by
  cases b <;> simp [golayBooleanCast, qSign]

/-- Full genuine mask images, central signs and inverse indices fix the complete labelled packet. -/
theorem generatedSeventhXiShortPacketVector_fixed_of_certificates
    (hsource : ∀ k : Fin 27624, griessShortQ (generatedSeventhXiShortPacketLabel k) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortPacketMask k))
    (hleft : ∀ k : Fin 27624,
      generatedSeventhXiShortPacketInverseIndex (generatedSeventhXiShortPacketImageIndex k) = k)
    (hright : ∀ k : Fin 27624,
      generatedSeventhXiShortPacketImageIndex (generatedSeventhXiShortPacketInverseIndex k) = k)
    (himage : ∀ k : Fin 27624,
      generatedSeventhXiShortQImageFast (generatedSeventhXiShortPacketMask k) =
        generatedSeventhXiShortPacketMask (generatedSeventhXiShortPacketImageIndex k))
    (hphase : ∀ k : Fin 27624,
      (if generatedSeventhXiShortQPhaseFast (generatedSeventhXiShortPacketMask k)
        then (-1 : ℤ) else 1) * generatedSeventhXiShortPacketCoefficient k =
          generatedSeventhXiShortPacketCoefficient (generatedSeventhXiShortPacketImageIndex k)) :
    localShortOperator generatedSeventhXiPlaneFiber generatedSeventhXiShortPacketVector =
      generatedSeventhXiShortPacketVector := by
  unfold generatedSeventhXiShortPacketVector
  apply generatedSeventhXiPlaneShort_sparse_fixed
    generatedSeventhXiShortPacketLabel
    (fun k => (generatedSeventhXiShortPacketCoefficient k : ℝ) / 32)
    (generatedSeventhXiShortPacketPermutation hleft hright)
  · intro k
    change (generatedSeventhXiPlaneQMatrixHom
      (griessShortQ (generatedSeventhXiShortPacketLabel k))).base =
        (griessShortQ (generatedSeventhXiShortPacketLabel
          (generatedSeventhXiShortPacketImageIndex k))).base
    rw [hsource k, hsource (generatedSeventhXiShortPacketImageIndex k),
      generatedSeventhXiShortQFast_image]
    change Multiplicative.ofAdd (monsterCo1GeometryBinaryMaskDecode _) =
      Multiplicative.ofAdd (monsterCo1GeometryBinaryMaskDecode _)
    rw [himage k]
  · intro k
    change qSign (Multiplicative.toAdd
      (generatedSeventhXiPlaneQMatrixHom
        (griessShortQ (generatedSeventhXiShortPacketLabel k))).coeff) *
      ((generatedSeventhXiShortPacketCoefficient k : ℝ) / 32) =
        (generatedSeventhXiShortPacketCoefficient (generatedSeventhXiShortPacketImageIndex k) : ℝ) /
          32
    rw [hsource k, generatedSeventhXiShortQFast_image]
    change qSign (golayBooleanCast
      (generatedSeventhXiShortQPhaseFast (generatedSeventhXiShortPacketMask k))) * _ = _
    rw [sign_bool]
    have h := congrArg (fun z : ℤ => (z : ℝ) / 32) (hphase k)
    simp only [Int.cast_mul] at h
    calc
      _ = ((if generatedSeventhXiShortQPhaseFast (generatedSeventhXiShortPacketMask k)
          then (-1 : ℤ) else 1) * generatedSeventhXiShortPacketCoefficient k : ℤ) / (32 : ℝ) := by
        push_cast
        ring
      _ = _ := by simpa only [Int.cast_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
