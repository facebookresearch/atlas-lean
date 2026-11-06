/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact mask parity tests certify the original full two-core line condition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineCertificate

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Exact row masks of all twelve actual two-core sign generators. -/
def monsterCo1GeometryBinarySignMasks (k : Fin 12) : Fin 24 → ℕ :=
  monsterCo1GeometryBinaryOperatorMasks ⟨k.val + 1, by omega⟩

/-- The row catalogue denotes the original actual sign matrices without changing any phase. -/
theorem monsterCo1GeometryBinarySignMasks_decode (k : Fin 12) :
    monsterCo1GeometrySignBinary k =
      monsterCo1GeometryBinaryMaskMatrix (monsterCo1GeometryBinarySignMasks k) := by
  have h : monsterCo1GeometryTransportOperatorMatrix ⟨k.val + 1, by omega⟩ =
      monsterCo1GeometrySignBinary k := by
    fin_cases k <;> rfl
  exact h.symm.trans (monsterCo1GeometryBinaryOperatorMasks_decode ⟨k.val + 1, by omega⟩)

/-- A complete parity check yields the literal actual two-core sign action. -/
theorem monsterCo1GeometryBinarySignMask_action (k : Fin 12) (b c : ℕ)
    (check : ∀ i : Fin 24,
      (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks k i) b).testBit 0 =
        c.testBit i.val) :
    monsterCo1GeometrySignBinary k *ᵥ monsterCo1GeometryBinaryMaskDecode b =
      monsterCo1GeometryBinaryMaskDecode c :=
  monsterCo1GeometryBinaryMaskVector_certificate _ _ _ _ b c
    (monsterCo1GeometryBinarySignMasks_decode k) rfl rfl check

/-- Complete parity checks on all actual two-core generators prove the original genuine line,
using actual transported points and one actual generator swapping the pair. -/
theorem monsterCo1GeometryVectorLineMask_certificate (g : Co1)
    (p q r : MonsterCo1GeometryPoint) (b c : ℕ) (w : Fin 12)
    (hp : g • monsterCo1GeometryBasePoint = p)
    (hq : (g⁻¹ • q).val = monsterCo1GeometryBinaryMaskDecode b)
    (hr : (g⁻¹ • r).val = monsterCo1GeometryBinaryMaskDecode c)
    (hbu : (Pi.single (11 : Fin 24) (1 : ZMod 2)) ≠ monsterCo1GeometryBinaryMaskDecode b)
    (hbv : (Pi.single (11 : Fin 24) (1 : ZMod 2)) ≠ monsterCo1GeometryBinaryMaskDecode c)
    (hbc : monsterCo1GeometryBinaryMaskDecode (n := 24) b ≠
      monsterCo1GeometryBinaryMaskDecode c)
    (hb : ∀ k : Fin 12,
      (∀ i : Fin 24,
        (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks k i) b).testBit 0 =
          b.testBit i.val) ∨
      (∀ i : Fin 24,
        (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks k i) b).testBit 0 =
          c.testBit i.val))
    (hc : ∀ k : Fin 12,
      (∀ i : Fin 24,
        (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks k i) c).testBit 0 =
          b.testBit i.val) ∨
      (∀ i : Fin 24,
        (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks k i) c).testBit 0 =
          c.testBit i.val))
    (hw : ∀ i : Fin 24,
      (monsterCo1GeometryBinaryMaskDot 24 (monsterCo1GeometryBinarySignMasks w i) b).testBit 0 =
        c.testBit i.val) : monsterCo1GeometryLine p q r := by
  apply monsterCo1GeometryVectorLine_certificate g p q r _ _ w hp hq hr hbu hbv hbc
  · intro k
    rcases hb k with h | h
    · exact Or.inl (monsterCo1GeometryBinarySignMask_action k b b h)
    · exact Or.inr (monsterCo1GeometryBinarySignMask_action k b c h)
  · intro k
    rcases hc k with h | h
    · exact Or.inl (monsterCo1GeometryBinarySignMask_action k c b h)
    · exact Or.inr (monsterCo1GeometryBinarySignMask_action k c c h)
  · exact monsterCo1GeometryBinarySignMask_action w b c hw

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
