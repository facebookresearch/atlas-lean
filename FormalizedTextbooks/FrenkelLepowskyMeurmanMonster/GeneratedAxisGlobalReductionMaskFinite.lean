/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi

/-! Bounded integer masks are in bijection with the genuine finite binary
coordinate module. This gives a checked finite certificate domain. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Bounded masks decode into the actual binary coordinate vectors. -/
def generatedAxisGlobalMaskDecodeFinite (n : ℕ) (a : Fin (2 ^ n)) : Fin n → ZMod 2 :=
  monsterCo1GeometryBinaryMaskDecode a.val

/-- The bound excludes discarded high bits, so exact coordinate decoding is injective. -/
theorem generatedAxisGlobalMaskDecodeFinite_injective (n : ℕ) :
    Function.Injective (generatedAxisGlobalMaskDecodeFinite n) := by
  intro a b he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have h := congrFun he (⟨i, hi⟩ : Fin n)
    cases ha : a.val.testBit i <;> cases hb : b.val.testBit i <;>
      simp_all [generatedAxisGlobalMaskDecodeFinite, monsterCo1GeometryBinaryMaskDecode]
  · have hn : n ≤ i := by omega
    have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hn
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.isLt hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.isLt hp)]

/-- Every genuine binary vector has a bounded integer mask, with no independent coding model. -/
theorem generatedAxisGlobalMaskDecodeFinite_bijective (n : ℕ) :
    Function.Bijective (generatedAxisGlobalMaskDecodeFinite n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨generatedAxisGlobalMaskDecodeFinite_injective n, ?_⟩
  simp [Fintype.card_pi]

/-- The exact finite-coordinate equivalence used to specialize orbit certificates. -/
noncomputable def generatedAxisGlobalMaskFiniteEquiv (n : ℕ) :
    Fin (2 ^ n) ≃ (Fin n → ZMod 2) :=
  Equiv.ofBijective (generatedAxisGlobalMaskDecodeFinite n)
    (generatedAxisGlobalMaskDecodeFinite_bijective n)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
