/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSpinLabels
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignTensorCoords

/-! Executable source label arithmetic for the genuine Golay sign tensor action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Bitwise addition of two actual twelve-bit physical spin labels. -/
def generatedAxisGlobalSpinLabelXor (a b : Fin 4096) : Fin 4096 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 12) a.isLt b.isLt⟩

/-- Actual coordinate addition is exactly this finite bitwise label addition. -/
theorem generatedAxisGlobalSpinLabelXor_coeff (a b : Fin 4096) :
    golayLabelCoefficients (generatedAxisGlobalSpinLabelXor a b) =
      golayLabelCoefficients a + golayLabelCoefficients b := by
  funext i
  change (if (a.val ^^^ b.val).testBit i.val then (1 : ZMod 2) else 0) =
    (if a.val.testBit i.val then 1 else 0) + (if b.val.testBit i.val then 1 else 0)
  cases ha : a.val.testBit i.val <;> cases hb : b.val.testBit i.val
  all_goals simp only [Nat.testBit_xor, ha, hb]
  all_goals decide

/-- The low original dictionary label of a physical twelve-bit row. -/
def generatedAxisGlobalSpinLabelLow (k : Fin 4096) : Fin 2048 :=
  ⟨k.val % 2048, Nat.mod_lt _ (by decide)⟩

/-- The low finite label is precisely the actual original dictionary label. -/
theorem generatedAxisGlobalSpinLabelLow_dictionary (k : Fin 4096) :
    generatedAxisGlobalSpinLabelLow k = spinDictionaryCode (golayLabelCoefficients k) := by
  apply Fin.ext
  simp only [generatedAxisGlobalSpinLabelLow, spinDictionaryCode, spinDictionaryLabel_coeff]

/-- A physical row splits into its actual low dictionary row and its actual all-one bit. -/
theorem generatedAxisGlobalSpinLabel_split (k : Fin 4096) :
    golayLabelCoefficients k = generatedFifthSpinLow (generatedAxisGlobalSpinLabelLow k) +
      (golayLabelCoefficients k 11) • (Pi.single 11 1 : SpinIndex) := by
  obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition (golayLabelCoefficients k)
  rw [← generatedAxisGlobalSpinLabelLow_dictionary] at hb
  have hh := congrFun hb 11
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    generatedFifth_spin_low_last, zero_add, mul_one] at hh
  rw [hh]
  exact hb

/-- The exact original input code for a source sign output dictionary code. -/
def generatedAxisGlobalSignInputCode (a : Fin 4096) (e : Fin 2048) : Fin 2048 :=
  generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabelXor ⟨e.val, by omega⟩ a)

/-- This finite source-code rule satisfies the genuine full spin translation equation. -/
theorem generatedAxisGlobalSignInputCode_translation (a : Fin 4096) (e : Fin 2048) :
    generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow (generatedAxisGlobalSignInputCode a e) +
        (golayLabelCoefficients a 11) • (Pi.single 11 1 : SpinIndex) := by
  let k := generatedAxisGlobalSpinLabelXor (⟨e.val, by omega⟩ : Fin 4096) a
  have hx := generatedAxisGlobalSpinLabelXor_coeff (⟨e.val, by omega⟩ : Fin 4096) a
  have hh := congrFun hx 11
  change golayLabelCoefficients k 11 = generatedFifthSpinLow e 11 +
    golayLabelCoefficients a 11 at hh
  rw [generatedFifth_spin_low_last, zero_add] at hh
  have hs := generatedAxisGlobalSpinLabel_split k
  rw [hh] at hs
  exact hx.symm.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
