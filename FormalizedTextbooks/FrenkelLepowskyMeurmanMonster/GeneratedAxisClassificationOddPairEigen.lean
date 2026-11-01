/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary

/-! The distinguished Hadamard spin state is a common eigenvector of all
actual pair-short operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every pair syndrome has zero all-one coordinate. -/
theorem generatedOddPairSyndrome_last (p : Fin 276) : griessPairSyndrome p 11 = 0 := by
  have hb : ∀ i : Fin 24, golayGeneratorBit 11 i = 1 := by decide +kernel
  simp only [griessPairSyndrome, hb]
  decide +kernel

private theorem low_zero : generatedOddSpinLow (0 : SpinIndex) = 0 := rfl

private theorem low_omega : generatedOddSpinLow (Pi.single (11 : Fin 12) 1) = 0 := by
  ext j
  simp [generatedOddSpinLow, Pi.single_apply, Fin.ext_iff]
  omega

/-- Every actual minus-pair operator fixes the distinguished Hadamard state. -/
theorem generatedOddSpin_pair_minus_eigen (p : Fin 276) :
    spinOperator (griessShortQ (Sum.inl (0, p))) (generatedOddSpinState 0 1 0) =
      generatedOddSpinState 0 1 0 := by
  rw [generatedOddSpinState_pauli, griessPairMinus_translation, griessPairMinus_modulation,
    low_zero, generatedOddPairSyndrome_last, zero_add]
  have hs : generatedOddSpinOutputSign (griessShortQ (Sum.inl (0, p))) = 0 := by
    simp only [generatedOddSpinOutputSign, griessShortQ_coeff, griessPairMinus_translation,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [hs]

/-- Every actual plus-pair operator negates the distinguished Hadamard state. -/
theorem generatedOddSpin_pair_plus_eigen (p : Fin 276) :
    spinOperator (griessShortQ (Sum.inl (1, p))) (generatedOddSpinState 0 1 0) =
      -generatedOddSpinState 0 1 0 := by
  rw [generatedOddSpinState_pauli, griessPairPlus_translation, griessPairPlus_modulation,
    low_omega, generatedOddPairSyndrome_last, zero_add]
  have hs : generatedOddSpinOutputSign (griessShortQ (Sum.inl (1, p))) = 1 := by
    unfold generatedOddSpinOutputSign
    rw [griessPairPlus_translation, griessShortQ_coeff]
    have hl : ∀ j : Fin 11, (Pi.single (11 : Fin 12) (1 : ZMod 2) : SpinIndex) j.castSucc = 0 := by
      intro j
      exact congrFun low_omega j
    simp only [Pi.single_eq_same, hl, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rw [hs]
  ext t
  simp only [generatedOddSpinState, Pi.neg_apply, qSign_add, qSign_one,
    one_mul, zero_add]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
