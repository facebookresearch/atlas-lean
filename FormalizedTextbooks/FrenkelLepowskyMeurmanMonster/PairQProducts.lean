/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Products of the preferred pair lifts in the source spin dictionary.
All pair cocodes have even weight, so these products have central bit zero.
Source: Seysen, arXiv:2002.10921v3, §§6.1–6.2.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

theorem griessPairSyndrome_omega (p : Fin 276) : griessPairSyndrome p 11 = 0 := by
  have hg : ∀ i : Fin 24, (golayGeneratorBit 11 i : ZMod 2) = 1 := by decide +kernel
  rw [griessPairSyndrome, hg, hg]
  decide

theorem griessPairQ_translation (s : Fin 2) (p : Fin 276) :
    spinTranslation (griessShortQ (Sum.inl (s, p))) =
      if s = 0 then 0 else Pi.single 11 1 := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [ite_true, griessPairMinus_translation]
  · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, griessPairPlus_translation]

theorem griessPairQ_modulation (s : Fin 2) (p : Fin 276) :
    spinModulation (griessShortQ (Sum.inl (s, p))) = griessPairSyndrome p := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · exact griessPairMinus_modulation p
  · exact griessPairPlus_modulation p

theorem griessPairQ_product_coeff (s t : Fin 2) (p q : Fin 276) :
    toAdd (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).coeff = 0 := by
  change (0 + 0) + ∑ k : Fin 12,
    spinTranslation (griessShortQ (Sum.inl (s, p))) k *
      spinModulation (griessShortQ (Sum.inl (t, q))) k = 0
  rw [griessPairQ_translation, griessPairQ_modulation]
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, ite_false, zero_add, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact griessPairSyndrome_omega q

theorem griessPairQ_product_sign (s t : Fin 2) (p q : Fin 276) :
    qSign (toAdd (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).coeff) = 1 := by
  rw [griessPairQ_product_coeff, qSign_zero]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
