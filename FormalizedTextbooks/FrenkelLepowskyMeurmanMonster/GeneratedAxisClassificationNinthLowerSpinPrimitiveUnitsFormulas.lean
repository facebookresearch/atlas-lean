/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQData

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Explicit original full-Q action of each positive primitive source letter. -/
def generatedNinthLowerSpinPrimitiveUnitsPositiveQImage (k : Fin 15) (q : Q) : Q :=
  if h : k.val < 11 then
    monsterNortonYImage (generatedNinthLowerSpinCode ⟨k.val, h⟩) q
  else if k.val = 11 then q
  else if h' : k.val < 14 then
    monsterSourcePermutationImage ⟨k.val - 12, by omega⟩ q
  else xiSpinGImage (xiSpinGammaImage q)

/-- Each positive primitive spin factor has its defining original full-Q conjugation. -/
theorem generatedNinth_lower_spin_primitive_units_positive_conjugation (k : Fin 15) (q : Q) :
    spinConjugation (generatedNinthLowerSpinPositiveFiber k).val.1 q =
      generatedNinthLowerSpinPrimitiveUnitsPositiveQImage k q := by
  unfold generatedNinthLowerSpinPositiveFiber generatedNinthLowerSpinPrimitiveUnitsPositiveQImage
  split_ifs
  · change spinConjugation
      (monsterNortonYSpin (generatedNinthLowerSpinCode _)) q = _
    exact monsterNortonYSpin_conjugation _ q
  · change spinConjugation 1 q = q
    rw [map_one]
    rfl
  · change spinConjugation (monsterSourcePermutationSpin _) q = _
    exact monsterSourcePermutationSpin_conjugation _ q
  · change spinConjugation xiSpinHolomorph q = _
    exact xiSpinHolomorph_conjugation q


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
