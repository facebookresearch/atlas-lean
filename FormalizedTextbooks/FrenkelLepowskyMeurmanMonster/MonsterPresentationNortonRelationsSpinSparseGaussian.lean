/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sparse integer basis transport for the actual 64-term translation Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem translate_twice (u v : SpinIndex) : (u + v) + v = u := by
  ext i
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem source_translation_iff (b n : Fin 4096) (a : XiGrayIndex) :
    nortonUIntegerLabel (golayLabelCoefficients n + xiGrayCode a) = b ↔
      n = nortonUIntegerLabel (golayLabelCoefficients b + xiGrayCode a) := by
  constructor
  · intro h
    have hs := congrArg golayLabelCoefficients h
    rw [nortonUIntegerLabel_inverse] at hs
    have ht := congrArg (fun u => u + xiGrayCode a) hs
    rw [translate_twice] at ht
    have hl := congrArg nortonUIntegerLabel ht
    simpa only [nortonUIntegerLabel_coeff] using hl
  · intro h
    have hs := congrArg golayLabelCoefficients h
    rw [nortonUIntegerLabel_inverse] at hs
    have ht := congrArg (fun u => u + xiGrayCode a) hs
    rw [translate_twice] at ht
    have hl := congrArg nortonUIntegerLabel ht
    simpa only [nortonUIntegerLabel_coeff] using hl

/-- A source basis delta has exactly the sixty-four actual Gaussian translated entries. -/
theorem monsterNortonUIntegerG_delta (b : Fin 4096) (c : ℤ) :
    nortonUIntegerG (Pi.single b c) = fun n =>
      ∑ a : XiGrayIndex,
        if n = nortonUIntegerLabel (golayLabelCoefficients b + xiGrayCode a) then
          xiGraySign a * c else 0 := by
  funext n
  simp only [nortonUIntegerG, Pi.single_apply, mul_ite, mul_zero,
    source_translation_iff]

/-- The actual integer Gaussian distributes over every finite sparse input packet. -/
theorem monsterNortonUIntegerG_sum {I : Type*} [Fintype I]
    (v : I → NortonUIntegerVector) :
    nortonUIntegerG (fun n => ∑ i, v i n) = fun n => ∑ i, nortonUIntegerG (v i) n := by
  funext n
  simp only [nortonUIntegerG, Finset.mul_sum]
  exact Finset.sum_comm

/-- Each finite source packet is transported by its exact translated basis formula. -/
theorem monsterNortonUIntegerG_packet {I : Type*} [Fintype I]
    (b : I → Fin 4096) (c : I → ℤ) :
    nortonUIntegerG (fun n => ∑ i, (Pi.single (b i) (c i) : NortonUIntegerVector) n) =
      fun n => ∑ i, ∑ a : XiGrayIndex,
        if n = nortonUIntegerLabel (golayLabelCoefficients (b i) + xiGrayCode a) then
          xiGraySign a * c i else 0 := by
  rw [monsterNortonUIntegerG_sum]
  simp_rw [monsterNortonUIntegerG_delta]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
