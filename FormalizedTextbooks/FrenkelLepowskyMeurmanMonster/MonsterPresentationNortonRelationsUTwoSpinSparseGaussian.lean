/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sparse integer basis transport for the actual 16-term translation Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem translate_twice (u v : SpinIndex) : (u + v) + v = u := by
  ext i
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem source_translation_iff (b n : Fin 4096) (a : Fin 16) :
    nortonUIntegerLabel (golayLabelCoefficients n + golayLabelCoefficients
      (monsterNortonUTwoGaussianSpinLabel a)) = b ↔
      n = nortonUIntegerLabel (golayLabelCoefficients b + golayLabelCoefficients
        (monsterNortonUTwoGaussianSpinLabel a)) := by
  constructor
  · intro h
    have hs := congrArg golayLabelCoefficients h
    rw [nortonUIntegerLabel_inverse] at hs
    have ht := congrArg (fun u => u + golayLabelCoefficients
      (monsterNortonUTwoGaussianSpinLabel a)) hs
    rw [translate_twice] at ht
    have hl := congrArg nortonUIntegerLabel ht
    simpa only [nortonUIntegerLabel_coeff] using hl
  · intro h
    have hs := congrArg golayLabelCoefficients h
    rw [nortonUIntegerLabel_inverse] at hs
    have ht := congrArg (fun u => u + golayLabelCoefficients
      (monsterNortonUTwoGaussianSpinLabel a)) hs
    rw [translate_twice] at ht
    have hl := congrArg nortonUIntegerLabel ht
    simpa only [nortonUIntegerLabel_coeff] using hl

/-- A source basis delta has exactly the sixteen actual Gaussian translated entries. -/
theorem monsterNortonUTwoGaussianInteger_delta (b : Fin 4096) (c : ℤ) :
    monsterNortonUTwoGaussianInteger (Pi.single b c) = fun n =>
      ∑ a : Fin 16,
        if n = nortonUIntegerLabel (golayLabelCoefficients b + golayLabelCoefficients
          (monsterNortonUTwoGaussianSpinLabel a)) then
          monsterNortonUTwoGaussianSign a * c else 0 := by
  funext n
  simp only [monsterNortonUTwoGaussianInteger, Pi.single_apply, mul_ite, mul_zero,
    source_translation_iff]

/-- The actual integer Gaussian distributes over every finite sparse input packet. -/
theorem monsterNortonUTwoGaussianInteger_sum {I : Type*} [Fintype I]
    (v : I → NortonUIntegerVector) :
    monsterNortonUTwoGaussianInteger (fun n => ∑ i, v i n) = fun n => ∑ i,
      monsterNortonUTwoGaussianInteger (v i) n := by
  funext n
  simp only [monsterNortonUTwoGaussianInteger, Finset.mul_sum]
  exact Finset.sum_comm

/-- Each finite source packet is transported by its exact translated basis formula. -/
theorem monsterNortonUTwoGaussianInteger_packet {I : Type*} [Fintype I]
    (b : I → Fin 4096) (c : I → ℤ) :
    monsterNortonUTwoGaussianInteger (fun n => ∑ i, (Pi.single (b i) (c i) :
      NortonUIntegerVector) n) =
      fun n => ∑ i, ∑ a : Fin 16,
        if n = nortonUIntegerLabel (golayLabelCoefficients (b i) + golayLabelCoefficients
          (monsterNortonUTwoGaussianSpinLabel a)) then
          monsterNortonUTwoGaussianSign a * c i else 0 := by
  rw [monsterNortonUTwoGaussianInteger_sum]
  simp_rw [monsterNortonUTwoGaussianInteger_delta]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
