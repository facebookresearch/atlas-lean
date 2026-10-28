/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sparse integer transport under the genuine extraspecial Q spin action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegerBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual integer Q action preserves every finite integer linear combination. -/
theorem monsterNortonUIntegerQ_sum {ι : Type*} [Fintype ι] (q : Q)
    (c : ι → ℤ) (v : ι → NortonUIntegerVector) :
    nortonUIntegerQ q (∑ a : ι, c a • v a) = ∑ a : ι, c a • nortonUIntegerQ q (v a) := by
  funext n
  simp only [nortonUIntegerQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual integer Q operator preserves subtraction. -/
theorem monsterNortonUIntegerQ_sub (q : Q) (v w : NortonUIntegerVector) :
    nortonUIntegerQ q (v - w) = nortonUIntegerQ q v - nortonUIntegerQ q w := by
  funext n
  simp only [nortonUIntegerQ, Pi.sub_apply, mul_sub]

/-- A single integer spin delta has the exact actual translated label and complete phase. -/
theorem monsterNortonUIntegerQ_delta (q : Q) (d : Fin 4096) :
    nortonUIntegerQ q (Pi.single d 1) =
      nortonUIntegerSign (spinPhase q (golayLabelCoefficients d + spinTranslation q)) •
        (Pi.single (nortonUIntegerLabel (golayLabelCoefficients d + spinTranslation q)) 1 :
          NortonUIntegerVector) := by
  have hs := nortonUIntegerQ_embed q (Pi.single d 1)
  conv_lhs at hs => rw [monsterNortonUIntegerEmbed_single]
  change spinOperator q (Pi.single (golayLabelCoefficients d) 1) =
    nortonUIntegerEmbed (nortonUIntegerQ q (Pi.single d 1)) at hs
  rw [monsterNortonQ_spin_delta] at hs
  funext n
  apply Int.cast_injective (α := ℝ)
  have hn := congrFun hs (golayLabelCoefficients n)
  have he : n = nortonUIntegerLabel (golayLabelCoefficients d + spinTranslation q) ↔
      golayLabelCoefficients n = golayLabelCoefficients d + spinTranslation q := by
    constructor
    · intro h
      rw [h, nortonUIntegerLabel_inverse]
    · intro h
      have hh := congrArg nortonUIntegerLabel h
      rwa [nortonUIntegerLabel_coeff] at hh
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, nortonUIntegerSign_real,
    Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, he]
  simpa only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, spinPhase, Pi.single_apply] using hn.symm

/-- A source Y integer vector transports through two genuine signed integer deltas. -/
theorem monsterNortonUIntegerQ_source_Y (q : Q) (d : Fin 2048) :
    nortonUIntegerQ q (monsterNortonSourceYInteger d) =
      nortonUIntegerSign (spinPhase q
        (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q)) •
          (Pi.single (nortonUIntegerLabel
            (golayLabelCoefficients ⟨d.val, by omega⟩ + spinTranslation q)) 1 :
              NortonUIntegerVector) -
        nortonUIntegerSign (spinPhase q
          (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q)) •
            (Pi.single (nortonUIntegerLabel
              (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + spinTranslation q)) 1 :
                NortonUIntegerVector) := by
  rw [monsterNortonSourceYInteger, monsterNortonUIntegerQ_sub,
    monsterNortonUIntegerQ_delta, monsterNortonUIntegerQ_delta]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
