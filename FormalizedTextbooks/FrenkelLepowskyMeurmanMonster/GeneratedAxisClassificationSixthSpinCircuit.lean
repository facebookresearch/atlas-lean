/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi

/-! An exact integer circuit for the original eight-factor sixth-axis spin word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original forward Parker permutation spin operator with its complete quadratic sign. -/
def generatedSixthIntegerPermutation (k : Fin 2) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n =>
  let t := (monsterSourcePermutationCode k).symm (golayLabelCoefficients n)
  nortonUIntegerSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) t) *
    v (nortonUIntegerLabel t)

/-- The finite integer operation embeds as the genuine original forward source spin lift. -/
theorem generatedSixth_integer_permutation_embed (k : Fin 2) (v : NortonUIntegerVector) :
    (monsterSourcePermutationSpin k).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedSixthIntegerPermutation k v) := by
  ext t
  simp only [monsterSourcePermutationSpin_apply, nortonUIntegerEmbed,
    generatedSixthIntegerPermutation, nortonUIntegerLabel_inverse,
    Int.cast_mul, nortonUIntegerSign_real]

/-- The actual original two-point Hadamard state, in integral source-label coordinates. -/
def generatedSixthIntegerSpinInitial (n : Fin 4096) : ℤ :=
  if generatedOddSpinLow (golayLabelCoefficients n) = 0 then
    nortonUIntegerSign (golayLabelCoefficients n 11) else 0

/-- The initial integer data is the genuine distinguished third-axis spin state. -/
theorem generatedSixth_integer_initial_embed :
    nortonUIntegerEmbed generatedSixthIntegerSpinInitial = generatedOddSpinState 0 1 0 := by
  ext t
  simp only [nortonUIntegerEmbed, generatedSixthIntegerSpinInitial,
    nortonUIntegerLabel_inverse, Int.cast_ite, Int.cast_zero, nortonUIntegerSign_real,
    generatedOddSpinState, zero_add, one_mul]

/-- The integer circuit retains three Gaussian factors and five actual source permutations. -/
def generatedSixthIntegerSpinWord (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerXi (generatedSixthIntegerPermutation 1
    (nortonUIntegerXi (generatedSixthIntegerPermutation 0
      (generatedSixthIntegerPermutation 1 (generatedSixthIntegerPermutation 0
        (nortonUIntegerXi (generatedSixthIntegerPermutation 0 v)))))))

/-- The circuit applied to the actual distinguished initial state. -/
def generatedSixthIntegerSpinNumerator : NortonUIntegerVector :=
  generatedSixthIntegerSpinWord generatedSixthIntegerSpinInitial

private def spinProjection : localFiberSubgroup →* SpinHolomorph :=
  (MonoidHom.fst SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype

private theorem spin_word_projection :
    spinProjection generatedSixthLocalFiber =
      xiSpinHolomorph * monsterSourcePermutationSpin 1 * xiSpinHolomorph *
        monsterSourcePermutationSpin 0 * monsterSourcePermutationSpin 1 *
        monsterSourcePermutationSpin 0 * xiSpinHolomorph * monsterSourcePermutationSpin 0 := by
  have hx : spinProjection xiSpinLocalFiber = xiSpinHolomorph := rfl
  have hp (k : Fin 2) : spinProjection (monsterSourcePermutationFiber k) =
      monsterSourcePermutationSpin k := rfl
  simp only [generatedSixthLocalFiber, map_mul, hx, hp]

private theorem spin_projection_apply (f : localFiberSubgroup) (v : SpinSpace) :
    f.val.1.val v = (spinProjection f).val v := rfl

private theorem abstract_spin_word_embed
    (p₀ p₁ x : SpinHolomorph) (P₀ P₁ X : NortonUIntegerVector → NortonUIntegerVector)
    (hp₀ : ∀ v, p₀.val (nortonUIntegerEmbed v) = nortonUIntegerEmbed (P₀ v))
    (hp₁ : ∀ v, p₁.val (nortonUIntegerEmbed v) = nortonUIntegerEmbed (P₁ v))
    (hx : ∀ v, x.val (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (X v)) (v : NortonUIntegerVector) :
    (x * p₁ * x * p₀ * p₁ * p₀ * x * p₀).val (nortonUIntegerEmbed v) =
      (1 / 512 : ℝ) • nortonUIntegerEmbed (X (P₁ (X (P₀ (P₁ (P₀ (X (P₀ v)))))))) := by
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hp₀, hp₁, hx, map_smul,
    smul_smul]
  norm_num

/-- The actual eight-factor operator embeds the integer circuit with exact denominator512. -/
theorem generatedSixth_integer_spin_word_embed (v : NortonUIntegerVector) :
    generatedSixthLocalFiber.val.1.val (nortonUIntegerEmbed v) =
      (1 / 512 : ℝ) • nortonUIntegerEmbed (generatedSixthIntegerSpinWord v) := by
  rw [spin_projection_apply, spin_word_projection]
  exact abstract_spin_word_embed (monsterSourcePermutationSpin 0)
    (monsterSourcePermutationSpin 1) xiSpinHolomorph
    (generatedSixthIntegerPermutation 0) (generatedSixthIntegerPermutation 1)
    nortonUIntegerXi (generatedSixth_integer_permutation_embed 0)
    (generatedSixth_integer_permutation_embed 1) nortonUIntegerXi_embed v

/-- The final numerator is the genuine spin image of the original third-axis state. -/
theorem generatedSixth_integer_spin_numerator_actual :
    generatedSixthLocalFiber.val.1.val (generatedOddSpinState 0 1 0) =
      (1 / 512 : ℝ) • nortonUIntegerEmbed generatedSixthIntegerSpinNumerator := by
  rw [← generatedSixth_integer_initial_embed, generatedSixth_integer_spin_word_embed]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
