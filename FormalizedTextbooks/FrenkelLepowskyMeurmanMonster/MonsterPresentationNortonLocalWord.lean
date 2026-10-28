/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete literal Norton u word as a genuine local spin/Leech fiber element. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82SourceBinding

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual seven-factor local fiber lift of the literal source Norton u word. -/
noncomputable def monsterNortonUFiber : localFiberSubgroup :=
  monsterSourceY82Fiber * localFiberIncl (sourceQCode 2049 1) *
    localFiberIncl (sourceQCocode (golayLabelCoefficients 1807)) *
      (monsterSourcePermutationFiber 0)⁻¹ * xiSpinLocalFiber *
        (monsterSourcePermutationFiber 1)⁻¹ * xiSpinLocalFiber

/-- Its image in the actual simultaneous-sign quotient H. -/
noncomputable def monsterNortonULocal : H :=
  QuotientGroup.mk' localDiagonalSubgroup monsterNortonUFiber

/-- The quotient image is exactly the product of the proved actual local source lifts. -/
theorem monsterNortonULocal_word :
    monsterNortonULocal = monsterSourceY82Local * inclQ (sourceQCode 2049 1) *
      inclQ (sourceQCocode (golayLabelCoefficients 1807)) *
        (monsterSourcePermutationLocal 0)⁻¹ * xiSpinLocal *
          (monsterSourcePermutationLocal 1)⁻¹ * xiSpinLocal := by
  simp only [monsterNortonULocal, monsterNortonUFiber, map_mul, map_inv]
  rfl

/-- The genuine local fiber word equals the complete literal Norton u in named G. -/
theorem monsterNortonULocal_generated :
    localIntoGenerated monsterNortonULocal = y555NortonActualU := by
  rw [monsterNortonULocal_word]
  simp only [map_mul, map_inv]
  rw [show localIntoGenerated monsterSourceY82Local = y555NortonActualY 82 0 from
    monsterSourceY82Generated_eq_actualWord]
  rfl

/-- The actual Norton word belongs to the actual local subgroup image. -/
theorem monsterNortonActualU_mem_local : y555NortonActualU ∈ localIntoGenerated.range :=
  ⟨monsterNortonULocal, monsterNortonULocal_generated⟩

/-- Its spin component is the exact product, with the two actual inverse Parker lifts. -/
theorem monsterNortonUFiber_spin :
    monsterNortonUFiber.val.1 = monsterSourceY82Spin * spinHolomorphIncl (sourceQCode 2049 1) *
      spinHolomorphIncl (sourceQCocode (golayLabelCoefficients 1807)) *
        (monsterSourcePermutationSpin 0)⁻¹ * xiSpinHolomorph *
          (monsterSourcePermutationSpin 1)⁻¹ * xiSpinHolomorph := rfl

/-- Its physical lattice component has the actual sign, permutation and xi orientations. -/
theorem monsterNortonUFiber_leech :
    monsterNortonUFiber.val.2 = monsterSourceY82Isometry *
      (omegaOrbitPermutationIsometry 0)⁻¹ * co1XiIsometry *
        (omegaOrbitPermutationIsometry 1)⁻¹ * co1XiIsometry := by
  change monsterSourceY82Isometry * 1 * 1 *
    (omegaOrbitPermutationIsometry 0)⁻¹ * co1XiIsometry *
      (omegaOrbitPermutationIsometry 1)⁻¹ * co1XiIsometry = _
  rw [mul_one, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
