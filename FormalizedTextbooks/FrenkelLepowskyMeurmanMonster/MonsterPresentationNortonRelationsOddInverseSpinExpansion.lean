/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete signed sparse basis expansion for the actual odd inverse spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactInverseSpinBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem add_right_eq (t u a : SpinIndex) : t + a = u ↔ t = u + a := by
  have ha : a + a = 0 := by
    ext j
    exact CharTwo.add_self_eq_zero (a j)
  constructor
  · intro h
    have hh := congrArg (fun x : SpinIndex => x + a) h
    simpa only [add_assoc, ha, add_zero] using hh
  · intro h
    rw [h, add_assoc, ha, add_zero]

private theorem q_basis (q : Q) (u : SpinIndex) :
    spinRepresentation q (Pi.single u 1) =
      qSign (spinPhase q (u + spinTranslation q)) •
        (Pi.single (u + spinTranslation q) 1 : SpinSpace) := by
  ext t
  rw [monsterMonomialSpinRepresentation_apply]
  simp only [Pi.single_apply, add_right_eq, Pi.smul_apply, smul_eq_mul]
  by_cases h : t = u + spinTranslation q
  · simp only [h, ite_true]
  · simp only [h, ite_false, mul_zero]

/-- The actual spin output of one inverse transition, including both V translations. -/
def monsterNortonOddInverseSpinExpansionIndex (u : SpinIndex) (a : Fin 64) : SpinIndex :=
  monsterNortonUCompactInverseBasisIndex (u + spinTranslation y555NortonVQ)
    (monsterNortonGrayCoefficients a) + spinTranslation y555NortonVQ

/-- Every transition carries its complete pre-V, inverse-U, and post-V phases. -/
def monsterNortonOddInverseSpinExpansionSign (u : SpinIndex) (a : Fin 64) : ℤ :=
  nortonUIntegerSign (spinPhase y555NortonVQ (u + spinTranslation y555NortonVQ)) *
    monsterNortonUCompactInverseBasisSign (u + spinTranslation y555NortonVQ)
      (monsterNortonGrayCoefficients a) *
    nortonUIntegerSign (spinPhase y555NortonVQ (monsterNortonOddInverseSpinExpansionIndex u a))

/-- The exact unnormalized signed sixty-four-entry output packet of a spin basis vector. -/
noncomputable def monsterNortonOddInverseSpinExpansionPacket (u : SpinIndex) : SpinSpace :=
  ∑ a : Fin 64, (monsterNortonOddInverseSpinExpansionSign u a : ℝ) •
    Pi.single (monsterNortonOddInverseSpinExpansionIndex u a) 1

private theorem incl_apply (q : Q) (x : SpinSpace) :
    (spinHolomorphIncl q).val x = spinRepresentation q x := rfl

set_option maxHeartbeats 2000000 in
-- Bound normalization of the concrete orthogonal word and its complete signed finite sum.
/-- The actual three-factor spin word gives its full signed basis packet. -/
theorem monsterNortonOddInverseSpinExpansion_basis (u : SpinIndex) :
    (spinHolomorphIncl y555NortonVQ * monsterNortonUFiber.val.1⁻¹ *
      spinHolomorphIncl y555NortonVQ).val (Pi.single u 1) =
      (1 / 8 : ℝ) • monsterNortonOddInverseSpinExpansionPacket u := by
  rw [nortonUIntegerSpin_mul_apply, nortonUIntegerSpin_mul_apply, incl_apply, incl_apply,
    q_basis, map_smul, monsterNortonUCompactInverseSpin_actual_basis_fin64]
  simp only [map_smul, map_sum, q_basis, smul_smul]
  simp only [monsterNortonOddInverseSpinExpansionPacket, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [monsterNortonOddInverseSpinExpansionSign, Int.cast_mul,
    nortonUIntegerSign_real, monsterNortonOddInverseSpinExpansionIndex]
  congr 1
  ring

private theorem sourceZ_apply (e : SpinHolomorph) (d : Fin 2048) :
    e.val (nortonUIntegerEmbed (monsterNortonSourceZInteger d)) =
      e.val (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1) +
        e.val (Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1) := by
  rw [monsterNortonSourceZInteger_embed]
  exact map_add e.val _ _

/-- The complete actual odd numerator is the negative sum of its two source basis packets. -/
theorem monsterNortonOddInverseSpinNumerator_expansion (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonOddInverseSpinNumerator d) =
      -(monsterNortonOddInverseSpinExpansionPacket
          (golayLabelCoefficients ⟨d.val, by omega⟩) +
        monsterNortonOddInverseSpinExpansionPacket
          (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) := by
  have h := monsterNortonOddInverseSpinNumerator_actual d
  rw [sourceZ_apply, monsterNortonOddInverseSpinExpansion_basis,
    monsterNortonOddInverseSpinExpansion_basis, ← smul_add] at h
  have ht := congrArg (fun x : SpinSpace => (-8 : ℝ) • x) h
  simp only [smul_smul] at ht
  norm_num at ht
  simpa only [neg_add] using ht.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
