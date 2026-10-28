/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact inverse-triality step in the literal first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegralTensorColumn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorInitial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact two source vectors corresponding to a physical spin delta. -/
noncomputable def monsterNortonLine01SourcePair (t : SpinIndex) (i : Fin 24) : GriessSpace :=
  (qSign (t 11) * (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1
    else 1)) • trialityXYZBasis 0 (finProdFinEquiv (spinDictionaryCode t, i)) +
    qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) •
      trialityXYZBasis 1 (finProdFinEquiv (spinDictionaryCode t, i))

/-- The whole reached state is a rational finite sum of genuine source X and Y vectors. -/
noncomputable def monsterNortonLine01TensorAfterVUExtraInverse : GriessSpace :=
  (1 / 64 : ℝ) • ∑ a : Fin 64,
    (monsterNortonLine01InitialSpinSigns a : ℝ) • ∑ i : Fin 24,
      (monsterNortonUNumerator1 i 0 : ℝ) •
        monsterNortonLine01SourcePair
          (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a)) i

private theorem physical_first_column (i : Fin 24) :
    monsterNortonUFiber.val.2.val (Pi.single 0 1) i =
      (1 / 4 : ℝ) * (monsterNortonUNumerator1 i 0 : ℝ) := by
  rw [monsterNortonUFiber_leech_matrix]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, monsterNortonUMatrixQ,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

private theorem sqrt_coefficient (s n : ℝ) :
    (1 / Real.sqrt 2 * (1 / 8)) * s * ((1 / 4) * n) * (1 / Real.sqrt 2) =
      (1 / 64) * s * n := by
  have hh : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (1 / Real.sqrt 2 : ℝ) * (1 / 8) * (1 / Real.sqrt 2) * (1 / 4) =
      1 / 64 := by
    field_simp
    nlinarith [hh]
  calc
    _ = ((1 / Real.sqrt 2) * (1 / 8) * (1 / Real.sqrt 2) * (1 / 4)) * s * n := by ring
    _ = _ := by rw [hs]

/-- Inverse triality after the verified v,u steps equals the entire displayed source state. -/
theorem monsterNortonLine01TensorExtraInverse_actual :
    sExtra.symm monsterNortonLine01TensorAfterVU =
      monsterNortonLine01TensorAfterVUExtraInverse := by
  rw [← monsterNortonLine01TensorU_actual, monsterNortonLine01TensorAfterV,
    monsterNortonIntegralTensorVector_first_column, monsterNortonUIntegerEmbed_single,
    map_smul, map_smul, monsterNortonUCompactSparseInverseTriality]
  have hr := Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    (monsterNortonUCompactBasisSign (golayLabelCoefficients 1038) a : ℝ) •
      ∑ i : Fin 24, monsterNortonUFiber.val.2.val (Pi.single 0 1) i •
        monsterNortonExtraInverseTensorDelta
          (monsterNortonUCompactBasisIndex (golayLabelCoefficients 1038) a) i)
  rw [← hr]
  change (1 / Real.sqrt 2 : ℝ) • ((1 / 8 : ℝ) • ∑ a : Fin 64,
    (monsterNortonUCompactBasisSign (golayLabelCoefficients 1038)
      (monsterNortonGrayCoefficients a) : ℝ) •
      ∑ i : Fin 24, monsterNortonUFiber.val.2.val (Pi.single 0 1) i •
        monsterNortonExtraInverseTensorDelta
          (monsterNortonUCompactBasisIndex (golayLabelCoefficients 1038)
            (monsterNortonGrayCoefficients a)) i) = _
  rw [monsterNortonLine01TensorAfterVUExtraInverse, smul_smul,
    Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hi : monsterNortonUCompactBasisIndex (golayLabelCoefficients 1038)
      (monsterNortonGrayCoefficients a) =
        golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a) :=
    (nortonUIntegerLabel_inverse _).symm.trans
      (congrArg golayLabelCoefficients (monsterNortonLine01Initial_transition_certificate a).1)
  rw [(monsterNortonLine01Initial_transition_certificate a).2, hi,
    smul_smul, smul_smul, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [physical_first_column]
  change _ • (_ • ((1 / Real.sqrt 2 : ℝ) •
    monsterNortonLine01SourcePair _ i)) = _
  rw [smul_smul, smul_smul, smul_smul, sqrt_coefficient]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
