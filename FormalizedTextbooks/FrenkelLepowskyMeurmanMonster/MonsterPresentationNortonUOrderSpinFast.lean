/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite lookup implementation of the actual Norton integer spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The 64 exact grey Gaussian signs in the source bit enumeration. -/
def monsterNortonSpinGraySigns : Vector ℤ 64 := ⟨#[1
  , 1, 1, -1, 1, -1, -1, -1, 1, -1,
  -1, -1, -1, -1, -1, 1, 1, -1, -1, -1,
  -1, -1, -1, 1, -1, -1, -1, 1, -1, 1,
  1, 1, 1, -1, -1, -1, -1, -1, -1, 1,
  -1, -1, -1, 1, -1, 1, 1, 1, -1, -1,
  -1, 1, -1, 1, 1, 1, -1, 1, 1, 1,
  1, 1, 1, -1
], by decide⟩

/-- The 64 actual grey code translation labels. -/
def monsterNortonSpinGrayShifts : Vector (Fin 4096) 64 := ⟨#[0
  , 1024, 3087, 2063, 3073, 2049, 14, 1038, 3074, 2050,
  13, 1037, 3, 1027, 3084, 2060, 3076, 2052, 11, 1035,
  5, 1029, 3082, 2058, 6, 1030, 3081, 2057, 3079, 2055,
  8, 1032, 3080, 2056, 7, 1031, 9, 1033, 3078, 2054,
  10, 1034, 3077, 2053, 3083, 2059, 4, 1028, 12, 1036,
  3075, 2051, 3085, 2061, 2, 1026, 3086, 2062, 1, 1025,
  15, 1039, 3072, 2048
], by decide⟩

set_option maxHeartbeats 2000000 in
-- Check the 64 code translations and their exact binomial-weight signs.
private theorem gray_data : ∀ a : Fin 64,
    monsterNortonSpinGraySigns.get a = xiGraySign (monsterNortonGrayCoefficients a) ∧
      monsterNortonSpinGrayShifts.get a =
        nortonUIntegerLabel (xiGrayCode (monsterNortonGrayCoefficients a)) := by
  decide +kernel

/-- Exact 64-term numerator, with the actual diagonal Gaussian folded into each summand. -/
def monsterNortonSpinFastXi (v : NortonUIntegerVector) : NortonUIntegerVector := fun n =>
  ∑ a : Fin 64, monsterNortonSpinGraySigns.get a *
    monsterNortonSpinSign 0 (monsterNortonSpinXor n (monsterNortonSpinGrayShifts.get a)) *
    v (monsterNortonSpinXor n (monsterNortonSpinGrayShifts.get a))

/-- The finite translation lookup is exactly the actual integer three-bases numerator. -/
theorem monsterNortonSpinFastXi_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastXi v = nortonUIntegerXi v := by
  funext n
  unfold monsterNortonSpinFastXi nortonUIntegerXi nortonUIntegerG nortonUIntegerGamma
  have he : ∀ a : Fin 64, xiGrayCode (monsterNortonGrayCoefficients a) =
      golayLabelCoefficients (monsterNortonSpinGrayShifts.get a) := by
    intro a
    rw [(gray_data a).2, nortonUIntegerLabel_inverse]
  have hr := Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    xiGraySign a * (nortonUIntegerGammaSign
      (golayLabelCoefficients (nortonUIntegerLabel (golayLabelCoefficients n + xiGrayCode a))) *
        v (nortonUIntegerLabel (golayLabelCoefficients n + xiGrayCode a))))
  change (∑ a : Fin 64, monsterNortonSpinGraySigns.get a *
      monsterNortonSpinSign 0 (monsterNortonSpinXor n (monsterNortonSpinGrayShifts.get a)) *
        v (monsterNortonSpinXor n (monsterNortonSpinGrayShifts.get a))) = _
  rw [← hr]
  apply Finset.sum_congr rfl
  intro a _
  change _ = xiGraySign (monsterNortonGrayCoefficients a) *
    (nortonUIntegerGammaSign (golayLabelCoefficients (nortonUIntegerLabel
      (golayLabelCoefficients n + xiGrayCode (monsterNortonGrayCoefficients a)))) *
      v (nortonUIntegerLabel
        (golayLabelCoefficients n + xiGrayCode (monsterNortonGrayCoefficients a))))
  rw [he, monsterNortonSpinXor_label, ← monsterNortonSpinSign_gamma, ← (gray_data a).1]
  ring

/-- Exact signed inverse source permutation, in finite source-label coordinates. -/
def monsterNortonSpinFastPermutation (k : Fin 2) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n =>
  monsterNortonSpinSign (if k = 0 then 1 else 2) n *
    v (monsterNortonSpinIndex (if k = 0 then 0 else 1) n)

/-- The finite table retains both actual Parker inverse signs and code relabelings. -/
theorem monsterNortonSpinFastPermutation_eq (k : Fin 2) (v : NortonUIntegerVector) :
    monsterNortonSpinFastPermutation k v = nortonUIntegerPermutationInverse k v := by
  fin_cases k <;> funext n
  · change monsterNortonSpinSign 1 n * v (monsterNortonSpinIndex 0 n) =
      nortonUIntegerSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData 0)
        (golayLabelCoefficients n)) *
          v (nortonUIntegerLabel (monsterSourcePermutationCode 0 (golayLabelCoefficients n)))
    rw [monsterNortonSpinSign_permutation_zero, monsterNortonSpinIndex_0]
  · change monsterNortonSpinSign 2 n * v (monsterNortonSpinIndex 1 n) =
      nortonUIntegerSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData 1)
        (golayLabelCoefficients n)) *
          v (nortonUIntegerLabel (monsterSourcePermutationCode 1 (golayLabelCoefficients n)))
    rw [monsterNortonSpinSign_permutation_one, monsterNortonSpinIndex_1]

/-- Exact finite y82 signed affine numerator. -/
def monsterNortonSpinFastY82 (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => monsterNortonSpinSign 3 n * v (monsterNortonSpinIndex 2 n)

/-- The finite signed affine table is the full actual y82 plus/minus numerator. -/
theorem monsterNortonSpinFastY82_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastY82 v = nortonUIntegerY82PlusMinus v := by
  funext n
  simp only [monsterNortonSpinFastY82, monsterNortonSpinSign_y82, monsterNortonSpinIndex_2]
  rfl

/-- Exact finite code factor numerator, including its actual central sign. -/
def monsterNortonSpinFastQCode (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => monsterNortonSpinSign 4 n * v (monsterNortonSpinXor n 2049)

/-- The finite code factor is the actual normalized source Q action. -/
theorem monsterNortonSpinFastQCode_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastQCode v = nortonUIntegerQ (sourceQCode 2049 1) v := by
  funext n
  unfold monsterNortonSpinFastQCode nortonUIntegerQ
  dsimp only
  rw [sourceQCode_translation, monsterNortonSpinXor_label, monsterNortonSpinSign_qcode]

/-- Exact finite cocode factor numerator. -/
def monsterNortonSpinFastQCocode (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => monsterNortonSpinSign 5 n * v n

/-- The finite cocode factor is the actual source character action. -/
theorem monsterNortonSpinFastQCocode_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastQCocode v =
      nortonUIntegerQ (sourceQCocode (golayLabelCoefficients 1807)) v := by
  funext n
  unfold monsterNortonSpinFastQCocode nortonUIntegerQ
  dsimp only
  rw [sourceQCocode_translation, add_zero, nortonUIntegerLabel_coeff,
    monsterNortonSpinSign_qcocode]

/-- Exact integral two-term Fourier numerator in twelve-bit source coordinates. -/
def monsterNortonSpinFastHadamard (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => (if n.val.testBit 11 then -1 else 1) * v n + v (monsterNortonSpinXor n 2048)

/-- The two-term finite numerator is the genuine last-coordinate Fourier operation. -/
theorem monsterNortonSpinFastHadamard_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastHadamard v = nortonUIntegerHadamard v := by
  have h : monsterSpinOmegaVector = golayLabelCoefficients 2048 := by decide +kernel
  funext n
  unfold monsterNortonSpinFastHadamard nortonUIntegerHadamard monsterSpinOmegaFlip
  dsimp only
  rw [h, monsterNortonSpinXor_label]
  change _ = (if (if n.val.testBit 11 then (1 : ZMod 2) else 0) = 0 then 1 else -1) *
    v n + v (monsterNortonSpinXor n 2048)
  cases n.val.testBit 11 <;> simp

/-- The nine exact integer primitives of one source word, in application order. -/
def monsterNortonSpinPrimitive : Fin 9 → NortonUIntegerVector → NortonUIntegerVector :=
  ![monsterNortonSpinFastXi, monsterNortonSpinFastPermutation 1,
    monsterNortonSpinFastXi, monsterNortonSpinFastPermutation 0,
    monsterNortonSpinFastQCocode, monsterNortonSpinFastQCode,
    monsterNortonSpinFastHadamard, monsterNortonSpinFastY82, monsterNortonSpinFastHadamard]

/-- Exact finite implementation of the complete integer Norton word. -/
def monsterNortonSpinFastU (v : NortonUIntegerVector) : NortonUIntegerVector :=
  monsterNortonSpinPrimitive 8 (monsterNortonSpinPrimitive 7 (monsterNortonSpinPrimitive 6
    (monsterNortonSpinPrimitive 5 (monsterNortonSpinPrimitive 4 (monsterNortonSpinPrimitive 3
      (monsterNortonSpinPrimitive 2
        (monsterNortonSpinPrimitive 1 (monsterNortonSpinPrimitive 0 v))))))))

/-- The finite primitive implementation equals the actual integer source numerator. -/
theorem monsterNortonSpinFastU_eq (v : NortonUIntegerVector) :
    monsterNortonSpinFastU v = nortonUIntegerU v := by
  change monsterNortonSpinFastHadamard (monsterNortonSpinFastY82
    (monsterNortonSpinFastHadamard (monsterNortonSpinFastQCode
      (monsterNortonSpinFastQCocode (monsterNortonSpinFastPermutation 0
        (monsterNortonSpinFastXi (monsterNortonSpinFastPermutation 1
          (monsterNortonSpinFastXi v)))))))) = _
  simp only [monsterNortonSpinFastXi_eq, monsterNortonSpinFastPermutation_eq,
    monsterNortonSpinFastQCocode_eq, monsterNortonSpinFastQCode_eq,
    monsterNortonSpinFastHadamard_eq, monsterNortonSpinFastY82_eq]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
