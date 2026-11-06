/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSpinData

/-! The genuine initial source spin factors have eight fixed literal support coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original low dictionary coordinate of the eight genuine source factors. -/
def generatedTwelfthTensorSourceInitialLabel : Fin 8 → Fin 8 → Fin 2048 :=
  ![![1805, 1803, 1543, 1547, 1152, 1163, 1339, 1342], ![1795, 1797, 1545, 1541, 1332, 1329,
    1153, 1162], ![1804, 1802, 1544, 1540, 1160, 1155, 1340, 1337], ![1794, 1796, 1542, 1546,
    1331, 1334, 1161, 1154], ![1719, 1727, 1981, 1983, 1423, 1072, 1087, 1422], ![1714, 1722,
    1974, 1972, 1410, 1078, 1081, 1411], ![1724, 1716, 1976, 1978, 1417, 1075, 1084, 1416],
    ![1721, 1713, 1971, 1969, 1412, 1077, 1082, 1413]]

/-- Every exact signed source coefficient on those original dictionary coordinates. -/
def generatedTwelfthTensorSourceInitialCoefficient : Fin 8 → Fin 8 → ℤ :=
  ![![1, 1, -1, -1, 1, 1, 1, 1], ![-1, -1, 1, 1, -1, -1, -1, -1], ![-1, -1, 1, 1, -1, -1, -1,
    -1], ![-1, -1, 1, 1, -1, -1, -1, -1], ![1, -1, -1, 1, -1, 1, -1, 1], ![1, -1, -1, 1, 1, 1,
    -1, -1], ![1, -1, -1, 1, -1, -1, 1, 1], ![-1, 1, 1, -1, -1, 1, -1, 1]]

/-- All literal support labels are the identical complete original dictionary labels. -/
theorem generatedTwelfth_tensor_source_initial_labels : ∀ r n : Fin 8,
    (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex r n)).1 =
      generatedTwelfthTensorSourceInitialLabel r n := by
  decide +kernel

/-- Every displayed coefficient is the full original Parker and physical code sign. -/
theorem generatedTwelfth_tensor_source_initial_coefficients : ∀ r n : Fin 8,
    generatedAxisGlobalIntSign
        (generatedFifthOddCoefficientPhaseData (generatedTwelfthTensorSourceIndex r n)) *
      (if (golayEncodedMask
        (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex r n)).1.val).testBit
          (generatedTwelfthTensorSourceCoordinate r).val then -1 else 1) =
      generatedTwelfthTensorSourceInitialCoefficient r n := by
  decide +kernel

/-- Integer signs preserve the genuine additive binary phase law. -/
theorem generatedTwelfth_tensor_source_int_sign_add (c d : ZMod 2) :
    generatedAxisGlobalIntSign (c + d) =
      generatedAxisGlobalIntSign c * generatedAxisGlobalIntSign d := by
  have h : ∀ c d : ZMod 2, generatedAxisGlobalIntSign (c + d) =
      generatedAxisGlobalIntSign c * generatedAxisGlobalIntSign d := by
    decide +kernel
  exact h c d

/-- The complete sparse source formula retains all zero and nonzero spin coordinates. -/
def generatedTwelfthTensorSourceInitialSparseSpin (r : Fin 8) (k : Fin 4096) : ℤ :=
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
    ∑ n : Fin 8,
      if k.val % 2048 = (generatedTwelfthTensorSourceInitialLabel r n).val then
        generatedTwelfthTensorSourceInitialCoefficient r n else 0

/-- The sparse formula is every exact original source coefficient, with no assumed support. -/
theorem generatedTwelfth_tensor_source_initial_sparse_actual (r : Fin 8) (k : Fin 4096) :
    generatedTwelfthTensorSourceSpinFast r k =
      generatedTwelfthTensorSourceInitialSparseSpin r k := by
  unfold generatedTwelfthTensorSourceSpinFast generatedTwelfthTensorSourceInitialSparseSpin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← generatedTwelfth_tensor_source_initial_labels r n]
  by_cases h : k.val % 2048 =
      (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex r n)).1.val
  · simp only [h, ↓reduceIte]
    rw [generatedTwelfth_tensor_source_int_sign_add]
    rw [show generatedAxisGlobalIntSign
        (generatedFifthOddCoefficientPhaseData (generatedTwelfthTensorSourceIndex r n)) *
        generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
        (if (golayEncodedMask
          (generatedFifthOddRootOutputData (generatedTwelfthTensorSourceIndex r n)).1.val).testBit
            (generatedTwelfthTensorSourceCoordinate r).val then -1 else 1) =
        generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
          (generatedAxisGlobalIntSign
            (generatedFifthOddCoefficientPhaseData (generatedTwelfthTensorSourceIndex r n)) *
            (if (golayEncodedMask
              (generatedFifthOddRootOutputData
                (generatedTwelfthTensorSourceIndex r n)).1.val).testBit
                (generatedTwelfthTensorSourceCoordinate r).val then -1 else 1)) by ring]
    rw [generatedTwelfth_tensor_source_initial_coefficients]
  · simp only [h, ↓reduceIte, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
