/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiLiteralData

/-! Ordinary numeral caches evaluate the unchanged signed original Xi tensor operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Complete literal source addresses, before their equality with the original cache is used. -/
def generatedSixthXiLiteralLabel (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel (fun i =>
    if (generatedSixthXiLiteralCoordinatePlanes k i).testBit n.val then 1 else 0)

/-- Complete original quadratic phases, read from the entire checked numeral plane. -/
def generatedSixthXiLiteralPhase (k : Fin 2) (n : Fin 4096) : ZMod 2 :=
  if (generatedSixthXiLiteralPhasePlanes k).testBit n.val then 1 else 0

/-- Full-plane equality identifies every literal source address with the original C cache. -/
theorem generatedSixth_xi_literal_label (k : Fin 2) (n : Fin 4096) :
    generatedSixthXiLiteralLabel k n = generatedSixthXiWordCachedLabel k n := by
  rw [generatedSixthXiLiteralLabel, generatedSixthXiWordCachedLabel,
    generatedSixth_xi_literal_coordinate_planes]

/-- Full-plane equality identifies every literal phase with the original signed C cache. -/
theorem generatedSixth_xi_literal_phase (k : Fin 2) (n : Fin 4096) :
    generatedSixthXiLiteralPhase k n = generatedSixthXiWordCachedPhase k n := by
  rw [generatedSixthXiLiteralPhase, generatedSixthXiWordCachedPhase,
    generatedSixth_xi_literal_phase_planes]

/-- The signed C operator on arbitrary integer vectors, using ordinary complete numerals. -/
def generatedSixthXiLiteralWordInteger (k : Fin 2) (v : NortonUIntegerVector)
    (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (generatedSixthXiLiteralPhase k n) * v (generatedSixthXiLiteralLabel k n)

/-- Every literal signed word equals the complete original operator on every integer vector. -/
theorem generatedSixth_xi_literal_word_integer (k : Fin 2) (v : NortonUIntegerVector) :
    generatedSixthXiLiteralWordInteger k v = generatedSixthXiWordCachedInteger k v := by
  funext n
  rw [generatedSixthXiLiteralWordInteger, generatedSixthXiWordCachedInteger,
    generatedSixth_xi_literal_label, generatedSixth_xi_literal_phase]

/-- Both original signed C words surround all sixty-four unchanged Gaussian terms. -/
def generatedSixthXiLiteralSpinInteger (v : NortonUIntegerVector) : NortonUIntegerVector :=
  generatedSixthXiLiteralWordInteger 1
    (generatedSixthIntegerXiCached (generatedSixthXiLiteralWordInteger 0 v))

/-- The literal evaluator equals the original complete conjugated-Xi spin operator. -/
theorem generatedSixth_xi_literal_spin_integer (v : NortonUIntegerVector) :
    generatedSixthXiLiteralSpinInteger v = generatedSixthXiCachedSpinInteger v := by
  rw [generatedSixthXiLiteralSpinInteger, generatedSixthXiCachedSpinInteger,
    generatedSixth_xi_literal_word_integer, generatedSixth_xi_literal_word_integer]

/-- Complete physical numerator with every original Gaussian contribution retained. -/
def generatedSixthXiLiteralRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
    generatedSixthXiLiteralSpinInteger
      (fun m => generatedSixthTensorFastExecutable m (generatedSixthXiPhysicalColumn i a)) n

/-- The complete corrected Xi tensor uses the original Q phase and translation. -/
def generatedSixthXiLiteralTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then 1 else 0) *
    generatedSixthXiLiteralRawTensor (generatedSixthSpinLabelXor n 538) i

/-- Literal optimization equals the full original signed tensor numerator everywhere. -/
theorem generatedSixth_xi_literal_tensor (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiLiteralTensor n i = generatedSixthXiCachedTensor n i := by
  simp only [generatedSixthXiLiteralTensor, generatedSixthXiLiteralRawTensor,
    generatedSixthXiCachedTensor, generatedSixthXiCachedRawTensor,
    generatedSixth_xi_literal_spin_integer]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
