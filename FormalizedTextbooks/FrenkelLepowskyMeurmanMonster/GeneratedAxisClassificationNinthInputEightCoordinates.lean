/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInputEightData

/-! Finite linearity gives an exact eight-state reduction of all original physical input columns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem finite_columns (a : Fin 64 → ℤ) (v : Fin 64 → Fin 24 → ℤ)
    (cols : Fin 8 → Fin 24) (c : Fin 24 → Fin 8 → ℤ)
    (hv : ∀ k i, v k i = ∑ b : Fin 8, c i b * v k (cols b)) (i : Fin 24) :
    (∑ k : Fin 64, a k * v k i) =
      ∑ b : Fin 8, c i b * ∑ k : Fin 64, a k * v k (cols b) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [hv k i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The original signed root amplitude at a source spin label, before its physical row. -/
def generatedNinthInputRootAmplitude (n : Fin 4096) (k : Fin 64) : ℤ :=
  nortonUIntegerSign (generatedFifthOddCoefficientPhaseData k) *
    nortonUIntegerSign (golayLabelCoefficients n 11) *
    (if (golayEncodedMask (generatedFifthOddRootOutputData k).1.val).testBit
      (generatedFifthOddRootOutputData k).2.val then -1 else 1) *
    (if n.val % 2048 = (generatedFifthOddRootOutputData k).1.val then 1 else 0)

private theorem sparse_amplitudes (i : Fin 24) (n : Fin 4096) :
    generatedNinthColumnInputSparse i n = ∑ k : Fin 64,
      generatedNinthInputRootAmplitude n k *
        generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2 i := rfl

/-- Every original input spin coordinate is an integer combination of the eight selected columns. -/
theorem generatedNinth_column_input_eight (i : Fin 24) (n : Fin 4096) :
    generatedNinthColumnInputInteger i n =
      ∑ b : Fin 8, generatedNinthInputBasisCoefficients i b *
        generatedNinthColumnInputInteger (generatedNinthInputBasisColumn b) n := by
  simp only [generatedNinth_column_input_sparse, sparse_amplitudes]
  exact finite_columns (generatedNinthInputRootAmplitude n)
    (fun k j => generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2 j)
    generatedNinthInputBasisColumn generatedNinthInputBasisCoefficients
    (fun k j => by simpa only [one_mul] using generatedNinth_input_basis_root_coordinate k j) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
