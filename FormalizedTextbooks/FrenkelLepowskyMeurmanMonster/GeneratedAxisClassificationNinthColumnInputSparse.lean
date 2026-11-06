/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnTensor

/-! The original physical row applied to the 64 signed input states as one finite sum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exactly 64 terms give the original sparse column input before its spin word. -/
def generatedNinthColumnInputSparse (i : Fin 24) (n : Fin 4096) : ℤ :=
  let t := golayLabelCoefficients n
  ∑ k : Fin 64,
    nortonUIntegerSign (generatedFifthOddCoefficientPhaseData k) *
      nortonUIntegerSign (t 11) *
      (if (golayEncodedMask (generatedFifthOddRootOutputData k).1.val).testBit
        (generatedFifthOddRootOutputData k).2.val then -1 else 1) *
      (if n.val % 2048 = (generatedFifthOddRootOutputData k).1.val then 1 else 0) *
      generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2 i

/-- Finite linearity and the genuine coordinate-unit support prove the sparse input formula. -/
theorem generatedNinth_column_input_sparse (i : Fin 24) (n : Fin 4096) :
    generatedNinthColumnInputInteger i n = generatedNinthColumnInputSparse i n := by
  unfold generatedNinthColumnInputInteger generatedNinthInputTensorInteger
    generatedNinthColumnInputSparse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (generatedFifthOddRootOutputData k).2]
  · simp only [ite_true]
    ring
  · intro j _ hj
    simp only [hj, ite_false, mul_zero]
  · intro hj
    exact False.elim (hj (Finset.mem_univ _))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
