/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTensorSupportData

/-! The selected thirteen labels determine every genuine affine spin sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_support_constant : ∀ i : Fin 13,
    generatedNinthTensorSupportAffine i 0 = 1 := by
  decide +kernel

private theorem generatedNinth_support_successor : ∀ i : Fin 13, ∀ j : Fin 12,
    generatedNinthTensorSupportAffine i j.succ =
      golayLabelCoefficients (generatedNinthTensorSupportLabels i) j := by
  decide +kernel

/-- Matrix evaluation is exactly the original affine spin character at every selected label. -/
theorem generatedNinth_tensor_support_evaluation (b : SpinIndex) (c : ZMod 2) (i : Fin 13) :
    (generatedNinthTensorSupportAffine *ᵥ Fin.cons c b) i =
      c + spinDot b (golayLabelCoefficients (generatedNinthTensorSupportLabels i)) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, generatedNinth_support_constant,
    generatedNinth_support_successor, one_mul]
  unfold spinDot
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Vanishing at the thirteen selected original labels forces both sign parameters to vanish. -/
theorem generatedNinth_tensor_support_detect (b : SpinIndex) (c : ZMod 2)
    (h : ∀ i : Fin 13,
      c + spinDot b (golayLabelCoefficients (generatedNinthTensorSupportLabels i)) = 0) :
    b = 0 ∧ c = 0 := by
  have he : generatedNinthTensorSupportAffine *ᵥ Fin.cons c b = 0 := by
    ext i
    rw [generatedNinth_tensor_support_evaluation]
    exact h i
  have hi := congrArg (fun v => generatedNinthTensorSupportInverse *ᵥ v) he
  rw [Matrix.mulVec_mulVec, generatedNinth_tensor_support_inverse,
    Matrix.one_mulVec, Matrix.mulVec_zero] at hi
  constructor
  · funext j
    have hj := congrFun hi j.succ
    simpa only [Fin.cons_succ, Pi.zero_apply] using hj
  · have hj := congrFun hi 0
    simpa only [Fin.cons_zero, Pi.zero_apply] using hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
