/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGreyFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftTensorKernel

/-! Finite sparse evaluation retains the actual grey, Parker and Pauli phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A sparse evaluation of the unchanged sixteen-term actual spin kernel. -/
def generatedFourthLiftSpinKernelFast (t v : SpinIndex) : ℤ :=
  ∑ o : Fin 4, ∑ s : Fin 4,
    generatedFourthLiftYRowCoefficient t o *
    generatedFourthLiftIntSign (generatedFourthLiftPPhaseFast
      (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o))) *
    generatedFourthLiftYRowCoefficient v s *
    (-generatedFourthLiftIntSign (generatedFourthLiftGammaPhaseFast
      (generatedFourthLiftYRowAddress v s))) *
    generatedFourthLiftGreyKernelFast
      (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o) +
        generatedFourthLiftYRowAddress v s)

/-- Sparse grey evaluation changes no coordinate of the actual spin kernel. -/
theorem generatedFourth_lift_spin_kernel_fast (t v : SpinIndex) :
    generatedFourthLiftSpinKernel t v = generatedFourthLiftSpinKernelFast t v := by
  simp only [generatedFourthLiftSpinKernel, generatedFourthLiftSpinKernelFast,
    generatedFourth_lift_grey_kernel_fast]

/-- Finite sparse integer numerator for the full spatial and spin tensor action. -/
def generatedFourthLiftSparseTensorFast (t : SpinIndex) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, if generatedFourthLiftSpatialNumerator i j = 0 then 0 else
    generatedFourthLiftSpatialNumerator i j *
      ∑ k : Fin 28, if j = generatedFourthQAffineTensorColumns k then
        ∑ s : Fin 4, generatedFourthLiftUnitWeight k s *
          generatedFourthLiftSpinKernelFast t (generatedFourthLiftSupportAddress k s) else 0

/-- This computable tensor numerator is the exact actual sparse operator numerator. -/
theorem generatedFourth_lift_sparse_tensor_fast (t : SpinIndex) (i : Fin 24) :
    generatedFourthLiftSparseTensorNumerator t i = generatedFourthLiftSparseTensorFast t i := by
  simp only [generatedFourthLiftSparseTensorNumerator, generatedFourthLiftSparseTensorFast,
    generatedFourth_lift_spin_kernel_fast]

/-- The actual Q correction retains its literal central bit and modulation phase. -/
def generatedFourthLiftSparseCorrectedFast (t : SpinIndex) (i : Fin 24) : ℤ :=
  generatedFourthLiftIntSign (spinPhase generatedFourthFlagXiCorrection t) *
    generatedFourthLiftSparseTensorFast (t + spinTranslation generatedFourthFlagXiCorrection) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
