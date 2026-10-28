/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelCount

/-! All nine genuine monomial candidates fix the whole original matrix through its actual root kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Each genuine monomial candidate is a complete original positive root-kernel word. -/
theorem generatedTwelfth_certified_kernel_letter_matrix_mem (g : Fin 9) :
    generatedTwelfthCertifiedKernelLetter g ∈ generatedTwelfthSpatialStabilizer := by
  have happend (w v : List (Fin 9)) : generatedTwelfthCertifiedKernelWord (w ++ v) =
      generatedTwelfthCertifiedKernelWord w * generatedTwelfthCertifiedKernelWord v := by
    simp only [generatedTwelfthCertifiedKernelWord, List.map_append, List.prod_append]
  have hword (a : Fin 32) (p : Fin 16) (h :
      generatedTwelfthCertifiedKernelSignWord a ++
        generatedTwelfthCertifiedKernelPermutationWord p = [g]) :
      generatedTwelfthCertifiedKernelLetter g ∈ generatedTwelfthSpatialStabilizer := by
    have he := generatedTwelfth_certified_kernel_monomial a p
    rw [← happend, h] at he
    have hf : generatedTwelfthCertifiedKernelLetter g =
        generatedTwelfthRootKernelMonomial false a p := by
      simpa only [generatedTwelfthCertifiedKernelWord, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one] using he
    rw [hf]
    exact generatedTwelfth_root_action_kernel_actual_matrix
      (generatedTwelfthRootKernelEnumeration (false, a, p))
  fin_cases g
  · exact hword 1 0 (by rfl)
  · exact hword 2 0 (by rfl)
  · exact hword 4 0 (by rfl)
  · exact hword 8 0 (by rfl)
  · exact hword 16 0 (by rfl)
  · exact hword 0 1 (by rfl)
  · exact hword 0 2 (by rfl)
  · exact hword 0 4 (by rfl)
  · exact hword 0 8 (by rfl)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
