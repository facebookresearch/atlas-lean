/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelMonomialData

/-! Every pointwise-octad physical permutation is bound to its entire genuine original word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original physical inverse coordinates of the five actual selected Mathieu generators. -/
def generatedTwelfthRootKernelLetterBackward : Fin 5 → Fin 24 → Fin 24 :=
  ![
  ![18, 1, 19, 3, 7, 9, 8, 4, 6, 5, 11, 10, 12, 23, 14, 20, 16, 17, 0, 2, 15, 21, 22, 13],
  ![0, 2, 1, 3, 4, 7, 6, 5, 21, 20, 22, 23, 13, 12, 14, 15, 17, 16, 18, 19, 9, 8, 10, 11],
  ![2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
  ![0, 1, 2, 18, 9, 13, 22, 7, 8, 4, 15, 21, 12, 5, 20, 10, 17, 16, 3, 19, 14, 11, 6, 23],
  ![17, 0, 2, 18, 10, 8, 23, 22, 11, 21, 9, 20, 4, 13, 14, 5, 19, 3, 16, 1, 7, 6, 15, 12]
]

/-- Every original inverse coordinate array is the complete inverse of its genuine forward array. -/
theorem generatedTwelfth_root_kernel_letter_inverse : ∀ g : Fin 5, ∀ i : Fin 24,
    generatedFifthSelectedOctadForward g (generatedTwelfthRootKernelLetterBackward g i) = i := by
  decide +kernel

/-- A true original selected-generator letter or its genuine group inverse. -/
def generatedTwelfthRootKernelPermutationLetter (l : Fin 5 × Bool) : golayAutomorphismSubgroup :=
  if l.2 then (generatedFifthSelectedOctadPermutation l.1)⁻¹
  else generatedFifthSelectedOctadPermutation l.1

/-- Full physical coordinates of every genuine letter retain its actual inverse orientation. -/
theorem generatedTwelfth_root_kernel_letter_actual (l : Fin 5 × Bool) (i : Fin 24) :
    (generatedTwelfthRootKernelPermutationLetter l).val i =
      if l.2 then generatedTwelfthRootKernelLetterBackward l.1 i
      else generatedFifthSelectedOctadForward l.1 i := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedFifthSelectedOctad_forward g i
  · exact generatedFifthPermutation_inverse_forward _ _ _
      (generatedFifthSelectedOctad_forward g) (generatedTwelfth_root_kernel_letter_inverse g) i

/-- Literal finite evaluation of each full original word at the physical coordinate. -/
def generatedTwelfthRootKernelFiniteWord (p : Fin 16) (i : Fin 24) : Fin 24 :=
  (generatedTwelfthRootKernelPermutationWord p).foldr
    (fun l x => if l.2 then generatedTwelfthRootKernelLetterBackward l.1 x
      else generatedFifthSelectedOctadForward l.1 x) i

set_option maxHeartbeats 64000000 in
-- Check every coordinate through the complete original positive and inverse letter sequence.
/-- Every entire recorded word has its exact original finite physical forward array. -/
theorem generatedTwelfth_root_kernel_finite_word : ∀ p : Fin 16, ∀ i : Fin 24,
    generatedTwelfthRootKernelFiniteWord p i =
      generatedTwelfthRootKernelPermutationForward p i := by
  decide +kernel

/-- The actual pointwise-octad permutation is the whole original selected-generator product. -/
def generatedTwelfthRootKernelPermutation (p : Fin 16) : golayAutomorphismSubgroup :=
  ((generatedTwelfthRootKernelPermutationWord p).map
    generatedTwelfthRootKernelPermutationLetter).prod

/-- Every actual original word has the genuine full physical permutation coordinates. -/
theorem generatedTwelfth_root_kernel_permutation_actual (p : Fin 16) (i : Fin 24) :
    (generatedTwelfthRootKernelPermutation p).val i =
      generatedTwelfthRootKernelPermutationForward p i := by
  rw [generatedTwelfthRootKernelPermutation]
  rw [generatedFifthPermutation_word_forward generatedTwelfthRootKernelPermutationLetter
    (fun l x => if l.2 then generatedTwelfthRootKernelLetterBackward l.1 x
      else generatedFifthSelectedOctadForward l.1 x) generatedTwelfth_root_kernel_letter_actual]
  exact generatedTwelfth_root_kernel_finite_word p i

/-- Both physical inverse coordinates are those of the entire true original permutation. -/
theorem generatedTwelfth_root_kernel_permutation_backward (p : Fin 16) (i : Fin 24) :
    (generatedTwelfthRootKernelPermutation p).val.symm i =
      generatedTwelfthRootKernelPermutationBackward p i := by
  exact generatedFifthPermutation_inverse_forward _ _ _
    (generatedTwelfth_root_kernel_permutation_actual p)
    (generatedTwelfth_root_kernel_permutation_inverse p) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
