/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootLabels

/-! Complete original finite octad indices of all canonical Fourth middle even terms. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Original finite catalogue indices, retaining all 63 actual root terms. -/
def generatedAxisGlobalCanonicalFourthEvenOctadIndex : Fin 63 → Fin 759 :=
  ![9, 508, 5, 211, 593, 210, 594, 170, 554, 173, 551, 591, 213, 592, 212, 552, 172, 553, 171, 2, 509, 131, 513, 132, 512, 130, 514, 133, 511, 7, 507, 526, 526, 223, 223, 603, 603, 523, 523, 27, 27, 183, 183, 566, 566, 30, 30, 28, 28, 184, 184, 563, 563, 33, 33, 143, 143, 606, 606, 224, 224, 144, 144]

set_option maxHeartbeats 4000000 in
/-- Every finite catalogue code is the original canonical root code. -/
theorem generatedAxisGlobalCanonicalFourthEvenOctadIndex_checked (j : Fin 63) :
    generatedAxisGlobalOctadCodeData (generatedAxisGlobalCanonicalFourthEvenOctadIndex j) =
      generatedFourthEvenRootCode j := by
  have h : ∀ j : Fin 63, generatedAxisGlobalOctadCodeData
      (generatedAxisGlobalCanonicalFourthEvenOctadIndex j) = generatedFourthEvenRootCode j := by
    decide +kernel
  exact h j

/-- The finite index is precisely the original actual preferred octad index. -/
theorem generatedAxisGlobalCanonicalFourthEvenOctadIndex_actual (j : Fin 63) :
    generatedAxisGlobalCanonicalFourthEvenOctadIndex j = generatedFourthEvenRootOctad j := by
  apply golayOctadLabel_injective
  rw [← generatedAxisGlobalOctadCodeData_actual,
    generatedAxisGlobalCanonicalFourthEvenOctadIndex_checked,
    generatedFourthEvenRootOctad_label]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
