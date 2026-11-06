/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootLabels

/-! Complete original finite octad indices of all canonical Fifth middle even terms. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Original finite catalogue indices, retaining all 56 actual root terms. -/
def generatedAxisGlobalCanonicalFifthEvenOctadIndex : Fin 56 → Fin 759 :=
  ![1, 6, 541, 540, 159, 160, 542, 539, 158, 161, 510, 506, 2, 509, 132, 512, 131, 513, 133, 511, 130, 514, 7, 507, 606, 605, 195, 197, 577, 575, 225, 224, 566, 564, 237, 235, 615, 617, 185, 183, 563, 565, 236, 234, 616, 618, 182, 184, 223, 222, 578, 576, 194, 196, 604, 603]

set_option maxHeartbeats 4000000 in
/-- Every finite catalogue code is the original canonical root code. -/
theorem generatedAxisGlobalCanonicalFifthEvenOctadIndex_checked (j : Fin 56) :
    generatedAxisGlobalOctadCodeData (generatedAxisGlobalCanonicalFifthEvenOctadIndex j) =
      generatedFifthEvenRootCode j := by
  have h : ∀ j : Fin 56, generatedAxisGlobalOctadCodeData
      (generatedAxisGlobalCanonicalFifthEvenOctadIndex j) = generatedFifthEvenRootCode j := by
    decide +kernel
  exact h j

/-- The finite index is precisely the original actual preferred octad index. -/
theorem generatedAxisGlobalCanonicalFifthEvenOctadIndex_actual (j : Fin 56) :
    generatedAxisGlobalCanonicalFifthEvenOctadIndex j = generatedFifthEvenRootOctad j := by
  apply golayOctadLabel_injective
  rw [← generatedAxisGlobalOctadCodeData_actual,
    generatedAxisGlobalCanonicalFifthEvenOctadIndex_checked,
    generatedFifthEvenRootOctad_label]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
