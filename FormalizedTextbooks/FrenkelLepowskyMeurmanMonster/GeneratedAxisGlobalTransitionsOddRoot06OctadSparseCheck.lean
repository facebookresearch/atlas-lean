/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseData

/-! Complete finite certificates for the original root-six positive sparse support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every stored candidate source key is its exact original preferred-short catalogue coordinate. -/
theorem generatedAxisGlobalOddRoot06OctadSparse_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddRoot06OctadSourceLabel p))
      generatedAxisGlobalOddRoot06OctadSparseTree := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- All 120 original nonzero support labels round trip through the complete sparse lookup. -/
theorem generatedAxisGlobalOddRoot06OctadSparse_roundtrip (p : Fin 120) :
    generatedAxisGlobalOddRoot06OctadSparseSource (generatedAxisGlobalOddRoot06OctadSourceLabel p) =
      some p := by
  revert p
  decide +kernel

/-- Each listed original nonzero short coefficient is a unit of squared value one. -/
theorem generatedAxisGlobalOddRoot06OctadSourceCoefficient_unit : ∀ p : Fin 120,
    generatedAxisGlobalOddRoot06OctadSourceCoefficient p ^ 2 = 1 := by
  decide +kernel

/-- Each actual preferred-vector sign is one of the two original global signs. -/
theorem generatedAxisGlobalOddRoot06OctadVectorSign_unit : ∀ p : Fin 120,
    generatedAxisGlobalOddRoot06OctadVectorSign p = 1 ∨
      generatedAxisGlobalOddRoot06OctadVectorSign p = -1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every transformed original short label lies entirely in the standard eight-coordinate octad. -/
theorem generatedAxisGlobalOddRoot06OctadTarget_physical_support : ∀ p : Fin 120, ∀ i : Fin 24,
    (0xff00 : ℕ).testBit i.val = false →
      generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadTargetLabel p) i = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
