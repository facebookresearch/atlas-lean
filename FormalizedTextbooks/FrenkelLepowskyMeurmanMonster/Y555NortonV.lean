/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The concrete Norton v=x_40e d_c01 in the named group G.
The source word is the pinned public mmgroup p3_to_mm construction of
Norton's 2002 five-generator presentation. Its order is checked in actual Q.
Source: mmgroup/src/mmgroup/bimm/p3_to_mm.py at public commit
728688938a1c9fd27f3aee9b63464ea6b8d17965 (BSD-2-Clause).
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual extraspecial element specified by the pinned public Norton-generator construction. -/
def y555NortonVQ : Q := sourceQCode 1038 0 * sourceQCocode (golayLabelCoefficients 3073)

/-- This concrete source word satisfies the involution relation in actual Q. -/
theorem y555NortonVQ_square : y555NortonVQ ^ 2 = 1 := by
  rw [pow_two]
  apply NormalizedCocycleExtension.Extension.ext
  · exact q_square_base _
  · apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (y555NortonVQ * y555NortonVQ).coeff = 0
    decide +kernel

/-- The word moves a genuine binary coordinate, so it is nontrivial in actual Q. -/
theorem y555NortonVQ_ne_one : y555NortonVQ ≠ 1 := by
  intro h
  have ht : spinTranslation y555NortonVQ 1 = 1 := by decide +kernel
  have hc := congrArg (fun q : Q => spinTranslation q 1) h
  rw [ht] at hc
  exact one_ne_zero hc

/-- Norton's v is an explicit element of the named generated group. -/
noncomputable def y555NortonV : ↥G := qIntoGenerated y555NortonVQ

/-- The concrete element agrees with the two actual source generator factors. -/
theorem y555NortonV_source_word : y555NortonV =
    sourceGeneratedCode 1038 0 * sourceGeneratedCocode (golayLabelCoefficients 3073) := by
  rw [y555NortonV, y555NortonVQ, map_mul]
  rfl

/-- Norton's involution relation holds in the actual named G. -/
theorem y555NortonV_square : y555NortonV ^ 2 = 1 := by
  rw [y555NortonV, ← map_pow, y555NortonVQ_square, map_one]

/-- The actual local embedding preserves the source word's nontriviality. -/
theorem y555NortonV_ne_one : y555NortonV ≠ 1 := by
  intro h
  apply y555NortonVQ_ne_one
  exact qIntoGenerated_injective (h.trans qIntoGenerated.map_one.symm)

/-- The concrete Norton word has exact order two in G. -/
theorem y555NortonV_order : orderOf y555NortonV = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime y555NortonV_square y555NortonV_ne_one

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
