/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple

namespace MetaMathlibExt

noncomputable section

example : hardyLittlewoodResidueCount 0 Fin.elim0 2 = 0 := by decide
example : hardyLittlewoodResidueCount 2 (fun i => (i.val : ℤ)) 2 = 2 := by decide

example : IsAdmissibleFinset ∅ := isAdmissibleFinset_empty
example : IsAdmissibleFinset {0} := isAdmissibleFinset_singleton_zero

/-- The tuple `(0, 1)` is not admissible: it covers both classes mod `2`. -/
example : ¬ IsHardyLittlewoodAdmissible 2 (fun i => (i.val : ℤ)) := by
  rw [isHardyLittlewoodAdmissible_iff_isAdmissibleFinset]
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  fin_cases r
  · exact hr 0 (by decide) rfl
  · exact hr 1 (by decide) rfl

#print axioms hardyLittlewoodResidueCount
#print axioms hardyLittlewoodPrimeTupleCount
#print axioms hardyLittlewoodSingularSeries

end

end MetaMathlibExt
