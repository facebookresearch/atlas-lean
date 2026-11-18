/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Electromagnetism.RectangularPECTraces
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Electromagnetism.RectangularPECTraces`

Concrete consumers of the rectangular-guide PEC trace API, and an axiom
audit of every production result.

## i. Overview

These are elaboration and non-vacuity checks at concrete values, not new
results. The guide widths are `a = 2` and `b = 3` throughout.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Zero fields
- B. Face predicates and per-face equivalences
- C. Headline equivalence and corners for the zero fields
- D. Constant tangential field failure at the origin
- E. Axiom audit

## iv. References

- `PhyslibExt.Electromagnetism.RectangularPECTraces`

## A. Zero fields
-/

@[expose] public section

open PhyslibExt.Electromagnetism.RectangularPECTraces

namespace PhyslibExtTest.Electromagnetism.RectangularPECTraces

/-- The zero fields satisfy the PEC traces for `a = 2`, `b = 3`. -/
example : rectangularGuidePECTraces 2 3 0 0 :=
  rectangularGuidePECTraces_zero 2 3

/-! ## B. Face predicates and per-face equivalences -/

/-- On the wall `x = 0` at the origin, the zero fields satisfy the three
explicit component conditions. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 1 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 2 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 0 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The per-face equivalence on `x = 0` at the origin, forward direction
for the zero fields. -/
example : tangentialElectricOnXWall 0 ![0, 0, 0] ∧ normalMagneticOnXWall 0 ![0, 0, 0] :=
  (xZeroWall_traces_iff_components 0 0 0 0).mpr ⟨rfl, rfl, rfl⟩

/-- The per-face equivalence on `y = 3` at `x = 0`, `z = 0`, backward
direction for the zero fields. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 3, 0] 0 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 3, 0] 2 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 3, 0] 1 = 0 :=
  (yTopWall_traces_iff_components 3 0 0 0 0).mp ⟨⟨rfl, rfl⟩, rfl⟩

/-! ## C. Headline equivalence and corners for the zero fields -/

/-- The explicit component conditions hold for the zero fields, by the
headline equivalence. -/
example : rectangularGuidePECComponentConditions 2 3 (fun _ => 0) (fun _ => 0) :=
  (rectangularGuidePECTraces_iff_componentConditions 2 3 (by norm_num) (by norm_num)
    _ _ contDiff_const contDiff_const).mp (rectangularGuidePECTraces_zero 2 3)

/-- At the corner line `x = 0`, `y = 0`, `z = 0`, the zero electric field
vanishes and its first two magnetic components vanish. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 0 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 1 = 0 :=
  cornerComponents_of_rectangularGuidePECTraces 2 3 (by norm_num) (by norm_num)
    0 0 (rectangularGuidePECTraces_zero 2 3) 0

/-- The electric field of the zero fields vanishes at all four corner
points in the plane `z = 0`. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![2, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 3, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![2, 3, 0] = 0 :=
  (allCornerComponents_of_rectangularGuidePECTraces 2 3 (by norm_num) (by norm_num)
    0 0 (rectangularGuidePECTraces_zero 2 3) 0).1

/-! ## D. Constant tangential field failure at the origin -/

/-- The constant field `E = (0, 1, 0)` with `B = 0` does not satisfy the
traces of the guide `a = 2`, `b = 3`. -/
example : ¬ rectangularGuidePECTraces 2 3 (fun _ => ![0, 1, 0]) 0 :=
  constantTangentialField_not_rectangularGuidePECTraces 2 3 (by norm_num)

/-- The same failure seen at the origin on the wall `x = 0`: the
tangential component `E ![0, 0, 0] 1 = 1` is nonzero. -/
example : ¬ rectangularGuidePECTraces 2 3 (fun _ => ![0, 1, 0]) 0 :=
  not_rectangularGuidePECTraces_of_tangentialElectricNeZero 2 3 _ _ 0 0 le_rfl
    (by norm_num) (by simp)

/-- A nonzero normal magnetic component on the wall `y = 3` at the
origin also breaks the traces. -/
example : ¬ rectangularGuidePECTraces 2 3 0 (fun _ => ![0, 1, 0]) :=
  not_rectangularGuidePECTraces_of_normalMagneticNeZero 2 3 _ _ 0 0 le_rfl
    (by norm_num) (by simp)

end PhyslibExtTest.Electromagnetism.RectangularPECTraces

/-! ## E. Axiom audit -/

#print axioms xZeroWall_traces_iff_components
#print axioms xTopWall_traces_iff_components
#print axioms yZeroWall_traces_iff_components
#print axioms yTopWall_traces_iff_components
#print axioms rectangularGuidePECTraces_iff_componentConditions
#print axioms cornerComponents_of_rectangularGuidePECTraces
#print axioms allCornerComponents_of_rectangularGuidePECTraces
#print axioms rectangularGuidePECTraces_zero
#print axioms not_rectangularGuidePECTraces_of_tangentialElectricNeZero
#print axioms not_rectangularGuidePECTraces_of_normalMagneticNeZero
#print axioms constantTangentialField_not_rectangularGuidePECTraces
