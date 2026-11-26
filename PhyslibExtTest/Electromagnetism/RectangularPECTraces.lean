/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Electromagnetism.RectangularPECTraces
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Electromagnetism.RectangularPECTraces`

Concrete consumers of the rectangular-guide PEC trace API, and an axiom
audit of every production result.

## i. Overview

These are elaboration and non-vacuity checks at concrete values, not new
results. The guide widths are `a = 2` and `b = 3`, except in the checks
that no field satisfies either predicate at the negative widths
`a = b = -1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Zero fields
- B. Face predicates and per-face equivalences
- C. Headline equivalence and corners
- D. Constant tangential field failure at the origin
- E. Negative widths
- F. Axiom audit

## iv. References

- `PhyslibExt.Electromagnetism.RectangularPECTraces`

## A. Zero fields
-/

@[expose] public section

open PhyslibExt.Electromagnetism.RectangularPECTraces

namespace PhyslibExtTest.Electromagnetism.RectangularPECTraces

/-- The zero fields satisfy the PEC traces for `a = 2`, `b = 3`. -/
example : rectangularGuidePECTraces 2 3 0 0 :=
  rectangularGuidePECTraces_zero 2 3 (by norm_num) (by norm_num)

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

/-! ## C. Headline equivalence and corners -/

/-- The headline equivalence applies to arbitrary fields, with no
smoothness or width hypothesis to discharge. -/
example (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    rectangularGuidePECTraces 2 3 E B ↔ rectangularGuidePECComponentConditions 2 3 E B :=
  traces_iff_componentConditions 2 3 E B

/-- The explicit component conditions hold for the zero fields, by the
headline equivalence. -/
example : rectangularGuidePECComponentConditions 2 3 (fun _ => 0) (fun _ => 0) :=
  (traces_iff_componentConditions 2 3 _ _).mp
    (rectangularGuidePECTraces_zero 2 3 (by norm_num) (by norm_num))

/-- At the corner line `x = 0`, `y = 0`, `z = 0`, the zero electric field
vanishes and its first two magnetic components vanish. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 0 = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] 1 = 0 :=
  cornerComponents_of_rectangularGuidePECTraces 2 3
    0 0 (rectangularGuidePECTraces_zero 2 3 (by norm_num) (by norm_num)) 0

/-- The electric field of the zero fields vanishes at all four corner
points in the plane `z = 0`. -/
example : (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![2, 0, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![0, 3, 0] = 0 ∧
    (0 : (Fin 3 → ℝ) → Fin 3 → ℝ) ![2, 3, 0] = 0 :=
  (allCornerComponents_of_rectangularGuidePECTraces 2 3
    0 0 (rectangularGuidePECTraces_zero 2 3 (by norm_num) (by norm_num)) 0).1

/-- The third magnetic component is left free at the corners: the constant
field `B = (0, 0, 1)` with `E = 0` satisfies the traces of the guide
`a = 2`, `b = 3`, the corner results give its first two components zero at
all four corner points in a plane `z = const`, and its third component is
`1` at each of them. -/
example (z : ℝ) :
    let B : (Fin 3 → ℝ) → Fin 3 → ℝ := fun _ => ![0, 0, 1]
    rectangularGuidePECTraces 2 3 0 B ∧
    (B ![0, 0, z] 0 = 0 ∧ B ![2, 0, z] 0 = 0 ∧ B ![0, 3, z] 0 = 0 ∧
      B ![2, 3, z] 0 = 0) ∧
    (B ![0, 0, z] 1 = 0 ∧ B ![2, 0, z] 1 = 0 ∧ B ![0, 3, z] 1 = 0 ∧
      B ![2, 3, z] 1 = 0) ∧
    (B ![0, 0, z] 2 = 1 ∧ B ![2, 0, z] 2 = 1 ∧ B ![0, 3, z] 2 = 1 ∧
      B ![2, 3, z] 2 = 1) := by
  intro B
  have h : rectangularGuidePECTraces 2 3 0 B := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩ <;> intro _ _ _ _ <;>
      simp [B, tangentialElectricOnXWall, normalMagneticOnXWall,
        tangentialElectricOnYWall, normalMagneticOnYWall]
  have hc := allCornerComponents_of_rectangularGuidePECTraces 2 3 0 B h z
  exact ⟨h, hc.2.1, hc.2.2, by simp [B]⟩

/-! ## D. Constant tangential field failure at the origin -/

/-- The constant field `E = (0, 1, 0)` with `B = 0` does not satisfy the
traces of the guide `a = 2`, `b = 3`. -/
example : ¬ rectangularGuidePECTraces 2 3 (fun _ => ![0, 1, 0]) 0 :=
  constantTangentialField_not_rectangularGuidePECTraces 2 3

/-- The same failure seen at the origin on the wall `x = 0`: the
tangential component `E ![0, 0, 0] 1 = 1` is nonzero. -/
example : ¬ rectangularGuidePECTraces 2 3 (fun _ => ![0, 1, 0]) 0 :=
  not_rectangularGuidePECTraces_of_tangentialElectricNeZero 2 3 _ _ 0 0 le_rfl
    (by norm_num) (by simp)

/-- The constant-field failure needs no width hypothesis: at the
degenerate height `b = 0` it holds as well. -/
example : ¬ rectangularGuidePECTraces 2 0 (fun _ => ![0, 1, 0]) 0 :=
  constantTangentialField_not_rectangularGuidePECTraces 2 0

/-- A nonzero normal magnetic component on the wall `y = 3` at the
origin also breaks the traces. -/
example : ¬ rectangularGuidePECTraces 2 3 0 (fun _ => ![0, 1, 0]) :=
  not_rectangularGuidePECTraces_of_normalMagneticNeZero 2 3 _ _ 0 0 le_rfl
    (by norm_num) (by simp)

/-! ## E. Negative widths -/

/-- No pair of fields satisfies the PEC traces at the negative widths
`a = b = -1`, where the intervals across the guide are empty. -/
example (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) : ¬ rectangularGuidePECTraces (-1) (-1) E B := by
  rintro ⟨⟨ha, -⟩, -⟩
  norm_num at ha

/-- No pair of fields satisfies the explicit component conditions at the
negative widths `a = b = -1`. -/
example (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    ¬ rectangularGuidePECComponentConditions (-1) (-1) E B := by
  rintro ⟨⟨ha, -⟩, -⟩
  norm_num at ha

/-- In particular the zero fields, which satisfy the traces at positive
widths, fail them at `a = b = -1`. -/
example : ¬ rectangularGuidePECTraces (-1) (-1) 0 0 := by
  rintro ⟨⟨ha, -⟩, -⟩
  norm_num at ha

end PhyslibExtTest.Electromagnetism.RectangularPECTraces

/-! ## F. Axiom audit -/

#print axioms xZeroWall_traces_iff_components
#print axioms xTopWall_traces_iff_components
#print axioms yZeroWall_traces_iff_components
#print axioms yTopWall_traces_iff_components
#print axioms traces_iff_componentConditions
#print axioms cornerComponents_of_rectangularGuidePECTraces
#print axioms allCornerComponents_of_rectangularGuidePECTraces
#print axioms rectangularGuidePECTraces_zero
#print axioms not_rectangularGuidePECTraces_of_tangentialElectricNeZero
#print axioms not_rectangularGuidePECTraces_of_normalMagneticNeZero
#print axioms constantTangentialField_not_rectangularGuidePECTraces
