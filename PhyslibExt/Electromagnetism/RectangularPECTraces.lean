/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Rectangular-guide PEC boundary traces

Pointwise perfect-electric-conductor (PEC) trace conditions on the four side
walls of a rectangular guide, stated as vanishing tangential electric and
normal magnetic components, and their equivalence to explicit component
conditions on each face.

## i. Overview

Let `a, b > 0` and let `E` and `B` be vector fields on three-dimensional
space. The guide has the four side walls `x = 0`, `x = a`, `y = 0` and
`y = b`, with no end caps in `z`. On an `x`-wall the tangential electric
components are the `y` and `z` components and the normal magnetic component
is the `x` component; on a `y`-wall the tangential electric components are
the `x` and `z` components and the normal magnetic component is the `y`
component. A wall point carries the remaining transverse coordinate in the
closed interval across the guide and an arbitrary `z` coordinate. Closed
intervals are used so that each corner line belongs to both adjacent walls.
Both predicates encode positive widths: each includes the conjunct
`0 < a ∧ 0 < b`, so neither holds for any field when a width is zero or
negative. Without it, a negative width would make the interval across the
guide empty, and the clauses of the two walls that interval spans would hold
for every field.

The fields are component functions `(Fin 3 → ℝ) → Fin 3 → ℝ`, a point
`p : Fin 3 → ℝ` having coordinates `p 0`, `p 1`, `p 2` read as `x`, `y`,
`z`. This representation is kept rather than adopting a canonical field
carrier, for two reasons. First, the canonical electric and magnetic field
types are time dependent maps from space points to Euclidean vectors; at a
fixed time, such a field gives exactly a component function of this form by
evaluating at the space point with the given coordinates and reading
components `0`, `1` and `2`, so the predicates here apply directly to the
components of a canonical field at fixed time. Second, no new field carrier
is needed to state pointwise wall conditions, and the free-space Maxwell
module in Physlib states boundary conditions as outside its current scope,
so this module depends only on Mathlib and neither restates nor uses any
bulk equation.

Normal `B = 0` is an explicitly chosen compatible condition for this mode
family, on the same footing as tangential `E = 0`. No result here derives
it, or any other part of the trace condition, from a bulk partial
differential equation: a field with a nonzero tangential electric component
on a wall fails the condition whatever equations it may solve elsewhere.
At a corner line, where an `x`-wall and a `y`-wall meet, all three electric
components and the first two magnetic components vanish; the third magnetic
component is left unconstrained, and the corner results state exactly that.
General Sobolev traces and curved boundaries are not treated.

The per-face equivalences are proved by unfolding the face predicates, so
they are definitional. The headline equivalence composes the four per-face
equivalences face by face, for any widths and any fields; it needs no
smoothness or width hypothesis, since the predicates are pointwise and each
side already carries the width conjunct. No Sobolev trace is claimed. The
corner results combine the two adjacent wall conditions at a corner point,
taking the positive widths from the trace predicate itself.
The validation results are the zero fields, which satisfy the traces for any
positive widths, and concrete failures from a single nonzero component on
one wall.

## ii. Key results

- `rectangularGuidePECTraces`: positive widths and the four-wall PEC trace
  condition.
- `rectangularGuidePECComponentConditions`: positive widths and the same
  condition spelled out as explicit component equations on each face.
- `xZeroWall_traces_iff_components`, `xTopWall_traces_iff_components`,
  `yZeroWall_traces_iff_components`, `yTopWall_traces_iff_components`:
  the per-face equivalences.
- `traces_iff_componentConditions`: for any widths and any fields, the
  four-wall trace condition holds exactly when the explicit component
  conditions hold on each face.
- `cornerComponents_of_rectangularGuidePECTraces` and
  `allCornerComponents_of_rectangularGuidePECTraces`: vanishing of all
  electric components and the first two magnetic components at corner
  lines.
- `rectangularGuidePECTraces_zero`: the zero fields satisfy the traces for
  positive widths.
- `not_rectangularGuidePECTraces_of_tangentialElectricNeZero` and
  `not_rectangularGuidePECTraces_of_normalMagneticNeZero`: one nonzero
  component on one wall breaks the condition.
- `constantTangentialField_not_rectangularGuidePECTraces`: the constant
  field `E = (0, 1, 0)` with `B = 0` fails for any widths.

## iii. Table of contents

- A. Face predicates
- B. Per-face equivalences
- C. Headline equivalence
- D. Corners
- E. Validation boundaries

## iv. References

- R. E. Collin, *Field Theory of Guided Waves*, 2nd ed., IEEE Press,
  1991: boundary conditions at a perfect electric conductor (vanishing
  tangential electric field and vanishing normal magnetic flux density)
  and modes of the rectangular waveguide.

## A. Face predicates
-/

@[expose] public section

namespace PhyslibExt.Electromagnetism.RectangularPECTraces

/-- Tangential electric field on an `x`-wall at `p`: the `y` and
`z` electric components vanish. -/
def tangentialElectricOnXWall (E : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ) :
    Prop :=
  E p 1 = 0 ∧ E p 2 = 0

/-- Tangential electric field on a `y`-wall at `p`: the `x` and
`z` electric components vanish. -/
def tangentialElectricOnYWall (E : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ) :
    Prop :=
  E p 0 = 0 ∧ E p 2 = 0

/-- Normal magnetic field on an `x`-wall at `p`: the `x` magnetic
component vanishes. -/
def normalMagneticOnXWall (B : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ) :
    Prop :=
  B p 0 = 0

/-- Normal magnetic field on a `y`-wall at `p`: the `y` magnetic
component vanishes. -/
def normalMagneticOnYWall (B : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ) :
    Prop :=
  B p 1 = 0

/-- The pointwise PEC traces on all four side walls of the
rectangular guide with positive widths `a` and `b`: the widths are
positive, and tangential `E` and normal `B` vanish on each wall. -/
def rectangularGuidePECTraces (a b : ℝ) (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    Prop :=
  (0 < a ∧ 0 < b) ∧
  (∀ y z : ℝ, 0 ≤ y → y ≤ b →
    tangentialElectricOnXWall E ![0, y, z] ∧ normalMagneticOnXWall B ![0, y, z]) ∧
  (∀ y z : ℝ, 0 ≤ y → y ≤ b →
    tangentialElectricOnXWall E ![a, y, z] ∧ normalMagneticOnXWall B ![a, y, z]) ∧
  (∀ x z : ℝ, 0 ≤ x → x ≤ a →
    tangentialElectricOnYWall E ![x, 0, z] ∧ normalMagneticOnYWall B ![x, 0, z]) ∧
  (∀ x z : ℝ, 0 ≤ x → x ≤ a →
    tangentialElectricOnYWall E ![x, b, z] ∧ normalMagneticOnYWall B ![x, b, z])

/-- Positive widths `a` and `b` and the explicit component zero
conditions on all four side walls, spelled out face by face. -/
def rectangularGuidePECComponentConditions (a b : ℝ)
    (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) : Prop :=
  (0 < a ∧ 0 < b) ∧
  (∀ y z : ℝ, 0 ≤ y → y ≤ b →
    E ![0, y, z] 1 = 0 ∧ E ![0, y, z] 2 = 0 ∧ B ![0, y, z] 0 = 0) ∧
  (∀ y z : ℝ, 0 ≤ y → y ≤ b →
    E ![a, y, z] 1 = 0 ∧ E ![a, y, z] 2 = 0 ∧ B ![a, y, z] 0 = 0) ∧
  (∀ x z : ℝ, 0 ≤ x → x ≤ a →
    E ![x, 0, z] 0 = 0 ∧ E ![x, 0, z] 2 = 0 ∧ B ![x, 0, z] 1 = 0) ∧
  (∀ x z : ℝ, 0 ≤ x → x ≤ a →
    E ![x, b, z] 0 = 0 ∧ E ![x, b, z] 2 = 0 ∧ B ![x, b, z] 1 = 0)

/-- A vector over `Fin 3` with all components zero is the zero vector. -/
private lemma vec_eq_zero_of_components (v : Fin 3 → ℝ)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 0) : v = 0 := by
  apply funext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- At a point carrying both an `x`-wall face and a `y`-wall face, the
electric field vanishes and the first two magnetic components vanish. -/
private lemma corner_of_faces (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ)
    (hX : tangentialElectricOnXWall E p ∧ normalMagneticOnXWall B p)
    (hY : tangentialElectricOnYWall E p ∧ normalMagneticOnYWall B p) :
    E p = 0 ∧ B p 0 = 0 ∧ B p 1 = 0 := by
  obtain ⟨⟨hEy, hEz⟩, hBx⟩ := hX
  obtain ⟨⟨hEx, -⟩, hBy⟩ := hY
  exact ⟨vec_eq_zero_of_components _ hEx hEy hEz, hBx, hBy⟩

/-! ## B. Per-face equivalences -/

/-- On the wall `x = 0`, tangential `E` and normal `B` vanish
exactly when the three explicit component conditions hold. -/
lemma xZeroWall_traces_iff_components (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (y z : ℝ) :
    (tangentialElectricOnXWall E ![0, y, z] ∧ normalMagneticOnXWall B ![0, y, z]) ↔
      (E ![0, y, z] 1 = 0 ∧ E ![0, y, z] 2 = 0 ∧ B ![0, y, z] 0 = 0) := by
  simp only [tangentialElectricOnXWall, normalMagneticOnXWall, and_assoc]

/-- On the wall `x = a`, tangential `E` and normal `B` vanish
exactly when the three explicit component conditions hold. -/
lemma xTopWall_traces_iff_components (a : ℝ) (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (y z : ℝ) :
    (tangentialElectricOnXWall E ![a, y, z] ∧ normalMagneticOnXWall B ![a, y, z]) ↔
      (E ![a, y, z] 1 = 0 ∧ E ![a, y, z] 2 = 0 ∧ B ![a, y, z] 0 = 0) := by
  simp only [tangentialElectricOnXWall, normalMagneticOnXWall, and_assoc]

/-- On the wall `y = 0`, tangential `E` and normal `B` vanish
exactly when the three explicit component conditions hold. -/
lemma yZeroWall_traces_iff_components (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x z : ℝ) :
    (tangentialElectricOnYWall E ![x, 0, z] ∧ normalMagneticOnYWall B ![x, 0, z]) ↔
      (E ![x, 0, z] 0 = 0 ∧ E ![x, 0, z] 2 = 0 ∧ B ![x, 0, z] 1 = 0) := by
  simp only [tangentialElectricOnYWall, normalMagneticOnYWall, and_assoc]

/-- On the wall `y = b`, tangential `E` and normal `B` vanish
exactly when the three explicit component conditions hold. -/
lemma yTopWall_traces_iff_components (b : ℝ) (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x z : ℝ) :
    (tangentialElectricOnYWall E ![x, b, z] ∧ normalMagneticOnYWall B ![x, b, z]) ↔
      (E ![x, b, z] 0 = 0 ∧ E ![x, b, z] 2 = 0 ∧ B ![x, b, z] 1 = 0) := by
  simp only [tangentialElectricOnYWall, normalMagneticOnYWall, and_assoc]

/-! ## C. Headline equivalence -/

/-- **PEC traces, component form.** For any widths and any fields, the
four-wall PEC trace condition holds exactly when the explicit component zero
conditions hold on each face. -/
lemma traces_iff_componentConditions (a b : ℝ) (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    rectangularGuidePECTraces a b E B ↔
      rectangularGuidePECComponentConditions a b E B := by
  constructor
  · rintro ⟨hpos, h1, h2, h3, h4⟩
    refine ⟨hpos, ?_, ?_, ?_, ?_⟩
    · intro y z hy0 hyb
      exact (xZeroWall_traces_iff_components E B y z).mp (h1 y z hy0 hyb)
    · intro y z hy0 hyb
      exact (xTopWall_traces_iff_components a E B y z).mp (h2 y z hy0 hyb)
    · intro x z hx0 hxa
      exact (yZeroWall_traces_iff_components E B x z).mp (h3 x z hx0 hxa)
    · intro x z hx0 hxa
      exact (yTopWall_traces_iff_components b E B x z).mp (h4 x z hx0 hxa)
  · rintro ⟨hpos, h1, h2, h3, h4⟩
    refine ⟨hpos, ?_, ?_, ?_, ?_⟩
    · intro y z hy0 hyb
      exact (xZeroWall_traces_iff_components E B y z).mpr (h1 y z hy0 hyb)
    · intro y z hy0 hyb
      exact (xTopWall_traces_iff_components a E B y z).mpr (h2 y z hy0 hyb)
    · intro x z hx0 hxa
      exact (yZeroWall_traces_iff_components E B x z).mpr (h3 x z hx0 hxa)
    · intro x z hx0 hxa
      exact (yTopWall_traces_iff_components b E B x z).mpr (h4 x z hx0 hxa)

/-! ## D. Corners -/

/-- At the corner line `x = 0`, `y = 0`, a field satisfying the
traces has all electric components zero and its first two magnetic
components zero. -/
lemma cornerComponents_of_rectangularGuidePECTraces (a b : ℝ)
    (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (h : rectangularGuidePECTraces a b E B) (z : ℝ) :
    E ![0, 0, z] = 0 ∧ B ![0, 0, z] 0 = 0 ∧ B ![0, 0, z] 1 = 0 := by
  obtain ⟨⟨ha, hb⟩, hx0, -, hy0, -⟩ := h
  exact corner_of_faces E B _ (hx0 0 z le_rfl hb.le) (hy0 0 z le_rfl ha.le)

/-- The same corner conclusion at all four corner lines
`(0, 0)`, `(a, 0)`, `(0, b)` and `(a, b)`. -/
lemma allCornerComponents_of_rectangularGuidePECTraces (a b : ℝ)
    (E B : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (h : rectangularGuidePECTraces a b E B) (z : ℝ) :
    (E ![0, 0, z] = 0 ∧ E ![a, 0, z] = 0 ∧ E ![0, b, z] = 0 ∧
      E ![a, b, z] = 0) ∧
    (B ![0, 0, z] 0 = 0 ∧ B ![a, 0, z] 0 = 0 ∧ B ![0, b, z] 0 = 0 ∧
      B ![a, b, z] 0 = 0) ∧
    (B ![0, 0, z] 1 = 0 ∧ B ![a, 0, z] 1 = 0 ∧ B ![0, b, z] 1 = 0 ∧
      B ![a, b, z] 1 = 0) := by
  obtain ⟨⟨ha, hb⟩, hx0, hxTop, hy0, hyTop⟩ := h
  have c00 := corner_of_faces E B _ (hx0 0 z le_rfl hb.le) (hy0 0 z le_rfl ha.le)
  have ca0 := corner_of_faces E B _ (hxTop 0 z le_rfl hb.le) (hy0 a z ha.le le_rfl)
  have c0b := corner_of_faces E B _ (hx0 b z hb.le le_rfl) (hyTop 0 z le_rfl ha.le)
  have cab := corner_of_faces E B _ (hxTop b z hb.le le_rfl) (hyTop a z ha.le le_rfl)
  exact ⟨⟨c00.1, ca0.1, c0b.1, cab.1⟩, ⟨c00.2.1, ca0.2.1, c0b.2.1, cab.2.1⟩,
    ⟨c00.2.2, ca0.2.2, c0b.2.2, cab.2.2⟩⟩

/-! ## E. Validation boundaries -/

/-- The zero fields satisfy the PEC traces for any positive widths. -/
lemma rectangularGuidePECTraces_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    rectangularGuidePECTraces a b 0 0 := by
  simp only [rectangularGuidePECTraces, tangentialElectricOnXWall, normalMagneticOnXWall,
    tangentialElectricOnYWall, normalMagneticOnYWall]
  exact ⟨⟨ha, hb⟩, fun _ _ _ _ => ⟨⟨rfl, rfl⟩, rfl⟩, fun _ _ _ _ => ⟨⟨rfl, rfl⟩, rfl⟩,
    fun _ _ _ _ => ⟨⟨rfl, rfl⟩, rfl⟩, fun _ _ _ _ => ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-- A nonzero tangential electric component on the wall `x = 0`
breaks the trace condition, whatever the bulk equations do. -/
lemma not_rectangularGuidePECTraces_of_tangentialElectricNeZero (a b : ℝ)
    (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) (y z : ℝ)
    (hy0 : 0 ≤ y) (hyb : y ≤ b) (h : E ![0, y, z] 1 ≠ 0) :
    ¬ rectangularGuidePECTraces a b E B := by
  intro hcon
  obtain ⟨-, hx0, -, -, -⟩ := hcon
  obtain ⟨⟨hEy, -⟩, -⟩ := hx0 y z hy0 hyb
  exact h hEy

/-- A nonzero normal magnetic component on the wall `y = b`
breaks the trace condition. -/
lemma not_rectangularGuidePECTraces_of_normalMagneticNeZero (a b : ℝ)
    (E B : (Fin 3 → ℝ) → Fin 3 → ℝ) (x z : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (h : B ![x, b, z] 1 ≠ 0) :
    ¬ rectangularGuidePECTraces a b E B := by
  intro hcon
  obtain ⟨-, -, -, -, hyTop⟩ := hcon
  obtain ⟨-, hBy⟩ := hyTop x z hx0 hxa
  exact h hBy

/-- Concrete failure: the constant field with electric component
`E = (0, 1, 0)` and zero magnetic field does not satisfy the traces
for any widths `a` and `b`. -/
lemma constantTangentialField_not_rectangularGuidePECTraces (a b : ℝ) :
    ¬ rectangularGuidePECTraces a b (fun _ => ![0, 1, 0]) 0 := by
  intro h
  refine not_rectangularGuidePECTraces_of_tangentialElectricNeZero a b _ _ 0 0 le_rfl
    h.1.2.le ?_ h
  simp

end PhyslibExt.Electromagnetism.RectangularPECTraces
