/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage

/-!
# Pushout rectangles in finite Waldhausen stages

Every four-index rectangle in a finite Waldhausen stage is a pushout.  The
proof views it as the right square in a horizontal paste: the left square and
the full outer square are the diagonal pushouts supplied by
`IsStage.isPushout_actualSquare`, and `IsPushout.of_left` cancels the left
pushout.

Equal indices are allowed throughout.  This module adds only the generic
finite-stage rectangle lemma; it constructs no Quillen span, flag, quotient
descent, simplicial comparison, realization, additivity, or Q/S equivalence.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- For `i ≤ j ≤ k ≤ l`, the square

```text
A(i,k) ──→ A(i,l)
  │           │
  ↓           ↓
A(j,k) ──→ A(j,l)
```

formed by the canonical horizontal and vertical stage maps is a pushout.
The statement is uniform when any adjacent indices are equal. -/
theorem IsStage.isPushout_intervalRectangle
    {n : ℕ} {A : Ar n ⥤ C} (hA : IsStage n A)
    {i j k l : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    IsPushout
      (A.map (horiz (hij.trans hjk) hkl))
      (A.map (vert hij hjk))
      (A.map (vert hij (hjk.trans hkl)))
      (A.map (horiz hjk hkl)) := by
  have hLeft := isPushout_actualSquare hA hij hjk
  have hOuter := isPushout_actualSquare hA hij (hjk.trans hkl)
  have hTop :
      A.map (horiz hij hjk) ≫
          A.map (horiz (hij.trans hjk) hkl) =
        A.map (horiz hij (hjk.trans hkl)) := by
    rw [← A.map_comp]
    apply A.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hBottom :
      A.map (fromDiag hjk) ≫ A.map (horiz hjk hkl) =
        A.map (fromDiag (hjk.trans hkl)) := by
    rw [← A.map_comp]
    apply A.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hOuter' :
      IsPushout
        (A.map (horiz hij hjk) ≫
          A.map (horiz (hij.trans hjk) hkl))
        (A.map (toDiag hij))
        (A.map (vert hij (hjk.trans hkl)))
        (A.map (fromDiag hjk) ≫ A.map (horiz hjk hkl)) := by
    simpa only [hTop, hBottom] using hOuter
  have hComm :
      A.map (horiz (hij.trans hjk) hkl) ≫
          A.map (vert hij (hjk.trans hkl)) =
        A.map (vert hij hjk) ≫ A.map (horiz hjk hkl) := by
    rw [← A.map_comp, ← A.map_comp]
    apply A.congr_map
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  exact hOuter'.of_left hComm hLeft

end CategoryTheory.Waldhausen.SConstruction
