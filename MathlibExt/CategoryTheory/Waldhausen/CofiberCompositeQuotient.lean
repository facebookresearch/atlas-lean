/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cofiber row of quotients of a composite cofibration

Let `C` have a zero object and a Waldhausen structure without gluing.
Given cofiber sequences `(i, q)`, `(i ≫ j, r)`, and `(j, s)` for
`i : X ⟶ Y` and `j : Y ⟶ Z`, the maps `α : Q ⟶ QXZ` and
`β : QXZ ⟶ QYZ` form a cofiber sequence when
`q ≫ α = j ≫ r` and `r ≫ β = s`.
The cofibration property of `α` and its quotient pushout follow from the
supplied cofiber pushouts and pasting cancellation.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let `C` have a zero object and a Waldhausen structure without gluing.
For `i : X ⟶ Y` and `j : Y ⟶ Z`, suppose `(i, q)`, `(i ≫ j, r)`,
and `(j, s)` are cofiber sequences, where `q : Y ⟶ Q`, `r : Z ⟶ QXZ`,
and `s : Z ⟶ QYZ`. If `α : Q ⟶ QXZ` and `β : QXZ ⟶ QYZ` satisfy
`q ≫ α = j ≫ r` and `r ≫ β = s`, then `(α, β)` is a cofiber sequence.
In particular, the cofibration property of `α` and its quotient pushout
are conclusions, not additional assumptions. -/
theorem IsCofiberSequence.quotient_comp
    {X Y Z Q QXZ QYZ : C}
    {i : X ⟶ Y} {j : Y ⟶ Z}
    {q : Y ⟶ Q} {r : Z ⟶ QXZ} {s : Z ⟶ QYZ}
    (hI : IsCofiberSequence i q)
    (hIJ : IsCofiberSequence (i ≫ j) r)
    (hJ : IsCofiberSequence j s)
    {α : Q ⟶ QXZ} {β : QXZ ⟶ QYZ}
    (hα : q ≫ α = j ≫ r) (hβ : r ≫ β = s) :
    IsCofiberSequence α β := by
  obtain ⟨_, zI, uI, pI⟩ := hI
  obtain ⟨_, zIJ, uIJ, pIJ⟩ := hIJ
  obtain ⟨hj, zJ, uJ, pJ⟩ := hJ
  have hz : zIJ = zI := (isZero_zero C).eq_of_tgt _ _
  have hu : uIJ = uI ≫ α := (isZero_zero C).eq_of_src _ _
  have pOuter : IsPushout (i ≫ j) zI r (uI ≫ α) := by
    simpa only [hz, hu] using pIJ.flip
  have pSquare : IsPushout j q r α := pOuter.of_left hα.symm pI.flip
  have hαcof : IsCofibration α :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout pSquare.flip hj
  let zQ : Q ⟶ (0 : C) := (isZero_zero C).from_ Q
  have hzQ : q ≫ zQ = zJ := (isZero_zero C).eq_of_tgt _ _
  have hcomm : α ≫ β = zQ ≫ uJ := by
    apply pI.hom_ext
    · exact (isZero_zero C).eq_of_src _ _
    · calc
        q ≫ (α ≫ β) = (q ≫ α) ≫ β := (Category.assoc _ _ _).symm
        _ = (j ≫ r) ≫ β := congrArg (fun h => h ≫ β) hα
        _ = j ≫ (r ≫ β) := Category.assoc _ _ _
        _ = j ≫ s := congrArg (fun h => j ≫ h) hβ
        _ = zJ ≫ uJ := pJ.w.symm
        _ = (q ≫ zQ) ≫ uJ := congrArg (fun h => h ≫ uJ) hzQ.symm
        _ = q ≫ (zQ ≫ uJ) := Category.assoc _ _ _
  have pOuterJ : IsPushout j (q ≫ zQ) (r ≫ β) uJ := by
    rw [hzQ, hβ]
    exact pJ.flip
  have pQuotient : IsPushout α zQ β uJ := pOuterJ.of_top hcomm pSquare
  exact ⟨hαcof, zQ, uJ, pQuotient.flip⟩

end CategoryTheory
