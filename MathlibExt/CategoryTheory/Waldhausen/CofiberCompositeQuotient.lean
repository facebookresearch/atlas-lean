/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cofiber row of quotients of a composite cofibration

For cofibrations X→Y→Z, the actual cofiber pushouts of X→Y, X→Z and Y→Z
make the compatible quotient maps Y/X→Z/X→Z/Y a cofiber sequence.
Both its first cofibration and its quotient pushout are derived by the
original pushout universal properties and pasting cancellation.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- The compatible original quotient maps of a pair of cofibrations form
a cofiber row. No quotient cofibration or pushout conclusion is an input. -/
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
