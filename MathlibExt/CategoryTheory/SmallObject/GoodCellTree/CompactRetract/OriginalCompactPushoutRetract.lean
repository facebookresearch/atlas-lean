/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.ArrowRetractRootNormalization
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.CompactRootIdempotentCapture
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalRootedQuotientPushout
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Compact pushout presentations of an actual original Arrow retract

The finite construction starts with the actual original Arrow retract
and original pushout square. It fixes the source internally, uses one
original Under presentation, captures the actual local idempotent and
returns a pushout with the ACTUAL given target. The compact replacement
is an explicit retract of a pushout of the SAME original f.

## Source and specialization

The existence result formalizes Jacob Lurie's *Higher Topos Theory*,
author PDF dated April 9, 2017, Lemma A.1.5.10, printed pages 805–806
(PDF pages 823–824):
<https://www.math.ias.edu/~lurie/papers/HTT.pdf>.
The source assumes a presentable, κ-accessible ordinary category, a regular
κ, a map between κ-compact objects, a pushout of that map and an actual
retract in the morphism category.

Here κ is `chi`, compactness is `IsCardinalPresentable`, the original
pushout is `H : IsPushout u f i c`, and its given retract is
`R : RetractArrow g i`. `existsCompactPushout` uses
`IsCardinalLocallyPresentable C chi`. The accessible variant supplies
cardinal accessibility and the working colimits explicitly. The construction
with a given presentation states its colimit and compact-piece assumptions
directly. The output retains `RetractArrow f' (pushout.inl alpha f)`, the
root equation `alpha ≫ v = u ≫ R.r.left`, and compactness of the entire
replacement Arrow. This explicit single-pushout retract gives the source's
weak-saturation conclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uJ vJ u v

namespace CategoryTheory.SmallObject.OriginalCompactPushoutRetract

open Limits

section FixedPresentation

variable {C : Type u} [Category.{v} C] [HasPushouts C] [HasCoequalizers C]
  {A B X Y D E : C} {i : A ⟶ B} {g : X ⟶ Y}
  (R : RetractArrow g i) (u : D ⟶ A) (f : D ⟶ E) (c : E ⟶ B)
  (H : IsPushout u f i c) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [HasCardinalFilteredColimits C chi]
  [IsCardinalPresentable D chi] [IsCardinalPresentable E chi]
  {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J chi]
  (p : ColimitPresentation J (Under.mk (u ≫ R.r.left)))

/-- One shared actual trace in the SAME original chosen presentation. -/
def data :
    CompactRootIdempotentCapture.Data (u ≫ R.r.left) f p
      (ArrowRetractRootNormalization.nativeIdempotent R u f c H) :=
  CompactRootIdempotentCapture.data (u ≫ R.r.left) f p chi
    (ArrowRetractRootNormalization.nativeIdempotent R u f c H)
    (ArrowRetractRootNormalization.nativeRoot_idempotent R u f c H)
    (ArrowRetractRootNormalization.nativeIdempotent_idempotent R u f c H)

/-- The original first capture index, before the actual equality refinement. -/
abbrev initialIndex : J :=
  CompactRootIdempotentCapture.initialIndex (u ≫ R.r.left) f p (data R u f c H chi p).1

/-- The actual final index of the same original chosen category J. -/
abbrev index : J :=
  CompactRootIdempotentCapture.index (u ≫ R.r.left) f p (data R u f c H chi p).1

/-- The complete original refinement arrow remains exposed with its actual two indices. -/
abbrev refinement : initialIndex R u f c H chi p ⟶ index R u f c H chi p :=
  CompactRootIdempotentCapture.refinement (u ≫ R.r.left) f p (data R u f c H chi p).1

/-- The actual first captured generator-target map is retained. -/
abbrev initialCell :
    E ⟶ OriginalPushoutRootPresentation.stage (u ≫ R.r.left) f p
      (initialIndex R u f c H chi p) :=
  CompactRootIdempotentCapture.initialCell (u ≫ R.r.left) f p (data R u f c H chi p).1

/-- The compact source is the actual right object of the selected original piece. -/
abbrev sourceObj : C := (p.diag.obj (index R u f c H chi p)).right

/-- The selected original root arrow is not replaced by another generator. -/
abbrev rootArrow : D ⟶ sourceObj R u f c H chi p :=
  (p.diag.obj (index R u f c H chi p)).hom

/-- The original compact-stage target is the native pushout of that SAME f. -/
abbrev cellTarget : C := pushout (rootArrow R u f c H chi p) f

/-- Its actual native original root inclusion. -/
abbrev cellRoot : sourceObj R u f c H chi p ⟶ cellTarget R u f c H chi p :=
  pushout.inl (rootArrow R u f c H chi p) f

/-- The actual whole original stage comparison into the normalized native endpoint. -/
abbrev stageComparison : cellTarget R u f c H chi p ⟶ pushout (u ≫ R.r.left) f :=
  CompactRootPushoutPresentation.comparison (u ≫ R.r.left) f p (index R u f c H chi p)

/-- The actual selected local idempotent is the shared trace's native descender. -/
abbrev endomorphism : cellTarget R u f c H chi p ⟶ cellTarget R u f c H chi p :=
  CompactRootIdempotentCapture.endomorphism (u ≫ R.r.left) f p (data R u f c H chi p).1

omit [HasCoequalizers C] in
/-- Actual original roots are fixed by the internally captured local endomorphism. -/
theorem endomorphism_root :
    cellRoot R u f c H chi p ≫ endomorphism R u f c H chi p = cellRoot R u f c H chi p :=
  CompactRootIdempotentCapture.endomorphism_root (u ≫ R.r.left) f p
    (ArrowRetractRootNormalization.nativeIdempotent R u f c H) (data R u f c H chi p)

omit [HasCoequalizers C] in
/-- Actual delayed equality proves idempotence of this SAME selected local endomorphism. -/
theorem endomorphism_idempotent :
    endomorphism R u f c H chi p ≫ endomorphism R u f c H chi p =
      endomorphism R u f c H chi p :=
  CompactRootIdempotentCapture.endomorphism_idempotent (u ≫ R.r.left) f p
    (ArrowRetractRootNormalization.nativeIdempotent R u f c H) (data R u f c H chi p)

omit [HasCoequalizers C] in
/-- Its endpoint intertwining is derived through every original map of the same presentation. -/
theorem endomorphism_intertwines :
    endomorphism R u f c H chi p ≫ stageComparison R u f c H chi p =
      stageComparison R u f c H chi p ≫
        ArrowRetractRootNormalization.nativeIdempotent R u f c H := by
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J chi
  let : IsConnected J := IsFiltered.isConnected J
  exact CompactRootIdempotentCapture.endomorphism_intertwines (u ≫ R.r.left) f p
    (ArrowRetractRootNormalization.nativeIdempotent R u f c H)
    (ArrowRetractRootNormalization.nativeRoot_idempotent R u f c H)
    (data R u f c H chi p)

/-- The actual compact quotient target is selected from this same local idempotent. -/
abbrev targetObj : C := OriginalRootedQuotientPushout.localObj (endomorphism R u f c H chi p)

/-- The compact replacement is the original root followed by its selected local projection. -/
abbrev arrow : sourceObj R u f c H chi p ⟶ targetObj R u f c H chi p :=
  OriginalRootedQuotientPushout.localRoot
    (cellRoot R u f c H chi p) (endomorphism R u f c H chi p)

/-- Its actual comparison to the GIVEN original retract source X. -/
abbrev toOriginalSource : sourceObj R u f c H chi p ⟶ X :=
  (p.ι.app (index R u f c H chi p)).right

/-- Its actual comparison to the GIVEN original retract target Y. -/
def toOriginalTarget : targetObj R u f c H chi p ⟶ Y :=
  OriginalRootedQuotientPushout.comparison (stageComparison R u f c H chi p)
    (ArrowRetractRootNormalization.nativeProjection R u f c H)
    (endomorphism R u f c H chi p) (endomorphism_idempotent R u f c H chi p)

omit [HasCoequalizers C] in
/-- The full selected root factor retains the original source projection R.r.left. -/
theorem root_toOriginalSource :
    rootArrow R u f c H chi p ≫ toOriginalSource R u f c H chi p = u ≫ R.r.left :=
  Under.w (p.ι.app (index R u f c H chi p))

omit [HasCoequalizers C] in
/-- The original small and whole native pushout UPs construct the actual selected stage square. -/
theorem originalStageIsPushout :
    IsPushout (toOriginalSource R u f c H chi p) (cellRoot R u f c H chi p)
      (pushout.inl (u ≫ R.r.left) f) (stageComparison R u f c H chi p) :=
  OriginalPushoutRootPresentation.stageIsPushout (u ≫ R.r.left) f p (index R u f c H chi p)

/-- The compact replacement is an ACTUAL Arrow retract of a pushout of the SAME original f. -/
def arrowRetract :
    RetractArrow (arrow R u f c H chi p) (pushout.inl (rootArrow R u f c H chi p) f) :=
  OriginalRootedQuotientPushout.localArrowRetract
    (cellRoot R u f c H chi p) (endomorphism R u f c H chi p)
    (endomorphism_idempotent R u f c H chi p) (endomorphism_root R u f c H chi p)

/-- The final square is DERIVED with the ACTUAL given original source X and target Y. -/
theorem isPushout :
    IsPushout (toOriginalSource R u f c H chi p) (arrow R u f c H chi p) g
      (toOriginalTarget R u f c H chi p) := by
  have h := OriginalRootedQuotientPushout.isPushout
    (toOriginalSource R u f c H chi p) (cellRoot R u f c H chi p)
    (pushout.inl (u ≫ R.r.left) f) (stageComparison R u f c H chi p)
    (originalStageIsPushout R u f c H chi p)
    (ArrowRetractRootNormalization.nativeInclusion R u f c H)
    (ArrowRetractRootNormalization.nativeProjection R u f c H)
    (ArrowRetractRootNormalization.nativeInclusion_projection R u f c H)
    (endomorphism R u f c H chi p) (endomorphism_idempotent R u f c H chi p)
    (endomorphism_intertwines R u f c H chi p)
    (ArrowRetractRootNormalization.nativeRoot_idempotent R u f c H)
  rw [ArrowRetractRootNormalization.nativeRoot_projection] at h
  exact h

/-- Every actual original cobase/retract-stable class keeps the same original f membership. -/
theorem property (Q : MorphismProperty C) [Q.IsStableUnderCobaseChange] [Q.IsStableUnderRetracts]
    (hf : Q f) : Q (arrow R u f c H chi p) :=
  MorphismProperty.of_retract (arrowRetract R u f c H chi p)
    (Q.pushout_inl (rootArrow R u f c H chi p) f hf)

omit [HasCoequalizers C] in
/-- Compactness of the source is from the selected ACTUAL original piece. -/
theorem sourcePresentable (hPieces : ∀ j, IsCardinalPresentable (p.diag.obj j).right chi) :
    IsCardinalPresentable (sourceObj R u f c H chi p) chi :=
  hPieces (index R u f c H chi p)

variable [LocallySmall.{w} C]

omit [HasCoequalizers C] in
/-- Compactness of the native local target uses only the three genuine compact span objects. -/
theorem cellTargetPresentable (hPieces : ∀ j, IsCardinalPresentable (p.diag.obj j).right chi) :
    IsCardinalPresentable (cellTarget R u f c H chi p) chi := by
  let : IsCardinalPresentable (sourceObj R u f c H chi p) chi :=
    sourcePresentable R u f c H chi p hPieces
  exact RelativeCellPresentability.ofPushout chi
    (IsPushout.of_hasPushout (rootArrow R u f c H chi p) f)

/-- The selected quotient target is compact by its actual original local object retract. -/
theorem targetPresentable (hPieces : ∀ j, IsCardinalPresentable (p.diag.obj j).right chi) :
    IsCardinalPresentable (targetObj R u f c H chi p) chi := by
  let : IsCardinalPresentable (cellTarget R u f c H chi p) chi :=
    cellTargetPresentable R u f c H chi p hPieces
  exact OriginalRootedQuotientPushout.localTargetPresentable
    (endomorphism R u f c H chi p) (endomorphism_idempotent R u f c H chi p) chi

/-- The ENTIRE actual replacement Arrow is compact at the same original regular rank. -/
theorem arrowPresentable (hPieces : ∀ j, IsCardinalPresentable (p.diag.obj j).right chi) :
    IsCardinalPresentable (Arrow.mk (arrow R u f c H chi p)) chi := by
  let : IsCardinalPresentable (sourceObj R u f c H chi p) chi :=
    sourcePresentable R u f c H chi p hPieces
  let : IsCardinalPresentable (cellTarget R u f c H chi p) chi :=
    cellTargetPresentable R u f c H chi p hPieces
  exact OriginalRootedQuotientPushout.localArrowPresentable
    (cellRoot R u f c H chi p) (endomorphism R u f c H chi p)
    (endomorphism_idempotent R u f c H chi p) chi

end FixedPresentation

section Existence

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A B X Y D E : C} {i : A ⟶ B} {g : X ⟶ Y}
  (R : RetractArrow g i) (u : D ⟶ A) (f : D ⟶ E) (c : E ⟶ B)
  (H : IsPushout u f i c) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable D chi] [IsCardinalPresentable E chi]

include H in
/-- Let `C` be χ-locally presentable at regular χ, with pushouts. Suppose
`u : D ⟶ A`, `f : D ⟶ E` and `c : E ⟶ B` form the given pushout
`H : IsPushout u f i c`, and `R : RetractArrow g i` is a given Arrow retract.
Both endpoints `D` and `E` of `f` must be χ-presentable at that same rank.
There are χ-presentable `D'` and `L`, maps `alpha : D ⟶ D'` and `v : D' ⟶ X`
with `alpha ≫ v = u ≫ R.r.left`, and `f' : D' ⟶ L` retracting the pushout
inclusion `pushout.inl alpha f` of the same `f`. The resulting square is
`IsPushout v f' g k`, and the entire replacement `Arrow.mk f'` is
χ-presentable. This is the fixed-rank form of Jacob Lurie's *Higher Topos
Theory* (author PDF, April 9, 2017), Lemma A.1.5.10, pp. 805–806. -/
theorem existsCompactPushout :
    ∃ (D' L : C) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable L chi)
      (alpha : D ⟶ D') (v : D' ⟶ X) (_ : alpha ≫ v = u ≫ R.r.left)
      (f' : D' ⟶ L) (k : L ⟶ Y) (_ : RetractArrow f' (pushout.inl alpha f)),
      IsPushout v f' g k ∧
        IsCardinalPresentable (Arrow.mk f') chi := by
  obtain ⟨J, jCategory, jFiltered, p, hPieces⟩ :=
    CompactRootPresentation.existsPresentation D chi (u ≫ R.r.left)
  let : EssentiallySmall.{w} J := essentiallySmall_of_small_of_locallySmall J
  let : HasCoequalizers C := inferInstance
  refine ⟨sourceObj R u f c H chi p, targetObj R u f c H chi p,
    sourcePresentable R u f c H chi p hPieces, targetPresentable R u f c H chi p hPieces,
    rootArrow R u f c H chi p, toOriginalSource R u f c H chi p,
    root_toOriginalSource R u f c H chi p, arrow R u f c H chi p,
    toOriginalTarget R u f c H chi p, arrowRetract R u f c H chi p,
    isPushout R u f c H chi p, arrowPresentable R u f c H chi p hPieces⟩

end Existence

section AccessibleInputs

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A B X Y D E : C} {i : A ⟶ B} {g : X ⟶ Y}
  (R : RetractArrow g i) (u : D ⟶ A) (f : D ⟶ E) (c : E ⟶ B)
  (H : IsPushout u f i c) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [IsCardinalAccessibleCategory C chi] [HasColimitsOfSize.{w, w} C]
  [IsCardinalPresentable D chi] [IsCardinalPresentable E chi]

include H in
/-- The actual supplied accessibility and working colimits suffice at the SAME chi. -/
theorem existsCompactPushoutOfAccessible :
    ∃ (D' L : C) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable L chi)
      (alpha : D ⟶ D') (v : D' ⟶ X) (_ : alpha ≫ v = u ≫ R.r.left)
      (f' : D' ⟶ L) (k : L ⟶ Y) (_ : RetractArrow f' (pushout.inl alpha f)),
      IsPushout v f' g k ∧
        IsCardinalPresentable (Arrow.mk f') chi := by
  let : IsCardinalLocallyPresentable C chi := { }
  exact existsCompactPushout R u f c H chi

end AccessibleInputs

end CategoryTheory.SmallObject.OriginalCompactPushoutRetract
