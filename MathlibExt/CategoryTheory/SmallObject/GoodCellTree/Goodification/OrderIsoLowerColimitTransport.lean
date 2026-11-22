/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Actual original lower-colimit transport through label order isomorphisms

The original label order isomorphism transports each whole lower preimage,
its complete vertex diagram and original lower-comparison cocone. The
actual old lower-colimit UP constructs the new one through that same
original index equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OrderIsoLowerColimitTransport

open Limits LowerSetColimits

variable {U V Q : Type w} [PartialOrder U] [PartialOrder V] [Preorder Q]
  {C : Type u} [Category.{v} C]
  (e : U ≃o V) (f : V →o Q) (F : V ⥤ C) (Y : Q ⥤ C)
  (beta : F ⟶ f.monotone.functor ⋙ Y) (L : LowerSetColimitData Y)

/-- The full actual original-label map uses the given original label order isomorphism. -/
def labels : U →o Q where
  toFun p := f (e p)
  monotone' := by intro a b h; exact f.monotone (e.monotone h)

/-- The complete reindexed original vertex diagram uses the actual original label functor. -/
abbrev diagram : U ⥤ C := e.equivalence.functor ⋙ F

/-- The actual natural vertex comparison retains the complete original component function. -/
def comparison : diagram e F ⟶ (labels e f).monotone.functor ⋙ Y :=
  Functor.whiskerLeft e.equivalence.functor beta

/-- The actual original lower preimage retains the same label order isomorphism. -/
def carrierIso (D : LowerSet Q) :
    OriginalLowerComparisonCocone.carrier (labels e f) D ≃o
      OriginalLowerComparisonCocone.carrier f D where
  toFun p := ⟨e p.1, p.2⟩
  invFun p := ⟨e.symm p.1, by
    have hp := p.2
    change f p.1 ∈ D at hp
    change f (e (e.symm p.1)) ∈ D
    rw [e.apply_symm_apply]
    exact hp⟩
  left_inv p := by apply Subtype.ext; exact e.symm_apply_apply p.1
  right_inv p := by apply Subtype.ext; exact e.apply_symm_apply p.1
  map_rel_iff' := by intro a b; exact e.le_iff_le

/-- The entire actual original lower diagram retains its complete object and Hom functions. -/
theorem diagram_eq (D : LowerSet Q) :
    restriction (diagram e F) (OriginalLowerComparisonCocone.carrier (labels e f) D) =
      (carrierIso e f D).equivalence.functor ⋙
        restriction F (OriginalLowerComparisonCocone.carrier f D) := rfl

/-- The full actual original lower cocone retains its selected point and original vertex legs. -/
theorem cocone_eq (D : LowerSet Q) :
    OriginalLowerComparisonCocone.cocone (labels e f) (diagram e F) Y
      (comparison e f F Y beta) L D =
    (OriginalLowerComparisonCocone.cocone f F Y beta L D).whisker
      (carrierIso e f D).equivalence.functor := rfl

/-- The actual old lower-colimit UP constructs the full reindexed original lower-colimit UP. -/
def isColimit (D : LowerSet Q)
    (hOld : IsColimit (OriginalLowerComparisonCocone.cocone f F Y beta L D)) :
    IsColimit
      (OriginalLowerComparisonCocone.cocone (labels e f) (diagram e F) Y
        (comparison e f F Y beta) L D) :=
  hOld.whiskerEquivalence (carrierIso e f D).equivalence

end CategoryTheory.SmallObject.OrderIsoLowerColimitTransport
