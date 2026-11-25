/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalCompactPushoutRetract

/-!
# Compact pushout retracts of actual bounded original cell trees

Use the merged compact-root construction on the actual bounded original
tree. Its whole original endpoint UP supplies the original square to
the finite Arrow-retract construction. No compact-root presentation,
local idempotent, endpoint Iso or coherent history is supplied as input.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.BoundedCellTreeCompactRetract

open Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (hP : HasCardinalLT P chi)
  (hSource : ∀ a : P, IsCardinalPresentable (s (T.label a)).left chi)
  (hTarget : ∀ a : P, IsCardinalPresentable (s (T.label a)).right chi)

/-- The whole original compact-root data is constructed internally by the actual merged producer. -/
abbrev compactData : CompactRootBaseChange.CompactRootPresentation chi T :=
  CompactRootBaseChange.compactRootPresentation chi T hP hSource hTarget

/-- The original actual compact tree endpoint arrow, with its selected new root. -/
abbrev compactArrow : Arrow C :=
  Arrow.mk (compactData chi T hP hSource hTarget).tree.hom

/-- The entire compact tree endpoint Arrow is presentable at the same supplied regular rank. -/
theorem compactArrowPresentable :
    IsCardinalPresentable (compactArrow chi T hP hSource hTarget) chi := by
  let H := compactData chi T hP hSource hTarget
  let : IsCardinalPresentable H.root chi := H.root_presentable
  let : IsCardinalPresentable H.tree.endpointObj.right chi := H.endpoint_presentable
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) (κ := chi)
    (X₁ := H.root) (X₂ := H.tree.endpointObj.right) H.tree.hom

/-- The actual original whole endpoint square is the SAME constructor's pushout, with both legs. -/
theorem originalEndpointPushout :
    IsPushout (compactData chi T hP hSource hTarget).rootMap
      (compactData chi T hP hSource hTarget).tree.hom T.hom
      (pushout.inl (compactData chi T hP hSource hTarget).tree.hom
          (compactData chi T hP hSource hTarget).rootMap ≫
        (compactData chi T hP hSource hTarget).endpointComparison.hom.right) :=
  (compactData chi T hP hSource hTarget).endpoint_isPushout.flip

/-- Assume `C` is χ-accessible at regular χ, with pushouts and colimits of
working size `(w, w)`. Let `T : CellTree s X` have a strict vertex bound
|P| < χ and χ-presentable sources and targets for every cell label used by
`T`. For a given `R : RetractArrow g T.hom`, there are χ-presentable `D'` and
`L`, a root factor `beta ≫ v = compactData.rootMap ≫ R.r.left`, and a map
`f' : D' ⟶ L` retracting a pushout of the same constructed compact tree arrow.
They give `IsPushout v f' g k` and a χ-presentable `Arrow.mk f'`.
Boundedness alone, without these ambient and endpoint hypotheses, is not
asserted to suffice. -/
theorem existsCompactPushout {A B : C} {g : A ⟶ B} (R : RetractArrow g T.hom) :
    ∃ (D' L : C) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable L chi)
      (beta : (compactData chi T hP hSource hTarget).root ⟶ D') (v : D' ⟶ A)
      (_ : beta ≫ v = (compactData chi T hP hSource hTarget).rootMap ≫ R.r.left)
      (f' : D' ⟶ L) (k : L ⟶ B)
      (_ : RetractArrow f'
        (pushout.inl beta (compactData chi T hP hSource hTarget).tree.hom)),
      IsPushout v f' g k ∧ IsCardinalPresentable (Arrow.mk f') chi := by
  let H := compactData chi T hP hSource hTarget
  let : IsCardinalPresentable H.root chi := H.root_presentable
  let : IsCardinalPresentable H.tree.endpointObj.right chi := H.endpoint_presentable
  exact OriginalCompactPushoutRetract.existsCompactPushoutOfAccessible R H.rootMap H.tree.hom
    (pushout.inl H.tree.hom H.rootMap ≫ H.endpointComparison.hom.right)
    H.endpoint_isPushout.flip chi

end CategoryTheory.SmallObject.BoundedCellTreeCompactRetract
