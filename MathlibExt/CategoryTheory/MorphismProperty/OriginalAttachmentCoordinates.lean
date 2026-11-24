/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.MorphismProperty.CoproductCellDecomposition
public import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w u v t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.OriginalGeneratingCellCoordinates

variable {C : Type u} [Category.{v} C]

/-- A further original cobase change of an isomorphism or of an original
I-pushout is again an isomorphism or an original I-pushout. -/
theorem originalCells_pushouts_le (I : MorphismProperty C) :
    (isomorphisms C ⊔ I.pushouts).pushouts ≤ isomorphisms C ⊔ I.pushouts := by
  rintro X Y f ⟨A, B, p, a, b, hp, sq⟩
  rcases hp with hIso | hI
  · exact Or.inl ((isomorphisms C).of_isPushout sq hIso)
  · exact Or.inr (I.pushouts.of_isPushout sq hI)

section OrderedLabels

variable [HasPushouts C] [HasCoproducts.{w} C]
  (I : MorphismProperty C) {α : Type t} {A B : α → C}
  (g : ∀ a, A a ⟶ B a) (hg : ∀ a, I (g a))
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)
  [LinearOrder c.ι] [WellFoundedLT c.ι]
  [SuccOrder (CoproductCells.cellOrder c.ι)]

/-- The original attachment is the cobase change of the actual original
coordinate chain. Both supplied cofan isomorphisms and the actual attachment
square are retained, and the endpoint arrow is literally the original f. -/
def attachmentCoordinateChain :
    (isomorphisms C ⊔ I.pushouts).TransfiniteCompositionOfShape (CoproductCells.cellOrder c.ι) f :=
      by
  let A' : c.ι → C := fun i => A (c.π i)
  let B' : c.ι → C := fun i => B (c.π i)
  let g' : ∀ i : c.ι, A' i ⟶ B' i := fun i => g (c.π i)
  have hG : MorphismProperty.ofHoms g' ≤ I := by
    rintro K L p ⟨i⟩
    exact hg (c.π i)
  let coordinate := (CoproductCells.coproductMapOriginalCells g').ofLE
    (sup_le_sup le_rfl (MorphismProperty.pushouts_monotone hG))
  let eA : (∐ A') ≅ c.cofan₁.pt :=
    (colimit.isColimit (Discrete.functor A')).coconePointUniqueUpToIso c.isColimit₁
  let eB : (∐ B') ≅ c.cofan₂.pt :=
    (colimit.isColimit (Discrete.functor B')).coconePointUniqueUpToIso c.isColimit₂
  have hA (i : c.ι) : Sigma.ι A' i ≫ eA.hom = c.cofan₁.inj i :=
    colimit.comp_coconePointUniqueUpToIso_hom c.isColimit₁ (Discrete.mk i)
  have hB (i : c.ι) : Sigma.ι B' i ≫ eB.hom = c.cofan₂.inj i :=
    colimit.comp_coconePointUniqueUpToIso_hom c.isColimit₂ (Discrete.mk i)
  have hArrow : eA.hom ≫ c.m = Limits.Sigma.map g' ≫ eB.hom := by
    apply Sigma.hom_ext
    intro i
    calc
      Sigma.ι A' i ≫ (eA.hom ≫ c.m) = c.cofan₁.inj i ≫ c.m := by
        rw [← Category.assoc, hA]
      _ = g' i ≫ c.cofan₂.inj i := c.hm i
      _ = g' i ≫ Sigma.ι B' i ≫ eB.hom := by rw [hB]
      _ = Sigma.ι A' i ≫ (Limits.Sigma.map g' ≫ eB.hom) := by rw [Sigma.ι_map_assoc]
  let original : (isomorphisms C ⊔ I.pushouts).TransfiniteCompositionOfShape
      (CoproductCells.cellOrder c.ι) c.m :=
    coordinate.ofArrowIso (Arrow.isoMk eA eB hArrow)
  exact (original.cobaseChange c.g₁ c.isPushout).ofLE (originalCells_pushouts_le I)

end OrderedLabels

/-- Every actual original attachment has an actual well ordered continuous
single-cell history on the same source and endpoint, in the original working
universe. Empty labels are handled by the coordinate chain's isomorphism stages. -/
theorem attachmentHasOriginalCoordinateHistory
    [HasPushouts C] [HasCoproducts.{w} C]
    (I : MorphismProperty C) {α : Type t} {A B : α → C}
    (g : ∀ a, A a ⟶ B a) (hg : ∀ a, I (g a))
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty ((isomorphisms C ⊔ I.pushouts).TransfiniteCompositionOfShape J f) := by
  obtain ⟨order, wf⟩ := exists_wellFoundedLT c.ι
  let _ : LinearOrder c.ι := order
  let _ : WellFoundedLT c.ι := wf
  let _ : SuccOrder (CoproductCells.cellOrder c.ι) := SuccOrder.ofLinearWellFoundedLT _
  exact ⟨CoproductCells.cellOrder c.ι, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨attachmentCoordinateChain I g hg c⟩⟩

end HomotopicalAlgebra.OriginalGeneratingCellCoordinates
