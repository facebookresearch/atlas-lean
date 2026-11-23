/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentPullbacks
import MathlibExt.CategoryTheory.SmallObject.Iteration.Pullbacks
import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentTerminalCardinalColimits
import MathlibExt.CategoryTheory.SmallObject.PresheafIterationCardinality

/-!
# Presheaf small-object API integration

Labelled attachments along monomorphic presheaf generators preserve arbitrary
pullbacks, and the same preservation holds through the pointed transfinite
iteration. Terminal attachments preserve cardinal-filtered colimits using
presentability of generator domains. Original fixed-cardinal terminal
factorizations retain their cellular maps and a common total-point bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u w s v uC vC

open CategoryTheory Limits MorphismProperty Opposite Cardinal

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.PresheafSmallObjectAPI

section PresheafAttachments

variable {D : Type w} [SmallCategory D] {ι : Type s} [Small.{max u w} ι]
  {A B : ι → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
  [∀ i, Mono (j i)]

-- Both components of every original Arrow span participate in the pullback.
example {P X Y Z : Arrow (Dᵒᵖ ⥤ Type (max u w))}
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) :
    IsPullback ((SmallObject.functor j).map a) ((SmallObject.functor j).map b)
      ((SmallObject.functor j).map f) ((SmallObject.functor j).map g) := by
  letI : PreservesLimitsOfShape WalkingCospan (SmallObject.functor j) :=
    SmallObject.presheafAttachment_preservesPullbacks j
  exact h.map (SmallObject.functor j)

-- Original cell labels retain their top and bottom maps under an arbitrary square.
example {X Y X' Y' : Dᵒᵖ ⥤ Type (max u w)}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} (τ : Arrow.mk p ⟶ Arrow.mk p')
    (d : Dᵒᵖ) (q : SmallObject.FunctorObjIndex j p)
    (z : (B q.i).obj d) (hz : z ∉ Set.range ((j q.i).app d)) :
    (SmallObject.functorMap j τ).app d
        (SmallObject.presheafAttachmentEquiv j p d (Sum.inr ⟨q, z, hz⟩)) =
      SmallObject.presheafAttachmentEquiv j p' d
        (Sum.inr ⟨SmallObject.FunctorObjIndex.mk q.i (q.t ≫ τ.left) (q.b ≫ τ.right)
          (by
            have hτ : τ.left ≫ p' = p ≫ τ.right := by
              simpa only [Arrow.mk_hom] using τ.w
            rw [Category.assoc, hτ, ← Category.assoc, q.w, Category.assoc]), z, hz⟩) := by
  simpa only [Sum.map_inr] using
    SmallObject.presheafAttachmentEquiv_naturality j τ d (Sum.inr ⟨q, z, hz⟩)

variable (κ : Cardinal.{max u w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasIterationOfShape κ.ord.ToType (Dᵒᵖ ⥤ Type (max u w))]

-- Apply the attachment theorem before iterating it at the original supplied ordinal.
example (k : κ.ord.ToType) {P X Y Z : Arrow (Dᵒᵖ ⥤ Type (max u w))}
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) :
    let T := (SmallObject.SuccStruct.ofNatTrans (SmallObject.ε j)).iteration κ.ord.ToType
    let Tk := ((SmallObject.SuccStruct.ofNatTrans (SmallObject.ε j)).iterationFunctor
      κ.ord.ToType).obj k
    IsPullback (T.map a) (T.map b) (T.map f) (T.map g) ∧
      IsPullback (Tk.map a) (Tk.map b) (Tk.map f) (Tk.map g) := by
  letI : PreservesLimitsOfShape WalkingCospan (SmallObject.functor j) :=
    SmallObject.presheafAttachment_preservesPullbacks j
  let T := (SmallObject.SuccStruct.ofNatTrans (SmallObject.ε j)).iteration κ.ord.ToType
  let Tk := ((SmallObject.SuccStruct.ofNatTrans (SmallObject.ε j)).iterationFunctor
    κ.ord.ToType).obj k
  letI : PreservesLimitsOfShape WalkingCospan T :=
    SmallObject.SuccStruct.arrow_iteration_preservesPullbacks_of_presheaf_equivalence
      (𝟭 (Dᵒᵖ ⥤ Type (max u w))) (SmallObject.ε j)
  letI : PreservesLimitsOfShape WalkingCospan Tk :=
    SmallObject.SuccStruct.arrow_iterationFunctor_obj_preservesPullbacks_of_presheaf_equivalence
      (𝟭 (Dᵒᵖ ⥤ Type (max u w))) (SmallObject.ε j) k
  exact ⟨h.map T, h.map Tk⟩

end PresheafAttachments

section TerminalFilteredColimits

variable {D : Type w} [SmallCategory D] {ι : Type s} [Small.{max u w} ι]
  {A B : ι → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
  [∀ i, Mono (j i)] (μ : Cardinal.{max u w}) [Fact μ.IsRegular]
  [∀ i, IsCardinalPresentable (A i) μ]

-- No presentability assumption on B is needed for the original terminal attachment cocone.
example {E : Type (max u w)} [SmallCategory E] [IsCardinalFiltered E μ]
    {F : E ⥤ Dᵒᵖ ⥤ Type (max u w)} (c : Cocone F) (hc : IsColimit c) :
    let K := (terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w)) ⋙
      SmallObject.functor j) ⋙ Arrow.leftFunc
    IsColimit (K.mapCocone c) := by
  let K := (terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w)) ⋙
    SmallObject.functor j) ⋙ Arrow.leftFunc
  letI : K.IsCardinalAccessible μ :=
    SmallObject.presheafAttachment_terminal_isCardinalAccessible j μ
  letI : PreservesColimitsOfShape E K :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible K μ E
  exact isColimitOfPreserves K hc

end TerminalFilteredColimits

section OriginalTerminalFactors

variable {D : Type w} [Category.{v} D] {C : Type uC} [Category.{vC} C]
  [HasTerminal C] (I : MorphismProperty C) (κ : Cardinal.{max u w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]
  (F : C ⥤ Dᵒᵖ ⥤ Type (max u w)) [F.IsEquivalence]
  (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ) (hκ : κ ≤ ξ)
  (hI :
    letI : I.IsSmall.{max u w} := SmallObject.isSmall I κ
    Cardinal.mk (Shrink.{max u w} I.toSet) ≤ ξ)
  (hA : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.left).Elements ≤ ξ)
  (hB : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.right).Elements ≤ ξ)

include hξ hκ hI hA hB

-- The bounded endpoint belongs to the same native relative-cell factorization.
example (X : C) (hX : Cardinal.mk (F.obj X).Elements ≤ 2 ^ ξ) :
    Cardinal.mk (F.obj (SmallObject.obj I κ (terminal.from X))).Elements ≤ 2 ^ ξ ∧
      Nonempty (HomotopicalAlgebra.RelativeCellComplex.{max u w}
        (fun _ : κ.ord.ToType => I.homFamily)
        (SmallObject.ιObj I κ (terminal.from X))) ∧
      I.rlp (SmallObject.πObj I κ (terminal.from X)) ∧
      SmallObject.ιObj I κ (terminal.from X) ≫
        SmallObject.πObj I κ (terminal.from X) = terminal.from X := by
  exact ⟨SmallObject.obj_terminal_mk_elements_le_of_presheaf_equivalence
      I κ F ξ hξ hκ hI hA hB X hX,
    ⟨SmallObject.relativeCellComplexιObj I κ (terminal.from X)⟩,
    SmallObject.rlp_πObj I κ (terminal.from X),
    SmallObject.ιObj_πObj I κ (terminal.from X)⟩

-- Two bounded endpoints use the original κ-middle action on an arbitrary source map.
example {X Y : C} (f : X ⟶ Y)
    (hX : Cardinal.mk (F.obj X).Elements ≤ 2 ^ ξ)
    (hY : Cardinal.mk (F.obj Y).Elements ≤ 2 ^ ξ) :
    Cardinal.mk (F.obj (SmallObject.obj I κ (terminal.from X))).Elements ≤ 2 ^ ξ ∧
      Cardinal.mk (F.obj (SmallObject.obj I κ (terminal.from Y))).Elements ≤ 2 ^ ξ ∧
      SmallObject.ιObj I κ (terminal.from X) ≫
          SmallObject.objMap I κ ((terminal.arrowFunctor C).map f) =
        f ≫ SmallObject.ιObj I κ (terminal.from Y) ∧
      SmallObject.objMap I κ ((terminal.arrowFunctor C).map f) ≫
          SmallObject.πObj I κ (terminal.from Y) =
        SmallObject.πObj I κ (terminal.from X) := by
  refine ⟨SmallObject.obj_terminal_mk_elements_le_of_presheaf_equivalence
      I κ F ξ hξ hκ hI hA hB X hX,
    SmallObject.obj_terminal_mk_elements_le_of_presheaf_equivalence
      I κ F ξ hξ hκ hI hA hB Y hY, ?_⟩
  have hi := SmallObject.ιObj_naturality I κ ((terminal.arrowFunctor C).map f)
  have hp := SmallObject.πObj_naturality I κ ((terminal.arrowFunctor C).map f)
  change SmallObject.ιObj I κ (terminal.from X) ≫
      SmallObject.objMap I κ ((terminal.arrowFunctor C).map f) =
    f ≫ SmallObject.ιObj I κ (terminal.from Y) at hi
  change SmallObject.objMap I κ ((terminal.arrowFunctor C).map f) ≫
      SmallObject.πObj I κ (terminal.from Y) =
    SmallObject.πObj I κ (terminal.from X) ≫ 𝟙 (⊤_ C) at hp
  exact ⟨hi, hp.trans (Category.comp_id _)⟩

end OriginalTerminalFactors

end MathlibExtTest.AlgebraicTopology.ModelCategory.PresheafSmallObjectAPI
