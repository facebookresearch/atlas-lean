/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import MathlibExt.CategoryTheory.Presentable.FunctorPresentability
public import MathlibExt.CategoryTheory.Functor.OriginalArrowBounds

/-!
# Compact roots for bounded original diagrams

At a regular cardinal, compact component attachments into an original diagram
factor through one stage of its actual compact directed presentation. The
original arrow bound controls the family size and the compactness of the
returned components.

This is the common-stage subargument of Jacob Lurie's *Higher Topos Theory*,
author version dated April 9, 2017, Lemma A.3.3.17, printed page 883
(PDF page 901). Its source application chooses an uncountable rank for later
countable slice closures; this compact-root subargument uses regularity.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace CategoryTheory.Presentable

open CategoryTheory.Limits CategoryTheory.SmallObject.CompactRootBaseChange

/-- One compact diagram captures all original compact component attachments,
with the actual natural transformation and all component factor equations. -/
theorem existsCompactDiagramRoot
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (χ : Cardinal.{w}) [Fact χ.IsRegular] [IsCardinalLocallyPresentable C χ]
    (hD : HasCardinalLT (Arrow D) χ) (F : D ⥤ C) (X : D → C)
    (hX : ∀ d : D, IsCardinalPresentable (X d) χ)
    (a : ∀ d : D, X d ⟶ F.obj d) :
    ∃ (F₀ : D ⥤ C) (u : F₀ ⟶ F) (a₀ : ∀ d : D, X d ⟶ F₀.obj d),
      IsCardinalPresentable F₀ χ ∧
        (∀ d : D, IsCardinalPresentable (F₀.obj d) χ) ∧
        ∀ d : D, a₀ d ≫ u.app d = a d := by
  let : Small.{w} (Arrow D) := hD.small
  let : Small.{w} D := small_of_small_arrow D
  let : LocallySmall.{w} D := locallySmall_of_small_arrow D
  let index := equivSmallModel.{w} D
  let : IsCardinalLocallyPresentable (D ⥤ C) χ :=
    HomPowerAccessibility.diagramLocallyPresentable C χ index
  let A := compactApproximation χ F
  let : PartialOrder A.index := A.partialOrder
  let : IsCardinalFiltered A.index χ := A.filtered
  have hStage (d : D) :
      ∃ j : A.index, ∃ b : X d ⟶ (A.presentation.diag.obj j).obj d,
        b ≫ (A.presentation.ι.app j).app d = a d := by
    let : IsCardinalPresentable (X d) χ := hX d
    let ev := (evaluation D C).obj d
    exact IsCardinalPresentable.exists_hom_of_isColimit χ
      (isColimitOfPreserves ev A.presentation.isColimit) (a d)
  choose stage factor hFactor using hStage
  let hObjects : HasCardinalLT D χ := hasCardinalLT_of_hasCardinalLT_arrow hD
  let j := IsCardinalFiltered.max stage hObjects
  let transition (d : D) : stage d ⟶ j :=
    IsCardinalFiltered.toMax stage hObjects d
  let F₀ := A.presentation.diag.obj j
  let u := A.presentation.ι.app j
  let a₀ (d : D) : X d ⟶ F₀.obj d :=
    factor d ≫ (A.presentation.diag.map (transition d)).app d
  have hF₀ : IsCardinalPresentable F₀ χ := A.presentable j
  refine ⟨F₀, u, a₀, hF₀, ?_, ?_⟩
  · intro d
    let : IsCardinalPresentable F₀ χ := hF₀
    let : (Completeness.cofree C χ index d).IsCardinalAccessible χ :=
      HomPowerAccessibility.cofree_isCardinalAccessible_of_hom_bounds
        C χ index d χ le_rfl (fun e => Functor.OriginalArrowBounds.homLt hD e d)
    exact Adjunction.isCardinalPresentable_leftAdjoint_obj
      (Completeness.evaluationCofreeAdjunction C χ index d) χ F₀
  · intro d
    change (factor d ≫ (A.presentation.diag.map (transition d)).app d) ≫
      (A.presentation.ι.app j).app d = a d
    rw [Category.assoc]
    have hTransition :
        (A.presentation.diag.map (transition d)).app d ≫
          (A.presentation.ι.app j).app d =
        (A.presentation.ι.app (stage d)).app d :=
      NatTrans.congr_app (A.presentation.w (transition d)) d
    rw [hTransition]
    exact hFactor d

end CategoryTheory.Presentable
