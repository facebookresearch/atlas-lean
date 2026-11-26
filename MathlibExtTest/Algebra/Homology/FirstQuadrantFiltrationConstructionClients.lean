/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration

/-!
# Clients of the complete horizontal-filtration construction

The actual filtration diagram has zero bottom and negative stages, agrees
with the natural-number filtration at nonnegative stages, and includes its
top stage by the identity on the total complex. Its transitions preserve
the structural inclusions into the total complex.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

example : (horizontalCompleteTotalFiltration K).diagram.obj (⊥ : EInt) =
    (HomologicalComplex.zero : ChainComplex C ℕ) := by
  change horizontalCompleteFilteredTotalComplex K ⊥ = _
  exact horizontalCompleteFilteredTotalComplex_bot K

example : (horizontalCompleteTotalFiltration K).diagram.obj ((-1 : ℤ) : EInt) =
    (HomologicalComplex.zero : ChainComplex C ℕ) := by
  simpa only [horizontalCompleteTotalFiltration_diagram_obj] using
    horizontalCompleteFilteredTotalComplex_coe_of_neg K (-1) (by decide)

example (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteTotalFiltration K).diagram.obj (a : EInt) =
      horizontalFilteredTotalComplex K a.toNat := by
  simpa only [horizontalCompleteTotalFiltration_diagram_obj] using
    horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha

example : (horizontalCompleteTotalFiltration K).ι.app (⊤ : EInt) =
    𝟙 (K.total (ComplexShape.down ℕ)) := by
  change horizontalCompleteFilteredTotalToTotal K ⊤ = _
  exact horizontalCompleteFilteredTotalToTotal_top K

example {i j : EInt} (h : i ≤ j) :
    (horizontalCompleteTotalFiltration K).diagram.map (homOfLE h) ≫
        (horizontalCompleteTotalFiltration K).ι.app j =
      (horizontalCompleteTotalFiltration K).ι.app i := by
  change horizontalCompleteFilteredTotalMap K h ≫
      horizontalCompleteFilteredTotalToTotal K j =
    horizontalCompleteFilteredTotalToTotal K i
  exact horizontalCompleteFilteredTotalMap_toTotal K h

end
