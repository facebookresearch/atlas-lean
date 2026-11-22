/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaBousfieldKanSource
public import MathlibExt.CategoryTheory.NerveOpposite
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Bousfield--Kan totals of left-comma nerves

For `F : C ⥤ D`, the left-comma nerves
`d ↦ nerve (StructuredArrow d F)` form a contravariant `Dᵒᵖ`-diagram. This
file constructs its map to the constant point diagram and the induced
Bousfield--Kan total map to `nerve Dᵒᵖ`, with its simplex-reversed variant
landing in `opFunctor.obj (nerve D)`.

This is the contravariant mirror of the right-comma total-to-target layer.

This is a strictly model-independent comparison layer. It makes no
contractibility, homotopy, weak-equivalence, Quillen-Theorem-A, or
homotopy-fiber claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe u

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

/-- The objectwise terminal map from left-comma nerves to the point diagram. -/
def leftCommaToPoint (F : C ⥤ D) :
    leftCommaNerveDiagram F ⟶ bkPointDiagram Dᵒᵖ where
  app _ := stdSimplex.isTerminalObj₀.from _
  naturality _ _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _

@[simp]
theorem leftCommaToPoint_app (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaToPoint F).app d = stdSimplex.isTerminalObj₀.from _ :=
  rfl

@[simp↓]
theorem leftCommaToPoint_app_apply (F : C ⥤ D) (d : Dᵒᵖ)
    (a : SimplexCategoryᵒᵖ) (x : (nerve (StructuredArrow d.unop F)).obj a) :
    ((leftCommaToPoint F).app d).app a x = deltaZeroSimplex a := by
  apply SSet.stdSimplex.objEquiv.injective
  exact Subsingleton.elim _ _

/-- Simplified naturality square for the objectwise point map. -/
theorem leftCommaToPoint_naturality (F : C ⥤ D)
    {d d' : Dᵒᵖ} (g : d ⟶ d') :
    (leftCommaNerveDiagram F).map g ≫ (leftCommaToPoint F).app d' =
      (leftCommaToPoint F).app d :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The left-comma BK total maps to `nerve Dᵒᵖ` by first forgetting each
comma nerve to the point diagram and then applying the point-diagram
comparison. -/
def leftCommaTotalToTarget (F : C ⥤ D) :
    bkHocolim (leftCommaNerveDiagram F) ⟶ nerve Dᵒᵖ :=
  bkHocolimMap (leftCommaToPoint F) ≫ (bkPointIsoNerve Dᵒᵖ).hom

@[simp]
theorem leftCommaTotalToTarget_app_mk (F : C ⥤ D) (n : ℕ) :
    (leftCommaTotalToTarget F).app (op ⦋n⦌) =
      (bkHocolimMap (leftCommaToPoint F)).app (op ⦋n⦌) ≫
        (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌) :=
  rfl

/-- Weighted-summand formula for the map from the left-comma total to
`nerve Dᵒᵖ`. -/
theorem leftCommaTotalToTarget_app_mk_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx Dᵒᵖ (CategoryBar.replUnit Dᵒᵖ) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Dᵒᵖ) (leftCommaNerveDiagram F) n p).app
          (op ⦋n⦌) ≫
      (leftCommaTotalToTarget F).app (op ⦋n⦌) =
    ((leftCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Dᵒᵖ) (bkPointDiagram Dᵒᵖ) n p).app (op ⦋n⦌) ≫
          (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌)) := by
  change (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit Dᵒᵖ) (leftCommaNerveDiagram F) n p).app
        (op ⦋n⦌) ≫
      ((bkHocolimMap (leftCommaToPoint F)).app (op ⦋n⦌) ≫
        (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌)) = _
  calc
    _ = ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit Dᵒᵖ) (leftCommaNerveDiagram F) n p).app
            (op ⦋n⦌) ≫
        (bkHocolimMap (leftCommaToPoint F)).app (op ⦋n⦌)) ≫
          (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌) :=
      (Category.assoc _ _ _).symm
    _ = (((leftCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit Dᵒᵖ) (bkPointDiagram Dᵒᵖ) n p).app
              (op ⦋n⦌)) ≫
        (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌) :=
      congrArg (· ≫ (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌))
        (bkHocolimMap_app_mk_ι (leftCommaToPoint F) n p)
    _ = ((leftCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit Dᵒᵖ) (bkPointDiagram Dᵒᵖ) n p).app (op ⦋n⦌) ≫
            (bkPointIsoNerve Dᵒᵖ).hom.app (op ⦋n⦌)) :=
      Category.assoc _ _ _

/-- The simplex-reversed variant of the target total, landing in the
reversal of `nerve D`. -/
def leftCommaTotalToTargetRev (F : C ⥤ D) :
    bkHocolim (leftCommaNerveDiagram F) ⟶
      SimplicialObject.opFunctor.obj (nerve D) :=
  leftCommaTotalToTarget F ≫ (nerveOppositeSimplicialIso D).hom

@[simp↓]
theorem leftCommaTotalToTargetRev_app_mk (F : C ⥤ D) (n : ℕ)
    (X : (bkHocolim (leftCommaNerveDiagram F)).obj (op ⦋n⦌)) :
    (leftCommaTotalToTargetRev F).app (op ⦋n⦌) X =
      ((leftCommaTotalToTarget F).app (op ⦋n⦌) X).unop := by
  change ((nerveOppositeSimplicialIso D).hom.app (op ⦋n⦌)
    ((leftCommaTotalToTarget F).app (op ⦋n⦌) X)) = _
  exact nerveOppositeSimplicialIso_hom_app_mk D n _

end SSet

end
