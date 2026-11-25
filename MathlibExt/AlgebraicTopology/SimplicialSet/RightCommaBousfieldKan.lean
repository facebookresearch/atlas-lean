/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSource
public import MathlibExt.CategoryTheory.CategoryBar.CommaRightPointNaturality
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Bousfield--Kan totals of right-comma nerves

For `F : C ⥤ D`, the right-comma nerves
`d ↦ nerve (CostructuredArrow F d)` form a covariant `D`-diagram.  This file
constructs its projection to the constant diagram on `nerve C`, its map to
the constant point diagram, and the two induced Bousfield--Kan total maps.

This is a strictly model-independent comparison layer.  It makes no
contractibility, homotopy, weak-equivalence, Quillen-Theorem-A, or
homotopy-fiber claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The objectwise terminal map from right-comma nerves to the point diagram. -/
def rightCommaToPoint (F : C ⥤ D) :
    rightCommaNerveDiagram.{max u w, max v w, u} F ⟶ bkPointDiagram D where
  app _ := stdSimplex.isTerminalObj₀.from _
  naturality _ _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _

@[simp]
theorem rightCommaToPoint_app (F : C ⥤ D) (d : D) :
    (rightCommaToPoint F).app d = stdSimplex.isTerminalObj₀.from _ :=
  rfl

@[simp↓]
theorem rightCommaToPoint_app_apply (F : C ⥤ D) (d : D)
    (a : SimplexCategoryᵒᵖ) (x : (nerve (CostructuredArrow F d)).obj a) :
    ((rightCommaToPoint F).app d).app a x = deltaZeroSimplex a := by
  apply SSet.stdSimplex.objEquiv.injective
  exact Subsingleton.elim _ _

/-- Simplified naturality square for the objectwise point map. -/
theorem rightCommaToPoint_naturality (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (rightCommaNerveDiagram.{max u w, max v w, u} F).map g ≫ (rightCommaToPoint F).app d' =
      (rightCommaToPoint F).app d :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The right-comma BK total maps to `nerve D` by first forgetting each
comma nerve to the point diagram and then applying the point-diagram
comparison. -/
def rightCommaTotalToTarget (F : C ⥤ D) :
    bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F) ⟶ nerve D :=
  bkHocolimMap (rightCommaToPoint F) ≫ (bkPointIsoNerve D).hom

@[simp]
theorem rightCommaTotalToTarget_app_mk (F : C ⥤ D) (n : ℕ) :
    (rightCommaTotalToTarget F).app (op ⦋n⦌) =
      (bkHocolimMap (rightCommaToPoint F)).app (op ⦋n⦌) ≫
        (bkPointIsoNerve D).hom.app (op ⦋n⦌) :=
  rfl

/-- Weighted-summand formula for the map from the right-comma total to
`nerve D`. -/
theorem rightCommaTotalToTarget_app_mk_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
          (op ⦋n⦌) ≫
      (rightCommaTotalToTarget F).app (op ⦋n⦌) =
    ((rightCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (bkPointDiagram D) n p).app (op ⦋n⦌) ≫
          (bkPointIsoNerve D).hom.app (op ⦋n⦌)) := by
  change (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
        (op ⦋n⦌) ≫
      ((bkHocolimMap (rightCommaToPoint F)).app (op ⦋n⦌) ≫
        (bkPointIsoNerve D).hom.app (op ⦋n⦌)) = _
  calc
    _ = ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
            (op ⦋n⦌) ≫
        (bkHocolimMap (rightCommaToPoint F)).app (op ⦋n⦌)) ≫
          (bkPointIsoNerve D).hom.app (op ⦋n⦌) :=
      (Category.assoc _ _ _).symm
    _ = (((rightCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (bkPointDiagram D) n p).app
              (op ⦋n⦌)) ≫
        (bkPointIsoNerve D).hom.app (op ⦋n⦌) :=
      congrArg (· ≫ (bkPointIsoNerve D).hom.app (op ⦋n⦌))
        (bkHocolimMap_app_mk_ι (rightCommaToPoint F) n p)
    _ = ((rightCommaToPoint F).app p.1.left).app (op ⦋n⦌) ≫
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (bkPointDiagram D) n p).app (op ⦋n⦌) ≫
            (bkPointIsoNerve D).hom.app (op ⦋n⦌)) :=
      Category.assoc _ _ _

end SSet

end
