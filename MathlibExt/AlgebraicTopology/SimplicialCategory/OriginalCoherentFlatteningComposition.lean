/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTwoBeadFlattening

/-!
# Exact original coherent composition through every flattening

Every full original flattening evaluates its whole union coefficient to
the same actual presented composition. The proof uses the original two
outer-operator relations and the original full composition relation.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.Flattening

open SimplicialEnrichment
open SSet.OriginalTwoBead.OrdinalCharts

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {s : SimplexCategoryᵒᵖ}
  {b : Bead K x y s} {c : Bead K y z s} (f : Flattening b c)

/-- The complete first coefficient evaluates to the same original first bead. -/
theorem left_evaluation :
    CoefficientGluing.leftMap b.dimension c.dimension ≫
      simplexHom K f.simplex (initial (b.dimension + c.dimension))
        (CoefficientGluing.middle b.dimension c.dimension) f.source_eq f.middle_eq =
      simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
        b.source_eq b.target_eq := by
  have ho := source_operator_factor (prefixOperator b.dimension c.dimension)
    f.simplex b.simplex f.left (initial b.dimension) (terminal b.dimension)
    (initial (b.dimension + c.dimension)) (CoefficientGluing.middle b.dimension c.dimension)
    (prefix_initial (b := b) (c := c)) (prefix_terminal (b := b) (c := c))
    b.source_eq b.target_eq f.source_eq f.middle_eq
  exact (congrArg (fun h => h ≫
    simplexHom K f.simplex (initial (b.dimension + c.dimension))
      (CoefficientGluing.middle b.dimension c.dimension) f.source_eq f.middle_eq)
        (CoefficientGluing.leftMap_original b.dimension c.dimension)).trans
    ((Category.assoc _ _ _).trans ho)

/-- The complete second coefficient evaluates to the same original second bead. -/
theorem right_evaluation :
    CoefficientGluing.rightMap b.dimension c.dimension ≫
      simplexHom K f.simplex (CoefficientGluing.middle b.dimension c.dimension)
        (terminal (b.dimension + c.dimension)) f.middle_eq f.target_eq =
      simplexHom K c.simplex (initial c.dimension) (terminal c.dimension)
        c.source_eq c.target_eq := by
  have ho := source_operator_factor (suffixOperator b.dimension c.dimension)
    f.simplex c.simplex f.right (initial c.dimension) (terminal c.dimension)
    (CoefficientGluing.middle b.dimension c.dimension) (terminal (b.dimension + c.dimension))
    (suffix_initial (b := b) (c := c)) (suffix_terminal (b := b) (c := c))
    c.source_eq c.target_eq f.middle_eq f.target_eq
  exact (congrArg (fun h => h ≫
    simplexHom K f.simplex (CoefficientGluing.middle b.dimension c.dimension)
      (terminal (b.dimension + c.dimension)) f.middle_eq f.target_eq)
        (CoefficientGluing.rightMap_original b.dimension c.dimension)).trans
    ((Category.assoc _ _ _).trans ho)

/-- The entire original two-coefficient diagram retains its genuine original composition. -/
theorem coefficient_evaluation :
    CoefficientGluing.map b.dimension c.dimension ≫
      simplexHom K f.simplex (initial (b.dimension + c.dimension))
        (terminal (b.dimension + c.dimension)) f.source_eq f.target_eq =
      (simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
          b.source_eq b.target_eq ⊗ₘ
        simplexHom K c.simplex (initial c.dimension) (terminal c.dimension)
          c.source_eq c.target_eq) ≫ eComp SSet.{u} (C := realization K) x y z := by
  let l := CoefficientGluing.leftMap b.dimension c.dimension
  let r := CoefficientGluing.rightMap b.dimension c.dimension
  let a := simplexHom K f.simplex (initial (b.dimension + c.dimension))
    (CoefficientGluing.middle b.dimension c.dimension) f.source_eq f.middle_eq
  let d := simplexHom K f.simplex (CoefficientGluing.middle b.dimension c.dimension)
    (terminal (b.dimension + c.dimension)) f.middle_eq f.target_eq
  have hc := simplexHom_composition f.simplex (initial (b.dimension + c.dimension))
    (CoefficientGluing.middle b.dimension c.dimension) (terminal (b.dimension + c.dimension))
    f.source_eq f.middle_eq f.target_eq
  have ht : (l ⊗ₘ r) ≫ (a ⊗ₘ d) =
      (simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
          b.source_eq b.target_eq ⊗ₘ
        simplexHom K c.simplex (initial c.dimension) (terminal c.dimension)
          c.source_eq c.target_eq) :=
    (tensorHom_comp_tensorHom l r a d).trans
      (congrArg₂ (fun h k => h ⊗ₘ k) f.left_evaluation f.right_evaluation)
  change ((l ⊗ₘ r) ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => (l ⊗ₘ r) ≫ h) hc).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ eComp SSet.{u} (C := realization K) x y z) ht)))

private theorem tensor_coefficient {X Y X' Y' : SSet.{u}} (a : X ⟶ X') (b : Y ⟶ Y')
    (s : SimplexCategoryᵒᵖ) (x : X.obj s) (y : Y.obj s) :
    (a ⊗ₘ b).app s (x, y) = (a.app s x, b.app s y) := rfl

private theorem coefficient_equation {X Y : SSet.{u}} {a b : X ⟶ Y}
    (h : a = b) (s : SimplexCategoryᵒᵖ) (p : X.obj s) :
    a.app s p = b.app s p :=
  ConcreteCategory.congr_hom (congr_app h s) p

/-- Every original flattening evaluates to the same actual original Hom composition. -/
theorem bead_evaluation :
    f.bead.evaluation =
      (eComp SSet.{u} (C := realization K) x y z).app s (b.evaluation, c.evaluation) := by
  have h := coefficient_equation f.coefficient_evaluation s
    (show (CoefficientGluing.beadHom b.dimension ⊗
      CoefficientGluing.beadHom c.dimension).obj s from (b.coefficient, c.coefficient))
  change _ = (eComp SSet.{u} (C := realization K) x y z).app s
    ((simplexHom K b.simplex (initial b.dimension) (terminal b.dimension)
        b.source_eq b.target_eq ⊗ₘ
      simplexHom K c.simplex (initial c.dimension) (terminal c.dimension)
        c.source_eq c.target_eq).app s (b.coefficient, c.coefficient)) at h
  rw [tensor_coefficient] at h
  exact h

end CategoryTheory.CoherentRealization.OriginalBead.Flattening
