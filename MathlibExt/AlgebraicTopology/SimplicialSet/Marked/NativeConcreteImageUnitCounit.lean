/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeConcreteImageIso

/-!
# Whole native simplex and sharp image unit/counit formulas

Both comparisons retain the actual chart units and original native
straightening counit. Their reverse maps read the original native unit,
and the whole unit squares follow from the same adjunction. These are
literal categorical formulas before any replacement or Quillen claim.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The simplex image comparison is the actual straightened chart unit followed by the original native counit. -/
theorem nativeSimplexImageIso_counit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (nativeSimplexImageIso B n σ).hom =
      (nativeStraightening B).map (nativeSimplexChartHomEquiv B n σ (nativeSimplexChart B n σ) (𝟙 _)) ≫
        (nativeStraighteningAdjunction B).counit.app (nativeSimplexChart B n σ) := by
  change ((nativeStraighteningAdjunction B).homEquiv _ _).symm _ = _
  exact (nativeStraighteningAdjunction B).homEquiv_counit _ _ _

/-- The sharp chart comparison has the same whole original chart-unit and native counit mate formula. -/
theorem nativeSharpImageIso_counit (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeSharpImageIso B σ).hom =
      (nativeStraightening B).map (nativeSharpChartHomEquiv B σ (nativeSharpChart B σ) (𝟙 _)) ≫
        (nativeStraighteningAdjunction B).counit.app (nativeSharpChart B σ) := by
  change ((nativeStraighteningAdjunction B).homEquiv _ _).symm _ = _
  exact (nativeStraighteningAdjunction B).homEquiv_counit _ _ _

/-- The reverse simplex chart map reads precisely the actual whole native straightening unit. -/
theorem nativeSimplexImageIso_inv_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativeSimplexChartHomEquiv B n σ ((nativeStraightening B).obj (nativeSimplexBasis B n σ))
      (nativeSimplexImageIso B n σ).inv =
        (nativeStraighteningAdjunction B).unit.app (nativeSimplexBasis B n σ) := by
  change nativeSimplexChartHomEquiv B n σ _
    ((nativeSimplexChartHomEquiv B n σ _).symm
      ((nativeStraighteningAdjunction B).homEquiv _ _ (𝟙 _))) = _
  rw [Equiv.apply_symm_apply]
  exact ((nativeStraighteningAdjunction B).homEquiv_unit _ _ (𝟙 _)).trans
    ((congrArg (fun f => (nativeStraighteningAdjunction B).unit.app (nativeSimplexBasis B n σ) ≫ f)
      ((nativeUnstraightening B).map_id _)).trans (Category.comp_id _))

/-- The reverse sharp chart map keeps the same actual whole native unit. -/
theorem nativeSharpImageIso_inv_homEquiv (B : SSet.{u}) (σ : B _⦋1⦌) :
    nativeSharpChartHomEquiv B σ ((nativeStraightening B).obj (nativeSharpBasis B σ))
      (nativeSharpImageIso B σ).inv =
        (nativeStraighteningAdjunction B).unit.app (nativeSharpBasis B σ) := by
  change nativeSharpChartHomEquiv B σ _
    ((nativeSharpChartHomEquiv B σ _).symm
      ((nativeStraighteningAdjunction B).homEquiv _ _ (𝟙 _))) = _
  rw [Equiv.apply_symm_apply]
  exact ((nativeStraighteningAdjunction B).homEquiv_unit _ _ (𝟙 _)).trans
    ((congrArg (fun f => (nativeStraighteningAdjunction B).unit.app (nativeSharpBasis B σ) ≫ f)
      ((nativeUnstraightening B).map_id _)).trans (Category.comp_id _))

/-- The complete native simplex unit maps to exactly the original simplex chart unit under its same image comparison. -/
theorem nativeSimplexImageIso_unit_square (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (nativeStraighteningAdjunction B).unit.app (nativeSimplexBasis B n σ) ≫
        (nativeUnstraightening B).map (nativeSimplexImageIso B n σ).hom =
      nativeSimplexChartHomEquiv B n σ (nativeSimplexChart B n σ) (𝟙 _) :=
  ((nativeStraighteningAdjunction B).homEquiv_unit _ _ (nativeSimplexImageIso B n σ).hom).symm.trans
    (nativeSimplexImageIso_homEquiv B n σ)

/-- The whole sharp-unit square retains the actual original marked chart unit and same native comparison. -/
theorem nativeSharpImageIso_unit_square (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeStraighteningAdjunction B).unit.app (nativeSharpBasis B σ) ≫
        (nativeUnstraightening B).map (nativeSharpImageIso B σ).hom =
      nativeSharpChartHomEquiv B σ (nativeSharpChart B σ) (𝟙 _) :=
  ((nativeStraighteningAdjunction B).homEquiv_unit _ _ (nativeSharpImageIso B σ).hom).symm.trans
    (nativeSharpImageIso_homEquiv B σ)

end SSet.Marked
