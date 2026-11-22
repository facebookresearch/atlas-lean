/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.EndComparison

/-!
# Ordering indices in Day free internal Hom

Uses the index braiding to compare the free-end target functor with the shifted internal-Hom
target in the opposite tensor order. Gives both component maps for every Day diagram and index
object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace NativeOmegaPreparation.DayIndexOrder
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  (r : I) (M : V)

/-- The final-factor translation uses the original right tensor index functor and original
coefficient internal Hom. -/
def rightTargetFunctor : DayFunctor I V ⥤ DayFunctor I V :=
  (DayFunctor.equiv I V).functor ⋙
    (Functor.whiskeringLeft I I V).obj (tensorRight r) ⋙
      (Functor.whiskeringRight I V V).obj (ihom M) ⋙ (DayFunctor.equiv I V).inverse

/-- The complete original index braiding compares first-factor and final-factor translations before
and after coefficient internal Hom. -/
def comparison : DayFreeEnd.targetFunctor r M ≅ rightTargetFunctor r M :=
  Functor.isoWhiskerLeft (DayFunctor.equiv I V).functor
    (Functor.isoWhiskerRight
      ((Functor.whiskeringLeft I I V).mapIso (BraidedCategory.tensorLeftIsoTensorRight r))
      ((Functor.whiskeringRight I V V).obj (ihom M) ⋙ (DayFunctor.equiv I V).inverse))

/-- The actual forward index-order comparison is the original full beta_(r,n) target map under
coefficient internal Hom. -/
theorem comparison_hom_component (G : DayFunctor I V) (n : I) :
    ((comparison r M).hom.app G).natTrans.app n =
      (ihom M).map (G.functor.map (β_ r n).hom) := rfl

/-- The actual inverse index-order comparison retains the unchanged inverse of that same original
braiding. -/
theorem comparison_inv_component (G : DayFunctor I V) (n : I) :
    ((comparison r M).inv.app G).natTrans.app n =
      (ihom M).map (G.functor.map (β_ r n).inv) := rfl

end NativeOmegaPreparation.DayIndexOrder
