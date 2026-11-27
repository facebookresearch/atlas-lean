/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageTransposeCoherence

/-!
# Whole original functor, quotient and arbitrary operator clients
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial

universe u v uD vD

namespace MathlibExtTest.KTheory.Waldhausen.DoubleStageTransposeCoherence

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original outer simplex operator retains its whole functor after interchange. -/
private theorem originalOuterOperator {a b : SimplexCategory} (α : a ⟶ b) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C a.len;
    letI := generalStageWaldhausenCategory C a.len;
    letI := generalStageHasZeroObject C b.len;
    letI := generalStageWaldhausenCategory C b.len;
    reindexDoubleStageOuter C α n ⋙ doubleStageTransposeFunctor C a.len n =
      doubleStageTransposeFunctor C b.len n ⋙ reindexDoubleStageInner C α n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C a.len
  let := generalStageWaldhausenCategory C a.len
  let := generalStageHasZeroObject C b.len
  let := generalStageWaldhausenCategory C b.len
  exact doubleStageTransposeFunctor_reindexOuter C α n

/-- Every original inner simplex operator retains its whole functor after interchange. -/
private theorem originalInnerOperator {a b : SimplexCategory} (α : a ⟶ b) (m : ℕ) :
    letI := generalStageHasZeroObject C a.len;
    letI := generalStageWaldhausenCategory C a.len;
    letI := generalStageHasZeroObject C b.len;
    letI := generalStageWaldhausenCategory C b.len;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    reindexDoubleStageInner C α m ⋙ doubleStageTransposeFunctor C m a.len =
      doubleStageTransposeFunctor C m b.len ⋙ reindexDoubleStageOuter C α m := by
  let := generalStageHasZeroObject C a.len
  let := generalStageWaldhausenCategory C a.len
  let := generalStageHasZeroObject C b.len
  let := generalStageWaldhausenCategory C b.len
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact doubleStageTransposeFunctor_reindexInner C α m

/-- The complete original quotient functor agrees before forgetting stage morphisms. -/
private theorem originalQuotientFunctor (m n : ℕ) :
    letI := generalStageHasZeroObject C (n + 1);
    letI := generalStageWaldhausenCategory C (n + 1);
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    doubleStageTransposeFunctor C m (n + 1) ⋙ StageFirstQuotient.quotient (Stage C m) n =
      (StageFirstQuotient.quotient_isWaldhausenExact C n).mapStage m ⋙
        doubleStageTransposeFunctor C m n := by
  let := generalStageHasZeroObject C (n + 1)
  let := generalStageWaldhausenCategory C (n + 1)
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact doubleStageTransposeFunctor_quotient C m n

/-- The original quotient still acts on the original successor-index cells. -/
private theorem originalQuotientCell (m n : ℕ) :
    letI := generalStageHasZeroObject C (n + 1);
    letI := generalStageWaldhausenCategory C (n + 1);
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ (A : Stage (Stage C (n + 1)) m) (x : Ar n) (y : Ar m),
      ((((StageFirstQuotient.quotient (Stage C m) n).obj
        ((doubleStageTransposeFunctor C m (n + 1)).obj A)).obj.obj x).obj.obj y) =
      (A.obj.obj y).obj.obj ((indexFunctor (SimplexCategory.δ (0 : Fin (n + 2)))).obj x) := by
  let := generalStageHasZeroObject C (n + 1)
  let := generalStageWaldhausenCategory C (n + 1)
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A x y
  rfl

variable {C}
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Independent original base universes retain the whole double-stage functor square. -/
private theorem wholeOriginalFunctorSquare (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject D n;
    letI := generalStageWaldhausenCategory D n;
    letI := generalStageHasZeroObject D m;
    letI := generalStageWaldhausenCategory D m;
    doubleStageTransposeFunctor C m n ⋙ mapDoubleStage hF n m =
      mapDoubleStage hF m n ⋙ doubleStageTransposeFunctor D m n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject D n
  let := generalStageWaldhausenCategory D n
  let := generalStageHasZeroObject D m
  let := generalStageWaldhausenCategory D m
  exact doubleStageTransposeFunctor_mapDoubleStage hF m n

/-- The original exact functor maps the original scalar morphism after either whole route. -/
private theorem originalMappedCoefficient (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject D n;
    letI := generalStageWaldhausenCategory D n;
    letI := generalStageHasZeroObject D m;
    letI := generalStageWaldhausenCategory D m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B) (x : Ar n) (y : Ar m),
      (((doubleStageTransposeFunctor C m n ⋙
          mapDoubleStage hF n m).map φ).hom.app x).hom.app y =
        F.map ((φ.hom.app y).hom.app x) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject D n
  let := generalStageWaldhausenCategory D n
  let := generalStageHasZeroObject D m
  let := generalStageWaldhausenCategory D m
  intro A B φ x y
  rfl

end MathlibExtTest.KTheory.Waldhausen.DoubleStageTransposeCoherence

end
