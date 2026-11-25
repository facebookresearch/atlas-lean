/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageTranspose
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageReindex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFirstQuotientDecomposition

/-!
# Original whole-functor coherence of double-stage interchange

The literal axis swap commutes with the actual double stage of an exact
functor, exchanges both original simplex directions, and retains the
original zeroth-face quotient functor. These are equations of whole
original functors before any nerve or realization is taken.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u v uD vD

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual outer original simplex operator becomes the actual inner operator. -/
theorem doubleStageTransposeFunctor_reindexOuter
    {a b : SimplexCategory} (α : a ⟶ b) (n : ℕ) :
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
  rfl

/-- The actual inner original simplex operator becomes the actual outer operator. -/
theorem doubleStageTransposeFunctor_reindexInner
    {a b : SimplexCategory} (α : a ⟶ b) (m : ℕ) :
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
  rfl

/-- Evaluation after interchange is the original exact interval evaluation mapped to stages. -/
theorem doubleStageTransposeFunctor_eval (m n : ℕ) (x : Ar n) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    doubleStageTransposeFunctor C m n ⋙ eval (Stage C m) n x =
      (evalIsGeneralStageWaldhausenExact C n x).mapStage m := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  rfl

/-- The actual quotient after interchange is the same staged original zeroth-face quotient. -/
theorem doubleStageTransposeFunctor_quotient (m n : ℕ) :
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
  rfl

variable {C}
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Interchange commutes with the entire original double-stage map of the original exact functor. -/
theorem doubleStageTransposeFunctor_mapDoubleStage (m n : ℕ) :
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
  rfl

end CategoryTheory.Waldhausen.SConstruction

end
