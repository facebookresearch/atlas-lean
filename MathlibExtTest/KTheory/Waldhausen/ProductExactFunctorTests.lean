/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ProductExactFunctor

/-!
# Generic clients for exact common-source pairing

The public pairing theorem retains three independent object and morphism
universe roles. Its actual paired functor has the original objects and
maps, and both original zero-insertion pairs reuse the same core facts.
No first-quotient or realization module is imported.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD uE vE

namespace MathlibExtTest.KTheory.Waldhausen.ProductExactFunctorTests

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : C ⥤ E}

/-- The original common-source pair is exact in all three independent category roles. -/
theorem originalCommonSourcePair (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    letI : WaldhausenCategoryWithoutGluing (D × E) := prodWaldhausen
    (F.prod' G).IsWaldhausenExact := hF.prod' hG

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
  [HasZeroObject E] [WaldhausenCategoryWithoutGluing E] in
/-- The complete original paired object keeps both actual functor values. -/
theorem originalPairObject (X : C) : (F.prod' G).obj X = (F.obj X, G.obj X) := rfl

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
  [HasZeroObject E] [WaldhausenCategoryWithoutGluing E] in
/-- The complete original paired map keeps both actual functor maps. -/
theorem originalPairMap {X Y : C} (f : X ⟶ Y) :
    (F.prod' G).map f = (F.map f, G.map f) := rfl

/-- The original zero-left pair uses the public core constant-zero and pairing facts. -/
theorem originalZeroLeftPair (C : Type uC) [Category.{vC} C]
    [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] :
    letI : WaldhausenCategoryWithoutGluing (C × C) := prodWaldhausen
    (((Functor.const C).obj (0 : C)).prod' (𝟭 C)).IsWaldhausenExact :=
  (Functor.IsWaldhausenExact.constantZero C C).prod'
    (Functor.IsWaldhausenExact.id (C := C))

/-- The original zero-right pair uses the same public core facts in the actual other order. -/
theorem originalZeroRightPair (C : Type uC) [Category.{vC} C]
    [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] :
    letI : WaldhausenCategoryWithoutGluing (C × C) := prodWaldhausen
    ((𝟭 C).prod' ((Functor.const C).obj (0 : C))).IsWaldhausenExact :=
  (Functor.IsWaldhausenExact.id (C := C)).prod'
    (Functor.IsWaldhausenExact.constantZero C C)

end MathlibExtTest.KTheory.Waldhausen.ProductExactFunctorTests

end
