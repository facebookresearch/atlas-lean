/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageProductEquivalence

/-!
# Finite-stage product equivalence consumer tests

Focused downstream checks for the public `stageProductEquivalence` API: its
forward direction is `stageProject`, its inverse is `stagePair`, plus the
unit component at an `Ar n` object and both product projections of the
counit component. All primary checks are cross-universe in independent
`v₁/u₁` and `v₂/u₂` universes. Uses the explicitly scoped product structure
`prodWaldhausen`; proves no weak-stage comparison, simplicial, realization,
additivity, K/G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageProductEquivalenceTests

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] (n : ℕ)

local instance prodWaldhausenIndependent
    {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroObject D] [WaldhausenCategoryWithoutGluing D] :
    WaldhausenCategoryWithoutGluing (C × D) := prodWaldhausen

/-- Forward direction of the equivalence is `stageProject`. -/
example : (stageProductEquivalence C D n).functor = stageProject C D n :=
  stageProductEquivalence_functor C D n

/-- Inverse direction of the equivalence is `stagePair`. -/
example : (stageProductEquivalence C D n).inverse = stagePair C D n :=
  stageProductEquivalence_inverse C D n

/-- Unit first projection acts as the identity at each `Ar n` object. -/
example (X : Stage (C × D) n) (a : Ar n) :
    ((((stageProductEquivalence C D n).unitIso.hom.app X).hom.app a).1) =
      𝟙 (X.obj.obj a).1 := by
  have tri := (stageProductEquivalence C D n).functor_unitIso_comp X
  have c1 : ((((stageProductEquivalence C D n).unitIso.hom.app X).hom.app a).1) ≫
      𝟙 (X.obj.obj a).1 = 𝟙 (X.obj.obj a).1 :=
    congrArg (fun m => ((m.1).hom.app a)) tri
  exact (Category.comp_id _).symm.trans c1

/-- Unit second projection acts as the identity at each `Ar n` object. -/
example (X : Stage (C × D) n) (a : Ar n) :
    ((((stageProductEquivalence C D n).unitIso.hom.app X).hom.app a).2) =
      𝟙 (X.obj.obj a).2 := by
  have tri := (stageProductEquivalence C D n).functor_unitIso_comp X
  have c1 : ((((stageProductEquivalence C D n).unitIso.hom.app X).hom.app a).2) ≫
      𝟙 (X.obj.obj a).2 = 𝟙 (X.obj.obj a).2 :=
    congrArg (fun m => ((m.2).hom.app a)) tri
  exact (Category.comp_id _).symm.trans c1

/-- Counit first projection acts as the identity at each `Ar n` object. -/
example (p : Stage C n × Stage D n) (a : Ar n) :
    ((((stageProductEquivalence C D n).counitIso.hom.app p).1).hom.app a) =
      𝟙 (p.1.obj.obj a) :=
  rfl

/-- Counit second projection acts as the identity at each `Ar n` object. -/
example (p : Stage C n × Stage D n) (a : Ar n) :
    ((((stageProductEquivalence C D n).counitIso.hom.app p).2).hom.app a) =
      𝟙 (p.2.obj.obj a) :=
  rfl

/-- Counit naturality at independent universes; folds in cross-universe inference. -/
example (C : Type u₁) [Category.{v₁} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    (D : Type u₂) [Category.{v₂} D] [Limits.HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (n : ℕ) (p q : Stage C n × Stage D n) (f : p ⟶ q) :
    (stagePair C D n ⋙ stageProject C D n).map f ≫
        (stageProductCounitApp C D n q).hom =
      (stageProductCounitApp C D n p).hom ≫ (𝟭 (Stage C n × Stage D n)).map f :=
  stageProductCounit_naturality C D n f

/-- Unit naturality at independent universes; folds in cross-universe inference. -/
example (C : Type u₁) [Category.{v₁} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    (D : Type u₂) [Category.{v₂} D] [Limits.HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (n : ℕ) (X Y : Stage (C × D) n) (f : X ⟶ Y) :
    (𝟭 (Stage (C × D) n)).map f ≫ (stageProductUnitApp C D n Y).hom =
      (stageProductUnitApp C D n X).hom ≫ (stageProject C D n ⋙ stagePair C D n).map f :=
  stageProductUnit_naturality C D n f

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageProductEquivalenceTests
