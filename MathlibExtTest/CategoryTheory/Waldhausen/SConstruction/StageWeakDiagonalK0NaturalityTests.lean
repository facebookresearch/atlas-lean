/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Naturality

/-!
# Combinatorial weak-diagonal K-zero naturality tests

These tests pin the explicit mapped-zero connector, conjugated object-edge
formula, arbitrary-element decode naturality, and identity/composition
orientations against `WaldhausenKTheory.K0.map`.  Type-zero and type-one
clients exercise the honest same-universe boundary.

Negative guards record that this API does not make the connector an identity,
bundle a continuous map, strengthen the generator formula to an unbased
strict formula, or construct a natural isomorphism.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0NaturalityTests

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- The connector runs from the image of the source zero vertex to the
selected target zero vertex. -/
example :
    SSet.FundamentalGroupoid.mk
        ((stageWeakDiagonalMap C D F).app (op ⦋0⦌)
          (stageWeakDiagonalZeroVertex C)) ≅
      SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex D) :=
  stageWeakDiagonalFundamentalBasepointIso C D F

/-- The induced based map has the expected multiplicative source and target. -/
example : stageWeakDiagonalFundamentalGroup C →*
    stageWeakDiagonalFundamentalGroup D :=
  stageWeakDiagonalFundamentalMap C D F

/-- An object generator maps by literal conjugation with the connector. -/
example (X : C) :
    stageWeakDiagonalFundamentalMap C D F
        (stageWeakDiagonalObjectGenerator C X) =
      End.of ((stageWeakDiagonalFundamentalBasepointIso C D F).inv ≫
        SSet.FundamentalGroupoid.homMk
          ((stageWeakDiagonalObjectEdge C X).map
            (stageWeakDiagonalMap C D F)) ≫
        (stageWeakDiagonalFundamentalBasepointIso C D F).hom) :=
  stageWeakDiagonalFundamentalMap_objectGenerator C D F X

/-- After decode, a mapped object generator is the class of `F.obj X`. -/
example (X : C) :
    stageWeakDiagonalFundamentalK0MulEquiv D
        (stageWeakDiagonalFundamentalMap C D F
          (stageWeakDiagonalObjectGenerator C X)) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk (F.obj X)) := by
  rw [stageWeakDiagonalFundamentalK0MulEquiv_naturality,
    stageWeakDiagonalFundamentalK0MulEquiv_objectGenerator]
  change Multiplicative.ofAdd
      (WaldhausenKTheory.K0.map F (WaldhausenKTheory.K0.mk X)) = _
  rw [WaldhausenKTheory.K0.map_mk]

/-- The public naturality law applies to an arbitrary fundamental element. -/
example (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalToK0 D
        (stageWeakDiagonalFundamentalMap C D F g) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.map F
        (Multiplicative.toAdd
          (stageWeakDiagonalFundamentalToK0 C g))) :=
  stageWeakDiagonalFundamentalToK0_naturality C D F g

/-- The identity-functor specialization agrees with `K0.map_id` after
decode; it does not assert equality of unbased fundamental-groupoid maps. -/
example (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalK0MulEquiv C
        (stageWeakDiagonalFundamentalMap C C (Functor.id C) g) =
      stageWeakDiagonalFundamentalK0MulEquiv C g := by
  rw [stageWeakDiagonalFundamentalK0MulEquiv_naturality]
  change Multiplicative.ofAdd
      (WaldhausenKTheory.K0.map (Functor.id C)
        (Multiplicative.toAdd
          (stageWeakDiagonalFundamentalK0MulEquiv C g))) = _
  rw [WaldhausenKTheory.K0.map_id]
  rfl

variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E

/-- Composite orientation is `G` after `F`, exactly as in `K0.map_comp`. -/
example (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalK0MulEquiv E
        (stageWeakDiagonalFundamentalMap C E (F ⋙ G) g) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.map G
        (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd
            (stageWeakDiagonalFundamentalK0MulEquiv C g)))) := by
  rw [stageWeakDiagonalFundamentalK0MulEquiv_naturality]
  change Multiplicative.ofAdd
      (WaldhausenKTheory.K0.map (F ⋙ G)
        (Multiplicative.toAdd
          (stageWeakDiagonalFundamentalK0MulEquiv C g))) = _
  rw [WaldhausenKTheory.K0.map_comp]
  rfl

/-- No continuous map is bundled on the combinatorial fundamental groups. -/
example : True := by
  fail_if_success
    exact (stageWeakDiagonalFundamentalMap C D F :
      ContinuousMap (stageWeakDiagonalFundamentalGroup C)
        (stageWeakDiagonalFundamentalGroup D))
  trivial

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalFundamentalMap_objectGenerator_strict

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalFundamentalBasepointIso_eq_refl

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalFundamentalMapNatIso

section TypeZero

variable (C0 D0 : Type) [Category.{0} C0] [Category.{0} D0]
  [Preadditive C0] [Preadditive D0]
  [Limits.HasZeroObject C0] [Limits.HasZeroObject D0]
  [HasBinaryBiproducts C0] [HasBinaryBiproducts D0]
  [ExactCategory C0] [ExactCategory D0]
variable (F0 : C0 ⥤ D0) [F0.Additive] [Functor.IsExact F0]

/-- The based map elaborates for small exact categories. -/
example :
    (letI : WaldhausenCategoryWithoutGluing C0 := ExactCategory.waldhausenCategory C0;
      letI : WaldhausenCategoryWithoutGluing D0 := ExactCategory.waldhausenCategory D0;
      stageWeakDiagonalFundamentalGroup C0 →*
        stageWeakDiagonalFundamentalGroup D0) :=
  stageWeakDiagonalFundamentalMap C0 D0 F0

end TypeZero

section TypeOne

variable (C1 D1 : Type 1) [Category.{1} C1] [Category.{1} D1]
  [Preadditive C1] [Preadditive D1]
  [Limits.HasZeroObject C1] [Limits.HasZeroObject D1]
  [HasBinaryBiproducts C1] [HasBinaryBiproducts D1]
  [ExactCategory C1] [ExactCategory D1]
variable (F1 : C1 ⥤ D1) [F1.Additive] [Functor.IsExact F1]

/-- The same API elaborates one universe higher without `ULift`. -/
example :
    (letI : WaldhausenCategoryWithoutGluing C1 := ExactCategory.waldhausenCategory C1;
      letI : WaldhausenCategoryWithoutGluing D1 := ExactCategory.waldhausenCategory D1;
      stageWeakDiagonalFundamentalGroup C1 →*
        stageWeakDiagonalFundamentalGroup D1) :=
  stageWeakDiagonalFundamentalMap C1 D1 F1

end TypeOne

end StageWeakDiagonalK0NaturalityTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
