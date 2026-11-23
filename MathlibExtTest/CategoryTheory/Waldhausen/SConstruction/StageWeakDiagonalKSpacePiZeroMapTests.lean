/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpacePiZeroMap

/-!
# Weak-diagonal K-space component-map tests

These tests pin the representative formula, identity, and `G`-after-`F`
composition orientation for the exact-functor map on path components.  They
also check universe inference and the intended set-level scope.  The raw
K-space maps remain homotopy-functorial rather than strictly functorial.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalKSpacePiZeroMapTests

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D
local instance : WaldhausenCategory E := ExactCategory.waldhausenCategory E

/-- The component map has the expected source and target sets. -/
example : ZerothHomotopy (stageWeakDiagonalKSpace C) →
    ZerothHomotopy (stageWeakDiagonalKSpace D) :=
  stageWeakDiagonalKSpacePiZeroMap C D F

/-- The public representative formula is exactly the landed raw map. -/
example (gamma : stageWeakDiagonalKSpace C) :
    stageWeakDiagonalKSpacePiZeroMap C D F (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk (stageWeakDiagonalKSpaceMap C D F gamma) :=
  stageWeakDiagonalKSpacePiZeroMap_mk C D F gamma

/-- Identity is strict only after passing to path components. -/
example : stageWeakDiagonalKSpacePiZeroMap C C (Functor.id C) = id :=
  stageWeakDiagonalKSpacePiZeroMap_id C

/-- Composition is direct `F ⋙ G` on the left and iterated `G` after `F`
on the right. -/
example : stageWeakDiagonalKSpacePiZeroMap C E (F ⋙ G) =
    stageWeakDiagonalKSpacePiZeroMap D E G ∘
      stageWeakDiagonalKSpacePiZeroMap C D F :=
  stageWeakDiagonalKSpacePiZeroMap_comp C D F E G

/-- The component construction does not bundle an unproved continuous map. -/
example : True := by
  fail_if_success
    exact (stageWeakDiagonalKSpacePiZeroMap C D F :
      ContinuousMap (ZerothHomotopy (stageWeakDiagonalKSpace C))
        (ZerothHomotopy (stageWeakDiagonalKSpace D)))
  trivial

/-- The component construction does not install a global group instance. -/
example : True := by
  fail_if_success
    exact inferInstanceAs (Group (ZerothHomotopy (stageWeakDiagonalKSpace C)))
  trivial

section TypeZero

variable (C0 D0 : Type) [Category.{0} C0] [Category.{0} D0]
  [Preadditive C0] [Preadditive D0]
  [Limits.HasZeroObject C0] [Limits.HasZeroObject D0]
  [HasBinaryBiproducts C0] [HasBinaryBiproducts D0]
  [ExactCategory C0] [ExactCategory D0]
variable (F0 : C0 ⥤ D0) [F0.Additive] [Functor.IsExact F0]

/-- The stage specialization elaborates for small exact categories. -/
example :
    (letI : WaldhausenCategory C0 := ExactCategory.waldhausenCategory C0;
      letI : WaldhausenCategory D0 := ExactCategory.waldhausenCategory D0;
      ZerothHomotopy (stageWeakDiagonalKSpace C0) →
        ZerothHomotopy (stageWeakDiagonalKSpace D0)) :=
  stageWeakDiagonalKSpacePiZeroMap C0 D0 F0

end TypeZero

section TypeOne

variable (C1 D1 : Type 1) [Category.{1} C1] [Category.{1} D1]
  [Preadditive C1] [Preadditive D1]
  [Limits.HasZeroObject C1] [Limits.HasZeroObject D1]
  [HasBinaryBiproducts C1] [HasBinaryBiproducts D1]
  [ExactCategory C1] [ExactCategory D1]
variable (F1 : C1 ⥤ D1) [F1.Additive] [Functor.IsExact F1]

/-- The same stage API elaborates one universe higher without `ULift`. -/
example :
    (letI : WaldhausenCategory C1 := ExactCategory.waldhausenCategory C1;
      letI : WaldhausenCategory D1 := ExactCategory.waldhausenCategory D1;
      ZerothHomotopy (stageWeakDiagonalKSpace C1) →
        ZerothHomotopy (stageWeakDiagonalKSpace D1)) :=
  stageWeakDiagonalKSpacePiZeroMap C1 D1 F1

end TypeOne

end StageWeakDiagonalKSpacePiZeroMapTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
