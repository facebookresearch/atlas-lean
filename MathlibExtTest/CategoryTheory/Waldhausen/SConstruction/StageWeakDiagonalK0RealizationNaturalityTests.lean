/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0RealizationNaturality

/-!
# Realized weak-diagonal K-zero naturality tests

These tests pin the based topological fundamental map, connector orientation,
realization/fundamental compatibility, and the final elementwise naturality
square.  Object generators, arbitrary classes, identity and composite exact
functors, and universe-zero and universe-one clients are covered.

Negative guards record the honest same-universe, set-level scope: this module
does not supply a mixed-universe stage map, a continuous loop-space map, a
strict raw-map equality, an additive equivalence, or a natural isomorphism.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0RealizationNaturalityTests

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D

/-- The realized map and mapped-zero connector induce the expected based
topological fundamental-group map. -/
example :
    FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) →*
      FundamentalGroup (stageWeakDiagonalReal D)
        (stageWeakDiagonalReal.basepoint D) :=
  stageWeakDiagonalTopologicalFundamentalMap C D F

/-- The root-path conjugation order is inverse connector, mapped loop,
connector. -/
example (gamma : stageWeakDiagonalKSpace C) :
    stageWeakDiagonalTopologicalFundamentalMap C D F
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).symm.trans
          ((gamma.map (stageWeakDiagonalReal.map C D F).hom.continuous).trans
            (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)))) := by
  change basedFundamentalGroupMap
      (stageWeakDiagonalReal.map C D F).hom
      (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) = _
  exact basedFundamentalGroupMap_mk
    (stageWeakDiagonalReal.map C D F).hom
    (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F) gamma

/-- Direct realization intertwines the combinatorial and topological based
fundamental-group maps. -/
example (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalRealizationFundamentalMulEquiv D
        (stageWeakDiagonalFundamentalMap C D F g) =
      stageWeakDiagonalTopologicalFundamentalMap C D F
        (stageWeakDiagonalRealizationFundamentalMulEquiv C g) :=
  stageWeakDiagonalRealizationFundamentalMulEquiv_naturality C D F g

/-- The final naturality theorem applies to every loop-space component. -/
example (q : ZerothHomotopy (stageWeakDiagonalKSpace C)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 D
        (stageWeakDiagonalKSpacePiZeroMap C D F q) =
      WaldhausenKTheory.K0.map F
        (stageWeakDiagonalKSpacePiZeroEquivK0 C q) :=
  stageWeakDiagonalKSpacePiZeroEquivK0_naturality C D F q

set_option backward.isDefEq.respectTransparency false in
/-- The component of an object loop maps to the K-zero class of the mapped
object. -/
example (X : C) :
    stageWeakDiagonalKSpacePiZeroEquivK0 D
        (stageWeakDiagonalKSpacePiZeroMap C D F
          (ZerothHomotopy.mk (stageWeakDiagonalObjectLoop C X))) =
      WaldhausenKTheory.K0.mk (F.obj X) := by
  rw [stageWeakDiagonalKSpacePiZeroEquivK0_naturality,
    stageWeakDiagonalKSpacePiZeroEquivK0_objectLoop,
    WaldhausenKTheory.K0.map_mk]

/-- Identity naturality is equality only after passing through the component
comparison and `K0.map_id`. -/
example (q : ZerothHomotopy (stageWeakDiagonalKSpace C)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 C
        (stageWeakDiagonalKSpacePiZeroMap C C (Functor.id C) q) =
      stageWeakDiagonalKSpacePiZeroEquivK0 C q := by
  rw [stageWeakDiagonalKSpacePiZeroEquivK0_naturality,
    WaldhausenKTheory.K0.map_id]
  rfl

variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance : WaldhausenCategory E := ExactCategory.waldhausenCategory E

/-- Composite orientation is `G` after `F`, as in `K0.map_comp`. -/
example (q : ZerothHomotopy (stageWeakDiagonalKSpace C)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 E
        (stageWeakDiagonalKSpacePiZeroMap C E (F ⋙ G) q) =
      WaldhausenKTheory.K0.map G
        (WaldhausenKTheory.K0.map F
          (stageWeakDiagonalKSpacePiZeroEquivK0 C q)) := by
  rw [stageWeakDiagonalKSpacePiZeroEquivK0_naturality,
    WaldhausenKTheory.K0.map_comp]
  rfl

section TypeZero

variable (C0 D0 : Type) [Category.{0} C0] [Category.{0} D0]
  [Preadditive C0] [Preadditive D0]
  [Limits.HasZeroObject C0] [Limits.HasZeroObject D0]
  [HasBinaryBiproducts C0] [HasBinaryBiproducts D0]
  [ExactCategory C0] [ExactCategory D0]
variable (F0 : C0 ⥤ D0) [F0.Additive] [Functor.IsExact F0]

local instance : WaldhausenCategory C0 := ExactCategory.waldhausenCategory C0
local instance : WaldhausenCategory D0 := ExactCategory.waldhausenCategory D0

/-- The final square elaborates for small exact categories. -/
example (q : ZerothHomotopy (stageWeakDiagonalKSpace C0)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 D0
        (stageWeakDiagonalKSpacePiZeroMap C0 D0 F0 q) =
      WaldhausenKTheory.K0.map F0
        (stageWeakDiagonalKSpacePiZeroEquivK0 C0 q) :=
  stageWeakDiagonalKSpacePiZeroEquivK0_naturality C0 D0 F0 q

end TypeZero

section TypeOne

variable (C1 D1 : Type 1) [Category.{1} C1] [Category.{1} D1]
  [Preadditive C1] [Preadditive D1]
  [Limits.HasZeroObject C1] [Limits.HasZeroObject D1]
  [HasBinaryBiproducts C1] [HasBinaryBiproducts D1]
  [ExactCategory C1] [ExactCategory D1]
variable (F1 : C1 ⥤ D1) [F1.Additive] [Functor.IsExact F1]

local instance : WaldhausenCategory C1 := ExactCategory.waldhausenCategory C1
local instance : WaldhausenCategory D1 := ExactCategory.waldhausenCategory D1

/-- The same square elaborates one universe higher without `ULift`. -/
example (q : ZerothHomotopy (stageWeakDiagonalKSpace C1)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 D1
        (stageWeakDiagonalKSpacePiZeroMap C1 D1 F1 q) =
      WaldhausenKTheory.K0.map F1
        (stageWeakDiagonalKSpacePiZeroEquivK0 C1 q) :=
  stageWeakDiagonalKSpacePiZeroEquivK0_naturality C1 D1 F1 q

end TypeOne

section MixedUniverseNegative

universe u₁ u₂ v₁ v₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [Preadditive C₁]
  [Limits.HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]
variable (D₂ : Type u₂) [Category.{v₂} D₂] [Preadditive D₂]
  [Limits.HasZeroObject D₂] [HasBinaryBiproducts D₂] [ExactCategory D₂]
variable (F₁₂ : C₁ ⥤ D₂) [F₁₂.Additive] [Functor.IsExact F₁₂]

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalTopologicalFundamentalMap C₁ D₂ F₁₂

end MixedUniverseNegative

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceContinuousMap_naturality

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceMap_naturality_strict

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpacePiZeroAddEquivK0_naturality

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpacePiZeroEquivK0NatIso

#print axioms stageWeakDiagonalTopologicalFundamentalMap
#print axioms stageWeakDiagonalRealizationFundamentalMulEquiv_naturality
#print axioms stageWeakDiagonalKSpacePiZeroEquivK0_naturality

end StageWeakDiagonalK0RealizationNaturalityTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
