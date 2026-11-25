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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageSourceQuotientNaturality

/-!
# Consumer checks for Stage source/quotient naturality

Focused public-API checks for `stageEvalNaturalityIso`,
`stageEvalNaturalityIsoGeneral`, `stageWeakEvalNaturalityIso`,
`sourceQuotientStageNaturalityIso`, and `sourceQuotientStageWeakNaturalityIso`
along a generic exact functor `F : C ⥤ D` over independent universes (so no
identity-functor-only coverage). Arbitrary-degree `n` evaluation and
weak-evaluation naturality are covered by type over `a : Ar n`.

Orientation: map-then-evaluate on the left, evaluate-then-map on the right.
Paired projections read back as `(0, 1)` source and `(1, 2)` quotient
evaluation naturality, so a first/second swap fails. The weak restriction is
covered by type plus first/second projections through `stageWeakInclusion`.

Nonclaims: no retraction, opposite, deformation, realization,
weak equivalence, additivity, K₀, spectrum, or Q/S comparison.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageSourceQuotientNaturalityTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

-- Generic evaluation naturality type; fails if the orientation flips.
noncomputable example (a : Ar 2) :
    mapStage C D F 2 ⋙ eval D 2 a ≅ eval C 2 a ⋙ F :=
  stageEvalNaturalityIso F a

-- Arbitrary-degree evaluation naturality type; fails if the orientation flips.
noncomputable example (n : ℕ) (a : Ar n) :
    mapStage C D F n ⋙ eval D n a ≅ eval C n a ⋙ F :=
  stageEvalNaturalityIsoGeneral F n a

-- Arbitrary-degree weak-evaluation naturality type through the inclusion.
noncomputable example (n : ℕ) (a : Ar n) :
    mapStageWeak C D F n ⋙ stageWeakInclusion D n ⋙ eval D n a ≅
      stageWeakInclusion C n ⋙ eval C n a ⋙ F :=
  stageWeakEvalNaturalityIso F n a

-- Paired projections; fails on a first/second swap.
example (X : Stage C 2) :
    ((sourceQuotientStageNaturalityIso F).hom.app X).1 =
      (stageEvalNaturalityIso F (interval (0 : Fin 3) 1 (by decide))).hom.app X ∧
    ((sourceQuotientStageNaturalityIso F).hom.app X).2 =
      (stageEvalNaturalityIso F (interval (1 : Fin 3) 2 (by decide))).hom.app X :=
  ⟨sourceQuotientStageNaturalityIso_hom_fst F X,
    sourceQuotientStageNaturalityIso_hom_snd F X⟩

-- Weak restriction type over independent universes.
noncomputable example :
    mapStageWeak C D F 2 ⋙ sourceQuotientStageWeak D ≅
      sourceQuotientStageWeak C ⋙ F.prod F :=
  sourceQuotientStageWeakNaturalityIso F

-- Weak projections through the inclusion; fails on a first/second swap and
-- locks the independent-universe instantiation.
example (X : StageWeakCategory C 2) :
    ((sourceQuotientStageWeakNaturalityIso F).hom.app X).1 =
      (stageEvalNaturalityIso F
        (interval (0 : Fin 3) 1 (by decide))).hom.app
        ((stageWeakInclusion C 2).obj X) ∧
    ((sourceQuotientStageWeakNaturalityIso F).hom.app X).2 =
      (stageEvalNaturalityIso F
        (interval (1 : Fin 3) 2 (by decide))).hom.app
        ((stageWeakInclusion C 2).obj X) :=
  ⟨sourceQuotientStageWeakNaturalityIso_hom_fst F X,
    sourceQuotientStageWeakNaturalityIso_hom_snd F X⟩

end StageSourceQuotientNaturalityTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
