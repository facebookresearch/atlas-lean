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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluationNaturality

/-!
# Consumer checks for evaluation and stage-two naturality

Focused public-API checks for `sourceNaturalityIso`, `quotientNaturalityIso`,
and `stageTwoNaturalityIso` along a generic exact functor `F : C ⥤ D` over
independent universes (so no identity-functor-only coverage).

Orientation: the lifted-then-evaluated composite is on the left and the
evaluated-then-mapped composite is on the right, as documented in the source
module. Per the source module, the Stage-2 underlying comparison is the
identity on off-diagonal objects and zero transport on diagonals. This file
only locks the orientations, the source/quotient identity computations, and
the off-diagonal/diagonal use-sites via public APIs; it unfolds no
implementation helpers and duplicates no proof.

Nonclaims: no paired sourceQuotient/splitSection naturality, nerve/realization,
additivity, K-space, or `π₀`.
-/

open CategoryTheory Limits ZeroObject
open CategoryTheory.Waldhausen.SConstruction

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluationNaturalityTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Orientation: source naturality runs lifted-then-source on the left. -/
noncomputable example :
    cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.source D ≅
      CofiberSequenceCategory.source C ⋙ F :=
  sourceNaturalityIso F

/-- Orientation: quotient naturality runs lifted-then-quotient on the left. -/
noncomputable example :
    cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.quotient D ≅
      CofiberSequenceCategory.quotient C ⋙ F :=
  quotientNaturalityIso F

/-- Orientation: stage-two naturality runs lifted-then-stage on the left. -/
noncomputable example :
    cofiberSequenceFunctor F ⋙ stageTwoFunctor D ≅
      stageTwoFunctor C ⋙ mapStage C D F 2 :=
  stageTwoNaturalityIso F

-- Source and quotient components compute as identities; fails on a swap.
example (S : CofiberSequenceCategory C) :
    (sourceNaturalityIso F).hom.app S = 𝟙 _ ∧
      (quotientNaturalityIso F).hom.app S = 𝟙 _ :=
  ⟨sourceNaturalityIso_hom_app F S, quotientNaturalityIso_hom_app F S⟩

/-- Off-diagonal Stage-2 underlying comparison at the `(0, 1)` interval.

Locks the off-diagonal use-site; the source module builds the identity
comparison there, distinct from diagonal zero transport. -/
noncomputable example (S : CofiberSequenceCategory C) :
    (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj
      (interval (0 : Fin 3) 1 (by decide))) ≅
      (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj
        (interval (0 : Fin 3) 1 (by decide))) :=
  stageTwoNaturalityUnderlyingAppIso F S _

/-- Diagonal Stage-2 underlying comparison at `diag 0`.

Locks the diagonal use-site; the source module uses zero transport there,
distinct from the off-diagonal identity comparison. -/
noncomputable example (S : CofiberSequenceCategory C) :
    (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj
      (diag (0 : Fin 3))) ≅
      (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj
        (diag (0 : Fin 3))) :=
  stageTwoNaturalityUnderlyingAppIso F S _

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluationNaturalityTests
