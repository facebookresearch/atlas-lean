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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageSourceQuotient
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Exact-functor naturality for Stage source/quotient evaluation

For an additive exact functor `F : C ⥤ D` between exact categories over
independent universes, evaluating a degree-`2` stage after `mapStage` agrees
with mapping after evaluation: `mapStage F 2 ⋙ eval D 2 a ≅ eval C 2 a ⋙ F`,
and the paired source/quotient version `mapStage F 2 ⋙ sourceQuotientStage D ≅
sourceQuotientStage C ⋙ F.prod F` plus its weak restriction through
`stageWeakInclusion`. The single-evaluation iso is degree-generic over `n`;
the paired version and the degree-two wrapper below specialize it to `n = 2`.

Orientation: the mapped-then-evaluated composite is on the left, the
evaluated-then-mapped composite is on the right, matching
`CofiberEvaluationNaturality.sourceNaturalityIso` and
`CofiberSourceQuotientNaturality.sourceQuotientNaturalityIso`.

Reuse map: `mapStage`/`mapStageWeak` with `mapStageWeak_inclusion`,
pointwise `eval`, the new `sourceQuotientStage`/`sourceQuotientStageWeak` with
their `rfl` obj/`fst`/`snd` laws, `Functor.prod` for `F.prod F`,
`Iso.prod` of the two evaluation components, `NatIso.ofComponents`,
`Prod.hom_ext`, `eqToIso`, and `Category.comp_id`/`id_comp`. The cofiber
naturality files are pattern-only and are not imported. A single
degree-generic `(n) (a : Ar n)` evaluation iso is the smallest reusable
surface: at `n = 2` it covers both `(0, 1)` and `(1, 2)` intervals without
duplicating named instances, and reused at the underlying stage object it
gives the weak evaluation iso. The degree-two `stageEvalNaturalityIso` is a
thin compatibility wrapper over the `n = 2` case.

Explicit nonclaims: no retraction opposite, no deformation, no realization,
no weak equivalence, no additivity, no K₀, no spectra, and no Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]

local instance stageSourceQuotientNaturalityWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C
local instance stageSourceQuotientNaturalityWaldhausenD : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Evaluation naturality, degree-generic: evaluating after `mapStage` agrees
with postcomposition after evaluation. The proof uses only `mapStage_obj/map`
(`rfl`), pointwise `eval`, and functor-comp associativity, so it never uses
interval structure or any `n = 2` fact. Components are `eqToIso (by rfl)`;
both composites send `X` to `F.obj (X.obj.obj a)` and `φ` to
`F.map (((forget C n).map φ).app a)`. -/
noncomputable def stageEvalNaturalityIsoGeneral (n : ℕ) (a : Ar n) :
    mapStage C D F n ⋙ eval D n a ≅ eval C n a ⋙ F :=
  NatIso.ofComponents (fun X => eqToIso (by rfl)) (fun {X Y} φ => by
    change F.map (((forget C n).map φ).app a) ≫ 𝟙 _ =
      𝟙 _ ≫ F.map (((forget C n).map φ).app a)
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Degree-two compatibility wrapper over `stageEvalNaturalityIsoGeneral`:
existing call sites elaborate unchanged. -/
noncomputable def stageEvalNaturalityIso (a : Ar 2) :
    mapStage C D F 2 ⋙ eval D 2 a ≅ eval C 2 a ⋙ F :=
  stageEvalNaturalityIsoGeneral F 2 a

/-- Paired source/quotient naturality: mapping then pairing agrees with
pairing then mapping via `F.prod F`. -/
noncomputable def sourceQuotientStageNaturalityIso :
    mapStage C D F 2 ⋙ sourceQuotientStage D ≅
      sourceQuotientStage C ⋙ F.prod F :=
  NatIso.ofComponents
    (fun X => Iso.prod
      ((stageEvalNaturalityIsoGeneral F 2
        (interval (0 : Fin 3) 1 (by decide))).app X)
      ((stageEvalNaturalityIsoGeneral F 2
        (interval (1 : Fin 3) 2 (by decide))).app X)) (by
    intro X Y φ
    apply Prod.hom_ext
    · have hSrc := (stageEvalNaturalityIsoGeneral F 2
        (interval (0 : Fin 3) 1 (by decide))).hom.naturality φ
      exact hSrc
    · have hQuo := (stageEvalNaturalityIsoGeneral F 2
        (interval (1 : Fin 3) 2 (by decide))).hom.naturality φ
      exact hQuo)

/-- First projection recovers the `(0, 1)` evaluation naturality,
preventing factor swapping. -/
@[simp]
theorem sourceQuotientStageNaturalityIso_hom_fst (X : Stage C 2) :
    ((sourceQuotientStageNaturalityIso F).hom.app X).1 =
      (stageEvalNaturalityIso F (interval (0 : Fin 3) 1 (by decide))).hom.app X :=
  rfl

/-- Second projection recovers the `(1, 2)` evaluation naturality,
preventing factor swapping. -/
@[simp]
theorem sourceQuotientStageNaturalityIso_hom_snd (X : Stage C 2) :
    ((sourceQuotientStageNaturalityIso F).hom.app X).2 =
      (stageEvalNaturalityIso F (interval (1 : Fin 3) 2 (by decide))).hom.app X :=
  rfl

/-- Weak evaluation naturality, degree-generic: evaluating through the weak
inclusion after `mapStageWeak` agrees with mapping after evaluation through
the inclusion. Components reuse the general Stage iso at the underlying stage
object; maps agree by `mapStageWeak_inclusion` (`rfl`) with strict functor
associativity. Orientation matches `stageEvalNaturalityIsoGeneral`:
mapped-then-evaluated on the left, evaluated-then-mapped on the right. -/
noncomputable def stageWeakEvalNaturalityIso (n : ℕ) (a : Ar n) :
    mapStageWeak C D F n ⋙ stageWeakInclusion D n ⋙ eval D n a ≅
      stageWeakInclusion C n ⋙ eval C n a ⋙ F :=
  NatIso.ofComponents
    (fun X => (stageEvalNaturalityIsoGeneral F n a).app
      ((stageWeakInclusion C n).obj X)) (by
    intro X Y φ
    have h := (stageEvalNaturalityIsoGeneral F n a).hom.naturality
      ((stageWeakInclusion C n).map φ)
    exact h)

/-- Weak restriction: mapping then pairing through the weak inclusion agrees
with pairing then mapping. Components reuse the Stage iso at the underlying
stage object; maps agree by `mapStageWeak_inclusion` (`rfl`) and the
`sourceQuotientStageWeak` `rfl` obj/map laws with strict functor
associativity. No new category theory. -/
noncomputable def sourceQuotientStageWeakNaturalityIso :
    mapStageWeak C D F 2 ⋙ sourceQuotientStageWeak D ≅
      sourceQuotientStageWeak C ⋙ F.prod F :=
  NatIso.ofComponents
    (fun X => (sourceQuotientStageNaturalityIso F).app
      ((stageWeakInclusion C 2).obj X)) (by
    intro X Y φ
    have h := (sourceQuotientStageNaturalityIso F).hom.naturality
      ((stageWeakInclusion C 2).map φ)
    exact h)

/-- Weak first projection recovers the `(0, 1)` evaluation naturality. -/
@[simp]
theorem sourceQuotientStageWeakNaturalityIso_hom_fst
    (X : StageWeakCategory C 2) :
    ((sourceQuotientStageWeakNaturalityIso F).hom.app X).1 =
      (stageEvalNaturalityIso F
        (interval (0 : Fin 3) 1 (by decide))).hom.app
        ((stageWeakInclusion C 2).obj X) :=
  rfl

/-- Weak second projection recovers the `(1, 2)` evaluation naturality. -/
@[simp]
theorem sourceQuotientStageWeakNaturalityIso_hom_snd
    (X : StageWeakCategory C 2) :
    ((sourceQuotientStageWeakNaturalityIso F).hom.app X).2 =
      (stageEvalNaturalityIso F
        (interval (1 : Fin 3) 2 (by decide))).hom.app
        ((stageWeakInclusion C 2).obj X) :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
