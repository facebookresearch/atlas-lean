/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_CarrierPins.lean`,
`Definitions/Def_AutomorphicForm_ProductionPins.lean`
and
`Definitions/Def_AutomorphicForm_ProductionPinsCompact.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.CarrierPins
public import MathlibExt.NumberTheory.NumberField.AdelicLevel

@[expose] public section

noncomputable section

/-!
# Production pins for automorphic forms, and the compact level

`productionPins F D` are the carrier pins `productionPinsOf` with fundamental set `D`, level
`levelOne (𝓞 F) F N` at every ideal `N`, the Hecke generator `heckeGen (𝓞 F) F v` at every
height-one prime `v`, and the adelic box `adelicBox F` as the conditioning set: the measure on
adelic `GL₂` is the Haar measure, and the measure on the adele ring is the additive Haar measure
conditioned on the adelic box, a probability measure. The compact production pins
`productionPinsCompact F D` intersect every level with `finiteAdelicGL2Subgroup F`, the matrices
whose infinite part is the identity: an adelic matrix `u` lies in the compact level at `N`
exactly when its finite part lies in `finiteLevelOne (𝓞 F) F N` and its infinite part is `1`.

The source fixes the fundamental set to the centre-cut Siegel set
`centreCutSiegelSet F (1/2) 1 (1/2) 2`, which this library does not provide yet. Both
constructions therefore take the fundamental set `D` as an explicit parameter, and the source's
facts about that set (it is measurable, with positive finite Haar measure) are not stated here.
-/

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

namespace AutomorphicForm

variable (F : Type*) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))

/-- The production pins with fundamental set `D`: level `levelOne (𝓞 F) F N` at every ideal
`N`, the Hecke generators `heckeGen (𝓞 F) F v`, the Haar measure on adelic `GL₂`, and the
additive Haar measure on the adele ring conditioned on `adelicBox F`. The source takes for `D`
the centre-cut Siegel set `centreCutSiegelSet F (1/2) 1 (1/2) 2`. -/
def productionPins : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

@[simp] theorem productionPins_mS : (productionPins F D).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_μ : (productionPins F D).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_D : (productionPins F D).D = D := rfl

@[simp] theorem productionPins_Z :
    (productionPins F D).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPins_U (N : Ideal (𝓞 F)) :
    (productionPins F D).U N = levelOne (𝓞 F) F N := rfl

@[simp] theorem productionPins_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPins F D).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPins_nS : (productionPins F D).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPins_ν :
    (productionPins F D).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem isHaarMeasure_productionPins_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPins F D).mS (productionPins F D).μ :=
  isHaarMeasure_productionPinsOf_μ F _ _ _ _

theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPins F D).nS (productionPins F D).ν :=
  isProbabilityMeasure_productionPinsOf_ν F _ _ _ _
    (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne

/-- The compact production pins with fundamental set `D`: the production pins with the level at
every ideal `N` intersected with `finiteAdelicGL2Subgroup F`, the adelic matrices whose infinite
part is the identity. -/
def productionPinsCompact : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

@[simp] theorem productionPinsCompact_mS :
    (productionPinsCompact F D).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_μ :
    (productionPinsCompact F D).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_D : (productionPinsCompact F D).D = D := rfl

@[simp] theorem productionPinsCompact_Z :
    (productionPinsCompact F D).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPinsCompact_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F D).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

@[simp] theorem productionPinsCompact_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPinsCompact F D).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPinsCompact_nS :
    (productionPinsCompact F D).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_ν :
    (productionPinsCompact F D).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem productionPinsCompact_μ_eq_productionPins_μ :
    (productionPinsCompact F D).μ = (productionPins F D).μ := rfl

theorem productionPinsCompact_D_eq_productionPins_D :
    (productionPinsCompact F D).D = (productionPins F D).D := rfl

theorem productionPinsCompact_ν_eq_productionPins_ν :
    (productionPinsCompact F D).ν = (productionPins F D).ν := rfl

theorem mem_productionPinsCompact_U_iff (N : Ideal (𝓞 F)) (u : AdelicGL2 (𝓞 F) F) :
    u ∈ (productionPinsCompact F D).U N ↔
      glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N ∧ glArch (𝓞 F) F u = 1 := by
  rw [productionPinsCompact_U, Subgroup.mem_inf, mem_levelOne_iff,
    mem_finiteAdelicGL2Subgroup_iff]

theorem glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F D).U N) :
    glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N :=
  ((mem_productionPinsCompact_U_iff F D N u).mp hu).1

theorem glArch_eq_one_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F D).U N) :
    glArch (𝓞 F) F u = 1 :=
  ((mem_productionPinsCompact_U_iff F D N u).mp hu).2

theorem productionPinsCompact_U_eq_productionPins_U_inf (N : Ideal (𝓞 F)) :
    (productionPinsCompact F D).U N = (productionPins F D).U N ⊓ finiteAdelicGL2Subgroup F :=
  rfl

theorem productionPinsCompact_U_le_productionPins_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F D).U N ≤ (productionPins F D).U N :=
  inf_le_left

theorem isHaarMeasure_productionPinsCompact_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPinsCompact F D).mS (productionPinsCompact F D).μ :=
  isHaarMeasure_productionPins_μ F D

theorem isProbabilityMeasure_productionPinsCompact_ν :
    @IsProbabilityMeasure _ (productionPinsCompact F D).nS (productionPinsCompact F D).ν :=
  isProbabilityMeasure_productionPins_ν F D

end AutomorphicForm

end
