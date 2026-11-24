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

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import MathlibExt.NumberTheory.NumberField.AdelicGL2LocalFiniteness

@[expose] public section

noncomputable section

/-!
# Carrier pins for automorphic forms, and the compact level

Carrier pins bundle the measure-theoretic and level data used on the
adelic group: a measure and a fundamental set on `GL₂` over the adeles,
a centre subgroup, a level subgroup at every ideal, a chosen local
generator at every height-one prime, and a measure on the adele ring.
The production pins take the centre to be the whole unit group.  The
compact production pins intersect every level subgroup with a fixed
finite-adelic subgroup; membership in such a level is therefore the
conjunction of the two membership conditions, and the compact level is
contained in the original level.
-/

open IsDedekindDomain NumberField MeasureTheory

namespace AutomorphicForm

/-- Carrier pins on the adelic group of a number field: measures,
a fundamental set, a centre subgroup, level subgroups, and local
generators. -/
structure CarrierPins (F : Type*) [Field F] [NumberField F] where
  /-- The measurable space structure on adelic `GL₂`. -/
  measurableSpaceGL : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F)
  /-- The measure on adelic `GL₂`. -/
  measureGL : @Measure _ measurableSpaceGL
  /-- The fundamental set in adelic `GL₂`. -/
  fundamentalSet : Set (NumberField.AdelicGL2 (𝓞 F) F)
  /-- The centre subgroup of the adele units. -/
  centreSubgroup : Subgroup (AdeleRing (𝓞 F) F)ˣ
  /-- The level subgroup at an ideal. -/
  levelSubgroup : Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F)
  /-- The chosen generator at a height-one prime. -/
  localGenerator :
    HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F
  /-- The measurable space structure on the adele ring. -/
  measurableSpaceAdele : MeasurableSpace (AdeleRing (𝓞 F) F)
  /-- The measure on the adele ring. -/
  measureAdele : @Measure _ measurableSpaceAdele

/-- Production pins from a fundamental set, level subgroups, local
generators, an adele set, and the two measures; the centre subgroup is
the whole unit group.  The adele set is the set on which the adele
measure is conditioned in applications; it is not part of the pins. -/
def productionPinsOf (F : Type*) [Field F] [NumberField F]
    (D : Set (NumberField.AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F)
    (_B : Set (AdeleRing (𝓞 F) F))
    (mS : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F))
    (μ : @Measure _ mS)
    (nS : MeasurableSpace (AdeleRing (𝓞 F) F))
    (ν : @Measure _ nS) : CarrierPins F where
  measurableSpaceGL := mS
  measureGL := μ
  fundamentalSet := D
  centreSubgroup := ⊤
  levelSubgroup := U
  localGenerator := gen
  measurableSpaceAdele := nS
  measureAdele := ν

@[simp]
theorem productionPinsOf_fundamentalSet (F : Type*) [Field F]
    [NumberField F] (D U gen B mS μ nS ν) :
    (productionPinsOf F D U gen B mS μ nS ν).fundamentalSet = D := rfl

@[simp]
theorem productionPinsOf_centreSubgroup (F : Type*) [Field F]
    [NumberField F] (D U gen B mS μ nS ν) :
    (productionPinsOf F D U gen B mS μ nS ν).centreSubgroup = ⊤ := rfl

@[simp]
theorem productionPinsOf_levelSubgroup (F : Type*) [Field F]
    [NumberField F] (D U gen B mS μ nS ν) :
    (productionPinsOf F D U gen B mS μ nS ν).levelSubgroup = U := rfl

@[simp]
theorem productionPinsOf_localGenerator (F : Type*) [Field F]
    [NumberField F] (D U gen B mS μ nS ν) :
    (productionPinsOf F D U gen B mS μ nS ν).localGenerator = gen := rfl

/-- The compact production pins: every level subgroup of the production
pins is intersected with a fixed finite-adelic subgroup. -/
def productionPinsCompact (F : Type*) [Field F] [NumberField F]
    (levelOneSubgroup :
      Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (finiteSubgroup : Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (D : Set (NumberField.AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (mS : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F))
    (μ : @Measure _ mS)
    (nS : MeasurableSpace (AdeleRing (𝓞 F) F))
    (ν : @Measure _ nS) : CarrierPins F :=
  productionPinsOf F D
    (fun N ↦ levelOneSubgroup N ⊓ finiteSubgroup) gen B mS μ nS ν

@[simp]
theorem productionPinsCompact_levelSubgroup (F : Type*) [Field F]
    [NumberField F] (levelOneSubgroup finiteSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) :
    (productionPinsCompact F levelOneSubgroup finiteSubgroup D gen B
      mS μ nS ν).levelSubgroup N =
      levelOneSubgroup N ⊓ finiteSubgroup := rfl

/-- Membership in a compact level is the conjunction of membership in
the original level and in the finite-adelic subgroup. -/
theorem mem_productionPinsCompact_levelSubgroup (F : Type*) [Field F]
    [NumberField F] (levelOneSubgroup finiteSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) (u : NumberField.AdelicGL2 (𝓞 F) F) :
    u ∈ (productionPinsCompact F levelOneSubgroup finiteSubgroup D gen
      B mS μ nS ν).levelSubgroup N ↔
      u ∈ levelOneSubgroup N ∧ u ∈ finiteSubgroup :=
  Subgroup.mem_inf

/-- The first component of a compact-level element lies in the original
level. -/
theorem mem_levelOne_of_mem_productionPinsCompact (F : Type*) [Field F]
    [NumberField F] (levelOneSubgroup finiteSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) {u : NumberField.AdelicGL2 (𝓞 F) F}
    (hu : u ∈ (productionPinsCompact F levelOneSubgroup finiteSubgroup
      D gen B mS μ nS ν).levelSubgroup N) :
    u ∈ levelOneSubgroup N := hu.1

/-- The second component of a compact-level element lies in the
finite-adelic subgroup. -/
theorem mem_finite_of_mem_productionPinsCompact (F : Type*) [Field F]
    [NumberField F] (levelOneSubgroup finiteSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) {u : NumberField.AdelicGL2 (𝓞 F) F}
    (hu : u ∈ (productionPinsCompact F levelOneSubgroup finiteSubgroup
      D gen B mS μ nS ν).levelSubgroup N) :
    u ∈ finiteSubgroup := hu.2

/-- Every compact level is contained in the corresponding original
level. -/
theorem productionPinsCompact_levelSubgroup_le (F : Type*) [Field F]
    [NumberField F] (levelOneSubgroup finiteSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) :
    (productionPinsCompact F levelOneSubgroup finiteSubgroup D gen B
      mS μ nS ν).levelSubgroup N ≤ levelOneSubgroup N :=
  inf_le_left

/-- When the finite-adelic subgroup is the whole group, the compact
level agrees with the original level. -/
theorem productionPinsCompact_levelSubgroup_of_top (F : Type*)
    [Field F] [NumberField F] (levelOneSubgroup D gen B mS μ nS ν)
    (N : Ideal (𝓞 F)) :
    (productionPinsCompact F levelOneSubgroup ⊤ D gen B
      mS μ nS ν).levelSubgroup N = levelOneSubgroup N := by
  simp

end AutomorphicForm

end
