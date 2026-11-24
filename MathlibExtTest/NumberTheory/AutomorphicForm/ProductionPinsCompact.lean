/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.ProductionPinsCompact

@[expose] public section

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm

universe u

namespace ProductionPinsCompactTest

/-- Consumer with the original binders: the compact production pins
have level given by intersecting the original level with the
finite-adelic subgroup, and centre the whole unit group. -/
theorem exactSource (F : Type u) [Field F] [NumberField F]
    (levelOneSubgroup :
      Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (finiteSubgroup : Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (D : Set (NumberField.AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (mS : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F))
    (μ : @Measure _ mS)
    (nS : MeasurableSpace (AdeleRing (𝓞 F) F))
    (ν : @Measure _ nS) :
    ∃ pins : CarrierPins F,
      pins.centreSubgroup = ⊤ ∧ pins.fundamentalSet = D ∧
      ∀ N : Ideal (𝓞 F),
        pins.levelSubgroup N = levelOneSubgroup N ⊓ finiteSubgroup :=
  ⟨productionPinsCompact F levelOneSubgroup finiteSubgroup D gen B mS μ nS ν,
    rfl, rfl, fun _ ↦ rfl⟩

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 (F : Type 1) [Field F] [NumberField F]
    (levelOneSubgroup :
      Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (finiteSubgroup : Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (D : Set (NumberField.AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (mS : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F))
    (μ : @Measure _ mS)
    (nS : MeasurableSpace (AdeleRing (𝓞 F) F))
    (ν : @Measure _ nS) :
    ∃ pins : CarrierPins F,
      pins.centreSubgroup = ⊤ ∧ pins.fundamentalSet = D ∧
      ∀ N : Ideal (𝓞 F),
        pins.levelSubgroup N = levelOneSubgroup N ⊓ finiteSubgroup :=
  ⟨productionPinsCompact F levelOneSubgroup finiteSubgroup D gen B mS μ nS ν,
    rfl, rfl, fun _ ↦ rfl⟩

/-- Boundary case: with the whole group as the finite-adelic subgroup,
the compact level is the original level; with a proper subgroup, an
element of the compact level lies in both components. -/
example (F : Type u) [Field F] [NumberField F]
    (levelOneSubgroup :
      Ideal (𝓞 F) → Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (finiteSubgroup : Subgroup (NumberField.AdelicGL2 (𝓞 F) F))
    (D : Set (NumberField.AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → NumberField.AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F))
    (mS : MeasurableSpace (NumberField.AdelicGL2 (𝓞 F) F))
    (μ : @Measure _ mS)
    (nS : MeasurableSpace (AdeleRing (𝓞 F) F))
    (ν : @Measure _ nS) (N : Ideal (𝓞 F))
    {u : NumberField.AdelicGL2 (𝓞 F) F}
    (hu : u ∈ (productionPinsCompact F levelOneSubgroup finiteSubgroup
      D gen B mS μ nS ν).levelSubgroup N) :
    u ∈ levelOneSubgroup N ∧ u ∈ finiteSubgroup ∧
      (productionPinsCompact F levelOneSubgroup ⊤ D gen B
        mS μ nS ν).levelSubgroup N = levelOneSubgroup N :=
  ⟨mem_levelOne_of_mem_productionPinsCompact F levelOneSubgroup
      finiteSubgroup D gen B mS μ nS ν N hu,
    mem_finite_of_mem_productionPinsCompact F levelOneSubgroup
      finiteSubgroup D gen B mS μ nS ν N hu,
    productionPinsCompact_levelSubgroup_of_top F levelOneSubgroup D gen
      B mS μ nS ν N⟩

end ProductionPinsCompactTest
