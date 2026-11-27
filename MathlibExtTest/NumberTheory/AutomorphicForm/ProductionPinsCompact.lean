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
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

universe u

namespace ProductionPinsCompactTest

/-- Consumer with the source's statement: the compact production pins carry the Haar measure on
adelic `GL₂`, the whole unit group as centre, the level `levelOne N ⊓ finiteAdelicGL2Subgroup F`
at every ideal `N`, the Hecke generators, and the additive Haar measure conditioned on the adelic
box, which is a probability measure. -/
theorem exactSource (F : Type u) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) :
    (productionPinsCompact F D).μ = adelicGLHaar (Fin 2) (𝓞 F) F ∧
      (productionPinsCompact F D).Z = ⊤ ∧ (productionPinsCompact F D).D = D ∧
      (∀ N : Ideal (𝓞 F),
        (productionPinsCompact F D).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (productionPinsCompact F D).gen v = heckeGen (𝓞 F) F v) ∧
      (productionPinsCompact F D).ν =
        @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) ∧
      @IsProbabilityMeasure _ (productionPinsCompact F D).nS (productionPinsCompact F D).ν :=
  ⟨rfl, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl, rfl,
    isProbabilityMeasure_productionPinsCompact_ν F D⟩

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 (F : Type 1) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) :
    (productionPinsCompact F D).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧
      (productionPinsCompact F D).ν =
        @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  ⟨(exactSource F D).2.2.2.1 N, (exactSource F D).2.2.2.2.2.1⟩

/-- Membership in a compact level: the finite part lies in the finite-adelic level and the
infinite part is the identity. -/
example (F : Type u) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (N : Ideal (𝓞 F)) (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ (productionPinsCompact F D).U N) :
    glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N ∧ glArch (𝓞 F) F u = 1 ∧
      u ∈ (productionPins F D).U N :=
  ⟨glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U F D N hu,
    glArch_eq_one_of_mem_productionPinsCompact_U F D N hu,
    productionPinsCompact_U_le_productionPins_U F D N hu⟩

/-- The Hecke generators have identity infinite part. -/
theorem heckeGen_mem_finiteAdelicGL2Subgroup (F : Type u) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Boundary probe: the Hecke generator at `v` lies outside every level `levelOne N`, since the
`(0, 0)` entry of its inverse is `ϖ⁻¹` at `v`, which is not integral. -/
theorem heckeGen_not_mem_levelOne (F : Type u) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∉ levelOne (𝓞 F) F N := by
  intro h
  have h' : heckeGenAt (𝓞 F) F v (uniformizerUnit (𝓞 F) F v) ∈ levelOne (𝓞 F) F N := h
  have hint := (mem_levelOne_iff.mp h').2.integral 0 0 v
  rw [← map_inv, ← map_inv] at hint
  have hentry :
      ((glFin (𝓞 F) F (heckeGenAt (𝓞 F) F v (uniformizerUnit (𝓞 F) F v)⁻¹) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) v =
        (((uniformizerUnit (𝓞 F) F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    localUnit_apply_self (𝓞 F) F v _
  rw [hentry, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
    valued_uniformizerUnit, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hint
  exact absurd hint (by decide)

/-- Boundary probe: no compact level is the whole group. The Hecke generator at `v` has identity
infinite part (`heckeGen_mem_finiteAdelicGL2Subgroup`) but lies outside every compact level. -/
theorem heckeGen_not_mem_productionPinsCompact_U (F : Type u) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∉ (productionPinsCompact F D).U N :=
  fun h ↦ heckeGen_not_mem_levelOne F N v (productionPinsCompact_U_le_productionPins_U F D N h)

end ProductionPinsCompactTest
