/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalMappingHomotopy

/-!
# The original maximally marked ordered-interval contraction

Pointwise minimum is a native simplicial map on the two original ordered
intervals. Its fully marked map contracts the original interval to its
source endpoint and retains the original identity at the other parameter
endpoint. The underlying interval is not asserted to be Kan.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Pointwise minimum on original ordered-interval simplices is the native simplicial contraction. -/
def intervalMinimum : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] where
  app n := ↾fun z => SSet.stdSimplex.objMk
    { toFun i := Min.min (SSet.stdSimplex.asOrderHom z.1 i) (SSet.stdSimplex.asOrderHom z.2 i)
      monotone' := fun i j hij => min_le_min
        ((SSet.stdSimplex.asOrderHom z.1).monotone hij) ((SSet.stdSimplex.asOrderHom z.2).monotone hij) }
  naturality n m a := by ext z; apply SSet.stdSimplex.ext; intro i; rfl

/-- The same entire original minimum map is marked with the original two maximal interval markings. -/
def markedIntervalMinimum : prod (max (Δ[1] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ max (Δ[1] : SSet.{u}) :=
  toMax intervalMinimum

/-- The original source parameter endpoint gives the literal constant source-endpoint interval map. -/
theorem markedIntervalMinimum_source :
    prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (max (Δ[1] : SSet.{u}))) ≫ markedIntervalMinimum =
      (zeroParameterUnitIso .maximal (max (Δ[1] : SSet.{u}))).hom ≫
        maximal.map (SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2)) := by
  apply Hom.ext
  ext n z
  let a : (Δ[0] : SSet.{u}).obj n := z.1
  let b : (Δ[1] : SSet.{u}).obj n := z.2
  apply SSet.stdSimplex.ext
  intro i
  change Min.min ((1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom a i)) (SSet.stdSimplex.asOrderHom b i) =
    (1 : Fin 2).succAbove ((0 : Fin 1).predAbove (SSet.stdSimplex.asOrderHom b i))
  have ha : SSet.stdSimplex.asOrderHom a i = 0 := Fin.eq_zero _
  have hb : (0 : Fin 1).predAbove (SSet.stdSimplex.asOrderHom b i) = 0 := Fin.eq_zero _
  rw [ha, hb]
  exact min_eq_left (Fin.zero_le _)

/-- The other original parameter endpoint retains the same whole identity interval map. -/
theorem markedIntervalMinimum_target :
    prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 (max (Δ[1] : SSet.{u}))) ≫ markedIntervalMinimum =
      (zeroParameterUnitIso .maximal (max (Δ[1] : SSet.{u}))).hom ≫ 𝟙 (max (Δ[1] : SSet.{u})) := by
  apply Hom.ext
  ext n z
  let a : (Δ[0] : SSet.{u}).obj n := z.1
  let b : (Δ[1] : SSet.{u}).obj n := z.2
  apply SSet.stdSimplex.ext
  intro i
  change Min.min ((0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom a i)) (SSet.stdSimplex.asOrderHom b i) =
    SSet.stdSimplex.asOrderHom b i
  have ha : SSet.stdSimplex.asOrderHom a i = 0 := Fin.eq_zero _
  rw [ha]
  exact min_eq_right (Fin.le_last _)

end SSet.Marked
