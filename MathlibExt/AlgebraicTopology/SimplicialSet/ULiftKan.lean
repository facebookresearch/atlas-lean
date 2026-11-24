/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

@[expose] public section

/-!
# Actual universe lifting of Kan simplicial sets

A compatible original horn face family in the lifted simplicial set is
lowered vertexwise to the same original simplicial set. Its actual Kan
filler lifts back with every whole supplied face equation preserved.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The actual simplicial universe-lift functor preserves genuine Kan complexes, with no
additional model or comparison hypothesis. -/
theorem kanComplex_ulift (X : SSet.{u}) [KanComplex X] :
    KanComplex (uliftFunctor.{v, u}.obj X) := by
  rw [KanComplex.iff]
  intro n i f hf
  let low : ∀ j : Fin (n + 2), j ≠ i → ((Δ[n] : SSet.{u}) ⟶ X) :=
    fun j hj => yonedaEquiv.symm (yonedaEquiv (f j hj)).down
  have hLow : horn.IsCompatible low := by
    cases n with
    | zero => trivial
    | succ n =>
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      apply yonedaEquiv.injective
      have h := congrArg (yonedaEquiv (X := uliftFunctor.{v, u}.obj X) (n := ⦋n⦌))
        (hf.δ_pred_comp j k hj hk hjk)
      have hDown := congrArg ULift.down h
      simp only [stdSimplex.yonedaEquiv_δ_comp] at hDown
      change X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (yonedaEquiv (f j hj)).down =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (yonedaEquiv (f k hk)).down at hDown
      simpa only [low, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using hDown
  refine ⟨yonedaEquiv.symm (ULift.up (yonedaEquiv hLow.liftOfKanComplex)), ?_⟩
  intro j hj
  apply yonedaEquiv.injective
  have h := congrArg (yonedaEquiv (X := X) (n := ⦋n⦌)) (hLow.δ_liftOfKanComplex j hj)
  have hOriginal : X.δ j (yonedaEquiv hLow.liftOfKanComplex) = (yonedaEquiv (f j hj)).down := by
    simpa only [low, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using h
  exact ULift.ext hOriginal

end SSet
