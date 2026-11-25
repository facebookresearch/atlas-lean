/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPiNaturality

/-!
# The original canonical Kan fibration theorem under universe lift

The exact original horn-lifting proof is promoted from QuillenFrameHomComplex.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v

open CategoryTheory MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

universe z

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial

/-- Original horn lifting proves that the actual universe-lift functor preserves every original
fibration. -/
theorem uliftFunctor_map_fibration {K M : SSet.{v}} (p : K ⟶ M) [Fibration p] :
    Fibration (SSet.uliftFunctor.{z, v}.map p) := by
  apply (fibration_iff _).mpr
  intro A B j hj
  rw [J, iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  refine ⟨?_⟩
  intro z b sq
  let f : ∀ j : Fin (n + 2), j ≠ i → ((Δ[n] : SSet.{max z v}) ⟶ SSet.uliftFunctor.{z, v}.obj K) :=
    fun j hj => SSet.horn.ι i j hj ≫ z
  have hf : SSet.horn.IsCompatible f := SSet.horn.IsCompatible.of_hom z
  let low : ∀ j : Fin (n + 2), j ≠ i → ((Δ[n] : SSet.{v}) ⟶ K) :=
    fun j hj => SSet.yonedaEquiv.symm (SSet.yonedaEquiv (f j hj)).down
  have hLow : SSet.horn.IsCompatible low := by
    cases n with
    | zero => trivial
    | succ n =>
      rw [SSet.horn.isCompatible_iff]
      intro j k hj hk hjk
      apply SSet.yonedaEquiv.injective
      have h := congrArg (SSet.yonedaEquiv (X := SSet.uliftFunctor.{z, v}.obj K) (n := ⦋n⦌))
        (hf.δ_pred_comp j k hj hk hjk)
      have hd := congrArg ULift.down h
      simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at hd
      change K.δ (k.pred (Fin.ne_zero_of_lt hjk)) (SSet.yonedaEquiv (f j hj)).down =
        K.δ (j.castPred (Fin.ne_last_of_lt hjk)) (SSet.yonedaEquiv (f k hk)).down at hd
      simpa only [low, SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using hd
  let b₀ : (Δ[n + 1] : SSet.{v}) ⟶ M := SSet.yonedaEquiv.symm (SSet.yonedaEquiv b).down
  have hComm (j : Fin (n + 2)) (hj : j ≠ i) : low j hj ≫ p = SSet.stdSimplex.δ j ≫ b₀ := by
    apply SSet.yonedaEquiv.injective
    have hh : f j hj ≫ SSet.uliftFunctor.{z, v}.map p = SSet.stdSimplex.δ j ≫ b := by
      dsimp only [f]
      rw [Category.assoc, sq.w, ← Category.assoc, SSet.horn.ι_ι]
    have hd := congrArg ULift.down
      (congrArg (SSet.yonedaEquiv (X := SSet.uliftFunctor.{z, v}.obj M) (n := ⦋n⦌)) hh)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp] at hd
    change p.app (op ⦋n⦌) (SSet.yonedaEquiv (f j hj)).down = M.δ j (SSet.yonedaEquiv b).down at hd
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp]
    simpa only [low, b₀, Equiv.apply_symm_apply] using hd
  obtain ⟨φ, hFaces, hBottom⟩ := hLow.exists_lift p b₀ hComm
  let δ : (Δ[n + 1] : SSet.{max z v}) ⟶ SSet.uliftFunctor.{z, v}.obj K :=
    SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv φ))
  refine CommSq.HasLift.mk' { l := δ, fac_left := ?_, fac_right := ?_ }
  · apply SSet.horn.hom_ext'
    intro j hj
    rw [← Category.assoc, SSet.horn.ι_ι]
    change SSet.stdSimplex.δ j ≫ δ = f j hj
    apply SSet.yonedaEquiv.injective
    have hh := congrArg (SSet.yonedaEquiv (X := K) (n := ⦋n⦌)) (hFaces j hj)
    have hOriginal : K.δ j (SSet.yonedaEquiv φ) = (SSet.yonedaEquiv (f j hj)).down := by
      simpa only [low, SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using hh
    exact ULift.ext hOriginal
  · apply SSet.yonedaEquiv.injective
    have hh := congrArg (SSet.yonedaEquiv (X := M) (n := ⦋n + 1⦌)) hBottom
    have hOriginal : p.app (op ⦋n + 1⦌) (SSet.yonedaEquiv φ) = (SSet.yonedaEquiv b).down := by
      simpa only [b₀, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh
    apply ULift.ext
    rw [SSet.yonedaEquiv_comp]
    have hδ : SSet.yonedaEquiv δ = ULift.up (SSet.yonedaEquiv φ) :=
        SSet.yonedaEquiv.apply_symm_apply _
    rw [hδ]
    exact hOriginal

end SSet.modelCategoryQuillen

end
