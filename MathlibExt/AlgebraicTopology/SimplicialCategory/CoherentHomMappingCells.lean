/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomMapping
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFlagEvaluation

/-!
# Whole original cell readback of the coherent right-mapping comparison

The actual whole enriched simplex carrying an original Hom cell has an
exact degreewise flag readback. Consequently the genuine comparison is
injective on every original scalar cell. Original objects and both
endpoint equations are retained; no simplicial inverse or weak
comparison is inferred from this section.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomMappingCells
open SimplicialEnrichment HomSimplex HomFlagEvaluation HomMapping
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- An actual enriched simplex with both supplied individual original object labels fixed. -/
abbrev FixedSimplex := {σ : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C //
  σ.obj (.mk (ULift.up (0 : Fin (n + 2)))) = x ∧
  σ.obj (.mk (ULift.up (Fin.last (n + 1)))) = y}

/-- The entire original Hom-simplex readback of an actual fixed-endpoint coherent simplex. -/
def read (σ : FixedSimplex x y (n := n)) : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y) :=
  evaluate x y σ.1 σ.2.1 σ.2.2

/-- The actual fixed-endpoint enriched simplex carrying a supplied original scalar Hom cell. -/
def construct (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) : FixedSimplex x y (n := n) :=
  ⟨simplex x y (SSet.yonedaEquiv.symm τ), object_front x y (0 : Fin (n + 1)), object_last x y⟩

/-- Every supplied original Hom cell has the exact whole flag readback under its actual endpoint labels. -/
theorem read_construct (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    read x y (construct x y τ) = SSet.yonedaEquiv.symm τ := evaluate_constructed x y (SSet.yonedaEquiv.symm τ)

/-- The actual whole enriched-simplex carrier is injective on each individual original scalar Hom cell. -/
theorem construct_injective : Function.Injective (construct x y (n := n)) := by
  intro τ υ h
  have hR := congrArg (read x y) h
  have hτ := read_construct x y τ
  have hυ := read_construct x y υ
  exact (SSet.yonedaEquiv (X := (x ⟶[SSet.{u}] y)) (n := ⦋n⦌)).symm.injective (hτ.symm.trans (hR.trans hυ))

/-- The genuine whole Hom-to-right-mapping-space map preserves and distinguishes every individual original
  cell in every degree. -/
theorem map_injective : Function.Injective ((HomMapping.map x y).app (op ⦋n⦌)) := by
  intro τ υ h
  have hV := congrArg (fun σ => ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val) h
  have hτ := HomMapping.map_readback x y τ
  have hυ := HomMapping.map_readback x y υ
  have hS : simplex x y (SSet.yonedaEquiv.symm τ) = simplex x y (SSet.yonedaEquiv.symm υ) :=
    (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm.injective (hτ.symm.trans (hV.trans hυ))
  apply construct_injective x y
  exact Subtype.ext hS

/-- The comparison is a genuine monomorphism of entire original Hom simplicial sets. -/
theorem map_mono : Mono (HomMapping.map x y) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ n => exact (mono_iff_injective _).mpr (map_injective x y)

/-- Distinct original cells stay distinct under the actual coherent mapping comparison. -/
theorem map_ne {τ υ : (x ⟶[SSet.{u}] y) _⦋n⦌} (h : τ ≠ υ) :
    (HomMapping.map x y).app (op ⦋n⦌) τ ≠ (HomMapping.map x y).app (op ⦋n⦌) υ :=
  fun he => h (map_injective x y he)

end CategoryTheory.CoherentRealization.HomMappingCells
