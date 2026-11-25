/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.CategoryTheory.Functor.EvaluationPresentations
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Evaluation presentations of a parallel-arrow diagram

The two arrows are multiplication by two and three on a lifted copy of the integers.
The product presentation recovers the nonsplit coordinate embedding by multiplication
by two. The coproduct presentation recovers multiplication by minus one.
-/

noncomputable section

namespace EvaluationPresentationsTests

open CategoryTheory Limits

universe v

abbrev P : ModuleCat.{v} ℤ := ModuleCat.of ℤ (ULift.{v} ℤ)

def twice : P ⟶ P := 𝟙 P + 𝟙 P

def thrice : P ⟶ P := twice + 𝟙 P

def diagram : WalkingParallelPair ⥤ ModuleCat.{v} ℤ := parallelPair twice thrice

def factors : WalkingParallelPair → ModuleCat.{v} ℤ := diagram.obj

def coordinates (k : WalkingParallelPair) : diagram.obj k ⟶ factors k :=
  𝟙 (diagram.obj k) + 𝟙 (diagram.obj k)

theorem coordinates_mono (k : WalkingParallelPair) : Mono (coordinates k) := by
  cases k <;> apply (ModuleCat.mono_iff_injective _).mpr
  all_goals
    intro x y h
    apply ULift.ext
    have hd := congrArg ULift.down h
    change x.down + x.down = y.down + y.down at hd
    omega

def embedding := Functor.evaluationProductMap diagram factors coordinates

theorem embedding_mono : Mono embedding :=
  Functor.evaluationProductMap_mono diagram factors coordinates coordinates_mono

def recoveredEmbedding : P ⟶ P :=
  embedding.app .zero ≫
    ((Pi.π (fun k => (evaluationRightAdjoint (ModuleCat.{v} ℤ) k).obj (factors k))
      .zero).app .zero ≫
        (evaluationAdjunctionLeft (ModuleCat.{v} ℤ) .zero).counit.app (factors .zero))

theorem recovered_embedding : recoveredEmbedding = twice :=
  Functor.evaluationProductMap_recover diagram factors coordinates .zero

theorem recovered_embedding_value : (recoveredEmbedding (ULift.up 3)).down = 6 := by
  rw [recovered_embedding]
  rfl

theorem embedding_component_nonzero : embedding.app .zero ≠ 0 := by
  intro hz
  have hr : recoveredEmbedding = 0 := by
    change embedding.app .zero ≫ _ = 0
    rw [hz, zero_comp]
  have hv := congrArg (fun f : P ⟶ P => (f (ULift.up 3)).down) hr
  rw [recovered_embedding] at hv
  change (6 : ℤ) = 0 at hv
  norm_num at hv

theorem embedding_neg_naturality :
    (-𝟙 diagram) ≫ embedding =
      embedding ≫ Pi.map (fun k =>
        (evaluationRightAdjoint (ModuleCat.{v} ℤ) k).map (-𝟙 (factors k))) := by
  apply Functor.evaluationProductMap_naturality
    (F := diagram) (G := diagram) (A := factors) (B := factors)
    coordinates coordinates (-𝟙 diagram) (fun k => -𝟙 (factors k))
  intro k
  change (-𝟙 (diagram.obj k)) ≫ coordinates k =
    coordinates k ≫ (-𝟙 (diagram.obj k))
  simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    Category.id_comp, Category.comp_id]

def negativeCoordinates (k : WalkingParallelPair) : factors k ⟶ diagram.obj k :=
  -𝟙 (diagram.obj k)

theorem negativeCoordinates_epi (k : WalkingParallelPair) :
    Epi (negativeCoordinates k) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  refine ⟨-x, ?_⟩
  change - -x = x
  exact neg_neg x

def projection := Functor.evaluationCoproductMap diagram factors negativeCoordinates

theorem projection_epi : Epi projection :=
  Functor.evaluationCoproductMap_epi diagram factors negativeCoordinates
    negativeCoordinates_epi

def recoveredProjection : P ⟶ P :=
  ((evaluationAdjunctionRight (ModuleCat.{v} ℤ) .zero).unit.app (factors .zero) ≫
    (Sigma.ι (fun k => (evaluationLeftAdjoint (ModuleCat.{v} ℤ) k).obj (factors k))
      .zero).app .zero) ≫ projection.app .zero

theorem recovered_projection : recoveredProjection = -𝟙 P :=
  Functor.evaluationCoproductMap_recover diagram factors negativeCoordinates .zero

theorem recovered_projection_value : (recoveredProjection (ULift.up 3)).down = -3 := by
  rw [recovered_projection]
  rfl

end EvaluationPresentationsTests
