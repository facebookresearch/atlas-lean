/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedRawHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentSourceFunctor

/-!
# Both SAME original raw Hom comparison maps are source natural

Every source simplicial map retains each entire native input map and
full coefficient lift. The original raw/component inverse maps commute
with the actual raw realization and full original component source maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom

variable {K L : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME full original input Hom map retains the entire original source composition. -/
theorem inputHomMap_source (f : K ⟶ L) (T : Object K x y q) :
    inputHomMap T ≫ (CoherentRealization.realizationMap f).map x y = inputHomMap (sourceObject f T) := by
  have h := pointedHomMap_comp T.input f (input_source T) (input_target T)
    (rfl : f.app (op ⦋0⦌) x = f.app (op ⦋0⦌) x)
    (rfl : f.app (op ⦋0⦌) y = f.app (op ⦋0⦌) y)
  change inputHomMap T ≫ ((CoherentRealization.realizationMap f).map x y ≫ 𝟙 _) =
    inputHomMap (sourceObject f T) at h
  exact (congrArg (fun e => inputHomMap T ≫ e) (Category.comp_id _)).symm.trans h

/-- EVERY entire original flagged evaluation retains its original input source map. -/
theorem evaluation_source (f : K ⟶ L) (T : Object K x y q) :
    ((CoherentRealization.realizationMap f).map x y).app q (evaluation T) = evaluation (sourceObject f T) :=
  ConcreteCategory.congr_hom (congr_app (inputHomMap_source f T) q)
    (coefficientLift T.necklace (jointCoefficient T))

namespace Components

/-- The full original raw evaluation map is natural for EVERY original source simplicial map. -/
theorem rawEvaluationMap_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    rawEvaluationMap K x y ≫ (CoherentRealization.realizationMap f).map x y =
      sourceMap f x y ≫ rawEvaluationMap L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro c
  induction c using _root_.Quotient.inductionOn' with
  | h T => exact evaluation_source f T

private theorem iso_forward_square {A B C D : SSet.{u}} (e : A ≅ B) (d : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : e.inv ≫ f = g ≫ d.inv) : f ≫ d.hom = e.hom ≫ g := by
  apply (cancel_mono d.inv).1
  calc
    (f ≫ d.hom) ≫ d.inv = f := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (e.hom ≫ e.inv) ≫ f := by rw [Iso.hom_inv_id, Category.id_comp]
    _ = (e.hom ≫ g) ≫ d.inv := by rw [Category.assoc, h, ← Category.assoc]

/-- The full original raw presentation map is natural for EVERY original source simplicial map. -/
theorem rawHomMap_source (f : K ⟶ L) (x y : K _⦋0⦌) :
    (CoherentRealization.realizationMap f).map x y ≫
        rawHomMap L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      rawHomMap K x y ≫ sourceMap f x y :=
  iso_forward_square (rawHomIso K x y) (rawHomIso L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
    ((CoherentRealization.realizationMap f).map x y) (sourceMap f x y) (rawEvaluationMap_source f x y)

/-- Both original comparison functors retain the complete original source naturality square. -/
theorem realizationMap_sourceFunctor (f : K ⟶ L) :
    CoherentRealization.realizationMap f ≫ realizationMap L = realizationMap K ≫ sourceFunctor f := by
  refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
  intro x y
  change ((CoherentRealization.realizationMap f).map x y ≫
    rawHomMap L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) ≫ 𝟙 _ =
      rawHomMap K x y ≫ sourceMap f x y
  exact (Category.comp_id _).trans (rawHomMap_source f x y)

/-- The actual original evaluation functor retains the complete original source naturality square. -/
theorem evaluationFunctor_source (f : K ⟶ L) :
    evaluationFunctor K ≫ CoherentRealization.realizationMap f = sourceFunctor f ≫ evaluationFunctor L := by
  refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
  intro x y
  change (rawEvaluationMap K x y ≫ (CoherentRealization.realizationMap f).map x y) ≫ 𝟙 _ =
    sourceMap f x y ≫ rawEvaluationMap L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
  exact (Category.comp_id _).trans (rawEvaluationMap_source f x y)

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
