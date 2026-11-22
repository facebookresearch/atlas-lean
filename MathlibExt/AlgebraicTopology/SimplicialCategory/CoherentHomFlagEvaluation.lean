/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathMaximumFlags
import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Exact original Hom-simplex readback by finite coherent flags

An actual enriched simplex with specified original first and last object
labels is evaluated on the whole original front-flag nerve. On the
maximum construction this reads back the supplied Hom simplex exactly.
This degreewise evaluation is not asserted to be a simplicial inverse.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFlagEvaluation
open SimplicialEnrichment HomSimplex PathLastMaximum PathMaximumFlags
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The original flag nerve, with every original front label retained, in the actual zero-to-last Hom. -/
def flagMap : (Δ[n] : SSet.{u}) ⟶ nerve (LastPath.{u} (0 : Fin (n + 1))) :=
  (SSet.stdSimplex.isoNerve.{u} n).hom ≫ nerveMap (flagFunctor.{u})

/-- Evaluating the actual original zero-to-last Hom of an enriched simplex along the finite front flags. -/
def evaluate (σ : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C)
    (hx : σ.obj (.mk (ULift.up (0 : Fin (n + 2)))) = x)
    (hy : σ.obj (.mk (ULift.up (Fin.last (n + 1)))) = y) :
    (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y) :=
  flagMap ≫ σ.map (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
    EqualityTransport.hom hx hy

/-- The actual whole flag nerve is a section of the original maximum Hom map. -/
theorem flag_maximum : flagMap.{u} (n := n) ≫
    (nerveMap (maximumFunctor (0 : Fin (n + 1))) ≫ (SSet.stdSimplex.isoNerve.{u} n).inv) = 𝟙 (Δ[n] : SSet.{u}) := by
  let a := (SSet.stdSimplex.isoNerve.{u} n).hom
  let f := nerveMap (flagFunctor.{u} (n := n))
  let g := nerveMap (maximumFunctor (0 : Fin (n + 1)))
  let b := (SSet.stdSimplex.isoNerve.{u} n).inv
  have h : f ≫ g = 𝟙 _ := (nerveMap_comp _ _).trans
    ((congrArg (fun F => nerveMap F) (flag_section.{u} (n := n))).trans nerveMap_id)
  change (a ≫ f) ≫ (g ≫ b) = _
  exact (Category.assoc a f _).trans
    ((congrArg (fun t => a ≫ t) (Category.assoc f g b).symm).trans
      ((congrArg (fun t => a ≫ (t ≫ b)) h).trans
        ((congrArg (fun t => a ≫ t) (Category.id_comp b)).trans (SSet.stdSimplex.isoNerve.{u} n).hom_inv_id)))

/-- The supplied original Hom simplex is recovered as an entire simplicial map from its actual enriched
  maximum construction. -/
theorem evaluate_constructed (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) :
    evaluate x y (simplex x y τ) (object_front x y (0 : Fin (n + 1))) (object_last x y) = τ := by
  have h := homMap_last x y τ (0 : Fin (n + 1))
  change flagMap ≫ homMap x y τ (0 : Fin (n + 1)).castSucc (Fin.last (n + 1)) ≫ _ = τ
  have hL : flagMap ≫ lastMap x y τ (0 : Fin (n + 1)) = τ := by
    change flagMap ≫ ((nerveMap (maximumFunctor (0 : Fin (n + 1))) ≫ (SSet.stdSimplex.isoNerve.{u} n).inv) ≫ τ) = τ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ τ) (flag_maximum (n := n))).trans (Category.id_comp τ))
  exact (congrArg (fun f => flagMap ≫ f) h).trans hL

/-- Every original scalar degree and individual supplied Hom cell has the exact flag readback. -/
theorem evaluate_constructed_apply (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))
    (q : SimplexCategoryᵒᵖ) (a : (Δ[n] : SSet.{u}).obj q) :
    (evaluate x y (simplex x y τ) (object_front x y (0 : Fin (n + 1))) (object_last x y)).app q a = τ.app q a :=
  congrArg (fun f => f.app q a) (evaluate_constructed x y τ)

end CategoryTheory.CoherentRealization.HomFlagEvaluation
