/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra

/-!
# Actual original Hom-chart restrictions

A full original Hom chart followed by its inverse evaluation retains
the whole original source restriction and both true endpoint
equations. This generic reduction uses the existing enriched
retargeting API and both genuine chart inverses.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalHomChartRestriction
open SimplicialEnrichment HornHomFaces

/-- The complete original chart restriction reads the same composite enriched functor at its true endpoints. -/
theorem retarget_inverse {A B C : Carrier.{u}} (d : A ⟶ B) (F : B ⟶ C)
    (a b : A) (a' b' : B) (ha : d.obj a = a') (hb : d.obj b = b')
    {x y : C} (hx : F.obj a' = x) (hy : F.obj b' = y)
    {Z : SSet.{u}} (e : (a' ⟶[SSet.{u}] b') ≅ Z) :
    (d.map a b ≫ eqToHom (congrArg₂ (fun a b : B => a ⟶[SSet.{u}] b) ha hb) ≫ e.hom) ≫
      (e.inv ≫ retargetMap F a' b' hx hy) =
        retargetMap (d ≫ F) a b ((congrArg F.obj ha).trans hx) ((congrArg F.obj hb).trans hy) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact HomRetargetAlgebra.restriction_reindex d F a b ha hb hx hy

end CategoryTheory.CoherentRealization.OriginalHomChartRestriction
