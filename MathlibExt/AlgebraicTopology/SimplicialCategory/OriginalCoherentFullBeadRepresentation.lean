/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFlatteningComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentGeneratorInterval

/-!
# Full original Hom simplices as complete original beads

For a quasicategory, every complete original generating path evaluates
as a full original simplex bead. The proof retains each actual generator
and its scalar flag, using genuine original two-bead flattenings.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment SimplicialQuiver

private theorem original_composition_cons {K : SSet.{u}}
    {x y z : K _⦋0⦌} {s : SimplexCategoryᵒᵖ}
    (p : Path (generatingQuiver K) s x y) (a : Arrow K y z s) :
    (eComp SSet.{u} (C := realization K) x y z).app s
      (_root_.Quotient.mk (congruence (relations K) s x y) p, originalEvaluation a) =
        _root_.Quotient.mk (congruence (relations K) s x z)
          (@Quiver.Path.cons (K _⦋0⦌) (quiverAt (generatingQuiver K) s) x y z p a) := by
  cases a
  rfl

/-- Every original finite generating path has its same Hom value as a complete original bead. -/
theorem original_path_represented {K : SSet.{u}} [SSet.Quasicategory K]
    {x y : K _⦋0⦌} {s : SimplexCategoryᵒᵖ}
    (p : Path (generatingQuiver K) s x y) :
    ∃ b : Bead K x y s,
      b.evaluation = _root_.Quotient.mk (congruence (relations K) s x y) p := by
  let : Quiver (K _⦋0⦌) := quiverAt (generatingQuiver K) s
  induction p with
  | nil =>
    exact ⟨identity K x s, evaluation_identity K x s⟩
  | @cons y z p a ih =>
    obtain ⟨b, hb⟩ := ih
    let c := trim a
    obtain ⟨f⟩ := exists_flattening b c
    refine ⟨f.bead, ?_⟩
    have hv : c.evaluation = originalEvaluation a := evaluation_trim a
    have h := f.bead_evaluation
    have hc : (eComp SSet.{u} (C := realization K) x y z).app s
        (b.evaluation, c.evaluation) =
      (eComp SSet.{u} (C := realization K) x y z).app s
        (_root_.Quotient.mk (congruence (relations K) s x y) p, originalEvaluation a) :=
      congrArg
      (fun t => (eComp SSet.{u} (C := realization K) x y z).app s t)
        (Prod.ext hb hv)
    exact h.trans (hc.trans (original_composition_cons p a))

/-- Every full original raw Hom simplex is represented by a complete original bead. -/
theorem original_hom_represented {K : SSet.{u}} [SSet.Quasicategory K]
    {x y : K _⦋0⦌} {s : SimplexCategoryᵒᵖ} (a : (hom K x y).obj s) :
    ∃ b : Bead K x y s, b.evaluation = a := by
  induction a using _root_.Quotient.inductionOn with
  | h p => exact original_path_represented p

end CategoryTheory.CoherentRealization.OriginalBead
