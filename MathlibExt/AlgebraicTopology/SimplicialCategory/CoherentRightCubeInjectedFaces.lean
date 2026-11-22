/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCanonicalCells
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNormalizedOrderImage

/-!
# Genuine injectivity of original right-cube face maps

The actual first maximum follows each original right-join operator.
For an injected operator, the embedded cut reflects the whole original
reduced path chain. Thus the actual quotient face maps are monomorphisms,
proved from the original prefix relations and order embeddings rather
than supplied as a relative-frame outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeInjectedFaces
open PathLastMaximum PathMaximumOperators RightCubeRelations RightCubeReduction RightCubeNormalForms
  RightCubeOrdinalEmbedding NormalizedOrderImage
variable {n m : ℕ}

/-- Every original right-join operator preserves the actual first maximum through its original front map. -/
theorem initialMaximum_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    initialMaximum (p ⋙ RightCubeOperator.functor θ) = θ.toOrderHom (initialMaximum p) :=
  RightCubeOperator.maximum_operator θ (p.obj 0)

/-- The original normalized injected path image is precisely its genuine embedded retained support at the
  same first maximum. -/
theorem normalized_image (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q)
    (k : Fin (q.unop.len + 1)) :
    ((normalize (p ⋙ RightCubeOperator.functor θ)).obj k).I =
      imageCut (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (p.obj k).I := by
  have hi : ULift.up.{u} (initialMaximum (p ⋙ RightCubeOperator.functor θ)).castSucc =
      lifted.{u} θ hθ (ULift.up (initialMaximum p).castSucc) :=
    (congrArg (fun i => ULift.up.{u} i.castSucc) (initialMaximum_operator θ p)).trans
      (lifted_front θ (initialMaximum p)).symm
  change {ULift.up.{u} (0 : Fin (m + 2))} ∪
    {y | y ∈ ({ULift.up.{u} (0 : Fin (m + 2))} ∪ (extension θ).toOrderHom.uliftMap '' (p.obj k).I) ∧
      ULift.up.{u} (initialMaximum (p ⋙ RightCubeOperator.functor θ)).castSucc ≤ y} = _
  rw [hi]
  exact imageCut_zero_adjunction (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (p.obj k).I

/-- The same injected original right-join image reflects equality of entire original canonical scalar chains. -/
theorem normalize_operator_injective (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} {p r : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q}
    (h : normalize (p ⋙ RightCubeOperator.functor θ) = normalize (r ⋙ RightCubeOperator.functor θ)) :
    normalize p = normalize r := by
  have ho : initialMaximum (p ⋙ RightCubeOperator.functor θ) = initialMaximum (r ⋙ RightCubeOperator.functor θ) :=
    (normalize_initialMaximum (p ⋙ RightCubeOperator.functor θ)).symm.trans
      ((congrArg initialMaximum h).trans (normalize_initialMaximum (r ⋙ RightCubeOperator.functor θ)))
  have hi : initialMaximum p = initialMaximum r := hθ
    ((initialMaximum_operator θ p).symm.trans (ho.trans (initialMaximum_operator θ r)))
  refine Functor.ext (fun k => ?_) ?_
  · apply SimplicialThickening.Path.ext
    have hSet := congrArg (fun a : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q => (a.obj k).I) h
    have hImage : imageCut (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (p.obj k).I =
        imageCut (lifted.{u} θ hθ) (ULift.up (initialMaximum r).castSucc) (r.obj k).I :=
      (normalized_image θ hθ p k).symm.trans (hSet.trans (normalized_image θ hθ r k))
    have hSame : imageCut (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (p.obj k).I =
        imageCut (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (r.obj k).I :=
      hImage.trans (congrArg (fun i : Fin (n + 1) => imageCut (lifted.{u} θ hθ) (ULift.up.{u} i.castSucc)
        (r.obj k).I) hi.symm)
    have hCut := cut_injective (lifted.{u} θ hθ) (ULift.up (initialMaximum p).castSucc) (p.obj k).I (r.obj k).I hSame
    change cut (ULift.up.{u} (initialMaximum p).castSucc) (p.obj k).I =
      cut (ULift.up.{u} (initialMaximum r).castSucc) (r.obj k).I
    exact hCut.trans (congrArg (fun i : Fin (n + 1) => cut (ULift.up.{u} i.castSucc) (r.obj k).I) hi)
  · intro k l f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Every scalar component of an actual injected original quotient operator is injective. -/
theorem app_injective (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((RightCubeCosimplicialMaps.map.{u} θ).app q) := by
  intro a b hab
  induction a using _root_.Quotient.inductionOn with
  | _ p =>
    induction b using _root_.Quotient.inductionOn with
    | _ r =>
      exact _root_.Quotient.sound ((setoid_iff_normalize_eq p r).mpr
        (normalize_operator_injective θ hθ (setoid_normalize (_root_.Quotient.exact hab))))

/-- The genuine original right-cube map of an injected front operator is a whole simplicial monomorphism. -/
theorem map_mono (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) : Mono
    (RightCubeCosimplicialMaps.map.{u} θ) := by
  constructor
  intro Z f g hfg
  ext q z
  exact app_injective θ hθ q (congr($(hfg).app q z))

end CategoryTheory.CoherentRealization.RightCubeInjectedFaces
