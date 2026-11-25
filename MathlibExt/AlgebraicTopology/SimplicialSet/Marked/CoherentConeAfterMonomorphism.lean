/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms

/-!
# Original positive-maximum cone monomorphism

The actual inclusion retains every whole original subset simplex; its
inverse-on-vertices detection proves injectivity in every scalar degree.
The resulting map is monic on the original marked carrier, with no
projective-class assumption substituted for this original inclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The whole original positive-maximum coefficient inclusion is actually monic as a marked map. -/
instance {n : ℕ} (i k : Vertex.{u} n) : Mono (coneAfterInclusion i k) := by
  apply (mono_iff_underlying _).mpr
  let _ : ∀ q : SimplexCategoryᵒᵖ, Mono ((coneAfterInclusion i k).hom.app q) := fun q =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro x y h
      change x ⋙ coneAfterForgetFunctor i k = y ⋙ coneAfterForgetFunctor i k at h
      refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
      exact congrArg (fun a => a.obj t) h)
  exact NatTrans.mono_of_mono_app _

end SSet.Marked.CoherentWeight
