/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSimplexChartRestriction

/-!
# Whole native unstraightening restriction readback

The original marked slice simplex restriction acts through the same
coherent unit pullback adjunction and original Yoneda representative.
Its raw unstraightening simplex is precisely the full cone pull along
the original ordinal map. All faces and degeneracies share this same
actual map; no representation or comparison outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Precomposing the whole original native marked simplex map reads exactly the same full unstraightening
  cone restriction under the original ordinal operator. -/
theorem nativeSimplexUn_pre_val (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : nativeSimplexBasis B m σ ⟶ (nativeUnstraightening B).obj F) :
    (nativeSimplexUnHomEquiv B n (B.map f.op σ) F (nativeSimplexRestriction B f σ ≫ g)).val =
      ((nativeSimplexUnHomEquiv B m σ F g).val).pull f.toOrderHom.uliftMap := by
  let a := Over.mapPullbackAdj (maximal.map (unit B))
  have h := a.homEquiv_naturality_left_symm (nativeSimplexRestriction B f σ) g
  have hy := congrArg (fun g' : (Over.map (maximal.map (unit B))).obj
    (nativeSimplexBasis B n (B.map f.op σ)) ⟶
      (coherentUnstraighteningFunctor (realization B)).obj F => SSet.yonedaEquiv g'.left.hom) h
  apply hy.trans
  change SSet.yonedaEquiv ((SSet.stdSimplex.map f) ≫
    (((a.homEquiv (nativeSimplexBasis B m σ) ((coherentUnstraighteningFunctor (realization B)).obj F)).symm
      g).left.hom)) = _
  exact (SSet.yonedaEquiv_naturality f _).symm

end SSet.Marked
