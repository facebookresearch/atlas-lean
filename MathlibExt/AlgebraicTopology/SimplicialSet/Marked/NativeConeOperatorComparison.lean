/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartRestrictionHom

/-!
# Original cone-operator readback of native chart restriction

The actual source simplex restriction acts on native unstraightening
by the same original cone direct-image operator. Reading the whole
native chart map through the original left-extension Hom correspondence
therefore retains its actual full cone section. This is the map
comparison needed for relative chart recognition, not an assumed
equivalence or desired cofibration.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The raw native unstraightening simplex of the actual chart restriction is the whole original cone
  restriction of the actual target chart unit. -/
theorem nativeChartRestriction_un_raw (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    (nativeSimplexUnHomEquiv B n (B.map f.op σ) (nativeSimplexChart B m σ)
      (nativeSimplexChartHomEquiv B n (B.map f.op σ) (nativeSimplexChart B m σ)
        (nativeSimplexChartRestriction B f σ))).val =
      ((nativeSimplexUnHomEquiv B m σ (nativeSimplexChart B m σ)
        (nativeSimplexChartHomEquiv B m σ (nativeSimplexChart B m σ) (𝟙 _))).val).pull
          f.toOrderHom.uliftMap := by
  have h := nativeChartRestriction_homEquiv B f σ (nativeSimplexChart B m σ) (𝟙 _)
  rw [Category.comp_id] at h
  exact (congrArg (fun g => (nativeSimplexUnHomEquiv B n (B.map f.op σ) (nativeSimplexChart B m σ) g).val) h).trans
    (nativeSimplexUn_pre_val B f σ (nativeSimplexChart B m σ) _)

end SSet.Marked
