/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRelativeSimplexCharts

/-!
# Original face and degeneracy maps of relative native charts

The preimage subcomplex under every original simplex operator keeps
precisely all original simplices. The canonical preimage map is lifted
with minimal markings over the unchanged base simplex. Native
straightening preserves the entire inclusion square and its unit
equation. No injection-only restriction or altered operator is used.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original whole simplex restriction lies over exactly the corresponding original restricted base simplex. -/
def nativeSimplexRestriction (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    nativeSimplexBasis B n (B.map f.op σ) ⟶ nativeSimplexBasis B m σ :=
  Over.homMk (minimal.map (SSet.stdSimplex.map f)) (Hom.ext (SSet.yonedaEquiv_symm_naturality_left f σ))

/-- The actual subcomplex preimage restriction retains its entire native preimage carrier and minimal marking. -/
def nativeSubcomplexRestriction (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌)
    (A : (Δ[m] : SSet.{u}).Subcomplex) :
    nativeSubcomplexBasis B n (B.map f.op σ) (A.preimage (SSet.stdSimplex.map f)) ⟶
      nativeSubcomplexBasis B m σ A :=
  Over.homMk (minimal.map (A.fromPreimage (SSet.stdSimplex.map f))) (by
    apply Hom.ext
    change A.fromPreimage (SSet.stdSimplex.map f) ≫ (A.ι ≫ SSet.yonedaEquiv.symm σ) =
      (A.preimage (SSet.stdSimplex.map f)).ι ≫ SSet.yonedaEquiv.symm (B.map f.op σ)
    rw [← Category.assoc, SSet.Subcomplex.fromPreimage_ι, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left])

/-- Every original face or degeneracy restriction preserves the full same-base subcomplex inclusion square. -/
theorem nativeSubcomplexRestriction_square (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (A : (Δ[m] : SSet.{u}).Subcomplex) :
    nativeSubcomplexRestriction B f σ A ≫ nativeSubcomplexInclusion B m σ A =
      nativeSubcomplexInclusion B n (B.map f.op σ) (A.preimage (SSet.stdSimplex.map f)) ≫
        nativeSimplexRestriction B f σ := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  exact A.fromPreimage_ι (SSet.stdSimplex.map f)

/-- The actual full native relative chart attachment is natural for every original simplex restriction,
  using the same native simplex image maps. -/
theorem nativeSubcomplexChartRestriction_square (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (A : (Δ[m] : SSet.{u}).Subcomplex) :
    (nativeStraightening B).map (nativeSubcomplexRestriction B f σ A) ≫
        nativeSubcomplexChartMap B m σ A =
      (nativeStraightening B).map
        (nativeSubcomplexInclusion B n (B.map f.op σ) (A.preimage (SSet.stdSimplex.map f))) ≫
        (nativeStraightening B).map (nativeSimplexRestriction B f σ) ≫
          (nativeSimplexImageIso B m σ).hom := by
  dsimp only [nativeSubcomplexChartMap]
  have h := congrArg (fun g => (nativeStraightening B).map g)
    (nativeSubcomplexRestriction_square B f σ A)
  rw [(nativeStraightening B).map_comp, (nativeStraightening B).map_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (nativeSimplexImageIso B m σ).hom) h).trans (Category.assoc _ _ _))

end SSet.Marked
