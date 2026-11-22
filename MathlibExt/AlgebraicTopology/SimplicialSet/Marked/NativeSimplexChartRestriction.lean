/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRelativeChartRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeConcreteImageUnitCounit

/-!
# Actual original simplex restriction maps between native charts

The original whole simplex restriction is straightened and transported
through the exact native image/unit isomorphisms. Its Hom readback is
precisely precomposition by that same original base simplex map and
the actual target chart unit. No substitute representing map or
relative cofibration is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every whole original ordinal operator gives the actual native chart map through native straightening and
  its exact image/unit isomorphisms. -/
def nativeSimplexChartRestriction (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    nativeSimplexChart B n (B.map f.op σ) ⟶ nativeSimplexChart B m σ :=
  (nativeSimplexImageIso B n (B.map f.op σ)).inv ≫
    (nativeStraightening B).map (nativeSimplexRestriction B f σ) ≫
      (nativeSimplexImageIso B m σ).hom

/-- The entire native restriction square uses precisely the same original straightened simplex map under its
  original unit-mate comparisons. -/
theorem nativeSimplexChartRestriction_square (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    (nativeSimplexImageIso B n (B.map f.op σ)).hom ≫ nativeSimplexChartRestriction B f σ =
      (nativeStraightening B).map (nativeSimplexRestriction B f σ) ≫
        (nativeSimplexImageIso B m σ).hom := by
  simp only [nativeSimplexChartRestriction, Iso.hom_inv_id_assoc]

/-- Whole original relative chart inclusions commute with their same native simplex restriction maps,
  retaining every original face or degeneracy. -/
theorem nativeRelativeChartRestriction_square (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (A : (Δ[m] : SSet.{u}).Subcomplex) :
    (nativeStraightening B).map (nativeSubcomplexRestriction B f σ A) ≫ nativeSubcomplexChartMap B m σ A =
      nativeSubcomplexChartMap B n (B.map f.op σ) (A.preimage (SSet.stdSimplex.map f)) ≫
        nativeSimplexChartRestriction B f σ := by
  have h := nativeSubcomplexChartRestriction_square B f σ A
  let a := (nativeStraightening B).map
    (nativeSubcomplexInclusion B n (B.map f.op σ) (A.preimage (SSet.stdSimplex.map f)))
  let e := nativeSimplexImageIso B n (B.map f.op σ)
  let g := (nativeStraightening B).map (nativeSimplexRestriction B f σ) ≫ (nativeSimplexImageIso B m σ).hom
  have hc : (a ≫ e.hom) ≫ (e.inv ≫ g) = a ≫ g :=
    (Category.assoc _ _ _).trans (congrArg (fun t => a ≫ t) (e.hom_inv_id_assoc g))
  exact h.trans hc.symm

end SSet.Marked
