/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertion

/-!
# Actual universal determination by the distinguished fixed-front simplex

Every resolving simplex is an actual operator of the distinguished
successor simplex. The genuine realization adjunction therefore detects
the equality of whole enriched functors from their distinguished
insertion. No assumed Hom chart or quotient normal form is needed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontInsertionExt
open SimplicialEnrichment FixedFrontInsertion

/-- Whole enriched maps out of the actual fixed-front realization are determined by their original
  distinguished successor simplex. -/
theorem functor_ext (n : ℕ) {C : Carrier.{u}}
    (F G : realization (FixedFrontCollapse.object.{u} n) ⟶ C)
    (h : FixedFrontInsertion.functor n ≫ F = FixedFrontInsertion.functor n ≫ G) : F = G := by
  apply (realizationAdjunction.homEquiv (FixedFrontCollapse.object n) C).injective
  ext q σ
  induction q using Opposite.rec with
  | _ m =>
    induction σ using _root_.Quotient.inductionOn with
    | _ a =>
      change simplexInto (FixedFrontCollapse.object n) ((FixedFrontCollapse.projection
        n).app (op m) a) ≫ F =
        simplexInto (FixedFrontCollapse.object n) ((FixedFrontCollapse.projection n).app (op
          m) a) ≫ G
      have ha := projected_functor n a
      exact (congrArg (fun H => H ≫ F) ha).symm.trans
        ((Category.assoc (coherentSimplexMap a.down) (FixedFrontInsertion.functor n) F).trans
          ((congrArg (fun H => coherentSimplexMap a.down ≫ H) h).trans
            ((Category.assoc (coherentSimplexMap a.down) (FixedFrontInsertion.functor n)
              G).symm.trans
              (congrArg (fun H => H ≫ G) ha))))

end CategoryTheory.CoherentRealization.FixedFrontInsertionExt
