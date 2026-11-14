/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

@[expose] public noncomputable section

/-!
# Integral pro-étale realization and its normalized finite reductions

This packet isolates the coefficient-normalized realization comparison needed
before transporting graded products and arithmetic actions onto Mathlib's
integral pro-étale carrier. It records no independently chosen product.

The comparison sends a class to its actual finite coefficient reductions.
The proper smooth prime-to-characteristic scope is essential for finiteness
and the Mittag–Leffler argument; no unrestricted inverse-limit assertion is
made for arbitrary cohomology towers.

References: Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8;
Stacks 03UT and 09BT. AxiomMath/Stacks implements completed constant sheaves
and pro-étale point comparison, but those generic objects do not identify this
specific Mathlib carrier and all its coefficient-induced projections.
-/

namespace WantedExt.AlgebraicGeometry.ProEtaleCoefficientComparisonWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

universe u

/-- The normalized comparison is bijective in the proper smooth setting.
Its coordinates are fixed by `reduction`; no abstract inverse map is supplied. -/
public theorem_wanted comparison_bijective (ell : ℕ) [Fact ell.Prime]
    [ReductionMaps ell] (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d i : ℕ) [IsProper X.hom]
    [SmoothOfRelativeDimension d X.hom] (hell : ell ≠ ringChar k) :
    Function.Bijective
      (comparison ell X.left i (reductions_commute ell X.left i))

end WantedExt.AlgebraicGeometry.ProEtaleCoefficientComparisonWanted
