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
# Integral `ℓ`-adic cohomology as the limit of finite-level cohomology

For a proper smooth scheme `X` over an algebraically closed field `k` and a prime `ℓ ≠ char k`, the
reductions `H^i(X, ℤ_ℓ) → H^i(X, ℤ/ℓ^(r+1))` identify the pro-étale cohomology `H^i(X, ℤ_ℓ)`
(Mathlib's `Scheme.EllAdicCohomology`) with the inverse limit of the finite-level groups. The
finite-level groups are finite, so the `lim¹` term vanishes (Mittag-Leffler).

References: Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8;
Stacks 03UT and 09BT.
-/

namespace WantedExt.AlgebraicGeometry.ProEtaleCoefficientComparisonWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

universe u

/-- For `X` proper and smooth over an algebraically closed field and `ℓ ≠ char k`, the map from
`H^i(X, ℤ_ℓ)` to the inverse limit of the `H^i(X, ℤ/ℓ^(r+1))` is bijective. -/
public theorem_wanted comparison_bijective (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (i : ℕ) [IsProper X.hom] [Smooth X.hom]
    (hell : ell ≠ ringChar k) :
    Function.Bijective
      (comparison ell X.left i (reductions_commute ell X.left i))

end WantedExt.AlgebraicGeometry.ProEtaleCoefficientComparisonWanted
