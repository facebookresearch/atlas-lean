/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public noncomputable section

/-!
# Integral compactly supported `ℓ`-adic cohomology as a limit

For a separated scheme `X` of finite type over an algebraically closed field `k`, a prime `ℓ`
invertible in `k`, and a compactification of `X`, the reductions identify compactly supported
cohomology with coefficients `ℤ_ℓ` (computed in the compactification,
`ContinuousAdicCompactSupports`) with the inverse limit of compactly supported cohomology with
coefficients `ℤ/ℓ^(r+1)`: the finite-level groups are finite, so the `lim¹` term vanishes.

Authors of the mathematical source: Bhargav Bhatt, Peter Scholze.
Source: The pro-étale topology for schemes, §6.8,
https://arxiv.org/abs/1309.1198; Stacks Tags 03UT, 09AH and 09BT.
-/

namespace WantedExt.AlgebraicGeometry.ContinuousAdicCompactSupports

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

universe u

/-- **Compactly supported ℓ-adic cohomology as a limit of finite levels.** Let $k$ be an
algebraically closed field, $ℓ$ a prime invertible in $k$, $X$ a separated $k$-scheme of finite type
(locally of finite type and quasi-compact) and `c` a chosen compactification of $X$. Then for every
$n$, the reduction map from $H^n_c(X, \mathbb Z_ℓ)$, computed in `c`, to the inverse limit of the
groups $H^n_c(X, \mathbb Z/ℓ^{r+1})$ is bijective. -/
public theorem_wanted compactSupportLimitComparison_bijective
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] (ellInvertible : (ell : k) ≠ 0)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (c : ClosedCompactification X) (n : ℕ) :
    Function.Bijective (compactSupportLimitComparison ell c n)

end WantedExt.AlgebraicGeometry.ContinuousAdicCompactSupports
