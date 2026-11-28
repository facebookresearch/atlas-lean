/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large normal subsets whose square is not the whole group (Kourovka Notebook Problem 20.74)

Kourovka Notebook, Problem 20.74 (L. Pyber), marked solved in the 21st issue: (a) conjecture: there
are only finitely many nonabelian finite simple groups `G` that have a normal subset `S` closed
under inversion such that `|S| > |G| / log₂ |G|` and `S² ≠ G`. (b) The same conjecture for the
groups `PSL(2, p)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74

@[expose] public section

namespace MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.74 (L. Pyber). UnsolvedMath record
UM-00701732 (`KOU-20.74`), dataset ulamai/UnsolvedMath v1.8.0.

A normal subset is closed under conjugation. "Only finitely many groups" (up to isomorphism) is
stated as a bound on their orders, which is equivalent since there are finitely many groups of each
order; for (b) it is a bound on the prime `p`, with `PSL(2, p) = Matrix.ProjectiveSpecialLinearGroup
(Fin 2) (ZMod p)`.
-/

end MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
