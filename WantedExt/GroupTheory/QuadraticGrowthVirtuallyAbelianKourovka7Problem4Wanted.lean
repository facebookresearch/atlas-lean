/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups of quadratic growth are almost abelian (Kourovka Notebook Problem 7.4)

Kourovka Notebook, Archive of Solved Problems, Problem 7.4 (V. V. Belyaev): is a finitely generated
group with quadratic growth almost abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import MathlibExt.GroupTheory.GroupGrowth

@[expose] public section

namespace MathlibExt.GroupTheory.QuadraticGrowthVirtuallyAbelianKourovka7Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.4 (V. V.
Belyaev). UnsolvedMath record UM-00700410 (`KOU-7.4`), dataset ulamai/UnsolvedMath v1.8.0.

Growth is MathlibExt's `Group.Generators.growth` for a finite generating family `P` (the number of
elements of word length at most `n`). Quadratic growth is read as growth bounded by `C (n + 1) ^ 2`;
this contains the groups whose growth is of order exactly `n²` and is the stronger statement. Almost
abelian means having an abelian subgroup of finite index.
-/

/-- Kourovka 7.4 (V. V. Belyaev): a finitely generated group of quadratic growth (its growth
function with respect to a finite generating family is at most `C (n + 1) ^ 2`) has an abelian
subgroup of finite index. -/
def quadraticGrowthVirtuallyAbelian : Prop :=
  ∀ (G : Type) [Group G] (ι : Type) [Finite ι] (P : Group.Generators G ι),
    (∃ C : ℕ, ∀ n : ℕ, P.growth n ≤ C * (n + 1) ^ 2) →
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

/--
Resolved true: the Kourovka Archive answers 7.4 "Yes, it is", citing Gromov (1981), by whom a
finitely generated group of polynomial growth is virtually nilpotent, and Wolf (1968) on the growth
of nilpotent and soluble groups. Gromov's theorem itself is
`MathlibExt.GroupTheory.GromovPolynomialGrowthWanted.gromov_polynomial_growth`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.4 (V. V. Belyaev);
resolution: M. Gromov, Groups of polynomial growth and expanding maps, Publ. Math. IHÉS 53 (1981),
53-73; J. A. Wolf, Growth of finitely generated solvable groups and curvature of Riemannian
manifolds, J. Differential Geom. 2 (1968), 421-446, Kourovka Archive, Problem 7.4: Yes, it is
(Gromov; Wolf); Gromov, Main theorem (p. 53): polynomial growth implies a nilpotent subgroup of
finite index; Wolf, Theorem 3.2: growth degree of a virtually nilpotent group,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted quadraticGrowthVirtuallyAbelian_holds : quadraticGrowthVirtuallyAbelian

end MathlibExt.GroupTheory.QuadraticGrowthVirtuallyAbelianKourovka7Problem4Wanted
