/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.VirtuallyNilpotentGrowth

/-!
# Gromov's polynomial growth theorem

M. Gromov, *Groups of polynomial growth and expanding maps*, Publ. Math. IHÉS 53 (1981), 53-73.
The introduction (p. 54) defines polynomial growth (`#B(r) ≤ C r^d` for `r ≥ 1`, which for word
balls is equivalent to `Group.Generators.HasPolynomialGrowth`'s `γ(n) ≤ C (n + 1)^d`), recalls that
a finitely generated group with a nilpotent subgroup of finite index has polynomial growth
(Wolf, Bass, Guivarc'h; Tits's appendix), and states the Main theorem: the converse.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PolynomialGrowthWanted

/-- **Gromov's polynomial growth theorem.** If a group `G` has a finite generating family `P` of
polynomial growth, then `G` has a nilpotent subgroup of finite index (Gromov, *Groups of polynomial
growth and expanding maps*, Publ. Math. IHÉS 53 (1981), Main theorem, p. 54; proof in §8). -/
theorem_wanted virtuallyNilpotent_of_hasPolynomialGrowth {G ι : Type*} [Group G] [Finite ι]
    (P : Group.Generators G ι) (h : P.HasPolynomialGrowth) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsNilpotent H

end MathlibExt.GroupTheory.PolynomialGrowthWanted
