/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import MathlibExt.GroupTheory.GroupGrowth

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

/-- **Virtually nilpotent groups have polynomial growth** (Wolf 1968, Bass 1972; the converse of
Gromov's theorem, as recalled in Gromov, *Groups of polynomial growth and expanding maps*, Publ.
Math. IHÉS 53 (1981), p. 54: "If a finitely generated group Γ has a nilpotent subgroup of finite
index then Γ has polynomial growth"). If `G` has a nilpotent subgroup of finite index, every finite
generating family of `G` has polynomial growth. -/
theorem_wanted hasPolynomialGrowth_of_virtuallyNilpotent {G ι : Type*} [Group G] [Finite ι]
    (P : Group.Generators G ι) (H : Subgroup G) (hH : H.FiniteIndex) (hn : Group.IsNilpotent H) :
    P.HasPolynomialGrowth

end MathlibExt.GroupTheory.PolynomialGrowthWanted
