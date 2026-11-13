/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of sparse varieties of groups (Kourovka Notebook Problem 6.16)

Kourovka Notebook, Archive of Solved Problems, Problem 6.16 (A. V. Kuznetsov): a variety is called
sparse if it has at most countably many subvarieties. How many sparse varieties of groups are there?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Continuum
public import WantedExt.GroupTheory.GroupVarietyShared
public import WantedExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SparseVarietiesKourovka6Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.16 (A. V.
Kuznetsov). UnsolvedMath record UM-00700363 (`KOU-6.16`), dataset ulamai/UnsolvedMath v1.8.0.

A variety of groups is represented by its laws, a fully invariant subgroup `N` of `FreeGroup ℕ`
(`IsFullyInvariant` of Kourovka 3.53); the groups of the variety are those satisfying every
word of `N` (`SatisfiesLaws` of the Kourovka 11.21 module). This correspondence is a bijection
reversing inclusion, so subvarieties of the variety with laws `N` correspond to fully invariant `N'
≥ N`, proper ones to `N' > N`. The count is the cardinality of the set of laws of sparse varieties.
-/

open MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted
  (IsFullyInvariant)

/-- Kourovka 6.16 (A. V. Kuznetsov): there are continuum many sparse varieties of groups (varieties
with at most countably many subvarieties). A variety is given by its laws `N`, a fully invariant
subgroup of `FreeGroup ℕ`; its subvarieties are given by the fully invariant `N'` with
`N ≤ N'`. -/
def sparseVarietiesContinuum : Prop :=
  Cardinal.mk {N : Subgroup (FreeGroup ℕ) // IsFullyInvariant N ∧
    {N' : Subgroup (FreeGroup ℕ) | IsFullyInvariant N' ∧ N ≤ N'}.Countable} = Cardinal.continuum

/--
Resolved true: the Kourovka Archive answers 6.16 "There are continuum of such varieties", citing
Kozhevnikov (2000) and Ivanov and Storozhev (2004): there are exactly continuum many varieties of
groups with at most countably many subvarieties. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 6.16 (A. V. Kuznetsov); resolution: P. A. Kozhevnikov, On
varieties of groups of large odd exponent, Dep. 1612-V00, VINITI, Moscow, 2000 (Russian); S. V.
Ivanov and A. M. Storozhev, On varieties of groups in which all periodic groups are abelian,
Contemp. Math. 360 (2004), 55-62, Ivanov-Storozhev construct uncountably many varieties with only
countably many subvarieties (zbMATH review Zbl 1082.20016); Kourovka Archive, Problem 6.16: There
are continuum of such varieties (Kozhevnikov; Ivanov, Storozhev),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sparseVarietiesContinuum_holds : sparseVarietiesContinuum

end MathlibExt.GroupTheory.SparseVarietiesKourovka6Problem16Wanted
