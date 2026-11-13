/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite simple characteristic quotients of free groups (Kourovka Notebook Problem 6.45)

Kourovka Notebook, Problem 6.45 (J. Wiegold), marked solved in the 21st issue: construct a
characteristic subgroup N of a finitely generated free group F such that F/N is infinite and simple.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupCharacteristicSimpleQuotientKourovka6Problem45Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 6.45 (J. Wiegold). UnsolvedMath record
UM-00700388 (`KOU-6.45`), dataset ulamai/UnsolvedMath v1.8.0.

The target is the resolving theorem for every rank `n ≥ 2` (the problem asks for one free group of
finite rank; rank `1` has no infinite simple quotient). Characteristic is Mathlib's
`Subgroup.Characteristic`; the normality needed for the quotient is bound explicitly.
-/

/-- Kourovka 6.45 (J. Wiegold): for every `n ≥ 2` the free group of rank `n` has a characteristic
subgroup `N` with `F ⧸ N` infinite and simple. -/
def freeGroupInfiniteSimpleCharacteristicQuotient : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (N : Subgroup (FreeGroup (Fin n))) (_ : N.Normal), N.Characteristic ∧
    Infinite (FreeGroup (Fin n) ⧸ N) ∧ IsSimpleGroup (FreeGroup (Fin n) ⧸ N)

/--
Resolved true: Coulon and Fournier-Facio, Theorem 1.1 (Corollary 4.2), prove that for all `n ≥ 2`
the free group of rank `n` has continuum many pairwise non-isomorphic infinite simple characteristic
quotients; the 21st issue marks 6.45 solved. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 6.45 (J. Wiegold); resolution: R. Coulon and F. Fournier-Facio, Infinite simple
characteristic quotients, arXiv:2312.11684, Theorem 1.1 (Corollary 4.2): for all n ≥ 2 the free
group of rank n admits continuum many pairwise non-isomorphic, 2-generated, infinite, simple,
characteristic quotients; marked solved in the 21st issue of the Kourovka Notebook,
https://arxiv.org/abs/2312.11684.
-/
public theorem_wanted freeGroupInfiniteSimpleCharacteristicQuotient_holds :
    freeGroupInfiniteSimpleCharacteristicQuotient

end MathlibExt.GroupTheory.FreeGroupCharacteristicSimpleQuotientKourovka6Problem45Wanted
