/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups in which elements of equal order are conjugate (Kourovka Notebook Problem 7.48)

Kourovka Notebook, Archive of Solved Problems, Problem 7.48 (S. A. Syskin): suppose that, in a
finite group `G`, each two elements of the same order are conjugate. Is then `|G| ≤ 6`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.SameOrderConjugateSmallGroupKourovka7Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.48 (S. A.
Syskin). UnsolvedMath record UM-00700442 (`KOU-7.48`), dataset ulamai/UnsolvedMath v1.8.0.

Conjugate is Mathlib's `IsConj`; the groups in question are `1`, `ℤ/2` and `S₃`.
-/

/-- Kourovka 7.48 (S. A. Syskin): if any two elements of the same order in a finite group `G` are
conjugate, then `|G| ≤ 6`. -/
def sameOrderConjugateOrderLeSix : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (∀ x y : G, orderOf x = orderOf y → IsConj x y) →
    Nat.card G ≤ 6

/--
Resolved true: the Kourovka Archive answers 7.48 "Yes, it is", modulo the classification of finite
simple groups, citing Fitzpatrick (1985) and Feit and Seitz (1989): the only such groups are `1`,
`ℤ/2` and `S₃`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
7.48 (S. A. Syskin); resolution: P. Fitzpatrick, Order conjugacy in finite groups, Proc. Roy. Irish
Acad. Sect. A 85 (1985), 53-58; W. Feit and G. M. Seitz, On finite rational groups and related
topics, Illinois J. Math. 33 (1989), 103-131, Kourovka Archive, Problem 7.48: Yes, it is, mod CFSG
(Fitzpatrick; Feit and Seitz), https://doi.org/10.1215/ijm/1255988808.
-/
public theorem_wanted sameOrderConjugateOrderLeSix_holds : sameOrderConjugateOrderLeSix

end MathlibExt.GroupTheory.SameOrderConjugateSmallGroupKourovka7Problem48Wanted
