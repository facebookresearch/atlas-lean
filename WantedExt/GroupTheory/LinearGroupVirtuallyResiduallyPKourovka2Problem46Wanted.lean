/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Matrix groups that are virtually residually finite p-groups (Kourovka Notebook Problem 2.46)

Kourovka Notebook, Archive of Solved Problems, Problem 2.46 (Yu. I. Merzlyakov): find conditions
under which a finitely generated matrix group is almost residually a finite `p`-group for some prime
`p`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.LinearGroupVirtuallyResiduallyPKourovka2Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.46 (Yu. I.
Merzlyakov). UnsolvedMath record UM-00700119 (`KOU-2.46`), dataset ulamai/UnsolvedMath v1.8.0.

Matrix groups are subgroups of `GLₙ(K)` for a (commutative) field `K`; almost residually a finite
`p`-group means having a subgroup of finite index in which every non-identity element survives in
some finite `p`-group quotient, that is, lies outside a normal subgroup of `p`-power index:
`IsResiduallyFiniteP` of `KourovkaNotebookShared`, reused here (the two readings agree for prime
`p`, and both targets assume `p` prime). The Archive's answer is that no condition is needed; it is
stated as two targets, by characteristic. In characteristic `0` the subgroup of finite index may
depend on `p` (`∀ᶠ p, ∃ H`), the reading under which the cited theorems hold (for `SLₙ(ℤ)`, `n ≥ 3`,
no subgroup of finite index is residually `p` for infinitely many `p`).
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsResiduallyFiniteP)

/-- Deprecated: `H` is residually a finite `p`-group in quotient form, every non-identity element
surviving in some finite `p`-group quotient of `H`. For prime `p` it is equivalent to
`KourovkaNotebookShared.IsResiduallyFiniteP`, which the statements below now use; the two differ
for non-prime `p`. -/
@[deprecated "Use `KourovkaNotebookShared.IsResiduallyFiniteP` (equivalent for prime `p`)."
  (since := "2026-10-23")]
def IsResiduallyFinitePGroup (p : ℕ) (H : Type) [Group H] : Prop :=
  ∀ h : H, h ≠ 1 → ∃ (N : Subgroup H) (_ : N.Normal), h ∉ N ∧ Finite (H ⧸ N) ∧
    IsPGroup p (H ⧸ N)

/-- Deprecated: the matrix group `G ≤ GLₙ(K)` has a subgroup of finite index that is residually a
finite `p`-group in quotient form (`IsResiduallyFinitePGroup`). For prime `p` it is equivalent to
`IsVirtuallyResiduallyFiniteP`, which the statements below now use; the two differ for non-prime
`p`. -/
@[deprecated "Use `IsVirtuallyResiduallyFiniteP` (equivalent for prime `p`)."
  (since := "2026-10-23")]
def IsVirtuallyResiduallyFinitePGroup (p : ℕ) {K : Type} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsResiduallyFinitePGroup p H

/-- The matrix group `G ≤ GLₙ(K)` has a subgroup of finite index that is residually a finite
`p`-group (`IsResiduallyFiniteP`; both statements below apply it for prime `p` only). -/
def IsVirtuallyResiduallyFiniteP (p : ℕ) {K : Type} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsResiduallyFiniteP p H

/-- Kourovka 2.46 (Yu. I. Merzlyakov), characteristic zero: a finitely generated matrix group over
a field of characteristic `0` has, for all but finitely many primes `p`, a subgroup of finite
index that is residually a finite `p`-group. -/
def charZeroLinearVirtuallyResiduallyP : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), Group.FG G →
    ∀ᶠ p in Filter.atTop, p.Prime → IsVirtuallyResiduallyFiniteP p G

/-- Kourovka 2.46, characteristic `p > 0`: a finitely generated matrix group over a field of
characteristic `p` has a subgroup of finite index that is residually a finite `p`-group. -/
def charPLinearVirtuallyResiduallyP : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (K : Type) [Field K] [CharP K p] (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), Group.FG G →
    IsVirtuallyResiduallyFiniteP p G

/--
Resolved true: the Kourovka Archive records that a finitely generated matrix group over a field of
characteristic `0` has, for almost all primes `p`, a subgroup of finite index that is residually a
finite `p`-group (Kargapolov; Merzlyakov, 1967; Platonov, 1968). Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.46 (Yu. I. Merzlyakov); resolution:
M. I. Kargapolov, Algebra i Logika 6 (1967), no. 5, 17-20; Yu. I. Merzlyakov, Soviet Math. Dokl. 8
(1967), 1538-1541; V. P. Platonov, Dokl. Akad. Nauk Belarus. SSR 12 (1968), no. 6, 492-494; A. I.
Tokarenko, Proc. Riga Algebr. Sem., 1969, 280-281, Kourovka Archive, Problem 2.46: a finitely
generated matrix group over a field of characteristic zero has a subgroup of finite index which is
residually a finite p-group for almost all primes p (Kargapolov, Merzlyakov, Platonov); over a field
of characteristic p > 0 it has a subgroup of finite index which is residually a finite p-group
(Platonov, Tokarenko), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted charZeroLinearVirtuallyResiduallyP_holds : charZeroLinearVirtuallyResiduallyP

/--
Resolved true: the Kourovka Archive records that a finitely generated matrix group over a field of
characteristic `p > 0` has a subgroup of finite index that is residually a finite `p`-group
(Platonov, 1968; Tokarenko, 1969). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 2.46 (Yu. I. Merzlyakov); resolution: M. I. Kargapolov, Algebra i Logika 6 (1967),
no. 5, 17-20; Yu. I. Merzlyakov, Soviet Math. Dokl. 8 (1967), 1538-1541; V. P. Platonov, Dokl. Akad.
Nauk Belarus. SSR 12 (1968), no. 6, 492-494; A. I. Tokarenko, Proc. Riga Algebr. Sem., 1969,
280-281, Kourovka Archive, Problem 2.46: a finitely generated matrix group over a field of
characteristic zero has a subgroup of finite index which is residually a finite p-group for almost
all primes p (Kargapolov, Merzlyakov, Platonov); over a field of characteristic p > 0 it has a
subgroup of finite index which is residually a finite p-group (Platonov, Tokarenko),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted charPLinearVirtuallyResiduallyP_holds : charPLinearVirtuallyResiduallyP

end MathlibExt.GroupTheory.LinearGroupVirtuallyResiduallyPKourovka2Problem46Wanted
