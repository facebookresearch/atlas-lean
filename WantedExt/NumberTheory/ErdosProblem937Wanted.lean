/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 937
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.KFull

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem937Wanted

/-! Source record `FC-ErdosProblem937`, ported from FormalConjectures
`ErdosProblems/937.lean` (`def IsCoprimePowerfulAP4`,
`theorem erdos_937`) and checked against erdosproblems.com/937. The
upstream `answer(True)` is dropped; the right-hand side is stated
directly. The canonical `Nat.IsKFull 2` predicate is reused. Status:
resolved true (Bajpai–Bennett–Chan [BBC24]); the registry links a
proof-bearing external Lean development. -/

/-- **Four-term progressions of pairwise coprime powerful numbers.** For natural numbers $a$ and
$d$, the numbers $a$, $a + d$, $a + 2d$, $a + 3d$ form a four-term arithmetic progression of
pairwise coprime powerful numbers when $d > 0$, each of the four numbers is powerful (that is,
$2$-full: nonzero and divisible by $p^2$ for every prime $p$ dividing it), and any two of the
four numbers are coprime. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  Nat.IsKFull 2 a ∧ Nat.IsKFull 2 (a + d) ∧ Nat.IsKFull 2 (a + 2 * d) ∧
  Nat.IsKFull 2 (a + 3 * d) ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

/-- **Statement of Erdős Problem 937.** There are infinitely many pairs of natural numbers
$(a, d)$ with $d > 0$ such that the four numbers $a$, $a + d$, $a + 2d$, $a + 3d$ are powerful
(each is nonzero and divisible by $p^2$ for every prime $p$ dividing it) and pairwise coprime;
that is, infinitely many four-term arithmetic progressions of pairwise coprime powerful numbers. -/
def conjecture : Prop :=
  {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite

/--
**Erdős Problem 937 holds (Bajpai–Bennett–Chan).** There are infinitely many pairs of natural
numbers $(a, d)$ with $d > 0$ such that the four numbers $a$, $a + d$, $a + 2d$, $a + 3d$ are
powerful (each is nonzero and divisible by $p^2$ for every prime $p$ dividing it) and pairwise
coprime. That is, there are infinitely many four-term arithmetic progressions of pairwise coprime
powerful numbers.

Source: Prajeet Bajpai, Michael A. Bennett, and Tsz Ho Chan, Arithmetic
progressions in squarefull numbers, International Journal of Number Theory 20 (2024), 19–45,
https://mathscinet.ams.org/mathscinet-getitem?mr=4688726. Moved from
`OpenConjectures/NumberTheory/ErdosProblem937`. Resolved true: Resolved true by
Bajpai–Bennett–Chan; a proof is available in an external Lean development.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem937Wanted
