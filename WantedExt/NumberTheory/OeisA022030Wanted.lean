/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OEIS A022030
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA022030Wanted

/-! Source record `FC-OeisA022030`, ported from FormalConjectures
`OEIS/22030.lean` and checked against oeis.org/A022030. A nonlinear
recurrence sequence (core Lean only). Test evaluations omitted (proofs
live upstream). Status: resolved true (Barker's linear recurrence holds;
formal proof upstream). -/

/-- **The sequence OEIS A022030.** The sequence of natural numbers with $a(0) = 4$, $a(1) = 16$ and,
for every natural number $n$, $a(n + 2) = \lfloor (a(n + 1)^2 + a(n) - 1) / a(n) \rfloor - 1$ if
$n$ is even and $a(n + 2) = \lfloor a(n + 1)^2 / a(n) \rfloor + 1$ if $n$ is odd. -/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

/-- **Barker's linear recurrence for A022030.** The statement that for every natural number
$n \ge 4$, the sequence $a$ of OEIS A022030 satisfies $a(n) = 4a(n - 1) - a(n - 3) + a(n - 4)$,
with the subtraction taken in the natural numbers (truncated at $0$). -/
def conjecture : Prop :=
  ∀ (n : ℕ) (_hn : 4 ≤ n),
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

/--
**Barker's linear recurrence for A022030 holds.** For every natural number $n \ge 4$, the
sequence $a$ of OEIS A022030 satisfies $a(n) = 4a(n - 1) - a(n - 3) + a(n - 4)$, with the
subtraction taken in the natural numbers (truncated at $0$).

Source: Kenta
Kitamura, Lean formal proof of Barker's linear recurrence,
https://github.com/KitaKen1/oeis-a022030-lean/blob/f74afc2/lean/OeisA022030FC.lean#L270-L275.
Moved from `OpenConjectures/NumberTheory/OeisA022030`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.OeisA022030Wanted
