/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 825
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.FactorisationProperties

@[expose] public section

open scoped ArithmeticFunction.sigma

namespace MathlibExt.NumberTheory.ErdosProblem825Wanted

/-! Source record `FC-ErdosProblem825`, ported from FormalConjectures
`ErdosProblems/825.lean` and checked against erdosproblems.com/825.
The upstream `answer(True)` is dropped. Status: resolved true externally
(Larsen); this repository records the statement but not a Lean proof. -/

/-- **Erdős Problem 825.** Write $\sigma(n)$ for the sum of the positive divisors of a positive
integer $n$, and call $n$ pseudoperfect if $n$ is the sum of the elements of some set of proper
divisors of $n$. The statement is the conjunction of two claims: there is a real $C > 0$ such
that every positive integer $n$ with $\sigma(n) > Cn$ is pseudoperfect, and every real $C > 0$
with this property satisfies $C > 2$. -/
def conjecture : Prop :=
  (∃ (C : ℝ) (_ : C > 0),
    ∀ (n) (_ : σ 1 n > C * n),
      Nat.Pseudoperfect n) ∧
  (∀ (C : ℝ), 0 < C →
    (∀ (n : ℕ) (_ : σ 1 n > C * n),
      Nat.Pseudoperfect n) →
    2 < C)

/--
**Erdős Problem 825 is true.** Write $\sigma(n)$ for the sum of the positive divisors of a
positive integer $n$, and call $n$ pseudoperfect if $n$ is the sum of the elements of some set
of proper divisors of $n$. Then there is a real $C > 0$ such that every positive integer $n$
with $\sigma(n) > Cn$ is pseudoperfect, and every real $C > 0$ with this property satisfies
$C > 2$.

Source: Daniel Larsen, Sufficiently abundant numbers are
pseudoperfect (repository commit 18411fce83ce49ee0adbb628de04603e003004f5; PDF blob
e0f990064466e347dea348bc2c6108cbd6a5c906),
https://github.com/Larsen-Daniel/Erdos-825/blob/18411fce83ce49ee0adbb628de04603e003004f5/825.pdf.
Moved from `OpenConjectures/NumberTheory/ErdosProblem825`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem825Wanted
