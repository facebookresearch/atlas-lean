/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-469: Let A be the set of positive pseudoperfect numbers minimal under
divisibility. The sum of `1 / n` over `n ∈ A` converges.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.FactorisationProperties
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted

/-! Source record `EP-469`. -/

/-- **Primitive pseudoperfect numbers.** A natural number $n$ lies in $A$, the set of primitive
pseudoperfect numbers, when $n > 0$, $n$ is pseudoperfect (it is positive and equal to the sum of
some set of distinct proper divisors of itself), and no proper divisor of $n$ (a divisor
$m \mid n$ with $m < n$) is pseudoperfect. -/
def InA (n : Nat) : Prop :=
  0 < n ∧ Nat.Pseudoperfect n ∧
    ∀ m, m ∣ n → m < n → ¬Nat.Pseudoperfect m

/-- **Erdős Problem 469 (statement).** The proposition that the reciprocals of the primitive
pseudoperfect numbers have finite sum: the family $(1/n)$, indexed by the natural numbers $n$
that are primitive pseudoperfect, is summable in $\mathbb{R}$. Here $n$ is pseudoperfect if
$n > 0$ and $n$ is the sum of some set of distinct proper divisors of $n$, and primitive
pseudoperfect if moreover no proper divisor of $n$ is pseudoperfect.

Source: [EP-469]. -/
def conjecture : Prop :=
  Summable (fun a : {n : Nat // InA n} => (1 : Real) / (a.val : Real))

/--
**Reciprocals of primitive pseudoperfect numbers have finite sum.** Call a natural number
$n$ pseudoperfect if $n > 0$ and $n$ is the sum of some set of distinct proper divisors of $n$,
and primitive pseudoperfect if moreover no proper divisor of $n$ is pseudoperfect. Then the
family $(1/n)$, indexed by the primitive pseudoperfect numbers $n$, is summable in $\mathbb{R}$,
that is, the sum of $1/n$ over all primitive pseudoperfect numbers $n$ is finite.

This is Erdős Problem 469, resolved true.

Source: plby/lean-proofs, Erdos469.lean, commit 68da20b96673899166e94638f5a7fffeb7231d35 (2026),
https://github.com/plby/lean-proofs/blob/68da20b96673899166e94638f5a7fffeb7231d35/src/latest/ErdosProblems/Erdos469.lean.
Moved from `OpenConjectures/NumberTheory/DivisorSumReciprocalConvergence`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted
