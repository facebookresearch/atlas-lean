/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Even Fibonacci pseudoprimes (Guy, Unsolved Problems in Number Theory, A12)

Guy, Unsolved Problems in Number Theory, Section A12: does there exist an even Fibonacci
pseudoprime? A Fibonacci pseudoprime of the first kind is a composite `n` with `L_n ≡ 1 (mod n)`,
where `L_n` are the Lucas numbers.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.LucasSequence

@[expose] public section

namespace MathlibExt.NumberTheory.EvenFibonacciPseudoprimeGuyProblemA12cWanted

/-!
Source: R. K. Guy, Unsolved Problems in Number Theory, Section A12 (even Fibonacci pseudoprimes; L.
Somer), as recorded in the UnsolvedMath problem GUY-A12c. UnsolvedMath record UM-00001877
(`GUY-A12c`), dataset ulamai/UnsolvedMath v1.8.0.

The record defines Fibonacci pseudoprimes of the `m`-th kind as odd composite `n` with
`V_n(m, -1) ≡ m (mod n)` and then asks for an even one; the oddness clause is dropped, since
otherwise the question is vacuous. The record cites Somer's bound for even Fibonacci pseudoprimes,
which concerns the first kind (`m = 1`, `V_n(1, -1) = L_n`), the standard reading; for other
parameters `m` even examples exist (Di Porto, after Proposition 2: for `k > 1`, `2^k` is a Fibonacci
pseudoprime of the `(2^k - 1)`-th kind), so the target uses the first kind. Composite means `1 < n`
and `n` not prime. The Lucas numbers `L₀ = 2`, `L₁ = 1`, `L_{n+2} = L_{n+1} + L_n` are
`MetaMathlibExt.lucasNumber`.
-/

/-- There is an even Fibonacci pseudoprime of the first kind: an even composite `n` with
`L_n ≡ 1 (mod n)`. -/
def existsEvenFibonacciPseudoprime : Prop :=
  ∃ n : ℕ, Even n ∧ 1 < n ∧ ¬ n.Prime ∧ MetaMathlibExt.lucasNumber n ≡ 1 [MOD n]

/--
Resolved false: Di Porto proves that there are no even Fibonacci pseudoprimes of the first kind,
that is, no even composite `n` with `L_n ≡ 1 (mod n)`. Source: R. K. Guy, Unsolved Problems in
Number Theory, Section A12 (even Fibonacci pseudoprimes; L. Somer), as recorded in the UnsolvedMath
problem GUY-A12c; resolution: A. Di Porto, Nonexistence of even Fibonacci pseudoprimes of the 1st
kind, Fibonacci Quart. 31 (1993), no. 2, 173-177, Theorem (Section 1): there do not exist even
Fibonacci pseudoprimes of the 1st kind, defined there as composite integers n with L_n ≡ 1 (mod n),
https://www.fq.math.ca/Scanned/31-2/diporto.pdf.
-/
public theorem_wanted existsEvenFibonacciPseudoprime_refuted : ¬ existsEvenFibonacciPseudoprime

end MathlibExt.NumberTheory.EvenFibonacciPseudoprimeGuyProblemA12cWanted
