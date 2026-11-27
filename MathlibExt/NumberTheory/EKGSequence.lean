/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **The EKG sequence.** A sequence $a_0, a_1, a_2, \dots$ of natural numbers is an EKG
sequence when $a_0 = 1$, $a_1 = 2$, and for every $n \ge 0$ the term $a_{n+2}$ is positive,
differs from each of $a_0, \dots, a_{n+1}$, satisfies $\gcd(a_{n+1}, a_{n+2}) > 1$, and
satisfies $a_{n+2} \le m$ for every positive integer $m$ that differs from each of
$a_0, \dots, a_{n+1}$ and has $\gcd(a_{n+1}, m) > 1$. Thus every term from $a_2$ on is the
least positive integer not used before that shares a factor greater than $1$ with the
previous term.

The indexing starts at $0$, so the source's $a_1 = 1$ and $a_2 = 2$ are $a_0$ and $a_1$ here.
The sequence begins $1, 2, 4, 6, 3, 9, 12, 8, 10, 5, \dots$

Source: JIS source `hofman1.tex`, lines 99–100,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Hofman/hofman1.tex>
(SHA-256 `1aa5911c072e187d31e51d722d7b2dbad3cf7e147ce4e01658e21a09105a2089`;
SHA-256 `a0fe543083e8c48473cd3fa58df152f49aa99d5132f657fd7b0feb3f77c04243`);
first terms at lines 104–112; concept `jis_term_4d5aa413ec3ba8694ef806b3`. -/
public def IsEKGSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧
    a 1 = 2 ∧
      ∀ n : ℕ,
        0 < a (n + 2) ∧
          (∀ i : ℕ, i < n + 2 → a i ≠ a (n + 2)) ∧
            Nat.gcd (a (n + 1)) (a (n + 2)) > 1 ∧
              ∀ m : ℕ,
                0 < m →
                  (∀ i : ℕ, i < n + 2 → a i ≠ m) →
                    Nat.gcd (a (n + 1)) m > 1 → a (n + 2) ≤ m

end

end MetaMathlibExt
