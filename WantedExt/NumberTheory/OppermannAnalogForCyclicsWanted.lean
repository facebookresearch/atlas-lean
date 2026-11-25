/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

namespace MetaMathlibExt

@[expose]
public section

/-- **Cohen's Oppermann conjecture for cyclic numbers.** For every natural number $n > 1$ there are
cyclic numbers $c$ and $c'$ with $n^2 - n < c < n^2 < c' < n^2 + n$. Moreover, let $C_L(n)$ and
$C_R(n)$ be the numbers of cyclic numbers in $[n^2 - n, n^2]$ and in $[n^2, n^2 + n]$, and let
$A_L$, $A_R$ and $A$ be the left-hand, right-hand and simplified approximations for cyclic numbers
near squares. Then, as $n \to \infty$ through the natural numbers, $C_L(n) \sim A_L(n)$,
$A_L(n) \sim A(n)$, $C_R(n) \sim A_R(n)$ and $A_R(n) \sim A(n)$.

Source: J. E. Cohen, *Conjectures about Primes and Cyclic Numbers*, J. Integer Seq. 28 (2025),
Article 25.4.1. Stable source identifiers: concept `jis_sem_804f8a678da69b6636b615f6`;
statement `jis_b6b3211114727e0910c9b5bb`, conjecture `conj:Oppermann` and
equations `eq:CyclicsInSquaresUsingPollackLeft` and
`eq:CyclicsInSquaresUsingPollackRight`.
-/
theorem_wanted oppermannAnalogForCyclicNumbers :
    (∀ n : ℕ, 1 < n →
      ∃ c c' : ℕ, IsCyclicNumber c ∧ n ^ 2 - n < c ∧ c < n ^ 2 ∧
        IsCyclicNumber c' ∧ n ^ 2 < c' ∧ c' < n ^ 2 + n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => (oppermannCyclicCountLeft n : ℝ))
      (fun n => oppermannCyclicLeftApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => oppermannCyclicLeftApproximation n)
      (fun n => oppermannCyclicApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => (oppermannCyclicCountRight n : ℝ))
      (fun n => oppermannCyclicRightApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => oppermannCyclicRightApproximation n)
      (fun n => oppermannCyclicApproximation n)

end

end MetaMathlibExt
