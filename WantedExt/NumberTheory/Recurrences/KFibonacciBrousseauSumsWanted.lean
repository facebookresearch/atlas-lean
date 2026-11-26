/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.Recurrences.FibonacciBrousseauSums
public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
public import MathlibExt.NumberTheory.Recurrences.KFibonacciShiftedBrousseauSum
public import MathlibExt.NumberTheory.Recurrences.PellBrousseauOdd
public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSumsKFibonacciPowerConvolution

/-!
# Brousseau sums of k-Fibonacci numbers

Statements from Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau
Sums*, Journal of Integer Sequences 27 (2024), Article 24.6.4.

The `k`-Fibonacci numbers `F_{k,n}` (`F_{k,0} = 0`, `F_{k,1} = 1`,
`F_{k,n} = k F_{k,n-1} + F_{k,n-2}`) are the Lucas sequence `U(k, -1)`,
`lucasU ⟨k, -1, _⟩`; the Fibonacci, Lucas and Pell numbers are `Nat.fib`, `lucasNumber` and
`pellNumber`, and the Pell–Lucas numbers `Q_n` (`Q_0 = Q_1 = 2`) are `lucasV ⟨2, -1, _⟩`.
The paper takes `k` a positive integer; the identities are stated for every nonzero integer
`k` (every integer `k` in Theorem 1).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Brousseau sums of $k$-Fibonacci numbers.** For an integer $k$, let $F_{k,n}$ be the
$k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$ ($F_{k,0} = 0$, $F_{k,1} = 1$,
$F_{k,n+2} = k F_{k,n+1} + F_{k,n}$), and let $C_k^{(p)}$ be the coefficient polynomials. For
every nonzero integer $k$ and all $n, p \ge 0$,
$$
k \sum_{i=0}^{n} i^p F_{k,i} = C_k^{(p)}(n) F_{k,n+1} + C_k^{(p)}(n+1) F_{k,n} - C_k^{(p)}(0),
$$
where $0^0 = 1$.

The paper assumes $k \ge 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 6 (`jis-2024-24.6.4-thm-6`). -/
public theorem_wanted kFibonacci_brousseau_sum (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ i =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ n - brousseauCoeff k p 0

end

end MetaMathlibExt
