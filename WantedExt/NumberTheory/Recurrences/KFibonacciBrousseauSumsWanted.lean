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
public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSum
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

end

end MetaMathlibExt
