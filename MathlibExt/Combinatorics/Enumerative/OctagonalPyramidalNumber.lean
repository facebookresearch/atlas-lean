/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Octagonal pyramidal numbers

The enumerative interpretation comes from Milan Janjić, *Binomial
Coefficients and Enumeration of Restricted Words*, Journal of Integer
Sequences 19 (2016), Article 16.7.3.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Octagonal pyramidal numbers.** For a natural number $k$, the $k$-th octagonal pyramidal
number is $k(k+1)(2k-1)/2$. -/
def octagonalPyramidalNumber (k : ℕ) : ℕ :=
  k * (k + 1) * (2 * k - 1) / 2

/-- **Compositions avoiding parts 2, 3 and 4.** For a natural number $k$, the restricted
compositions of $k + 14$ are the ordered compositions of $k + 14$ into $k$ positive parts with no
part equal to $2$, $3$ or $4$, that is, the tuples $(c_1, \dots, c_k)$ of positive integers with
$c_1 + \dots + c_k = k + 14$ and $c_i \notin \{2, 3, 4\}$ for every $i$.

Source: concept `jis_sem_775e702cd81d5e5e2661ccc9`, statement `jis_4f77f6102ca88eba755447c5`.
-/
def octagonalPyramidalCompositions (k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 (k + 14) \ {2, 3, 4}).filter
    fun c => ∑ i, c i = k + 14

end

end MetaMathlibExt
