/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Generalized Leonardo numbers

The generalized Leonardo sequence has initial values one and constant term `k` in its recurrence.
The companion sequence is determined by sums of pairs of generalized Leonardo numbers.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Leonardo numbers.** For an integer $k$, the generalized Leonardo numbers
$L_{k,0}, L_{k,1}, L_{k,2}, \ldots$ are the integers defined by $L_{k,0} = L_{k,1} = 1$ and
$L_{k,n+2} = L_{k,n+1} + L_{k,n} + k$ for all $n \ge 0$.

The paper takes $k$ positive; here $k$ may be any integer.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly 62.3 (2024), introduction. -/
public def genLeonardo (k : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => genLeonardo k (n + 1) + genLeonardo k n + k

/-- **Generalized Leonardo number of index two.** For every integer $k$, the generalized
Leonardo number $L_{k,2}$ equals $2 + k$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardo_two (k : ℤ) : genLeonardo k 2 = 2 + k := rfl

/-- **Dual generalized Leonardo numbers.** For an integer $k$, let $L_{k,n}$ denote the generalized
Leonardo numbers. The dual generalized Leonardo numbers $M_{k,n}$, for natural numbers $n$, are
defined by $M_{k,0} = 1 - k$ and $M_{k,n+1} = L_{k,n} + L_{k,n+2}$, so that
$M_{k,n} = L_{k,n-1} + L_{k,n+1}$ for $n \ge 1$.

This agrees with the paper's Definition 2.1, which sets $M_{k,0} = 1 - k$, $M_{k,1} = k + 3$, and
$M_{k,n+1} = M_{k,n} + M_{k,n-1} + 2k$ for $n \ge 1$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*,
Fibonacci Quarterly 62.3 (2024), Definition 2.1 and identity (2.1). -/
public def genLeonardoCompanion (k : ℤ) : ℕ → ℤ
  | 0 => 1 - k
  | n + 1 => genLeonardo k n + genLeonardo k (n + 2)

/-- **The dual generalized Leonardo number of index one.** For every integer $k$, the dual
generalized Leonardo number $M_{k,1}$ equals $3 + k$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardoCompanion_one (k : ℤ) :
    genLeonardoCompanion k 1 = 3 + k := by
  change genLeonardo k 0 + genLeonardo k 2 = 3 + k
  have h0 : genLeonardo k 0 = 1 := rfl
  rw [h0, genLeonardo_two]
  ring

end

end MetaMathlibExt
