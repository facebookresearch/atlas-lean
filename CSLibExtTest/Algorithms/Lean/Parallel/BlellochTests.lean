/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.Blelloch
public meta import CSLibExt.Algorithms.Lean.Parallel.Blelloch
public import Mathlib.Algebra.FreeMonoid.Basic
public meta import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Blelloch scan tests

Executed fixtures: in the free monoid (concatenation, so the order of the factors is checked),
`blellochList` on the singletons `[0], [1], …, [2 ^ k - 1]` returns the exclusive prefixes
`[], [0], [0, 1], …` for `k = 0, …, 6`; over `ℕ` with `+` (as `Multiplicative ℕ`) it agrees with
the running sums on 50 pseudo-random arrays of length `2 ^ k`, `k ≤ 6`. The work is
`2 ^ (k + 1) - 2` and the span `2 k`. Each run throws on a mismatch. Closed checks instantiate
the theorems.
-/

namespace Cslib.Algorithms.Lean.Parallel.PrefixSum

#eval do
  for k in [0, 1, 2, 3, 4, 5, 6] do
    let n := 2 ^ k
    let xs : List (FreeMonoid ℕ) := (List.range n).map FreeMonoid.of
    let out := (blellochList k xs).map FreeMonoid.toList
    unless out == (List.range n).map List.range do throw (IO.userError s!"k = {k}: {out}")
    unless blellochWork k + 2 == 2 ^ (k + 1) && blellochSpan k == 2 * k do
      throw (IO.userError s!"cost at k = {k}")
  let mut s := 9
  for _ in [0:50] do
    s := (s * 1103515245 + 12345) % 2147483648
    let k := s / 7 % 7
    let mut xs : List ℕ := []
    for _ in [0:2 ^ k] do
      s := (s * 1103515245 + 12345) % 2147483648
      xs := xs ++ [s / 11 % 100]
    let out := (blellochList k (xs.map Multiplicative.ofAdd)).map Multiplicative.toAdd
    let expect := (List.range (2 ^ k)).map fun j => (xs.take j).sum
    unless out == expect do throw (IO.userError s!"sums: {xs} gave {out}")
  IO.println "free monoid, k = 0..6: exclusive prefixes in order; 50 random sum arrays agree; \
    work 2^(k+1) - 2, span 2k"

/-! Closed checks -/

example (xs : List (FreeMonoid ℕ)) (h : xs.length = 2 ^ 5) (j : ℕ) (hj : j < 2 ^ 5) :
    (blellochList 5 xs).getD j 1 = seg (fun i => xs.getD i 1) 0 j :=
  getD_blellochList_eq_seg 5 xs h j hj

#print axioms blelloch_eq_seg
#print axioms getD_blellochList_eq_seg

end Cslib.Algorithms.Lean.Parallel.PrefixSum
