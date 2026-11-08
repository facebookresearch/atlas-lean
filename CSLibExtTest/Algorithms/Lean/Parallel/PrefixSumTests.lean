/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.PrefixSum
public meta import CSLibExt.Algorithms.Lean.Parallel.PrefixSum
public import Mathlib.Algebra.FreeMonoid.Basic
public meta import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Parallel prefix sum tests

Executed fixtures: the tabulated Kogge-Stone scan `scanList` with `Nat.clog 2 n` rounds is
compared with sequential prefix products for every length `n ≤ 100`, in the additive monoid
`Multiplicative ℕ` (prefix sums of positive values) and in the noncommutative free monoid on
characters (prefix strings, so the order of the factors is checked); with one round too few it is
shown to be wrong. A 20000-element input checks the tabulated rounds at scale.
Each run throws on a mismatch. The work of the rounds is checked against `n K`. Closed checks
instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Parallel.PrefixSum

/-- Sequential prefix products, for comparison. -/
private meta def seqPrefix {M : Type} [Monoid M] (xs : List M) : List M :=
  (xs.scanl (· * ·) 1).tail

#eval do
  for n in List.range 101 do
    let K := Nat.clog 2 n
    let sums : List (Multiplicative ℕ) :=
      (List.range n).map fun i => Multiplicative.ofAdd (i * i % 7 + 1)
    unless scanList K sums == seqPrefix sums do throw (IO.userError s!"sums wrong for n = {n}")
    let word : List (FreeMonoid Char) :=
      (List.range n).map fun i => FreeMonoid.of (Char.ofNat (97 + i % 26))
    unless (scanList K word).map FreeMonoid.toList == (seqPrefix word).map FreeMonoid.toList do
      throw (IO.userError s!"strings wrong for n = {n}")
    if 2 ≤ n then
      if scanList (K - 1) sums == seqPrefix sums then
        throw (IO.userError s!"{K - 1} rounds already suffice for n = {n}")
    unless work n K ≤ n * K do throw (IO.userError s!"work bound fails for n = {n}")
  IO.println "n = 0..100: Nat.clog 2 n rounds give all prefix sums and prefix strings; \
    one round fewer does not (n ≥ 2)"

-- a long input: each round is a linear lockstep traversal
#eval do
  let n := 20000
  let xs : List (Multiplicative ℕ) := (List.range n).map fun i => Multiplicative.ofAdd (i % 13)
  unless scanList (Nat.clog 2 n) xs == seqPrefix xs do throw (IO.userError "long input wrong")
  IO.println s!"n = {n}: {Nat.clog 2 n} rounds give all prefix sums"

#eval
  let w : List (FreeMonoid Char) := "kogge".toList.map FreeMonoid.of
  IO.println s!"prefixes of \"kogge\": \
    {(scanList 3 w).map fun m => String.ofList (FreeMonoid.toList m)}; \
    work for n = 100: {work 100 7} ≤ {100 * 7}"

/-! Closed checks -/

example (xs : List (FreeMonoid Char)) (i : ℕ) (hi : i < xs.length) :
    (scanList (Nat.clog 2 xs.length) xs).getD i 1 = prefixProd (fun j => xs.getD j 1) i :=
  getD_scanList_eq_prefix xs (Nat.le_pow_clog (by decide) _) hi

#print axioms koggeStone_eq_seg
#print axioms koggeStone_eq_prefix
#print axioms getD_scanList_eq_prefix
#print axioms work_le

end Cslib.Algorithms.Lean.Parallel.PrefixSum
