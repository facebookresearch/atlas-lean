/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.StringMatching.RabinKarp
public import CSLibExt.Algorithms.Lean.StringMatching.RabinKarp

@[expose] public section

set_option autoImplicit false

open Cslib.Algorithms.Lean.TimeM

private meta def verify (name : String) (d q : Nat) (pattern text expected : List Nat)
    (operations : Nat) (hq : 0 < q) : IO Unit := do
  let result := rabinKarpMatches d q pattern text hq
  if result.ret != expected || result.time != operations then
    throw <| IO.userError s!"{name}: got shifts={result.ret}, operations={result.time}"
  IO.println s!"{name}: shifts={result.ret}, operations={result.time}"

-- Literal expectations come from the source figures and independently counted primitive operations.
#eval do
  verify "CLRS Figure 32.4" 10 13 [ 3, 1, 4, 1, 5 ]
    [ 2, 3, 5, 9, 0, 2, 3, 1, 4, 1, 5, 2, 6, 7, 3, 9, 9, 2, 1 ] [ 6 ] 161 (by decide)
  verify "CLRS exercise 32.2-1" 10 11 [ 2, 6 ]
    [ 3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3 ] [ 6 ] 141 (by decide)
  verify "borrow-sensitive final match" 10 13 [ 0, 0, 1, 1, 2 ]
    [ 3, 0, 0, 1, 1, 2 ] [ 1 ] 54 (by decide)
  verify "overlapping matches" 10 13 [ 1, 1 ]
    [ 1, 1, 1 ] [ 0, 1 ] 28 (by decide)
  verify "final alignment" 10 13 [ 2, 3 ]
    [ 9, 9, 2, 3 ] [ 2 ] 36 (by decide)
  verify "first-symbol hash-hit mismatch" 10 1 [ 1, 2 ]
    [ 9, 9, 9 ] [  ] 26 (by decide)
  verify "last-symbol hash-hit mismatch" 10 1 [ 1, 1, 2 ]
    [ 1, 1, 1, 1 ] [  ] 38 (by decide)
  verify "no hash hits" 10 13 [ 1, 2 ]
    [ 4, 4, 4 ] [  ] 24 (by decide)
  verify "late spurious hit" 10 3 [ 1, 2, 3 ]
    [ 1, 2, 6 ] [  ] 27 (by decide)
  verify "one-symbol pattern" 10 13 [ 7 ]
    [ 7, 1, 7 ] [ 0, 2 ] 26 (by decide)
  verify "equal lengths" 10 13 [ 1, 2, 3 ]
    [ 1, 2, 3 ] [ 0 ] 27 (by decide)
  verify "empty pattern boundaries" 10 13 [  ]
    [ 1, 2 ] [ 0, 1, 2 ] 0 (by decide)
  verify "empty pattern and text" 10 13 [  ]
    [  ] [ 0 ] 0 (by decide)
  verify "nonempty pattern empty text" 10 13 [ 1, 2 ]
    [  ] [  ] 3 (by decide)
  verify "overlength attempted setup" 10 13 [ 1, 2, 3 ]
    [ 1, 2 ] [  ] 17 (by decide)
  verify "leading-zero overlapping words" 10 13 [ 0, 0 ]
    [ 0, 0, 0 ] [ 0, 1 ] 28 (by decide)
  verify "radix zero arbitrary digits" 0 13 [ 8, 2 ]
    [ 7, 2, 8, 2 ] [ 2 ] 35 (by decide)
  verify "radix one source unary alphabet" 1 2 [ 0, 0 ]
    [ 0, 0, 0 ] [ 0, 1 ] 28 (by decide)
  verify "radix one arbitrary symbols" 1 5 [ 1, 2 ]
    [ 2, 1, 2 ] [ 1 ] 27 (by decide)
  verify "modulus one core" 10 1 [ 4, 5 ]
    [ 4, 5, 4, 5 ] [ 0, 2 ] 37 (by decide)
  verify "smallest prime" 2 2 [ 1 ]
    [ 0, 1, 1, 0 ] [ 1, 2 ] 34 (by decide)
  verify "fixed-prime all-spurious countermodel" 2 3 [ 0, 0 ]
    [ 1, 1, 1, 1 ] [  ] 37 (by decide)

-- Canonical window hashes distinguish source spurious hits from exact reported matches.
#guard Nat.ofDigits 10 ([3, 1, 4, 1, 5] : List Nat).reverse % 13 = 7
#guard Nat.ofDigits 10 ([6, 7, 3, 9, 9] : List Nat).reverse % 13 = 7
#guard Nat.ofDigits 10 ([0, 0, 1, 1, 2] : List Nat).reverse % 13 = 8
#guard Nat.ofDigits 10 ([3, 0, 0, 1, 1] : List Nat).reverse % 13 = 7
#guard ((7 + 13 - 3 * (10 ^ 4 % 13) % 13) * 10 + 2) % 13 = 8
#guard ((7 - 3 * (10 ^ 4 % 13) % 13) * 10 + 2) % 13 = 2

-- Primality and valid digits alone do not make fixed-modulus spurious hits unlikely.
#guard Nat.Prime 3
#guard ([0, 0] : List Nat).all (· < 2)
#guard ([1, 1, 1, 1] : List Nat).all (· < 2)
#guard Nat.ofDigits 2 ([0, 0] : List Nat).reverse % 3 =
  Nat.ofDigits 2 ([1, 1] : List Nat).reverse % 3

end
