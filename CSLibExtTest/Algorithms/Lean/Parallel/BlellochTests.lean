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
the theorems. Independent multiplication-site enumeration checks both timed phases and
scheduled rounds for every length 0..100, including non-power-of-two inputs and idle phases.
Positive site counts reject zero-work no-op clients.
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

-- Both phases contribute work, including multiplication by the identity.
example : (blellochListT 2 ([2, 3, 5, 7] : List ℕ)).ret = [1, 2, 6, 30] := by decide
example : (blellochListT 2 ([2, 3, 5, 7] : List ℕ)).time = (6, 4) := by decide
example : (blellochListT 0 ([7] : List ℕ)).time = (0, 0) := by decide
example : (blellochListT 2 ([] : List ℕ)).ret = [] := by decide
example : (blellochListT 2 ([] : List ℕ)).time = (0, 4) := by decide
example : (pairListT ([2, 3, 5] : List ℕ)).time = (1, 0) := by decide
example : (expandT ([11, 13] : List ℕ) [2, 3, 5]).time = (1, 0) := by decide

example : (blellochListT 1 ([1, 1] : List (FreeMonoid Empty))).time = (2, 2) := by decide

#eval do
  let xs : List (FreeMonoid Char) :=
    [FreeMonoid.of 'w', FreeMonoid.of 'x', FreeMonoid.of 'y', FreeMonoid.of 'z']
  let run := blellochListT 2 xs
  unless run.ret.map FreeMonoid.toList == [[], ['w'], ['w', 'x'], ['w', 'x', 'y']] do
    throw (IO.userError "timed exclusive scan reversed factors")
  unless run.time == (6, 4) do throw (IO.userError "timed exclusive scan lost a phase tick")
  IO.println "timed exclusive scan: ordered products, work 6, rounds 4"

-- Enumerate pair and expansion sites, using only the original pure outputs for their shape.
#eval do
  let mut cases := 0
  let mut rejected := 0
  for n in List.range 101 do
    let xs : List (FreeMonoid Char) :=
      (List.range n).map fun i => FreeMonoid.of (Char.ofNat (97 + i % 26))
    for K in [0, Nat.clog 2 n, Nat.clog 2 n + 2] do
      let mut input := xs
      let mut sites := 0
      let mut rounds := 0
      for k in (List.range K).reverse do
        let mut pairSites := 0
        for i in List.range input.length do
          if i % 2 == 0 && i + 1 < input.length then pairSites := pairSites + 1
        unless (pairListT input).time == (pairSites, 0) do
          throw (IO.userError s!"exclusive pair sites: n={n}, K={K}, k={k}")
        let pairs := pairList input
        let scanned := blellochList k pairs
        let mut expandSites := 0
        for i in List.range scanned.length do
          if 2 * i + 1 < input.length then expandSites := expandSites + 1
        unless (expandT scanned input).time == (expandSites, 0) do
          throw (IO.userError s!"exclusive expansion sites: n={n}, K={K}, k={k}")
        sites := sites + pairSites + expandSites
        rounds := rounds + 2
        input := pairs
      let run := blellochListT K xs
      unless run.time == (sites, rounds) do
        throw (IO.userError s!"exclusive sites: n={n}, K={K}, got {run.time}")
      unless run.ret.map FreeMonoid.toList == (blellochList K xs).map FreeMonoid.toList do
        throw (IO.userError s!"exclusive erasure: n={n}, K={K}")
      let noOp : TimeM (ℕ × ℕ) (List (FreeMonoid Char)) := ⟨xs, (0, rounds)⟩
      if 0 < sites then
        if noOp.time == (sites, rounds) then
          throw (IO.userError s!"exclusive no-op incorrectly accepted: n={n}, K={K}")
        rejected := rejected + 1
      cases := cases + 1
  unless cases == 303 && rejected == 198 do throw (IO.userError "exclusive site coverage missing")
  IO.println (s!"exclusive multiplication sites: lengths 0..100, {cases} scans, " ++
    s!"{rejected} zero-work no-op clients rejected; both phases and idle rounds checked")

-- The power-of-two cost contract rejects a no-op even when it records the right rounds.
example :
    let noOp : ℕ → List ℕ → TimeM (ℕ × ℕ) (List ℕ) := fun k xs => ⟨xs, (0, 2 * k)⟩
    ¬ ∀ k xs, xs.length = 2 ^ k → (noOp k xs).time = (blellochWork k, blellochSpan k) := by
  change ¬ ∀ (k : ℕ) (xs : List ℕ),
    xs.length = 2 ^ k → (0, 2 * k) = (blellochWork k, blellochSpan k)
  intro h
  have hbad : (0, 2) ≠ (blellochWork 1, blellochSpan 1) := by decide
  exact hbad (h 1 [2, 3] rfl)

universe u
example {M : Type u} [Monoid M] (k : ℕ) (xs : List M) :
    (blellochListT k xs).ret = blellochList k xs := ret_blellochListT k xs
example {M : Type u} [Monoid M] (k : ℕ) (xs : List M) (h : xs.length = 2 ^ k) :
    (blellochListT k xs).time.1 = 2 ^ (k + 1) - 2 := blellochListT_work_eq k xs h
example {M : Type u} [Monoid M] (k : ℕ) (xs : List M) (h : xs.length = 2 ^ k) :
    (blellochListT k xs).time.2 = 2 * k := blellochListT_rounds_eq k xs h

#print axioms ret_blellochListT
#print axioms time_blellochListT
#print axioms blellochListT_work_eq
#print axioms blellochListT_rounds_eq

/-! Closed checks -/

example (xs : List (FreeMonoid ℕ)) (h : xs.length = 2 ^ 5) (j : ℕ) (hj : j < 2 ^ 5) :
    (blellochList 5 xs).getD j 1 = seg (fun i => xs.getD i 1) 0 j :=
  getD_blellochList_eq_seg 5 xs h j hj

#print axioms blelloch_eq_seg
#print axioms getD_blellochList_eq_seg

end Cslib.Algorithms.Lean.Parallel.PrefixSum
