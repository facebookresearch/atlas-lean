/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.MatchingLowerBound
public meta import CSLibExt.Algorithms.Lean.Online.MatchingLowerBound

/-!
# Online matching lower bound tests

Executed fixtures: for `n = 1, …, 6` and five deterministic algorithms (the production greedy
matcher, first free neighbour, last free neighbour, never match, and a history-dependent rule),
the adversary's `2 n` arrivals have a perfect matching (`adversaryOpt`: distinct, each a neighbour
of its arrival) while the algorithm matches at most `n`; the greedy rules match exactly `n`.
Focused production-matcher cases cover neighbour order, duplicates, replay, exhaustion, and empty
inputs. Each run throws on a violation. Closed checks instantiate the lower-bound, bridge, and
tightness theorems.
-/

namespace Cslib.Algorithms.Lean.Online.MatchingLowerBound

#eval show IO Unit from do
  let cases : List (String × List (List (Fin 3)) × List (Fin 3) × Option (Fin 3)) :=
    [("out-of-order neighbours", [], [2, 1, 0], some 0),
     ("duplicate neighbours", [], [2, 2, 1, 1], some 1),
     ("replayed history", [[2, 1], [], [1, 0, 0]], [0, 1, 2], some 2),
     ("used neighbour", [[1]], [1, 1], none),
     ("exhausted vertices", [[2], [1], [0]], [0, 1, 2], none),
     ("empty neighbours", [], [], none)]
  for (name, h, nbrs, expected) in cases do
    let actual := (greedyMatcher (a := 3)).choose h nbrs
    unless actual == expected do
      throw (IO.userError s!"{name}: got {actual}, expected {expected}")
  unless (greedyMatcher (a := 0)).choose [] [] == none do
    throw (IO.userError "empty left-vertex set: expected no proposal")
  IO.println "greedyMatcher: six choice fixtures and the empty left-vertex set passed"

/-- The left vertices proposed so far are not tracked by `choose`, so the greedy rules recompute
them by replaying the history. -/
private meta def replayUsed {a : ℕ} (pick : List (Fin a) → List (Fin a) → Option (Fin a))
    (h : List (List (Fin a))) : List (Fin a) :=
  h.foldl (fun used nbrs => match pick used nbrs with
    | some i => if i ∈ nbrs ∧ i ∉ used then i :: used else used
    | none => used) []

private meta def greedyBy {a : ℕ} (pick : List (Fin a) → List (Fin a) → Option (Fin a)) :
    OnlineMatcher a := ⟨fun h nbrs => pick (replayUsed pick h) nbrs⟩

private meta def firstFree {a : ℕ} (used nbrs : List (Fin a)) : Option (Fin a) :=
  nbrs.find? (· ∉ used)

private meta def lastFree {a : ℕ} (used nbrs : List (Fin a)) : Option (Fin a) :=
  nbrs.reverse.find? (· ∉ used)

#eval do
  for n in [1, 2, 3, 4, 5, 6] do
    let algs : List (String × OnlineMatcher (2 * n)) :=
      [("production greedy", greedyMatcher),
       ("first free", greedyBy firstFree), ("last free", greedyBy lastFree),
       ("never", ⟨fun _ _ => none⟩),
       ("history", ⟨fun h nbrs => if h.length % 4 == 0 then nbrs.getLast? else nbrs.head?⟩)]
    for (name, A) in algs do
      let σ := adversary A [] (gadgets n)
      let m := adversaryOpt A [] (gadgets n)
      unless σ.length == 2 * n && m.length == 2 * n && m.Nodup do
        throw (IO.userError s!"{name}, n = {n}: bad instance")
      unless (List.zip m σ).all (fun p => p.1 ∈ p.2) do
        throw (IO.userError s!"{name}, n = {n}: not a matching")
      let k := matched A [] [] σ
      unless k ≤ n do throw (IO.userError s!"{name}, n = {n}: matched {k}")
      if (name == "production greedy" || name == "first free" || name == "last free") && k != n then
        throw (IO.userError s!"{name}, n = {n}: greedy matched {k}")
  IO.println "n = 1..6, five algorithms: perfect matching of size 2n, algorithm matches ≤ n"

/-! Closed checks -/

example (A : OnlineMatcher 8) :
    ∃ σ m, IsPerfect σ m ∧ m.length = 8 ∧ σ.length = 8 ∧ matched A [] [] σ ≤ 4 :=
  exists_perfect_matched_le 4 A

-- ratio `3 / 5 > 1/2` with additive constant `2` fails for `n = 3`
example (A : OnlineMatcher (2 * 3)) :
    ∃ σ m, IsPerfect σ m ∧ 5 * matched A [] [] σ + 2 < 3 * m.length :=
  not_competitive_of_lt 3 (by decide) (by decide) A

-- and for any additive constant, at some size
example (A : ∀ n, OnlineMatcher (2 * n)) (b : ℕ) :
    ∃ n σ m, IsPerfect σ m ∧ 5 * matched (A n) [] [] σ + b < 3 * m.length :=
  not_competitive A (by decide) b

example (A : OnlineMatcher 6) : ∃ σ : List (List (Fin 6)), ∃ M,
    BipartiteMatching.IsMatching (toAdj σ) M ∧ M.card = 6 ∧ matched A [] [] σ ≤ 3 :=
  exists_isMatching_matched_le 3 A

example (σ : List (List (Fin 3))) :
    matched greedyMatcher [] [] σ = (greedyUsed σ).length :=
  matched_greedyMatcher σ

example (σ : List (List (Fin 3))) :
    matched greedyMatcher [] [] σ =
      (BipartiteMatching.pairs (Online.BipartiteMatching.greedyAll (toAdj σ))).card :=
  matched_greedyMatcher_eq_card σ

example {σ : List (List (Fin 3))} {M : Finset (Fin 3 × Fin σ.length)}
    (hM : BipartiteMatching.IsMatching (toAdj σ) M) :
    M.card ≤ 2 * matched greedyMatcher [] [] σ :=
  card_le_two_mul_matched_greedyMatcher hM

example {σ : List (List (Fin 3))} {m : List (Fin 3)} (hm : IsPerfect σ m) :
    m.length ≤ 2 * matched greedyMatcher [] [] σ :=
  length_le_two_mul_matched_greedyMatcher hm

example (n : ℕ) : ∃ σ m, IsPerfect σ m ∧ m.length = 2 * n ∧
    2 * matched (greedyMatcher (a := 2 * n)) [] [] σ = m.length :=
  greedy_tight n

#print axioms greedyMatcher
#print axioms matched_greedyMatcher
#print axioms matched_greedyMatcher_eq_card
#print axioms card_le_two_mul_matched_greedyMatcher
#print axioms length_le_two_mul_matched_greedyMatcher
#print axioms greedy_tight
#print axioms not_competitive
#print axioms not_competitive_of_lt
#print axioms exists_perfect_matched_le

end Cslib.Algorithms.Lean.Online.MatchingLowerBound
