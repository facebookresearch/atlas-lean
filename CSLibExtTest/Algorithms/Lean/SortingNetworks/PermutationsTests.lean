/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Permutations
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.Permutations

/-!
# Permutation principle tests

Executed fixtures: on 300 pseudo-random comparator networks on `2` to `5` wires, sorting all
`n!` permutations of `Fin n` agrees with `sortsBool` (all `2 ^ n` Boolean inputs), as the
permutation principle and the 0-1 principle predict; both verdicts occur. Each run throws on a
disagreement. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks

/-- Whether a network sorts all permutations of `Fin n`. -/
private meta def sortsPerms {n : ℕ} (net : Network n) : Bool :=
  (List.range n).permutations.all fun l =>
    let out := run net fun i => l.getD i.val 0
    (List.finRange n).all fun i => (List.finRange n).all fun j => !(i ≤ j) || out i ≤ out j

#eval do
  let mut s := 21
  let mut yes := 0
  let mut no := 0
  for _ in [0:300] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 4 + 2
    s := (s * 1103515245 + 12345) % 2147483648
    let len := s / 11 % 12
    let mut pairs : List (ℕ × ℕ) := []
    for _ in [0:len] do
      s := (s * 1103515245 + 12345) % 2147483648
      let i := s / 13 % n
      s := (s * 1103515245 + 12345) % 2147483648
      let j := s / 13 % n
      pairs := pairs ++ [(min i j, max i j)]
    let net : Network n := pairs.filterMap fun (p : ℕ × ℕ) =>
      if h : p.1 < n ∧ p.2 < n then some (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else none
    let a := sortsPerms net
    unless a == sortsBool net do throw (IO.userError s!"disagree on {pairs} ({n} wires)")
    if a then yes := yes + 1 else no := no + 1
  IO.println s!"300 random networks: permutations and 0-1 inputs agree ({yes} sort, {no} do not)"

/-! Closed checks -/

example (net : Network 4) (h : ∀ σ : Equiv.Perm (Fin 4), Monotone (run net σ)) :
    Sorts net ℤ := sorts_of_sorts_perm h ℤ

#print axioms sorts_of_sorts_perm
#print axioms sorts_of_sorts_injective

end Cslib.Algorithms.Lean.SortingNetworks
