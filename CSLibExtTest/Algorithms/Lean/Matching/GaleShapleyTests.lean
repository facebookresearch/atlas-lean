/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matching.GaleShapley
public meta import CSLibExt.Algorithms.Lean.Matching.GaleShapley

/-!
# Gale-Shapley tests

Executed fixtures: for `n = 1, …, 6`, 30 pseudo-random preference profiles each (rankings built
from random swaps). The output of `galeShapley` is a perfect matching (`partnerM` and `partnerW`
are inverse), it is stable, it uses at most `n²` proposals, and no free proposer can still propose.
Against every stable matching found by brute force over all `n!` matchings, every proposer does
at least as well and every receiver at least as badly. The worst proposal count seen is printed.
Each run throws on a violation. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Matching.GaleShapley

#eval do
  let mut s := 41
  let mut worst := 0
  for n in [1, 2, 3, 4, 5, 6] do
    for _ in [0:30] do
      -- random rankings, by random swaps
      let mut mps : Array (Equiv.Perm (Fin n)) := #[]
      let mut wps : Array (Equiv.Perm (Fin n)) := #[]
      for side in [0, 1] do
        for _ in [0:n] do
          let mut σ : Equiv.Perm (Fin n) := Equiv.refl (Fin n)
          for k in [0:n] do
            s := (s * 1103515245 + 12345) % 2147483648
            let j := s / 7 % (k + 1)
            if h : j < n ∧ k < n then σ := σ.trans (Equiv.swap ⟨k, h.2⟩ ⟨j, h.1⟩)
          if side == 0 then mps := mps.push σ else wps := wps.push σ
      let mp : Fin n → Equiv.Perm (Fin n) := fun m => mps.getD m.val (Equiv.refl (Fin n))
      let wp : Fin n → Equiv.Perm (Fin n) := fun w => wps.getD w.val (Equiv.refl (Fin n))
      let st := galeShapley mp wp
      let μ : Fin n → Fin n := partnerM st
      let μinv : Fin n → Fin n := partnerW st
      let men : List (Fin n) := List.finRange n
      unless men.all (fun m => μinv (μ m) == m) && men.all (fun w => μ (μinv w) == w) do
        throw (IO.userError s!"n = {n}: not a perfect matching")
      unless chooser st == none do throw (IO.userError "a free proposer can still propose")
      let props := men.foldl (fun acc m => acc + st.next[m]) 0
      unless props ≤ n * n do throw (IO.userError s!"{props} proposals")
      worst := max worst props
      let blocks (ν νinv : Fin n → Fin n) : Bool := men.any fun m => men.any fun w =>
        (mp m).symm w < (mp m).symm (ν m) && (wp w).symm m < (wp w).symm (νinv w)
      if blocks μ μinv then throw (IO.userError s!"n = {n}: not stable")
      -- every stable matching, by brute force
      for l in (men.permutations : List (List (Fin n))) do
        let ν : Fin n → Fin n := fun m => List.getD l (m : ℕ) m
        let νinv : Fin n → Fin n := fun w => (men.find? fun m => ν m == w).getD w
        unless blocks ν νinv do
          for m in men do
            unless (mp m).symm (μ m) ≤ (mp m).symm (ν m) do
              throw (IO.userError s!"n = {n}: a proposer does better in a stable matching")
          for w in men do
            unless (wp w).symm (νinv w) ≤ (wp w).symm (μinv w) do
              throw (IO.userError s!"n = {n}: a receiver does worse in a stable matching")
  IO.println s!"n = 1..6, 30 profiles each: perfect, stable, proposer-optimal, receiver-pessimal; \
    at most {worst} proposals"

/-! Closed checks -/

example (mp wp : Fin 4 → Equiv.Perm (Fin 4)) :
    MathlibExt.Combinatorics.Matching.GaleShapley.IsStable (mprefs mp) (wprefs wp)
      (gsMatching mp wp) :=
  isStable_gsMatching mp wp

example (mp' wp' : Fin 3 → MathlibExt.Order.StrictTotalOrder (Fin 3)) :
    ∃ σ τ : Fin 3 → Equiv.Perm (Fin 3), mprefs σ = mp' ∧ wprefs τ = wp' ∧
      MathlibExt.Combinatorics.Matching.GaleShapley.IsStable mp' wp' (gsMatching σ τ) :=
  let ⟨σ, τ, h1, h2, h3, _⟩ := exists_rankings_gsMatching mp' wp'
  ⟨σ, τ, h1, h2, h3⟩

#print axioms gsMatching_proposer_optimal
#print axioms gsMatching_receiver_pessimal
#print axioms sum_next_galeShapley_le

end Cslib.Algorithms.Lean.Matching.GaleShapley
