/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.RazborovMonotoneClique

/-! # Tests for the adjacency-matrix clique function and its monotone circuit bound -/

namespace CSLibExtTest.Computability.Complexity.RazborovMonotoneClique

open MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique
open Cslib.Complexity.Classes

-- At the empty graph the required clique has size zero.
example : cliqueHolds 0 [] :=
  ⟨∅, rfl, by simp, by simp⟩

-- For six vertices the entries at offsets 1 and 6 give both directions of a two-clique.
example : cliqueHolds 6 [false, true, false, false, false, false, true] := by
  refine ⟨{0, 1}, by decide, by simp, ?_⟩
  simp [Finset.mem_insert, Finset.mem_singleton]

-- The matrix ends before offset 6. Its one directed edge cannot supply both directions.
example : ¬ cliqueHolds 6 [false, true] := by
  rintro ⟨S, hcard, _, hcl⟩
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (by rw [hcard]; decide)
  have offset (i : ℕ) (h : [false, true].getD i false = true) : i = 1 := by
    cases i with
    | zero => contradiction
    | succ i => cases i <;> simp_all
  have := offset _ (hcl a ha b hb hne)
  have := offset _ (hcl b hb a ha hne.symm)
  omega

-- Specialize the polynomial to a quadratic in the number of input bits.
example : ∃ n : ℕ, ∀ C : List (ACGate (n * n)), WellFormedCircuit C → IsMonotoneCircuit C →
    (∀ x : List Bool, x.length = n * n →
      ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔ cliqueHolds n x)) →
    (n * n) ^ 2 < C.length := by
  obtain ⟨n, hn⟩ := razborov_monotone_clique (Polynomial.X ^ 2)
  refine ⟨n, fun C hwf hm hc => ?_⟩
  have bound := hn C hwf hm hc
  rwa [Polynomial.eval_pow, Polynomial.eval_X] at bound

end CSLibExtTest.Computability.Complexity.RazborovMonotoneClique
