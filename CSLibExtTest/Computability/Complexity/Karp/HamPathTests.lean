/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPath
public meta import CSLibExt.Computability.Complexity.Karp.HamPath

/-! Tests for Sipser's SAT-to-HAMPATH construction. -/

namespace Cslib.Complexity.Karp.HamPathTests

open Cslib.CookLevin Cslib.Logic.PL

/-- Depth-first search for a Hamiltonian path ending at `t`; `vis` are the visited vertices
before the current vertex `u`. -/
private def dfs (n : ℕ) (es : List (ℕ × ℕ)) (t : ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, vis, u =>
      if vis.length + 1 = n then u == t
      else es.any fun e => e.1 == u && e.2 != u && !vis.contains e.2 && dfs n es t f (u :: vis) e.2

/-- Brute force: does the construction for `φ` have a Hamiltonian path? -/
private def hamOf (φ : CNF) : Bool :=
  let m := φ.length
  let k := (hamVars φ).length
  dfs (hpT m k + 1) (hamEdges φ) (hpT m k) (hpT m k + 2) [] (hpT m 0)

/-- Brute force: is `φ` satisfiable (over its variables)? -/
private def satOf (φ : CNF) : Bool :=
  let vs := hamVars φ
  (List.range (2 ^ vs.length)).any fun a =>
    φ.all fun C => C.any fun l => (vs.idxOf l.1 |> fun i => a / 2 ^ i % 2 == 1) == l.2

-- Sizes: `n = m + k (3 m + 2) + 1`.
#guard toHam [] = Path.encodeP 0 0 1 []
#guard (hamEdges [[(0, true)]]).length = 4 + 6 + 2
-- The construction has a Hamiltonian path exactly when the formula is satisfiable.
#guard hamOf [] && satOf []
#guard !hamOf [[]] && !satOf [[]]
#guard hamOf [[(0, true)]] && hamOf [[(0, false)]]
#guard !hamOf [[(0, true)], [(0, false)]] && !satOf [[(0, true)], [(0, false)]]
#guard hamOf [[(0, true), (0, false)]]
#guard hamOf [[(0, true), (1, false)], [(1, true)]] && satOf [[(0, true), (1, false)], [(1, true)]]
#guard !hamOf [[(0, true), (1, true)], [(0, false)], [(1, false)]]
#guard hamOf [[(5, true)], [(2, false), (5, true)]]
#guard hamOf [[(0, true), (1, true)], [(0, false), (1, false)], [(0, true), (1, false)]]
-- Sweep: all formulas with two clauses over the literals of two variables (one or two literals
-- per clause), against the brute-force satisfiability check.
#guard
  let lits : List (ℕ × Bool) := [(0, true), (0, false), (1, true), (1, false)]
  let cls : List CNFClause := lits.map ([·]) ++ (lits.flatMap fun a => lits.map fun b => [a, b])
  cls.all fun C => cls.all fun D => hamOf [C, D] == satOf [C, D]
-- Undecodable inputs go to a no-instance.
#guard reduceHam [true] = noHam && !dfs 2 [] 0 3 [] 0

end Cslib.Complexity.Karp.HamPathTests
