/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathForward
public meta import CSLibExt.Computability.Complexity.Karp.HamPathForward

/-! Tests for the forward direction of SAT ≤ HAMPATH: the path built from a satisfying
assignment is a Hamiltonian path of the construction. -/

namespace Cslib.Complexity.Karp.HamPathForwardTests

open Cslib.CookLevin Cslib.Logic.PL

/-- The least diamond whose variable, valued by `σ`, is a literal of clause `j`. -/
private def pick (φ : CNF) (σ : ℕ → Bool) (j : ℕ) : ℕ :=
  let vs := hamVars φ
  ((List.range vs.length).find? fun i => (vs.getD i 0, σ (vs.getD i 0)) ∈ φ.getD j []).getD 0

/-- The path of `hfPath` for `φ` and `σ`, with the least-diamond choice. -/
private def pathOf (φ : CNF) (σ : ℕ → Bool) : List ℕ :=
  hfPath φ.length (hamVars φ).length (pick φ σ) fun i => σ ((hamVars φ).getD i 0)

/-- Is `pathOf φ σ` a Hamiltonian path of the construction for `φ` (`IsHamPath`, checked
field by field)? -/
private def okOf (φ : CNF) (σ : ℕ → Bool) : Bool :=
  let n := hpT φ.length (hamVars φ).length + 1
  let p := pathOf φ σ
  decide p.Nodup && p.length == n && p.all (· < n) && p.head? == some (hpT φ.length 0) &&
    p.getLast? == some (hpT φ.length (hamVars φ).length) &&
    (p.zip p.tail).all fun e => (hamEdges φ).contains e

-- One clause, one variable: the row runs left to right and picks up clause `0`.
#guard pathOf [[(0, true)]] (fun _ => true) = [1, 2, 3, 0, 4, 5, 6]
-- The same clause negated: the row runs right to left, detour `hpR 2 → 0 → hpR 1`.
#guard pathOf [[(0, false)]] (fun _ => false) = [1, 5, 4, 0, 3, 2, 6]
#guard okOf [[(0, true)]] (fun _ => true) && okOf [[(0, false)]] (fun _ => false)
#guard okOf [] (fun _ => true)
#guard okOf [[(0, true), (1, false)], [(1, true)]] (fun _ => true)
#guard okOf [[(5, true)], [(2, false), (5, true)]] (fun x => x == 5)
#guard okOf [[(0, true), (1, true)], [(0, false), (1, false)], [(0, true), (1, false)]]
  (fun x => x == 0)
-- A clause satisfied in two diamonds is picked up once, in the first.
#guard okOf [[(0, true), (1, true)], [(1, true)]] (fun _ => true)
-- An assignment that falsifies a clause leaves that clause vertex off the path.
#guard !okOf [[(0, true)], [(1, true)]] (fun x => x == 0)

end Cslib.Complexity.Karp.HamPathForwardTests
