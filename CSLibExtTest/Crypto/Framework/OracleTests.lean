/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Oracle
public import CSLibExt.Crypto.SymmetricKey.PRF
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for oracle computations and query cost

* A two-query algorithm runs, lists its queries (`[0, 1]`) and records its transcript as expected,
  and is `2`- but not `1`-query bounded.
* `CSLibExt/Crypto/SymmetricKey/PRF.lean` re-exports this API: its `OracleComp`, `run`, `queries`,
  `run_congr` and `run_bind` are the framework's declarations, not copies.
* `evalPMF` against a deterministic oracle is the point mass at the run; a randomized oracle's
  transcripts respect the query bound.
* `runStateful` answers the `i`-th query with a counter-indexed oracle and records the transcript
  in query order; `queryAt` reads the `j`-th query.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Oracle

open Cslib.Crypto.Framework FreeM OracleComp

/-- Query `0`, then query the answer, and output the second answer. -/
def twice : OracleComp (ZMod 5) (ZMod 5) (ZMod 5) :=
  .query 0 fun y => .query y fun z => .done z

example : twice.run (fun x : ZMod 5 => x + 1) = 2 := by decide

example : twice.queries (fun x : ZMod 5 => x + 1) = [0, 1] := by decide

example : (twice.queries fun x : ZMod 5 => x + 1).length ≤ 2 :=
  length_queries_le _ (q := 2) fun _ _ => trivial

example : IsQueryBounded 2 twice := fun _ _ => trivial

example : IsQueryBounded 7 twice := IsQueryBounded.mono (by norm_num) (q := 2) fun _ _ => trivial

/-- The bound `2` is tight: `twice` is not `1`-query bounded. -/
example : ¬ IsQueryBounded 1 twice := fun h => h 0

/-- The PRF development's names resolve to the framework's declarations (`export`ed by
`CSLibExt/Crypto/SymmetricKey/PRF.lean`, not copied). -/
example : @Cslib.Crypto.PRF.OracleComp = @OracleComp := rfl
example : @Cslib.Crypto.PRF.OracleComp.run = @OracleComp.run := rfl
example : @Cslib.Crypto.PRF.OracleComp.queries = @OracleComp.queries := rfl

/-- A PRF-side computation runs with the framework's semantics. -/
example : Cslib.Crypto.PRF.OracleComp.run (fun x : ZMod 5 => x + 1) twice = 2 := by decide

example : evalPMF (fun x : ZMod 5 => PMF.pure (x + 1)) twice = PMF.pure 2 := by
  rw [OracleComp.evalPMF_pure_comp]
  rfl

example : evalLog (fun x : ZMod 5 => PMF.pure (x + 1)) twice = PMF.pure (2, [(0, 1), (1, 2)]) := by
  simp only [twice, evalLog, PMF.pure_bind, PMF.pure_map]
  rfl

/-- Against a uniformly random oracle, every transcript of `twice` has at most two entries. -/
example : ∀ p ∈
    (evalLog (fun _ : ZMod 5 => Cslib.Probability.PMF.uniformOfFintype (ZMod 5)) twice).support,
    p.2.length ≤ 2 :=
  length_le_of_mem_support_evalLog _ (q := 2) fun _ _ => trivial

/-! ### Stateful oracle runs (`OracleComp.runStateful`) -/

section Stateful

/-- Two queries, `1` then `2`; the output is the sum of the answers. -/
def twoQ : OracleComp ℕ ℕ ℕ := .liftBind 1 fun a => .liftBind 2 fun b => .pure (a + b)

/-- The counter oracle `s i x = 10 i + x`. -/
def s10 (i x : ℕ) : ℕ := 10 * i + x

/-- From counter `0` the answers are `s10 0 1 = 1` and `s10 1 2 = 12`, in query order. -/
example : runStateful s10 0 twoQ = (13, [(1, 1), (2, 12)]) := by decide

/-- From counter `5` the answers are `51` and `62`. -/
example : runStateful s10 5 twoQ = (113, [(1, 51), (2, 62)]) := by decide

example : queryAt s10 0 twoQ 1 = some 2 ∧ queryAt s10 0 twoQ 2 = none := by decide

end Stateful

end Cslib.Crypto.FrameworkTests.Oracle
