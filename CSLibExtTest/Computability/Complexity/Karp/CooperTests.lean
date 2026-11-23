/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Cooper

namespace Cslib.Complexity.Cooper

/-- Cooper's worked example has output probability `5 / 8`: 10 of the 16 root
assignments satisfy it. -/
example : (cooperNet cooperEx).outProb = 5 / 8 := outProb_cooperEx

/-- The unsatisfiable control has output probability `0`. -/
example : (cooperNet cooperUnsat).outProb = 0 := outProb_cooperUnsat

/-- A formula is satisfiable iff its network's output probability is positive. -/
example (φ : Cslib.Logic.PL.CNF) : Cslib.Logic.PL.CNFSat φ ↔ 0 < (cooperNet φ).outProb :=
  cnfSat_iff_outProb_pos φ

/-- The reduction map is correct on every bit string. -/
example (x : List Bool) : Cslib.CookLevin.satDec x = bnPosDec (reduceBN x) :=
  satDec_eq_bnPosDec_reduceBN x

/-- Direct computation: the example's network has 20 nodes, with roots for
variables 1, 2, 3, 4 at indices 12, 6, 4, 2 (latest occurrence first). -/
example : (cooperNet cooperEx).length = 20 := by decide

example : (coopSt cooperEx).roots = [(1, 12), (2, 6), (3, 4), (4, 2)] := by decide

end Cslib.Complexity.Cooper
