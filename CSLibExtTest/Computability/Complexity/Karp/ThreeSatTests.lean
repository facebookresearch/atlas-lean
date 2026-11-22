/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatCorrect
public meta import CSLibExt.Computability.Complexity.Karp.ThreeSatCorrect

/-! Tests for the SAT-to-3SAT translation. -/

namespace Cslib.Complexity.Karp.Tests

open Cslib.CookLevin Cslib.Logic.PL

-- Fresh numbers are odd and their codes are `true`, `u` times `false`, `true`.
#guard (List.range 4).map fresh = [3, 5, 9, 17]
#guard Computability.encodeNat (fresh 2) = [true, false, false, true]

-- Short clauses are only renamed; the empty clause stays.
#guard to3 [[(1, true)], [], [(0, false)]] = [[(2, true)], [], [(0, false)]]

-- A clause of length 4 becomes a chain of four clauses with fresh numbers 2, 1, 0.
#guard to3 [[(1, true), (2, false), (3, true), (4, false)]] =
  [[(2, true), (fresh 2, true)], [(fresh 2, false), (4, false), (fresh 1, true)],
   [(fresh 1, false), (6, true), (fresh 0, true)], [(fresh 0, false), (8, false)]]

-- Fresh numbers are handed out from the last clause backwards.
#guard to3 [[(1, true), (2, true)], [(3, true), (4, true)]] =
  [[(2, true), (fresh 1, true)], [(fresh 1, false), (4, true)],
   [(6, true), (fresh 0, true)], [(fresh 0, false), (8, true)]]

-- Every output clause has at most three literals.
#guard is3 (to3 [[(1, true), (2, false), (3, true), (4, false), (5, true)], [(7, false)], []])
#guard !is3 [[(1, true), (2, false), (3, true), (4, false)]]

-- `reduce3` decodes, translates and re-encodes; undecodable input goes to `[]`.
#guard reduce3 (encodeCNF [[(1, true), (2, true)]]) =
  encodeCNF [[(2, true), (fresh 0, true)], [(fresh 0, false), (4, true)]]
#guard reduce3 [true] = []

-- The completeness witness: when `v` satisfies `φ`, `lift v φ` satisfies `to3 φ`; the only true
-- literal of the long clause is first, in the middle, or last.
#guard
  let φ : CNF := [[(1, true), (2, true), (3, true), (4, true)], [(5, false), (6, true)]]
  [fun n => n == 1, fun n => n == 2 || n == 6, fun n => n == 4 || n == 5 || n == 6].all fun v =>
    φ.all (Cslib.Algorithms.SAT.DPLL.clauseSatisfied v) &&
      (to3 φ).all (Cslib.Algorithms.SAT.DPLL.clauseSatisfied (lift v φ))

example (φ : CNF) : is3 (to3 φ) = true := is3_to3 φ
example (φ : CNF) : CNFSat (to3 φ) ↔ CNFSat φ := cnfSat_to3_iff φ
example (x : List Bool) : satDec x = sat3Dec (reduce3 x) := satDec_eq_sat3Dec_reduce3 x

end Cslib.Complexity.Karp.Tests
