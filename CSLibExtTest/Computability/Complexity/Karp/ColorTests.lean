/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public meta import CSLibExt.Computability.Complexity.Karp.Color

/-! Tests for the 3-COLOR encoding and the SAT-to-3-COLOR construction. -/

namespace Cslib.Complexity.Karp.ColorTests

open Cslib.CookLevin Cslib.Logic.PL

-- The encoding: `n` in unary, then each edge's endpoints in unary.
#guard encodeE 3 [(0, 2)] = [true, true, true, false, false, true, true, false]

/-- Brute-force 3-colorability of an edge list on `n` vertices (for small tests only). -/
private def col3 (n : ℕ) (es : List (ℕ × ℕ)) : Bool :=
  ((List.range n).foldr (fun _ cs => cs.flatMap fun c => [0, 1, 2].map (· :: c)) [[]]).any
    fun c => es.all fun e => e.1 == e.2 || c.getD e.1 0 != c.getD e.2 0

-- A unit clause: palette, one occurrence (vertices 3, 4), its output joined to `F` and `B`.
#guard colSt [[(0, true)]] =
  ⟨5, [(0, true, 3, 4)], [(0, 1), (0, 2), (1, 2), (3, 4), (3, 2), (4, 2), (3, 1), (3, 2)]⟩

-- Two literals: walked from the last; one OR gadget (vertices 7, 8, 9).
#guard (colSt [[(1, true), (2, false)]]).em.drop 3 =
  [(3, 4), (3, 2), (4, 2), (5, 6), (5, 2), (6, 2),
   (5, 7), (3, 8), (7, 8), (7, 9), (8, 9), (9, 2), (9, 1), (9, 2)]
#guard (colSt [[(1, true), (2, false)]]).next = 10

-- Opposite occurrences of one variable in two clauses: consistency edges `(3, 5), (4, 6)`.
#guard ((colSt [[(1, true)], [(1, false)]]).em.drop 3).take 10 =
  [(3, 4), (3, 2), (4, 2), (3, 1), (3, 2), (5, 6), (5, 2), (6, 2), (3, 5), (4, 6)]
-- Equal occurrences: `(3, 6), (4, 5)`.
#guard ((colSt [[(1, true)], [(1, true)]]).em.drop 8).take 5 =
  [(5, 6), (5, 2), (6, 2), (3, 6), (4, 5)]

-- The empty clause: a vertex joined to the whole palette.
#guard colSt [[]] = ⟨4, [], [(0, 1), (0, 2), (1, 2), (3, 0), (3, 1), (3, 2)]⟩

-- Satisfiability matches 3-colorability on small formulas.
#guard col3 (colSt [[(1, true), (2, false)]]).next (colSt [[(1, true), (2, false)]]).em
#guard col3 (colSt [[(1, true)], [(1, true)]]).next (colSt [[(1, true)], [(1, true)]]).em
#guard !col3 (colSt [[(1, true)], [(1, false)]]).next (colSt [[(1, true)], [(1, false)]]).em
#guard !col3 (colSt [[]]).next (colSt [[]]).em
#guard !col3 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

-- The bit-string reduction.
#guard reduceCol (encodeCNF [[(0, true)]]) = toCol [[(0, true)]]
#guard reduceCol [true] = noCol

end Cslib.Complexity.Karp.ColorTests
