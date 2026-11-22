/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Clique
public import CSLibExt.Computability.Complexity.Karp.CliqueCorrect
public meta import CSLibExt.Computability.Complexity.Karp.Clique

/-! Tests for the CLIQUE, INDEPENDENT-SET and VERTEX-COVER encodings and reductions. -/

namespace Cslib.Complexity.Karp.CliqueTests

open Cslib.CookLevin Cslib.Logic.PL

-- Pair order: rows ascending, columns descending.
#guard pairs 4 = [(0, 3), (0, 2), (0, 1), (1, 3), (1, 2), (2, 3)]
#guard (pairs 5).length = 10
#guard pairs 1 = [] ∧ pairs 0 = []

-- Adjacency is symmetric and read through the pair order.
#guard adjBits 4 [true, false, false, false, true, false] 0 3 = true
#guard adjBits 4 [true, false, false, false, true, false] 3 0 = true
#guard adjBits 4 [true, false, false, false, true, false] 2 1 = true
#guard adjBits 4 [true, false, false, false, true, false] 0 1 = false

-- The two unary numbers parse back; anything after them is the bit list.
#guard decodeKG (encodeKG 2 3 [true, false, true]) = some (2, 3, [true, false, true])
#guard decodeKG [true, true] = none

/-- `(x₁ ∨ ¬x₂) ∧ ¬x₁`. -/
private def φ : CNF := [[(1, true), (2, false)], [(1, false)]]

-- Occurrences in formula order, and Karp's graph: only `¬x₂` (vertex 1) and `¬x₁` (vertex 2)
-- are adjacent (vertices 0, 2 are complementary; 0, 1 share a clause).
#guard occs φ = [(0, 1, true), (0, 2, false), (1, 1, false)]
#guard toClique φ = encodeKG 2 3 [false, false, true]
#guard reduceClique (encodeCNF φ) = toClique φ
#guard reduceClique [true] = noKG
-- An empty clause has no vertices.
#guard toClique [[], [(0, true)]] = encodeKG 2 1 []

-- Complementing bits, and `k ↦ n - k`.
#guard flipKG (encodeKG 2 3 [false, false, true]) = encodeKG 2 3 [true, true, false]
#guard isToVc (encodeKG 2 3 [false, false, true]) = encodeKG 1 3 [false, false, true]
#guard isToVc (encodeKG 4 3 [false, false, true]) = noKG
#guard flipKG [false] = noKG

-- Correctness on samples: `x₁ = x₂ = false` satisfies `φ`, so Karp's graph has a 2-clique and its
-- complement a 2-independent set; `x₁ ∧ ¬x₁` is unsatisfiable, so its graph has no 2-clique.
example : cliqueDec (toClique φ) = true := by
  rw [← reduceClique_encodeCNF, ← satDec_eq_cliqueDec_reduceClique,
    DenseSAT.ToBinary.satDec_encodeCNF]
  exact ⟨fun _ => false, by simp [φ]⟩
example : indSetDec (flipKG (toClique φ)) = true := by
  rw [← cliqueDec_eq_indSetDec_flipKG, ← reduceClique_encodeCNF,
    ← satDec_eq_cliqueDec_reduceClique, DenseSAT.ToBinary.satDec_encodeCNF]
  exact ⟨fun _ => false, by simp [φ]⟩
example : cliqueDec (toClique [[(1, true)], [(1, false)]]) = false := by
  rw [← reduceClique_encodeCNF, ← satDec_eq_cliqueDec_reduceClique, Bool.eq_false_iff, ne_eq,
    DenseSAT.ToBinary.satDec_encodeCNF]
  rintro ⟨v, hv⟩
  simp at hv

end Cslib.Complexity.Karp.CliqueTests
