/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pauplin's formula tests

* Non-vacuity witness: the quartet `((0, 1), (2, 3))` with edge lengths `1, 2` (cherry `0, 1`),
  `3` (internal edge) and `4, 5` (cherry `2, 3`) is a `UTree` with distinct leaf labels; its
  pairs, tree length `15` and balanced minimum-evolution length `6 + 9 = 15` are evaluated by
  hand, and the theorems instantiate on it.
* The Kraft equality at leaf `0` of the quartet: `1/2 + 1/4 + 1/4 = 1`.
* Boundary: the two-leaf tree (one edge, coefficient `2^0 = 1`), and a tree with a negative
  edge length (Pauplin's formula holds for all real lengths).
* `bmeLength` for another dissimilarity on the same topology (all distances `1`).
-/

namespace MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution

/-- The quartet `((0, 1), (2, 3))` with edge lengths `1, 2, 3, 4, 5`. -/
noncomputable def quartet : UTree (Fin 4) :=
  ⟨.node 1 (.leaf 0) 2 (.leaf 1), 3, .node 4 (.leaf 2) 5 (.leaf 3)⟩

example : quartet.pairs = [(0, 1, 0 + 1 + 2 + 0, 0 + 0 + 2), (2, 3, 0 + 4 + 5 + 0, 0 + 0 + 2),
    (0, 2, 0 + 1 + 3 + (0 + 4), 0 + 1 + (0 + 1) + 1),
    (0, 3, 0 + 1 + 3 + (0 + 5), 0 + 1 + (0 + 1) + 1),
    (1, 2, 0 + 2 + 3 + (0 + 4), 0 + 1 + (0 + 1) + 1),
    (1, 3, 0 + 2 + 3 + (0 + 5), 0 + 1 + (0 + 1) + 1)] := rfl

example : quartet.length = 15 := by
  norm_num [quartet, UTree.length, RTree.length]

/-- Non-vacuity witness: the quartet has distinct leaf labels. -/
theorem quartet_nodup : quartet.labels.Nodup := by
  simp [quartet, UTree.labels, RTree.leaves]

/-- The path-length dissimilarity of the quartet. -/
noncomputable def quartetDist : Fin 4 → Fin 4 → ℝ
  | 0, 1 | 1, 0 => 3
  | 2, 3 | 3, 2 => 9
  | 0, 2 | 2, 0 => 8
  | 0, 3 | 3, 0 => 9
  | 1, 2 | 2, 1 => 9
  | 1, 3 | 3, 1 => 10
  | _, _ => 0

-- Direct evaluation: `(3 + 9) / 2 + (8 + 9 + 9 + 10) / 4 = 15`.
example : quartet.bmeLength quartetDist = 15 := by
  norm_num [UTree.bmeLength, quartet, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff,
    quartetDist]

-- The theorem gives the same value.
example : quartet.bmeLength quartetDist = quartet.length := by
  apply UTree.bmeLength_eq_length
  · intro p hp
    simp only [quartet, UTree.pairs, RTree.pairs, RTree.leaves, List.map, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [quartetDist]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [quartetDist]

-- Kraft at leaf `0`: `1/2 + 1/4 + 1/4 = 1`, directly and by the theorem.
example : (quartet.pairs.map fun p =>
    if p.1 = 0 ∨ p.2.1 = 0 then pauplinCoeff p.2.2.2 else 0).sum = 1 := by
  norm_num [quartet, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff]

example : (quartet.pairs.map fun p =>
    if p.1 = 3 ∨ p.2.1 = 3 then pauplinCoeff p.2.2.2 else 0).sum = 1 :=
  UTree.kraft_leaf quartet quartet_nodup 3 (by simp [quartet, UTree.labels, RTree.leaves])

-- Rooted Kraft on the cherry `(0, 1)`: `1/2 + 1/2 = 1`.
example : ((RTree.node 1 (.leaf (0 : Fin 4)) 2 (.leaf 1)).leaves.map fun p =>
    ((2 : ℝ) ^ p.2.2)⁻¹).sum = 1 := RTree.kraft _

/-! ## Boundary cases -/

/-- The two-leaf tree: one edge of length `5`. -/
noncomputable def twoLeaf : UTree (Fin 2) := ⟨.leaf 0, 5, .leaf 1⟩

-- One pair, one edge, coefficient `2 ^ (1 - 1) = 1`.
example : (twoLeaf.pairs.map fun p => pauplinCoeff p.2.2.2 * p.2.2.1).sum = 5 := by
  norm_num [twoLeaf, UTree.pairs, RTree.leaves, RTree.pairs, pauplinCoeff]

-- A negative edge length: Pauplin's formula is an identity of linear forms.
example : (UTree.pairs (⟨.node (-1) (.leaf (0 : Fin 3)) 2 (.leaf 1), 3, .leaf 2⟩ : UTree (Fin 3))
    |>.map fun p => pauplinCoeff p.2.2.2 * p.2.2.1).sum = 4 := by
  rw [UTree.bmeLength_pathLength]
  norm_num [UTree.length, RTree.length]

-- The all-ones dissimilarity has BME length `2 · 1/2 + 4 · 1/4 = 2`: it is the path-length
-- metric of the same topology with pendant edges `1/2` and internal edge `0`, of length `2`.
example : quartet.bmeLength (fun _ _ => 1) = 2 := by
  norm_num [UTree.bmeLength, quartet, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff]

/-- An asymmetric dissimilarity on the quartet leaves, for the orientation-invariance tests:
`d i j = i + 2 * j`, so `d 0 1 = 2` but `d 1 0 = 1`. -/
noncomputable def asymDist : Fin 4 → Fin 4 → ℝ := fun x y => (x.val : ℝ) + 2 * (y.val : ℝ)

/-- The quartet with the two sides of the root edge swapped: the same unrooted topology, with
every cross pair listed in the opposite orientation. -/
noncomputable def quartetSwapped : UTree (Fin 4) := ⟨quartet.right, quartet.len, quartet.left⟩

/-- The quartet with the children of the `(0, 1)` cherry swapped: the same unrooted topology,
with the cherry pair listed as `(1, 0)`. -/
noncomputable def quartetCherrySwapped : UTree (Fin 4) :=
  ⟨.node 2 (.leaf (1 : Fin 4)) 1 (.leaf 0), 3, .node 4 (.leaf 2) 5 (.leaf 3)⟩

-- Orientation invariance: `bmeLength` of the `asymDist` dissimilarity is `9` on the quartet,
-- and reparsing the same topology with swapped sides or a swapped cherry does not change it.
-- Without symmetrization the two parses give different values.
example : quartet.bmeLength asymDist = 9 := by
  norm_num [UTree.bmeLength, quartet, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff,
    asymDist]

example : quartet.bmeLength asymDist = quartetSwapped.bmeLength asymDist := by
  norm_num [UTree.bmeLength, quartet, quartetSwapped, UTree.pairs, RTree.pairs, RTree.leaves,
    pauplinCoeff, asymDist]

example : quartet.bmeLength asymDist = quartetCherrySwapped.bmeLength asymDist := by
  norm_num [UTree.bmeLength, quartet, quartetCherrySwapped, UTree.pairs, RTree.pairs,
    RTree.leaves, pauplinCoeff, asymDist]

end MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution
