/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwoDefs

namespace MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo

open MetaMathlibExt.BitstringEncoding
open StrongConnectivityAugmentation
  (StrongConnectivityAugmentationInstance weight StrongConnectivityAugmentationFeasible arcDigraph)

/-- Two vertices, no arcs, `w(0, 1) = 1` and `w(1, 0) = 2` (and `1` on the diagonal), with
bound `B`. -/
private abbrev pair (B : ℕ) : StrongConnectivityAugmentationInstance :=
  (2, [], [[1, 1], [2, 1]], B)

private theorem pair_three_wellFormed : WellFormed (pair 3) := by
  unfold WellFormed StrongConnectivityAugmentation.WellFormed weight; decide

private theorem pair_two_wellFormed : WellFormed (pair 2) := by
  unfold WellFormed StrongConnectivityAugmentation.WellFormed weight; decide

/-- Adding both pairs `(0, 1)` and `(1, 0)`, of total weight `3`, makes the two vertices
strongly connected. -/
private theorem pair_three_feasible : StrongConnectivityAugmentationFeasible (pair 3) := by
  have hadj : ∀ u v : Fin 2, u ≠ v →
      (arcDigraph 2 ([] ++ [(0, 1), (1, 0)])).Adj u v := by
    have h : ∀ u v : Fin 2, u ≠ v → ((u : ℕ), (v : ℕ)) ∈ ([] : List (ℕ × ℕ)) ++ [(0, 1), (1, 0)] := by
      decide
    exact h
  refine ⟨[(0, 1), (1, 0)], by decide, by decide, fun u v => ?_⟩
  by_cases huv : u = v
  · exact huv ▸ .refl
  · exact .single (hadj u v huv)

/-- On two vertices, reaching the other vertex `b` from `a` needs the pair `(a, b)`. -/
private theorem needs_pair (A : List (ℕ × ℕ)) {a b : Fin 2} (hab : a ≠ b)
    (h : Relation.ReflTransGen (arcDigraph 2 ([] ++ A)).Adj a b) :
    ((a : ℕ), (b : ℕ)) ∈ A := by
  have key : ∀ y, Relation.ReflTransGen (arcDigraph 2 ([] ++ A)).Adj a y →
      y = a ∨ ((a : ℕ), (b : ℕ)) ∈ A := by
    intro y hy
    induction hy with
    | refl => exact .inl rfl
    | @tail y c _ hyc ih =>
      rcases ih with rfl | hmem
      · by_cases hca : c = y
        · exact .inl hca
        · right
          have hcb : c = b := by
            have := c.isLt
            have := b.isLt
            have := y.isLt
            have h1 : (c : ℕ) ≠ y := fun h => hca (Fin.ext h)
            have h2 : (b : ℕ) ≠ y := fun h => hab (Fin.ext h).symm
            exact Fin.ext (by omega)
          subst hcb
          simpa [arcDigraph] using hyc
      · exact .inr hmem
  rcases key b h with rfl | hmem
  · exact absurd rfl hab
  · exact hmem

/-- Two distinct members of a list contribute both their values to the sum. -/
private theorem two_le_sum (f : ℕ × ℕ → ℕ) {l : List (ℕ × ℕ)} {x y : ℕ × ℕ} (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x ≠ y) : f x + f y ≤ (l.map f).sum := by
  have p1 := List.perm_cons_erase hx
  have hy' : y ∈ l.erase x := (List.mem_erase_of_ne (Ne.symm hxy)).mpr hy
  have p2 := List.perm_cons_erase hy'
  rw [(p1.map f).sum_eq, List.map_cons, List.sum_cons, (p2.map f).sum_eq, List.map_cons,
    List.sum_cons]
  omega

/-- With bound `2` the pair is infeasible: strong connectivity needs both `(0, 1)` and
`(1, 0)`, of total weight `3`. -/
private theorem pair_two_infeasible : ¬ StrongConnectivityAugmentationFeasible (pair 2) := by
  rintro ⟨A, -, hw, hconn⟩
  have h01 := needs_pair A (by decide : (0 : Fin 2) ≠ 1) (hconn 0 1)
  have h10 := needs_pair A (by decide : (1 : Fin 2) ≠ 0) (hconn 1 0)
  have := two_le_sum (fun a => StrongConnectivityAugmentation.weight [[1, 1], [2, 1]] a.1 a.2)
    h01 h10 (by decide)
  change (A.map fun a => weight [[1, 1], [2, 1]] a.1 a.2).sum ≤ 2 at hw
  have hw01 : StrongConnectivityAugmentation.weight [[1, 1], [2, 1]] ((0 : Fin 2) : ℕ)
      ((1 : Fin 2) : ℕ) = 1 := by decide
  have hw10 : StrongConnectivityAugmentation.weight [[1, 1], [2, 1]] ((1 : Fin 2) : ℕ)
      ((0 : Fin 2) : ℕ) = 2 := by decide
  simp only [hw01, hw10] at this
  omega

/-- The path `0 → 1 → 2` with weights `1` and bound `1`: feasible for the general problem by
adding `(2, 0)`. -/
private abbrev path : StrongConnectivityAugmentationInstance :=
  (3, [(0, 1), (1, 2)], [[1, 1, 1], [1, 1, 1], [1, 1, 1]], 1)

private theorem path_feasible : StrongConnectivityAugmentationFeasible path := by
  have hadj : ∀ u : Fin 3, (arcDigraph 3 ([(0, 1), (1, 2)] ++ [(2, 0)])).Adj u (u + 1) := by
    have h : ∀ u : Fin 3, ((u : ℕ), ((u + 1 : Fin 3) : ℕ)) ∈ [(0, 1), (1, 2)] ++ [(2, 0)] := by
      decide
    exact h
  refine ⟨[(2, 0)], by decide, by decide, fun u v => ?_⟩
  have hv : v = u ∨ v = u + 1 ∨ v = u + 1 + 1 := by revert u v; decide
  rcases hv with rfl | rfl | rfl
  · exact .refl
  · exact .single (hadj u)
  · exact .tail (.single (hadj u)) (hadj (u + 1))

private theorem path_parent_wellFormed : StrongConnectivityAugmentation.WellFormed path := by
  unfold StrongConnectivityAugmentation.WellFormed StrongConnectivityAugmentation.weight; decide

/-- The restriction requires `G` to have no arcs. -/
private theorem path_not_wellFormed : ¬ WellFormed path := fun h => absurd h.2.1 (by decide)

/-- A weight `3` is outside `{1, 2}`. -/
example : ¬ WellFormed ((2, [], [[1, 3], [1, 1]], 5) : StrongConnectivityAugmentationInstance) := by
  unfold WellFormed StrongConnectivityAugmentation.WellFormed weight; decide

/-- The decision problem accepts the encoding of `pair 3`. -/
example : strongConnectivityAugmentationWeightsOneTwoDec (bitEncode (pair 3)) = true := by
  simp [strongConnectivityAugmentationWeightsOneTwoDec, pair_three_wellFormed,
    pair_three_feasible]

/-- It rejects the encoding of the well-formed but infeasible `pair 2`. -/
example : strongConnectivityAugmentationWeightsOneTwoDec (bitEncode (pair 2)) = false := by
  simp [strongConnectivityAugmentationWeightsOneTwoDec, pair_two_infeasible]

/-- `pair 2` is well formed, so infeasibility is what rejects it. -/
example : WellFormed (pair 2) := pair_two_wellFormed

/-- The general problem accepts `path`; the restriction rejects it because `G` has arcs. -/
example :
    StrongConnectivityAugmentation.strongConnectivityAugmentationDec (bitEncode path) = true ∧
      strongConnectivityAugmentationWeightsOneTwoDec (bitEncode path) = false :=
  ⟨by simp [StrongConnectivityAugmentation.strongConnectivityAugmentationDec,
      path_parent_wellFormed, path_feasible],
    by simp [strongConnectivityAugmentationWeightsOneTwoDec, path_not_wellFormed]⟩

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : strongConnectivityAugmentationWeightsOneTwoDec [true] = false := by
  have h : bitDecode (α := StrongConnectivityAugmentationInstance) [true] = none := rfl
  simp [strongConnectivityAugmentationWeightsOneTwoDec, h]

end MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentationWeightsOneTwo
