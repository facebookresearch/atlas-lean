/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matching.ShortAugmentingPath
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! Tests for the short augmenting path bound and for disjoint augmenting paths. -/

namespace MetaMathlibExt.ShortAugmentingPathTest

open SimpleGraph
open scoped symmDiff

/-- A shared edge and two additional edges give a gap of two. The comparison matching
leaves vertices uncovered in the complete graph, and the floor forces a one-edge walk. -/
example : ∃ (u v : Fin 8) (p : (⊤ : SimpleGraph (Fin 8)).Walk u v),
    IsAugmentingWalk {s(0, 1)} p ∧ p.length = 1 := by
  let M : Finset (Sym2 (Fin 8)) := {s(0, 1)}
  let N : Finset (Sym2 (Fin 8)) := {s(0, 1), s(2, 3), s(4, 5)}
  obtain ⟨u, v, p, hp, hle⟩ := exists_isAugmentingWalk_length_le ⊤ M N
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbound : 2 * (M.card / (N.card - M.card)) + 1 = 1 := by decide
  exact ⟨u, v, p, hp, by have := hp.2.2.2.2.2; omega⟩

private lemma path_length_bounds {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    u.val ≤ v.val + p.length ∧ v.val ≤ u.val + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    have := pathGraph_adj.mp h
    simp only [Walk.length_cons]
    omega

/-- When just the middle edge of a four-vertex path is matched, the bound of three is sharp. -/
example : ∃ (u v : Fin 4) (p : (pathGraph 4).Walk u v),
    IsAugmentingWalk {s(1, 2)} p ∧ p.length = 3 := by
  let M : Finset (Sym2 (Fin 4)) := {s(1, 2)}
  let N : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}
  obtain ⟨u, v, p, hp, hle⟩ := exists_isAugmentingWalk_length_le (pathGraph 4) M N
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbound : 2 * (M.card / (N.card - M.card)) + 1 = 3 := by decide
  have hends : ∀ x y : Fin 4, x ≠ y → x ∉ s(1, 2) → y ∉ s(1, 2) →
      x.val + 3 ≤ y.val ∨ y.val + 3 ≤ x.val := by decide
  have := hends u v hp.1 (hp.2.2.1 _ (by simp [M])) (hp.2.2.2.1 _ (by simp [M]))
  have := path_length_bounds p
  exact ⟨u, v, p, hp, by omega⟩

/-- With no gap and no vertices, the theorem supplies the empty family. -/
example : ∃ P : Fin 0 → (u : Fin 0) × (v : Fin 0) × (⊥ : SimpleGraph (Fin 0)).Walk u v,
    (∀ i, IsAugmentingWalk ∅ (P i).2.2 ∧ ∀ e ∈ (P i).2.2.edges, e ∈ (∅ : Finset _)) ∧
      ∀ i j, i ≠ j → List.Disjoint (P i).2.2.support (P j).2.2.support := by
  exact exists_disjoint_augmentingWalks (⊥ : SimpleGraph (Fin 0)) ∅ ∅
    (by simp) (by simp) (by simp) (by simp)

/-- A shared edge, a three-edge alternating path, and a single-edge component give two
vertex-disjoint augmenting walks without using the shared edge. -/
example : ∃ (u v x y : Fin 8) (p : (⊤ : SimpleGraph (Fin 8)).Walk u v)
    (q : (⊤ : SimpleGraph (Fin 8)).Walk x y),
    IsAugmentingWalk {s(0, 1), s(3, 4)} p ∧ IsAugmentingWalk {s(0, 1), s(3, 4)} q ∧
      (∀ e ∈ p.edges ++ q.edges, e ∈ ({s(2, 3), s(3, 4), s(4, 5), s(6, 7)} : Finset _)) ∧
      List.Disjoint p.support q.support := by
  let M : Finset (Sym2 (Fin 8)) := {s(0, 1), s(3, 4)}
  let N : Finset (Sym2 (Fin 8)) := {s(0, 1), s(2, 3), s(4, 5), s(6, 7)}
  obtain ⟨P, hP, hdisj⟩ := exists_disjoint_augmentingWalks ⊤ M N
    (by decide) (by decide) (by decide) (by decide)
  have hgap : N.card - M.card = 2 := by decide
  let i : Fin (N.card - M.card) := ⟨0, by rw [hgap]; decide⟩
  let j : Fin (N.card - M.card) := ⟨1, by rw [hgap]; decide⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  refine ⟨(P i).1, (P i).2.1, (P j).1, (P j).2.1, (P i).2.2, (P j).2.2,
    (hP i).1, (hP j).1, ?_, hdisj i j hij⟩
  have hdiff : M ∆ N = {s(2, 3), s(3, 4), s(4, 5), s(6, 7)} := by decide
  rw [← hdiff]
  intro e he
  exact (List.mem_append.mp he).elim ((hP i).2 e) ((hP j).2 e)

end MetaMathlibExt.ShortAugmentingPathTest
