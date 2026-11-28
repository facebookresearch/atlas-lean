/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Prod
import MathlibExt.Combinatorics.SimpleGraph.CartesianOppositionProducts

open MetaMathlibExt SimpleGraph

private instance : DecidableRel (pathGraph 3 □ pathGraph 4).Adj :=
  fun _ _ => decidable_of_iff _ boxProd_adj.symm

private def gridReflection : pathGraph 3 □ pathGraph 4 ≃g pathGraph 3 □ pathGraph 4 :=
  ⟨Fin.revPerm.prodCongr Fin.revPerm, (by decide : ∀ p q : Fin 3 × Fin 4,
    (pathGraph 3 □ pathGraph 4).Adj (p.1.rev, p.2.rev) (q.1.rev, q.2.rev) ↔
      (pathGraph 3 □ pathGraph 4).Adj p q) _ _⟩

private def deleted : Finset (Fin 3 × Fin 4) := {(1, 1), (1, 2)}

-- No diagonal step from the deletion center, unlike in the strong product.
example : ¬ (pathGraph 3 □ pathGraph 4).Adj (1, 1) (0, 2) := by decide

-- Independently check the witness on P₃ □ P₄. Keeping vertices (0, 1) and (1, 0)
-- exercises the first-coordinate-only and second-coordinate-only cases respectively.
example : IsCompatiblyAlmostOpposable (pathGraph 3 □ pathGraph 4) := by
  apply (isCompatiblyAlmostOpposable_iff_exists_involution _).mpr
  refine ⟨(1, 1), ↑deleted, (by decide : (1, 1) ∈ deleted), ?_, gridReflection, ?_, ?_⟩
  · have h : ∀ p : Fin 3 × Fin 4, p ∈ deleted →
        p = (1, 1) ∨ (pathGraph 3 □ pathGraph 4).Adj (1, 1) p := by decide
    exact fun p hp => Set.mem_insert_iff.mpr (h p hp)
  · intro p
    exact Prod.ext (Fin.rev_rev p.1) (Fin.rev_rev p.2)
  · simp only [compl_adj]
    change ∀ p : Fin 3 × Fin 4, p ∉ deleted →
      (p.1.rev, p.2.rev) ∉ deleted ∧
        p ≠ (p.1.rev, p.2.rev) ∧ ¬ (pathGraph 3 □ pathGraph 4).Adj p (p.1.rev, p.2.rev)
    decide

-- The singleton product permits the empty induced subgraph after deletion.
example : IsCompatiblyAlmostOpposable ((⊥ : SimpleGraph Unit) □ (⊥ : SimpleGraph Unit)) := by
  apply (isCompatiblyAlmostOpposable_iff_exists_involution _).mpr
  refine ⟨((), ()), Set.univ, Set.mem_univ _, ?_, .refl, fun _ => rfl, ?_⟩
  · exact fun p _ => Set.mem_insert_iff.mpr (Or.inl (Subsingleton.elim p _))
  · exact fun p hp => (hp (Set.mem_univ p)).elim

private def pathThreeReflection : pathGraph 3 ≃g pathGraph 3 :=
  ⟨Fin.revPerm, (by decide : ∀ x y : Fin 3,
    (pathGraph 3).Adj x.rev y.rev ↔ (pathGraph 3).Adj x y) _ _⟩

private def pathFourReflection : pathGraph 4 ≃g pathGraph 4 :=
  ⟨Fin.revPerm, (by decide : ∀ x y : Fin 4,
    (pathGraph 4).Adj x.rev y.rev ↔ (pathGraph 4).Adj x y) _ _⟩

-- Client example: the hypotheses hold with different deletion sets in the two factors.
example : IsCompatiblyAlmostOpposable (pathGraph 3 □ pathGraph 4) := by
  have hα : Function.Involutive pathThreeReflection := Fin.rev_involutive
  have hleft : ∀ x ∉ ({1} : Set (Fin 3)),
      pathThreeReflection x ∉ ({1} : Set (Fin 3)) ∧ (pathGraph 3)ᶜ.Adj x (pathThreeReflection x) := by
    simp only [Set.mem_singleton_iff, compl_adj]
    change ∀ x : Fin 3, x ≠ 1 → x.rev ≠ 1 ∧ x ≠ x.rev ∧ ¬ (pathGraph 3).Adj x x.rev
    decide
  have hG : IsCompatiblyAlmostOpposable (pathGraph 3) :=
    (isCompatiblyAlmostOpposable_iff_exists_involution _).mpr
      ⟨1, {1}, Set.mem_singleton 1, fun _ hx => Set.mem_insert_iff.mpr (Or.inl hx),
        pathThreeReflection, hα, hleft⟩
  let T : Finset (Fin 4) := {1, 2}
  have hH : IsCompatiblyAlmostOpposable (pathGraph 4) := by
    apply (isCompatiblyAlmostOpposable_iff_exists_involution _).mpr
    refine ⟨1, ↑T, (by decide : (1 : Fin 4) ∈ T), ?_, pathFourReflection,
      Fin.rev_involutive, ?_⟩
    · have h : ∀ y : Fin 4, y ∈ T → y = 1 ∨ (pathGraph 4).Adj 1 y := by decide
      exact fun y hy => Set.mem_insert_iff.mpr (h y hy)
    · simp only [compl_adj]
      change ∀ y : Fin 4, y ∉ T → y.rev ∉ T ∧ y ≠ y.rev ∧ ¬ (pathGraph 4).Adj y y.rev
      decide
  exact isCompatiblyAlmostOpposable_boxProd _ _ hG hH
    ⟨1, pathThreeReflection, hα, (exists_compatible_opposition_iff hα).mpr hleft⟩
