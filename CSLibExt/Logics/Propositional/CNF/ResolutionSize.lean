/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Resolution proof size and width: tree-like versus DAG-like derivations
-/
module

public import CSLibExt.Logics.Propositional.CNF.Resolution

/-!
# Resolution proof size and width

Tree-like resolution derivations are the existing resolution rules as data:
each derived clause is used once, so a shared subderivation is copied. Their
size counts derivation nodes; their width (occurrence width, since clauses
are lists and duplicates are kept) is the largest clause length occurring.
DAG-like derivations are ordered lists of clauses, each an input clause or
the resolvent (with both pivot-membership side conditions) of two earlier
entries; their size is the entry count. Tree derivations convert to the
existing derivability predicate and back, and every tree derivation yields
a DAG derivation of the same clause with no greater size. The examples compute both measures on
explicit refutations. One exhibits the cost of unfolding a shared
subderivation: a 10-entry DAG refutation whose copied tree form has 13
nodes. That is a statement about those two exhibited proofs only; the same
formula also has a 9-node tree refutation (see the tests), and no
optimality or tree-versus-DAG separation is claimed.
-/

@[expose] public section

namespace Cslib
namespace Logic
namespace LegacyPL
namespace CNF

variable {φ : CNF} {C : CNFClause} {l : List CNFClause}

/-- Tree-like resolution derivations as data. -/
inductive TreeDerivation (φ : CNF) : CNFClause → Type
  | ax {C : CNFClause} (h : C ∈ φ) : TreeDerivation φ C
  | resolve (x : Nat) {C D : CNFClause} (hC : TreeDerivation φ C)
      (hD : TreeDerivation φ D) (hxC : (x, true) ∈ C) (hxD : (x, false) ∈ D) :
      TreeDerivation φ (CNFClause.resolvent x C D)

namespace TreeDerivation

/-- The number of nodes (leaves plus resolution steps) of a tree derivation. -/
def size {φ : CNF} {C : CNFClause} : TreeDerivation φ C → Nat
  | .ax _ => 1
  | .resolve _ hC hD _ _ => hC.size + hD.size + 1

/-- The largest clause length occurring in a tree derivation. -/
def width {φ : CNF} {C : CNFClause} : TreeDerivation φ C → Nat
  | .ax _ => C.length
  | @TreeDerivation.resolve _ x C D hC hD _ _ =>
      max (max hC.width hD.width) (CNFClause.resolvent x C D).length

/-- Every tree derivation is a derivability proof. -/
theorem toDerivable : (d : TreeDerivation φ C) → φ.ResolutionDerivable C := by
  intro d
  induction d with
  | ax h => exact ResolutionDerivable.ax h
  | resolve x hC hD hxC hxD ihC ihD =>
      exact ResolutionDerivable.resolve x ihC ihD hxC hxD

/-- Every derivability proof has a tree derivation. -/
theorem ofDerivable : φ.ResolutionDerivable C → Nonempty (TreeDerivation φ C) := by
  intro h
  induction h with
  | ax h => exact ⟨TreeDerivation.ax h⟩
  | resolve x hC hD hxC hxD ihC ihD =>
      obtain ⟨tC⟩ := ihC
      obtain ⟨tD⟩ := ihD
      exact ⟨TreeDerivation.resolve x tC tD hxC hxD⟩

end TreeDerivation

/-- The two-variable unsatisfiable formula: all four sign combinations. -/
def exTwoVar : CNF :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
   [(0, false), (1, true)], [(0, false), (1, false)]]

/-- The explicit refutation: resolve on variable `1` twice, then on `0`. -/
def exTwoVarDerivation : TreeDerivation exTwoVar [] :=
  .resolve (C := [(0, true), (0, true)]) (D := [(0, false), (0, false)]) 0
    (.resolve (C := [(0, true), (1, true)]) (D := [(0, true), (1, false)]) 1
      (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
    (.resolve (C := [(0, false), (1, true)]) (D := [(0, false), (1, false)]) 1
      (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
    (by decide) (by decide)

/-- Its computed tree size is `7`. -/
theorem exTwoVar_size : exTwoVarDerivation.size = 7 := by
  rfl

/-- Its computed width is `2`. -/
theorem exTwoVar_width : exTwoVarDerivation.width = 2 := by
  rfl

/-- DAG-like derivations as ordered lists of clauses. -/
inductive DAGDerivation (φ : CNF) : List CNFClause → Prop
  | nil : DAGDerivation φ []
  | snoc {l : List CNFClause} {C : CNFClause} (h : DAGDerivation φ l)
      (hC : C ∈ φ ∨ ∃ x C₁ C₂, C₁ ∈ l ∧ C₂ ∈ l ∧ (x, true) ∈ C₁ ∧ (x, false) ∈ C₂ ∧
        C = CNFClause.resolvent x C₁ C₂) :
      DAGDerivation φ (l ++ [C])

namespace DAGDerivation

/-- Every clause occurring in a DAG derivation has a tree derivation. -/
theorem exists_tree (h : DAGDerivation φ l) (hC : C ∈ l) :
    Nonempty (TreeDerivation φ C) := by
  induction h generalizing C with
  | nil =>
      simp at hC
  | snoc _ hmem ih =>
      simp only [List.mem_append, List.mem_singleton] at hC
      rcases hC with hCl | rfl
      · exact ih hCl
      · rcases hmem with hax | ⟨x, C₁, C₂, h1, h2, hx1, hx2, rfl⟩
        · exact ⟨TreeDerivation.ax hax⟩
        · obtain ⟨t1⟩ := ih h1
          obtain ⟨t2⟩ := ih h2
          exact ⟨TreeDerivation.resolve x t1 t2 hx1 hx2⟩

end DAGDerivation

/-- The sharing example: the clause `[(0, true), (0, true)]` is derived once
and then used in two different branches. The claim compares the two
exhibited proofs only; no optimality over all tree or DAG refutations is
asserted, and no tree-versus-DAG separation is claimed for this formula. -/
def exDagFormula : CNF :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
   [(0, false), (3, true)], [(0, false), (4, true)],
   [(3, false), (4, false)]]

/-- Its DAG derivation: five input clauses, the shared clause once, two
branch clauses, one combined clause, and the empty clause: ten entries. -/
def exDagList : List CNFClause :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
   [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)], [(4, true)],
   [(3, false), (4, false)], [(4, false)], []]

/-- The sharing list is a DAG derivation of the empty clause. -/
theorem exDag_valid : DAGDerivation exDagFormula exDagList := by
  have h1 : DAGDerivation exDagFormula [[(0, true), (1, true)]] :=
    DAGDerivation.snoc (C := [(0, true), (1, true)]) DAGDerivation.nil
      (Or.inl (by decide))
  have h2 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)]] :=
    DAGDerivation.snoc (C := [(0, true), (1, false)]) h1 (Or.inl (by decide))
  have h3 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)]] :=
    DAGDerivation.snoc (C := [(0, true), (0, true)]) h2
      (Or.inr ⟨1, [(0, true), (1, true)], [(0, true), (1, false)],
        by decide, by decide, by decide, by decide, rfl⟩)
  have h4 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)]] :=
    DAGDerivation.snoc (C := [(0, false), (3, true)]) h3 (Or.inl (by decide))
  have h5 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)]] :=
    DAGDerivation.snoc (C := [(3, true)]) h4
      (Or.inr ⟨0, [(0, true), (0, true)], [(0, false), (3, true)],
        by decide, by decide, by decide, by decide, rfl⟩)
  have h6 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)]] :=
    DAGDerivation.snoc (C := [(0, false), (4, true)]) h5 (Or.inl (by decide))
  have h7 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)], [(4, true)]] :=
    DAGDerivation.snoc (C := [(4, true)]) h6
      (Or.inr ⟨0, [(0, true), (0, true)], [(0, false), (4, true)],
        by decide, by decide, by decide, by decide, rfl⟩)
  have h8 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)], [(4, true)],
       [(3, false), (4, false)]] :=
    DAGDerivation.snoc (C := [(3, false), (4, false)]) h7 (Or.inl (by decide))
  have h9 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)], [(4, true)],
       [(3, false), (4, false)], [(4, false)]] :=
    DAGDerivation.snoc (C := [(4, false)]) h8
      (Or.inr ⟨3, [(3, true)], [(3, false), (4, false)],
        by decide, by decide, by decide, by decide, rfl⟩)
  have h10 : DAGDerivation exDagFormula
      [[(0, true), (1, true)], [(0, true), (1, false)], [(0, true), (0, true)],
       [(0, false), (3, true)], [(3, true)], [(0, false), (4, true)], [(4, true)],
       [(3, false), (4, false)], [(4, false)], []] :=
    DAGDerivation.snoc (C := []) h9
      (Or.inr ⟨4, [(4, true)], [(4, false)],
        by decide, by decide, by decide, by decide, rfl⟩)
  exact h10

/-- Its DAG size (entry count) is `10`. -/
theorem exDag_size : exDagList.length = 10 := by
  rfl

/-- The tree form of the exhibited DAG refutation above, with the shared
subderivation copied into both branches, has size `13`: the unfolding cost
of that one DAG proof. -/
def exTreeDerivation : TreeDerivation exDagFormula [] :=
  .resolve (C := [(4, true)]) (D := [(4, false)]) 4
    (.resolve (C := [(0, true), (0, true)]) (D := [(0, false), (4, true)]) 0
      (.resolve (C := [(0, true), (1, true)]) (D := [(0, true), (1, false)]) 1
        (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
      (.ax (by decide)) (by decide) (by decide))
    (.resolve (C := [(3, true)]) (D := [(3, false), (4, false)]) 3
      (.resolve (C := [(0, true), (0, true)]) (D := [(0, false), (3, true)]) 0
        (.resolve (C := [(0, true), (1, true)]) (D := [(0, true), (1, false)]) 1
          (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))
        (.ax (by decide)) (by decide) (by decide))
      (.ax (by decide)) (by decide) (by decide))
    (by decide) (by decide)

/-- Its computed tree size is `13`, more than the exhibited DAG size `10`;
a regrouped 9-node tree refutation of the same formula also exists, so this
compares two exhibited proofs, not optima. -/
theorem exTree_size : exTreeDerivation.size = 13 := by
  rfl


private theorem DAGDerivation.append {φ : CNF} {l₁ l₂ : List CNFClause}
    (h₁ : DAGDerivation φ l₁) (h₂ : DAGDerivation φ l₂) :
    DAGDerivation φ (l₁ ++ l₂) := by
  induction h₂ generalizing l₁ with
  | nil => simpa using h₁
  | @snoc l C h hC ih =>
      have ih' := ih h₁
      have heq : l₁ ++ (l ++ [C]) = (l₁ ++ l) ++ [C] := by
        simp [List.append_assoc]
      rw [heq]
      exact DAGDerivation.snoc ih' (by
        rcases hC with hax | ⟨x, C₁, C₂, h1, h2, hx1, hx2, rfl⟩
        · exact Or.inl hax
        · exact Or.inr ⟨x, C₁, C₂,
            List.mem_append.mpr (Or.inr h1),
            List.mem_append.mpr (Or.inr h2),
            hx1, hx2, rfl⟩)

/-- Every tree derivation yields a DAG derivation of the same clause
with no greater size:
the concatenation of the two subderivations (sharing between them is
allowed but not needed) followed by the final clause. -/
theorem TreeDerivation.exists_dag (d : TreeDerivation φ C) :
    ∃ l, DAGDerivation φ l ∧ C ∈ l ∧ l.length ≤ d.size := by
  induction d with
  | ax h =>
      refine ⟨[_], DAGDerivation.snoc DAGDerivation.nil (Or.inl h), by simp,
        by simp [TreeDerivation.size]⟩
  | resolve x hC hD hxC hxD ihC ihD =>
      obtain ⟨l₁, hdag₁, hmem₁, hlen₁⟩ := ihC
      obtain ⟨l₂, hdag₂, hmem₂, hlen₂⟩ := ihD
      have happ : DAGDerivation φ (l₁ ++ l₂) := DAGDerivation.append hdag₁ hdag₂
      have hCmem : _ ∈ l₁ ++ l₂ := List.mem_append.mpr (Or.inl hmem₁)
      have hDmem : _ ∈ l₁ ++ l₂ := List.mem_append.mpr (Or.inr hmem₂)
      have hR : DAGDerivation φ ((l₁ ++ l₂) ++ [CNFClause.resolvent x _ _]) :=
        DAGDerivation.snoc happ
          (Or.inr ⟨x, _, _, hCmem, hDmem, hxC, hxD, rfl⟩)
      refine ⟨(l₁ ++ l₂) ++ [CNFClause.resolvent x _ _], hR, by simp, ?_⟩
      simp only [List.length_append, List.length_singleton] at hlen₁ hlen₂ ⊢
      change l₁.length + l₂.length + 1 ≤ hC.size + hD.size + 1
      omega

end CNF
end LegacyPL
end Logic
end Cslib
