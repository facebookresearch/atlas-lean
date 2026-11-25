/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DSeparationCompleteness

/-!
# Tests for the completeness of d-separation

* A single edge `0 → 1`: the empty set does not d-separate its two ends, so some network on the
  edge makes `X₀` and `X₁` dependent, with two values and with three values per node.
* The collider `0 → 2 ← 1` with a child `2 → 3`: conditioning on the child `3` of the collider,
  not on the collider itself, activates the path `0 → 2 ← 1`, so some network on this graph
  makes `X₀` and `X₁` dependent given `X₃`; the same holds with the larger set `{1, 2}` in place
  of `{1}`.
-/

@[expose] public section

namespace Cslib.MachineLearning.DSeparationCompletenessTests

open Cslib.MachineLearning GraphicalModels Convexity MetaMathlibExt.FiniteWeight

/-- The single edge `0 → 1` with values in `β`, with constant tables. -/
noncomputable def edgeNet (β : Type) (a : β) : BayesNet β 2 where
  pa k := if h : (k : ℕ) = 0 then ∅ else {⟨0, by omega⟩}
  cpt _ _ := StdSimplex.single a

theorem edgeNet_edge {β : Type} (a : β) : (edgeNet β a).Edge 0 1 :=
  ⟨by decide, by simp [edgeNet]⟩

/-- The empty set does not d-separate the two ends of an edge. -/
theorem edgeNet_not_dSeparated {β : Type} (a : β) :
    ¬(edgeNet β a).DSeparated ↑({0} : Finset (Fin 2)) ↑({1} : Finset (Fin 2))
      ↑(∅ : Finset (Fin 2)) := by
  intro h
  obtain ⟨i, hi, -⟩ := h 0 (by simp) 1 (by simp) [0, 1]
    ⟨by decide, List.isChain_pair.2 (Or.inl (edgeNet_edge a)), rfl, rfl⟩
  simp at hi

/-- Completeness on a single edge with two values. -/
example : ∃ b' : BayesNet Bool 2, b'.pa = (edgeNet Bool false).pa ∧
    ¬CondIndep b'.joint ↑({0} : Finset (Fin 2)) ↑({1} : Finset (Fin 2))
      ↑(∅ : Finset (Fin 2)) :=
  BayesNet.exists_not_condIndep_of_not_dSeparated _ _ _ _ (by decide) (by decide) (by decide)
    (edgeNet_not_dSeparated false)

/-- Completeness on a single edge with three values. -/
example : ∃ b' : BayesNet (Fin 3) 2, b'.pa = (edgeNet (Fin 3) 0).pa ∧
    ¬CondIndep b'.joint ↑({0} : Finset (Fin 2)) ↑({1} : Finset (Fin 2))
      ↑(∅ : Finset (Fin 2)) :=
  BayesNet.exists_not_condIndep_of_not_dSeparated _ _ _ _ (by decide) (by decide) (by decide)
    (edgeNet_not_dSeparated 0)

/-- The collider `0 → 2 ← 1` with a child `2 → 3`, with constant tables. -/
noncomputable def colliderChildNet : BayesNet Bool 4 where
  pa k := match k with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => ∅
    | ⟨2, _⟩ => {0, 1}
    | ⟨3, _⟩ => {2}
    | ⟨_ + 4, h⟩ => absurd h (by omega)
  cpt _ _ := StdSimplex.single false

/-- Conditioning on the child `3` of the collider `2` leaves the path `0 → 2 ← 1` unblocked. -/
theorem colliderChildNet_not_dSeparated :
    ¬colliderChildNet.DSeparated ↑({0} : Finset (Fin 4)) ↑({1} : Finset (Fin 4))
      ↑({3} : Finset (Fin 4)) := by
  have e02 : colliderChildNet.Edge 0 2 := by decide
  have e12 : colliderChildNet.Edge 1 2 := by decide
  have e23 : colliderChildNet.Edge 2 3 := by decide
  intro h
  obtain ⟨i, hi, hb⟩ := h 0 (by simp) 1 (by simp) [0, 2, 1]
    ⟨by decide, List.isChain_cons_cons.2 ⟨Or.inl e02, List.isChain_pair.2 (Or.inr e12)⟩, rfl,
      rfl⟩
  obtain rfl : i = 0 := by simp at hi; omega
  rcases hb with ⟨-, -, hd⟩ | ⟨hc, -⟩
  · exact hd 3 (Relation.ReflTransGen.single e23) (by simp)
  · exact hc ⟨e02, e12⟩

/-- **Activation through a descendant.** Some network on the graph of `colliderChildNet` makes
`X₀` and `X₁` dependent given the child `X₃` of their common child. -/
theorem exists_not_condIndep_colliderChild : ∃ b' : BayesNet Bool 4,
    b'.pa = colliderChildNet.pa ∧ ¬CondIndep b'.joint ↑({0} : Finset (Fin 4))
      ↑({1} : Finset (Fin 4)) ↑({3} : Finset (Fin 4)) :=
  BayesNet.exists_not_condIndep_of_not_dSeparated _ _ _ _ (by decide) (by decide) (by decide)
    colliderChildNet_not_dSeparated

/-- A larger set: `{1, 2}` contains `1`, so `{3}` does not d-separate `{0}` from `{1, 2}` either,
and the theorem applies to these sets as well. -/
example : ∃ b' : BayesNet Bool 4, b'.pa = colliderChildNet.pa ∧
    ¬CondIndep b'.joint ↑({0} : Finset (Fin 4)) ↑({1, 2} : Finset (Fin 4))
      ↑({3} : Finset (Fin 4)) := by
  refine BayesNet.exists_not_condIndep_of_not_dSeparated _ _ _ _ (by decide) (by decide)
    (by decide) fun h => colliderChildNet_not_dSeparated fun x hx y hy p hp =>
      h x hx y (by simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hy; simp [hy]) p hp

end Cslib.MachineLearning.DSeparationCompletenessTests
