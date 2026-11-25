/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DSeparation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for d-separation

* The chain `0 → 1 → 2`: `{1}` d-separates `0` from `2`, so every factorization over the chain
  has `X 0 ⊥ X 2 | X 1`. The uniform distribution on three bits is such a factorization, and so
  is `copy3` (a fair bit copied along the chain), where `X 0` and `X 2` are dependent without
  conditioning on `X 1`.
* The collider `0 → 2 ← 1`: the empty set d-separates the two parents, so they are independent;
  given the common child `{2}` they are not d-separated (the trail `0 → 2 ← 1` is active).
-/

@[expose] public section

namespace Cslib.MachineLearning.DSeparationTests

open Cslib.MachineLearning GraphicalModels MetaMathlibExt.FiniteWeight
  MathlibExt.Combinatorics.Digraph.PathCoverWanted

/-- A digraph on `Fin 3` whose edges increase the vertex is acyclic. -/
theorem isAcyclic_of_lt {G : Digraph (Fin 3)} (h : ∀ i j, G.Adj i j → i < j) : G.IsAcyclic := by
  intro x hx
  have : ∀ a b, Relation.TransGen G.Adj a b → a < b := fun a b hab => by
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact lt_irrefl x (this x x hx)

/-- The chain `0 → 1 → 2`. -/
def chain : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

theorem isAcyclic_chain : chain.IsAcyclic :=
  isAcyclic_of_lt fun i j h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- On the chain, a trail to `2` that is active given `{1}` (after any previous vertex) starts
at `2`: the last step into `2` comes from `1`, a non-collider in `{1}`. -/
theorem chain_activeFrom {u w : Fin 3} (t : Trail chain u w) (hw : w = 2) (p : Option (Fin 3))
    (ht : Trail.ActiveFrom {1} p t) : u = 2 := by
  induction t generalizing p with
  | nil => exact hw
  | cons h t ih =>
    rename_i u x w
    obtain ⟨-, hnc, ht'⟩ := ht
    have hx := ih hw (some u) ht'
    subst hx
    rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at h
    have hu : u = 1 := by
      rcases h.2 with (⟨-, h⟩ | ⟨rfl, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h (by decide)
      · rfl
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    subst hu
    refine absurd (Finset.mem_singleton_self 1) (hnc ?_)
    rintro ⟨-, -, x, hx, -, h21⟩
    cases Option.mem_some_iff.mp hx
    rcases h21 with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

theorem dSeparated_chain : DSeparated chain {0} {2} {1} := by
  intro a ha b hb t ht
  rw [Set.mem_singleton_iff] at ha hb
  subst ha hb
  exact absurd (chain_activeFrom t rfl none ht) (by decide)

example {α : Type*} [Fintype α] (p : (Fin 3 → α) → ℝ)
    (hp : FactorizesOverDAG chain p) : CondIndep p {0} {2} ({1} : Finset (Fin 3)) :=
  hp.condIndep isAcyclic_chain dSeparated_chain

/-- The uniform distribution on three bits factorizes over the chain, with every conditional
probability `1 / 2`. -/
theorem factorizesOverDAG_uniform : FactorizesOverDAG chain fun _ : Fin 3 → Bool => (1 / 8 : ℝ) :=
  ⟨fun _ _ => 1 / 2, fun _ => fun _ _ _ => rfl, fun _ _ => by norm_num, by
    funext x
    simp only [Finset.prod_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num⟩

example : CondIndep (fun _ : Fin 3 → Bool => (1 / 8 : ℝ)) {0} {2} ({1} : Finset (Fin 3)) :=
  factorizesOverDAG_uniform.condIndep isAcyclic_chain dSeparated_chain

/-- `X 0` is a fair bit and `X 2 = X 1 = X 0`. -/
noncomputable def copy3 (x : Fin 3 → Bool) : ℝ :=
  if x 1 = x 0 ∧ x 2 = x 1 then 1 / 2 else 0

/-- The conditional probability tables of `copy3`. -/
noncomputable def copyFactor (v : Fin 3) (x : Fin 3 → Bool) : ℝ :=
  if v = 0 then 1 / 2 else if x v = x (v - 1) then 1 else 0

theorem factorizesOverDAG_copy3 : FactorizesOverDAG chain copy3 := by
  refine ⟨copyFactor, fun v x y h => ?_, fun v x => ?_, ?_⟩
  · by_cases h0 : v = 0
    · simp [copyFactor, h0]
    · have hp : chain.Adj (v - 1) v := by fin_cases v <;> simp_all [chain]
      simp only [copyFactor, h0, ite_false]
      rw [h v (Set.mem_insert _ _), h (v - 1) (Set.mem_insert_of_mem _ hp)]
  · by_cases h0 : v = 0
    · simp only [copyFactor, h0, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_bool]
      norm_num
    · have hne : v - 1 ≠ v := by fin_cases v <;> decide
      simp only [copyFactor, h0, ite_false, Function.update_self, Function.update_of_ne hne]
      simp
  · funext x
    simp only [Finset.prod_apply, Fin.prod_univ_three, copyFactor, copy3]
    by_cases h1 : x 1 = x 0 <;> by_cases h2 : x 2 = x 1 <;> simp [h1, h2]

example : CondIndep copy3 {0} {2} ({1} : Finset (Fin 3)) :=
  factorizesOverDAG_copy3.condIndep isAcyclic_chain dSeparated_chain

/-- Without conditioning on `X 1`, `X 0` and `X 2` are dependent under `copy3`. -/
example : ¬CondIndep copy3 {0} {2} ∅ := by
  intro h
  have hx := h ![true, true, false]
  have hnn : ∀ y, 0 ≤ copy3 y := fun y => by unfold copy3; split_ifs <;> norm_num
  have hzero : marginal copy3 ({0} ∪ {2} ∪ ∅) ![true, true, false] = 0 := by
    refine Finset.sum_eq_zero fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have h0 := hy 0 (by simp)
    have h2 := hy 2 (by simp)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two] at h0 h2
    simp only [copy3, h0, h2]
    split_ifs with hc
    · exact absurd (hc.2.trans hc.1) (by simp)
    · rfl
  have hpos : ∀ (U : Set (Fin 3)) (z : Fin 3 → Bool), (∀ v ∈ U, z v = ![true, true, false] v) →
      copy3 z = 1 / 2 → 0 < marginal copy3 U ![true, true, false] := by
    intro U z hz hcz
    classical
    unfold marginal
    refine lt_of_lt_of_le (by norm_num [hcz] : (0 : ℝ) < copy3 z) ?_
    apply Finset.single_le_sum (fun y _ => hnn y)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hz
  have hA := hpos ({0} ∪ ∅) ![true, true, true] (by simp) (by simp [copy3])
  have hB := hpos ({2} ∪ ∅) ![false, false, false] (by simp) (by simp [copy3])
  rw [hzero, zero_mul] at hx
  exact absurd hx (ne_of_lt (mul_pos hA hB))

/-- The collider `0 → 2 ← 1`. -/
def collider : Digraph (Fin 3) where
  Adj i j := (i = 0 ∨ i = 1) ∧ j = 2

theorem isAcyclic_collider : collider.IsAcyclic :=
  isAcyclic_of_lt fun i j h => by rcases h with ⟨rfl | rfl, rfl⟩ <;> decide

/-- On the collider, a trail to `1` that is active given `∅` starts at `1`, or at `2` with no
parent of `2` before it: passing through `2` between its two parents is blocked. -/
theorem collider_activeFrom {u w : Fin 3} (t : Trail collider u w) (hw : w = 1)
    (p : Option (Fin 3)) (ht : Trail.ActiveFrom ∅ p t) :
    u = 1 ∨ (u = 2 ∧ ∀ q ∈ p, ¬collider.Adj q 2) := by
  induction t generalizing p with
  | nil => exact .inl hw
  | cons h t ih =>
    rename_i u x w
    obtain ⟨hc, -, ht'⟩ := ht
    rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at h
    rcases ih hw (some u) ht' with rfl | ⟨rfl, hnot⟩
    · have hu : u = 2 := by
        rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact h
      subst hu
      refine .inr ⟨rfl, fun q hq hq2 => ?_⟩
      obtain ⟨s, hs, -⟩ := hc ⟨q, hq, 1, rfl, hq2, ⟨.inr rfl, rfl⟩⟩
      simp at hs
    · rcases h.2 with h | ⟨h, -⟩
      · exact absurd h (hnot u rfl)
      · exact absurd h (by decide)

theorem dSeparated_collider : DSeparated collider {0} {1} ∅ := by
  intro a ha b hb t ht
  rw [Set.mem_singleton_iff] at ha hb
  subst ha hb
  rcases collider_activeFrom t rfl none ht with h | ⟨h, -⟩ <;> exact absurd h (by decide)

example {α : Type*} [Fintype α] (p : (Fin 3 → α) → ℝ)
    (hp : FactorizesOverDAG collider p) : CondIndep p {0} {1} (∅ : Finset (Fin 3)) :=
  hp.condIndep isAcyclic_collider dSeparated_collider

/-- Observing the common child connects the parents: the trail `0 → 2 ← 1` is active given
`{2}`. -/
example : ¬DSeparated collider {0} {1} {2} := by
  intro h
  have h02 : collider.toSimpleGraphInclusive.Adj 0 2 := by
    rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
    exact ⟨by decide, .inl ⟨.inl rfl, rfl⟩⟩
  have h21 : collider.toSimpleGraphInclusive.Adj 2 1 := by
    rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
    exact ⟨by decide, .inr ⟨.inr rfl, rfl⟩⟩
  refine h 0 rfl 1 rfl (.cons h02 (.cons h21 .nil))
    ⟨fun ⟨_, hq, _⟩ => by simp at hq, fun _ => by decide,
      fun _ => ⟨2, by simp, .refl⟩, fun hnc => absurd ⟨0, rfl, 1, rfl, ⟨.inl rfl, rfl⟩,
        ⟨.inr rfl, rfl⟩⟩ hnc, (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))⟩

end Cslib.MachineLearning.DSeparationTests
