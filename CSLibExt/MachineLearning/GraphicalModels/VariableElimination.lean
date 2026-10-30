/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import Mathlib.Tactic.Ring

/-!
# Variable elimination and sum-product on trees

A pairwise model on a tree has vertices `0, …, n` listed so that every vertex `k + 1` has a parent
`par k ≤ k` (vertex `0` is the root). It has a unary factor on each vertex and a pairwise factor
on each edge (between vertex `k + 1` and its parent), with values in `ℝ`. The unnormalized weight
of an assignment `x` is the product of all factors, and the partition function is the sum of the
weights over all assignments.

The last vertex is a leaf (no vertex has a later parent), so it can be summed out: its message
`m a = ∑ b, pair (b, a) * unary_leaf b` is multiplied into the unary factor of its parent. Repeating
this until only the root is left is variable elimination in reverse topological order, that is,
sum-product message passing from the leaves to the root.

## Main results

* `eliminate`: the model on `0, …, n` obtained from a model on `0, …, n + 1` by summing out the last
  vertex; `sum_weight_mul_eliminate`: it has the same weighted sums of any function of the root.
* `rootMessage`: the product of the root's unary factor and the messages arriving at the root after
  eliminating all other vertices; `sum_weight_mul_eq`: **variable elimination is exact**: for every
  function `g` of the root value, `∑ x, weight x * g (x 0) = ∑ a, rootMessage a * g a`. In
  particular `partition_eq` computes the partition function and `rootMarginal_eq` the unnormalized
  marginal of the root.

A Bayesian network whose graph is a tree is the case with the prior as the root's unary factor and
the conditional probability tables as edge factors (see the tests). Hidden Markov models are the
chain case with emission factors as unary factors; their forward algorithm is in
`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset

variable {α : Type*}

/-- A pairwise model on a tree with vertices `0, …, n` in topological order. -/
structure TreeModel (α : Type*) (n : ℕ) where
  /-- The parent of vertex `k + 1`, among the vertices `0, …, k`. -/
  par : (k : Fin n) → Fin (k + 1)
  /-- The unary factor of each vertex. -/
  unary : Fin (n + 1) → α → ℝ
  /-- The factor of the edge between vertex `k + 1` (first argument) and its parent (second). -/
  pair : Fin n → α → α → ℝ

namespace TreeModel
variable {n : ℕ}

/-- The parent of vertex `k + 1`, as a vertex. -/
def parent (m : TreeModel α n) (k : Fin n) : Fin (n + 1) :=
  ⟨m.par k, by have := (m.par k).2; have := k.2; omega⟩

/-- The unnormalized weight of an assignment: the product of all factors. -/
noncomputable def weight (m : TreeModel α n) (x : Fin (n + 1) → α) : ℝ :=
  (∏ i, m.unary i (x i)) * ∏ k, m.pair k (x k.succ) (x (m.parent k))

/-- The parent of the last vertex, as a vertex of the smaller tree. -/
def lastParent (m : TreeModel α (n + 1)) : Fin (n + 1) :=
  ⟨m.par (Fin.last n), by have := (m.par (Fin.last n)).2; simp at this; omega⟩

/-- The message from the last vertex to its parent. -/
noncomputable def message [Fintype α] (m : TreeModel α (n + 1)) (a : α) : ℝ :=
  ∑ b, m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b

/-- Sum out the last vertex: multiply its message into the unary factor of its parent. -/
noncomputable def eliminate [Fintype α] (m : TreeModel α (n + 1)) :
    TreeModel α n where
  par k := m.par k.castSucc
  unary i a := m.unary i.castSucc a * if i = m.lastParent then m.message a else 1
  pair k := m.pair k.castSucc

theorem parent_castSucc [Fintype α] (m : TreeModel α (n + 1)) (k : Fin n) :
    m.parent k.castSucc = (m.eliminate.parent k).castSucc :=
  rfl

theorem parent_last (m : TreeModel α (n + 1)) :
    m.parent (Fin.last n) = m.lastParent.castSucc :=
  rfl

theorem weight_snoc [Fintype α] (m : TreeModel α (n + 1)) (y : Fin (n + 1) → α)
    (b : α) :
    m.weight (Fin.snoc y b) = ((∏ i, m.unary i.castSucc (y i)) *
        ∏ k, m.eliminate.pair k (y k.succ) (y (m.eliminate.parent k))) *
      (m.pair (Fin.last n) b (y m.lastParent) * m.unary (Fin.last (n + 1)) b) := by
  rw [weight, Fin.prod_univ_castSucc (n := n + 1),
    Fin.prod_univ_castSucc (fun k : Fin (n + 1) =>
      m.pair k ((Fin.snoc y b : Fin (n + 2) → α) k.succ)
        ((Fin.snoc y b : Fin (n + 2) → α) (m.parent k))), parent_last]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, parent_castSucc, Fin.succ_last]
  simp only [eliminate]
  ring

theorem eliminate_weight [Fintype α] (m : TreeModel α (n + 1))
    (y : Fin (n + 1) → α) :
    m.eliminate.weight y = ((∏ i, m.unary i.castSucc (y i)) *
        ∏ k, m.eliminate.pair k (y k.succ) (y (m.eliminate.parent k))) *
      m.message (y m.lastParent) := by
  rw [weight]
  simp only [eliminate, prod_mul_distrib, prod_ite_eq', mem_univ, ↓reduceIte]
  ring

/-- **One step of variable elimination**: summing out the last vertex preserves every weighted sum
of a function of the root. -/
theorem sum_weight_mul_eliminate [Fintype α] (m : TreeModel α (n + 1)) (g : α → ℝ) :
    ∑ x, m.weight x * g (x 0) = ∑ y, m.eliminate.weight y * g (y 0) := by
  rw [sum_snoc]
  refine sum_congr rfl fun y _ => ?_
  have hroot : ∀ b, (Fin.snoc y b : Fin (n + 2) → α) 0 = y 0 := fun b =>
    Fin.snoc_castSucc (α := fun _ => α) b y 0
  simp only [hroot, ← sum_mul, weight_snoc, ← mul_sum, eliminate_weight, message]

/-- The unnormalized marginal of the root computed by variable elimination: eliminate the vertices
from the last one down, then read off the root's unary factor. -/
noncomputable def rootMessage [Fintype α] : {n : ℕ} → TreeModel α n → α → ℝ
  | 0, m => m.unary 0
  | _ + 1, m => rootMessage m.eliminate

/-- **Variable elimination is exact**: for every function `g` of the root value,
`∑ x, weight x * g (x 0) = ∑ a, rootMessage a * g a`. -/
theorem sum_weight_mul_eq [Fintype α] :
    ∀ {n : ℕ} (m : TreeModel α n) (g : α → ℝ),
      ∑ x, m.weight x * g (x 0) = ∑ a, m.rootMessage a * g a
  | 0, m, g => by
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp [weight, rootMessage]
  | _ + 1, m, g => by
    rw [sum_weight_mul_eliminate, sum_weight_mul_eq m.eliminate g]
    rfl

/-- Variable elimination computes the partition function. -/
theorem partition_eq [Fintype α] {n : ℕ} (m : TreeModel α n) :
    ∑ x, m.weight x = ∑ a, m.rootMessage a := by
  simpa using m.sum_weight_mul_eq fun _ => 1

/-- Variable elimination computes the unnormalized marginal of the root. -/
theorem rootMarginal_eq [Fintype α] [DecidableEq α] {n : ℕ} (m : TreeModel α n) (a : α) :
    ∑ x with x 0 = a, m.weight x = m.rootMessage a := by
  have h := m.sum_weight_mul_eq fun b => if b = a then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, sum_filter]

end TreeModel

end Cslib.MachineLearning.GraphicalModels
