/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.VariableElimination
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Belief propagation on trees: every marginal, and max-product MAP decoding

`VariableElimination.lean` computes the marginal of the root of a pairwise tree model by sending
messages from the leaves up to the root. Belief propagation also sends messages down the tree,
so that every vertex receives a message through each of its edges, and computes the marginal of
every vertex.

**Sum-product.** The belief of a vertex `v` combines the messages from its subtree, which variable
elimination of the later vertices multiplies into its unary factor, with the message from its
parent. The message from the parent is computed from the parent's belief in the model without
`v`'s subtree, the cavity distribution (Pearl's π-message). On the numbered tree this is a
recursion on the number of vertices:

* `dropLast`: the model without its last vertex (a leaf); `weight_snoc_dropLast`: the weight
  of a model is the weight of the dropped model times the factors at the last vertex.
* `belief m v`: for the last vertex, its unary factor times `downMessage m`, where
  `downMessage m b = ∑ a, pair b a * belief (dropLast m) (lastParent) a`; for every other vertex,
  its belief in the eliminated model `m.eliminate`.
* `sum_weight_mul_eq_belief` (**belief propagation is exact on trees**): for every vertex `v`
  and every function `g` of its value, `∑ x, weight x * g (x v) = ∑ a, belief v a * g a`. Hence
  `marginal_eq_belief`: `belief v a` is the unnormalized marginal of `v` at `a`, and
  `belief_zero`: at the root it is variable elimination's `rootMessage`.

**Max-product.** Replacing sums by maxima computes the largest weight and a maximizing assignment
(the MAP assignment), for nonnegative factors (`NonnegFactors`):

* `maxMessage`, `maxEliminate`: the max-product message of the last vertex and the model with the
  last vertex maximized out; `maxWeight`: the maximum computed by maximizing out the vertices from
  the last one down.
* `decode`: back-tracking: decode the smaller model, then give the last vertex a value attaining
  its max-product message at its parent's decoded value.
* `weight_le_maxWeight`, `weight_decode`, `weight_le_weight_decode` (**max-product decoding finds
  a MAP assignment**): every assignment has weight at most `maxWeight`, and the decoded
  assignment attains it.

The forward algorithm and the Viterbi algorithm for hidden Markov models (the chain case) are in
`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`.

## References

* J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988, Chapter 4.
* D. Koller and N. Friedman, *Probabilistic Graphical Models*, MIT Press, 2009, Chapters 10
  and 13.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset

variable {α : Type*}

namespace TreeModel

variable {n : ℕ}

/-! ### Sum-product: every marginal -/

/-- The model without its last vertex, which is a leaf: its unary factor and the factor of its
edge are discarded. -/
def dropLast (m : TreeModel α (n + 1)) : TreeModel α n where
  par k := m.par k.castSucc
  unary i := m.unary i.castSucc
  pair k := m.pair k.castSucc

theorem parent_castSucc_dropLast (m : TreeModel α (n + 1)) (k : Fin n) :
    m.parent k.castSucc = (m.dropLast.parent k).castSucc :=
  rfl

theorem weight_snoc_dropLast (m : TreeModel α (n + 1)) (y : Fin (n + 1) → α) (b : α) :
    m.weight (Fin.snoc y b) = m.dropLast.weight y *
      (m.pair (Fin.last n) b (y m.lastParent) * m.unary (Fin.last (n + 1)) b) := by
  rw [weight, Fin.prod_univ_castSucc (n := n + 1),
    Fin.prod_univ_castSucc (fun k : Fin (n + 1) =>
      m.pair k ((Fin.snoc y b : Fin (n + 2) → α) k.succ)
        ((Fin.snoc y b : Fin (n + 2) → α) (m.parent k))), parent_last]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, parent_castSucc_dropLast,
    Fin.succ_last]
  simp only [weight, dropLast]
  ring

/-- Summing out the last vertex preserves weighted sums of a function of any other vertex. -/
theorem sum_weight_mul_eliminate_castSucc [Fintype α] (m : TreeModel α (n + 1))
    (v : Fin (n + 1)) (g : α → ℝ) :
    ∑ x, m.weight x * g (x v.castSucc) = ∑ y, m.eliminate.weight y * g (y v) := by
  rw [sum_snoc]
  refine sum_congr rfl fun y _ => ?_
  have hv : ∀ b, (Fin.snoc y b : Fin (n + 2) → α) v.castSucc = y v := fun b =>
    Fin.snoc_castSucc (α := fun _ => α) b y v
  simp only [hv, ← sum_mul, weight_snoc, ← mul_sum, eliminate_weight, message]

mutual

/-- The **belief** of each vertex computed by sum-product message passing: the product of its
unary factor, the messages from its subtree and the message from its parent. -/
noncomputable def belief [Fintype α] : {n : ℕ} → TreeModel α n → Fin (n + 1) → α → ℝ
  | 0, m => fun _ => m.unary 0
  | _ + 1, m => Fin.lastCases (fun b => m.unary (Fin.last _) b * downMessage m b)
      (belief m.eliminate)

/-- The message from the parent of the last vertex to the last vertex: the edge factor summed
against the parent's belief in the model without the last vertex. -/
noncomputable def downMessage [Fintype α] : {n : ℕ} → TreeModel α (n + 1) → α → ℝ
  | _, m => fun b => ∑ a, m.pair (Fin.last _) b a * belief m.dropLast m.lastParent a

end

theorem belief_last [Fintype α] (m : TreeModel α (n + 1)) (b : α) :
    belief m (Fin.last (n + 1)) b = m.unary (Fin.last (n + 1)) b * downMessage m b := by
  simp [belief]

theorem belief_castSucc [Fintype α] (m : TreeModel α (n + 1)) (v : Fin (n + 1)) :
    belief m v.castSucc = belief m.eliminate v := by
  simp [belief]

theorem downMessage_apply [Fintype α] (m : TreeModel α (n + 1)) (b : α) :
    downMessage m b = ∑ a, m.pair (Fin.last n) b a * belief m.dropLast m.lastParent a := by
  simp [downMessage]

/-- **Belief propagation is exact on trees**: for every vertex `v` and every function `g` of its
value, `∑ x, weight x * g (x v) = ∑ a, belief v a * g a`. -/
theorem sum_weight_mul_eq_belief [Fintype α] :
    ∀ {n : ℕ} (m : TreeModel α n) (v : Fin (n + 1)) (g : α → ℝ),
      ∑ x, m.weight x * g (x v) = ∑ a, belief m v a * g a
  | 0, m, v, g => by
    obtain rfl := Fin.fin_one_eq_zero v
    rw [sum_weight_mul_eq, rootMessage]
    simp [belief]
  | n + 1, m, v, g => by
    induction v using Fin.lastCases with
    | last =>
      rw [sum_snoc]
      simp only [Fin.snoc_last, weight_snoc_dropLast, belief_last, downMessage_apply]
      have h : ∀ y : Fin (n + 1) → α, ∑ b, m.dropLast.weight y *
          (m.pair (Fin.last n) b (y m.lastParent) * m.unary (Fin.last (n + 1)) b) * g b =
          m.dropLast.weight y * (fun a => ∑ b, m.pair (Fin.last n) b a *
            m.unary (Fin.last (n + 1)) b * g b) (y m.lastParent) := fun y => by
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by ring
      rw [sum_congr rfl fun y _ => h y, sum_weight_mul_eq_belief m.dropLast m.lastParent
        (fun a => ∑ b, m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b * g b)]
      simp only [sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
    | cast v =>
      rw [sum_weight_mul_eliminate_castSucc, sum_weight_mul_eq_belief m.eliminate v g,
        belief_castSucc]

/-- The belief of a vertex is its unnormalized marginal. -/
theorem marginal_eq_belief [Fintype α] [DecidableEq α] (m : TreeModel α n) (v : Fin (n + 1))
    (a : α) : ∑ x with x v = a, m.weight x = belief m v a := by
  have h := m.sum_weight_mul_eq_belief v fun b => if b = a then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, sum_filter]

/-- At the root, the belief is variable elimination's root message. -/
theorem belief_zero [Fintype α] : ∀ {n : ℕ} (m : TreeModel α n), belief m 0 = m.rootMessage
  | 0, m => by
    funext a
    simp [belief, rootMessage]
  | n + 1, m => by
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl, belief_castSucc,
      belief_zero m.eliminate]
    rfl

/-! ### Max-product: MAP assignments -/

variable [Fintype α] [Nonempty α]

/-- The factors of the model are nonnegative. -/
def NonnegFactors (m : TreeModel α n) : Prop :=
  (∀ i a, 0 ≤ m.unary i a) ∧ ∀ k a b, 0 ≤ m.pair k a b

/-- The max-product message from the last vertex to its parent. -/
noncomputable def maxMessage (m : TreeModel α (n + 1)) (a : α) : ℝ :=
  univ.sup' univ_nonempty fun b => m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b

/-- Maximize out the last vertex: multiply its max-product message into the unary factor of its
parent. -/
noncomputable def maxEliminate (m : TreeModel α (n + 1)) : TreeModel α n where
  par k := m.par k.castSucc
  unary i a := m.unary i.castSucc a * if i = m.lastParent then m.maxMessage a else 1
  pair k := m.pair k.castSucc

theorem maxEliminate_weight (m : TreeModel α (n + 1)) (y : Fin (n + 1) → α) :
    m.maxEliminate.weight y = m.dropLast.weight y * m.maxMessage (y m.lastParent) := by
  simp only [weight, maxEliminate, dropLast, prod_mul_distrib, prod_ite_eq', mem_univ,
    ↓reduceIte]
  have hp : ∀ k : Fin n, m.maxEliminate.parent k = m.dropLast.parent k := fun _ => rfl
  simp only [parent] at hp ⊢
  ring

omit [Fintype α] [Nonempty α] in
theorem NonnegFactors.weight_nonneg {m : TreeModel α n} (h : m.NonnegFactors)
    (x : Fin (n + 1) → α) : 0 ≤ m.weight x :=
  mul_nonneg (prod_nonneg fun i _ => h.1 i _) (prod_nonneg fun k _ => h.2 k _ _)

omit [Fintype α] [Nonempty α] in
theorem NonnegFactors.dropLast {m : TreeModel α (n + 1)} (h : m.NonnegFactors) :
    m.dropLast.NonnegFactors :=
  ⟨fun _ a => h.1 _ a, fun _ a b => h.2 _ a b⟩

theorem NonnegFactors.maxEliminate {m : TreeModel α (n + 1)} (h : m.NonnegFactors) :
    m.maxEliminate.NonnegFactors := by
  refine ⟨fun i a => mul_nonneg (h.1 _ a) ?_, fun _ a b => h.2 _ a b⟩
  split_ifs
  · obtain ⟨b⟩ := ‹Nonempty α›
    exact (mul_nonneg (h.2 (Fin.last n) b a) (h.1 (Fin.last (n + 1)) b)).trans
      (le_sup' (fun b => m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b) (mem_univ b))
  · exact zero_le_one

private theorem sup'_eq_choose (f : α → ℝ) :
    univ.sup' univ_nonempty f = f (exists_max_image univ f univ_nonempty).choose :=
  le_antisymm (sup'_le _ _ fun b _ =>
    (exists_max_image univ f univ_nonempty).choose_spec.2 b (mem_univ b)) (le_sup' f (mem_univ _))

/-- The maximum weight, computed by maximizing out the vertices from the last one down. -/
noncomputable def maxWeight : {n : ℕ} → TreeModel α n → ℝ
  | 0, m => univ.sup' univ_nonempty (m.unary 0)
  | _ + 1, m => maxWeight m.maxEliminate

/-- **Max-product decoding**: decode the model with the last vertex maximized out, then give the
last vertex a value attaining its max-product message at its parent's decoded value. -/
noncomputable def decode : {n : ℕ} → TreeModel α n → Fin (n + 1) → α
  | 0, m => fun _ => (exists_max_image univ (m.unary 0) univ_nonempty).choose
  | _ + 1, m => Fin.snoc (decode m.maxEliminate) (exists_max_image univ (fun b =>
      m.pair (Fin.last _) b (decode m.maxEliminate m.lastParent) * m.unary (Fin.last _) b)
      univ_nonempty).choose

omit [Fintype α] [Nonempty α] in
private theorem weight_zero (m : TreeModel α 0) (x : Fin 1 → α) :
    m.weight x = m.unary 0 (x 0) := by
  simp [weight]

/-- Every assignment has weight at most `maxWeight`. -/
theorem weight_le_maxWeight : ∀ {n : ℕ} {m : TreeModel α n}, m.NonnegFactors →
    ∀ x, m.weight x ≤ m.maxWeight
  | 0, m, _, x => by
    rw [weight_zero, maxWeight]
    exact le_sup' (m.unary 0) (mem_univ _)
  | n + 1, m, hm, x => by
    rw [maxWeight, ← Fin.snoc_init_self x, weight_snoc_dropLast]
    refine le_trans ?_ (weight_le_maxWeight hm.maxEliminate (Fin.init x))
    rw [maxEliminate_weight]
    refine mul_le_mul_of_nonneg_left ?_ (hm.dropLast.weight_nonneg _)
    exact le_sup' (fun b => m.pair (Fin.last n) b _ * m.unary (Fin.last (n + 1)) b) (mem_univ _)

/-- The decoded assignment attains `maxWeight`. -/
theorem weight_decode : ∀ {n : ℕ} (m : TreeModel α n), m.weight m.decode = m.maxWeight
  | 0, m => by
    rw [weight_zero, maxWeight, sup'_eq_choose]
    rfl
  | n + 1, m => by
    rw [maxWeight, ← weight_decode m.maxEliminate, decode, weight_snoc_dropLast,
      maxEliminate_weight, maxMessage, sup'_eq_choose]

/-- **Max-product decoding finds a MAP assignment** of a model with nonnegative factors. -/
theorem weight_le_weight_decode {m : TreeModel α n} (hm : m.NonnegFactors) (x : Fin (n + 1) → α) :
    m.weight x ≤ m.weight m.decode :=
  (weight_le_maxWeight hm x).trans_eq (weight_decode m).symm

end TreeModel

end Cslib.MachineLearning.GraphicalModels
