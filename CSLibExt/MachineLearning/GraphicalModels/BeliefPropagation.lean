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

/-- **Removing the last vertex.** For a tree model with vertices $0, \dots, n + 1$, the tree model
on $0, \dots, n$ with the same parents, unary factors and edge factors: the last vertex, which is
a leaf, is removed together with its unary factor and the factor of its edge. -/
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

/-- **Summing out the last vertex preserves weighted sums at the other vertices.** Let $m$ be a
pairwise tree model on the vertices $0, \dots, n + 1$ with values in a finite type $\alpha$, and
let $m'$ be the model on the vertices $0, \dots, n$ obtained from $m$ by summing out its last
vertex. Write $w_m$ and $w_{m'}$ for their unnormalized weights. Then for every vertex $v \le n$
and every function $g : \alpha \to \mathbb{R}$,
$$\sum_x w_m(x)\, g(x_v) = \sum_y w_{m'}(y)\, g(y_v),$$
where $x$ and $y$ range over all assignments of values in $\alpha$ to the vertices of $m$ and of
$m'$. -/
theorem sum_weight_mul_eliminate_castSucc [Fintype α] (m : TreeModel α (n + 1))
    (v : Fin (n + 1)) (g : α → ℝ) :
    ∑ x, m.weight x * g (x v.castSucc) = ∑ y, m.eliminate.weight y * g (y v) := by
  rw [sum_snoc]
  refine sum_congr rfl fun y _ => ?_
  have hv : ∀ b, (Fin.snoc y b : Fin (n + 2) → α) v.castSucc = y v := fun b =>
    Fin.snoc_castSucc (α := fun _ => α) b y v
  simp only [hv, ← sum_mul, weight_snoc, ← mul_sum, eliminate_weight, message]

mutual

/-- **Sum-product belief.** The belief of each vertex of a tree model over a finite set of values,
computed by sum-product message passing: the product of its unary factor, the messages from its
subtree and the message from its parent. Recursively, in a model with a single vertex the belief
of that vertex is its unary factor; in a model with vertices $0, \dots, n + 1$ the belief of the
last vertex at a value $b$ is its unary factor at $b$ times the downward message to the last
vertex at $b$, and the belief of every other vertex is its belief in the model with the last
vertex summed out. -/
noncomputable def belief [Fintype α] : {n : ℕ} → TreeModel α n → Fin (n + 1) → α → ℝ
  | 0, m => fun _ => m.unary 0
  | _ + 1, m => Fin.lastCases (fun b => m.unary (Fin.last _) b * downMessage m b)
      (belief m.eliminate)

/-- **Downward message to the last vertex.** For a tree model with vertices $0, \dots, n + 1$ over
a finite set of values, the message from the parent $p$ of the last vertex to the last vertex at
a value $b$ is the sum over all values $a$ of $\psi(b, a)\, \beta(a)$, where $\psi$ is the factor
of the edge between the last vertex and $p$ (last vertex first) and $\beta(a)$ is the belief of
$p$ at $a$ in the model without the last vertex. -/
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

/-- **Belief propagation is exact on trees.** Let $m$ be a pairwise tree model on the vertices
$0, \dots, n$ with values in a finite type $\alpha$, let $w$ be its unnormalized weight, and let
$b_v$ be the belief of vertex $v$ computed by sum-product message passing. Then for every vertex
$v$ and every function $g : \alpha \to \mathbb{R}$,
$$\sum_x w(x)\, g(x_v) = \sum_{a \in \alpha} b_v(a)\, g(a),$$
where $x$ ranges over all assignments of values in $\alpha$ to the vertices. -/
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

/-- **Beliefs are the unnormalized marginals.** For every tree model over a finite set of values,
every vertex $v$ and every value $a$, the belief of $v$ at $a$ is the unnormalized marginal of $v$
at $a$: the sum of the weights of all assignments $x$ with $x_v = a$. -/
theorem marginal_eq_belief [Fintype α] [DecidableEq α] (m : TreeModel α n) (v : Fin (n + 1))
    (a : α) : ∑ x with x v = a, m.weight x = belief m v a := by
  have h := m.sum_weight_mul_eq_belief v fun b => if b = a then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, sum_filter]

/-- **Belief at the root is the root message.** For every tree model over a finite set of values,
the belief of the root, vertex $0$, is the root message computed by variable elimination: the two
agree at every value. -/
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

/-- **Nonnegative factors.** A tree model has nonnegative factors when all its unary factors and
all its edge factors take only nonnegative values. -/
def NonnegFactors (m : TreeModel α n) : Prop :=
  (∀ i a, 0 ≤ m.unary i a) ∧ ∀ k a b, 0 ≤ m.pair k a b

/-- **Max-product message.** For a tree model with vertices $0, \dots, n + 1$ over a finite
nonempty set of values, the max-product message from the last vertex to its parent at a value $a$
is the maximum over all values $b$ of $\psi(b, a)\, \phi(b)$, where $\psi$ is the factor of the
edge between the last vertex and its parent and $\phi$ is the unary factor of the last vertex. -/
noncomputable def maxMessage (m : TreeModel α (n + 1)) (a : α) : ℝ :=
  univ.sup' univ_nonempty fun b => m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b

/-- **Maximizing out the last vertex.** For a tree model with vertices $0, \dots, n + 1$ over a
finite nonempty set of values, the tree model on $0, \dots, n$ with the same parents and edge
factors whose unary factor at the parent of the last vertex is multiplied by the max-product
message of the last vertex; the other unary factors are unchanged. -/
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

/-- **Max-product value.** For a tree model over a finite nonempty set of values, the value
computed by maximizing out the vertices from the last one down: for a single vertex it is the
maximum of its unary factor over all values, and for more vertices it is the max-product value of
the model with the last vertex maximized out.

When all factors are nonnegative, this is the largest weight of an assignment. -/
noncomputable def maxWeight : {n : ℕ} → TreeModel α n → ℝ
  | 0, m => univ.sup' univ_nonempty (m.unary 0)
  | _ + 1, m => maxWeight m.maxEliminate

/-- **Max-product decoding.** An assignment of a tree model over a finite nonempty set of values,
defined by recursion on the number of vertices. For a single vertex, its value is one that
maximizes its unary factor. For vertices $0, \dots, n + 1$, the vertices $0, \dots, n$ get the
decoding of the model with the last vertex maximized out, and the last vertex gets a value $b$
maximizing $\psi(b, a)\, \phi(b)$, where $a$ is the decoded value of its parent, $\psi$ is the
factor of the edge between the last vertex and its parent and $\phi$ is the unary factor of the
last vertex; that is, $b$ attains the max-product message of the last vertex at $a$. -/
noncomputable def decode : {n : ℕ} → TreeModel α n → Fin (n + 1) → α
  | 0, m => fun _ => (exists_max_image univ (m.unary 0) univ_nonempty).choose
  | _ + 1, m => Fin.snoc (decode m.maxEliminate) (exists_max_image univ (fun b =>
      m.pair (Fin.last _) b (decode m.maxEliminate m.lastParent) * m.unary (Fin.last _) b)
      univ_nonempty).choose

omit [Fintype α] [Nonempty α] in
private theorem weight_zero (m : TreeModel α 0) (x : Fin 1 → α) :
    m.weight x = m.unary 0 (x 0) := by
  simp [weight]

/-- **The max-product value bounds every weight.** Let $m$ be a pairwise tree model with values in
a finite nonempty type $\alpha$ whose unary and pairwise factors are all nonnegative, and let $M$
be its max-product value, obtained by maximizing out the vertices from the last one down. Then
every assignment of values in $\alpha$ to the vertices has weight at most $M$. -/
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

/-- **Max-product decoding attains the max-product value.** Let $m$ be a pairwise tree model with
values in a finite nonempty type, and let $M$ be its max-product value, obtained by maximizing out
the vertices from the last one down. Then the weight of the assignment produced by max-product
decoding equals $M$. -/
theorem weight_decode : ∀ {n : ℕ} (m : TreeModel α n), m.weight m.decode = m.maxWeight
  | 0, m => by
    rw [weight_zero, maxWeight, sup'_eq_choose]
    rfl
  | n + 1, m => by
    rw [maxWeight, ← weight_decode m.maxEliminate, decode, weight_snoc_dropLast,
      maxEliminate_weight, maxMessage, sup'_eq_choose]

/-- **Max-product decoding finds a MAP assignment.** Let $m$ be a pairwise tree model with values
in a finite nonempty type $\alpha$ whose unary and pairwise factors are all nonnegative. Then every
assignment of values in $\alpha$ to the vertices has weight at most the weight of the assignment
produced by max-product decoding. -/
theorem weight_le_weight_decode {m : TreeModel α n} (hm : m.NonnegFactors) (x : Fin (n + 1) → α) :
    m.weight x ≤ m.weight m.decode :=
  (weight_le_maxWeight hm x).trans_eq (weight_decode m).symm

end TreeModel

end Cslib.MachineLearning.GraphicalModels
