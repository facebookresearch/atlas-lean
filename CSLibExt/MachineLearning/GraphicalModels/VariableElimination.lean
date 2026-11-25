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

/-- **Pairwise model on a tree.** For a type $\alpha$ of values and $n \in \mathbb{N}$, a pairwise
tree model on the vertices $0, \dots, n$ consists of a parent $p(k + 1) \in \{0, \dots, k\}$ for
each vertex $k + 1$ with $k < n$ (so vertex $0$ is the root and every vertex comes after its
parent), a unary factor $\varphi_i : \alpha \to \mathbb{R}$ for each vertex $i \le n$, and for each
$k < n$ a pairwise factor $\psi_k(a, b) \in \mathbb{R}$ on the edge between vertex $k + 1$ and its
parent, defined for all $a, b \in \alpha$, where $a$ is the value at vertex $k + 1$ and $b$ the
value at its parent. -/
structure TreeModel (α : Type*) (n : ℕ) where
  /-- The parent of vertex `k + 1`, among the vertices `0, …, k`. -/
  par : (k : Fin n) → Fin (k + 1)
  /-- The unary factor of each vertex. -/
  unary : Fin (n + 1) → α → ℝ
  /-- The factor of the edge between vertex `k + 1` (first argument) and its parent (second). -/
  pair : Fin n → α → α → ℝ

namespace TreeModel
variable {n : ℕ}

/-- **Parent of a vertex.** In a pairwise tree model on the vertices $0, \dots, n$, for $k < n$ the
parent of vertex $k + 1$ is the parent recorded by the model, an element of $\{0, \dots, k\}$,
regarded as one of the vertices $0, \dots, n$. -/
def parent (m : TreeModel α n) (k : Fin n) : Fin (n + 1) :=
  ⟨m.par k, by have := (m.par k).2; have := k.2; omega⟩

/-- **Weight of an assignment in a tree model.** Let $\alpha$ be a type and let $m$ be a pairwise
model on a tree with vertices $0, \dots, n$, with unary factors $\varphi_i : \alpha \to \mathbb{R}$
for each vertex $i$, and with factor $\psi_k : \alpha \times \alpha \to \mathbb{R}$ on the edge
between vertex $k + 1$ and its parent $p(k + 1)$ for each $k < n$. The unnormalized weight of an
assignment $x : \{0, \dots, n\} \to \alpha$ is the real number
$$w(x) = \prod_{i=0}^{n} \varphi_i(x_i) \cdot \prod_{k=0}^{n-1} \psi_k(x_{k+1}, x_{p(k+1)}),$$
the product of all factors evaluated at $x$. -/
noncomputable def weight (m : TreeModel α n) (x : Fin (n + 1) → α) : ℝ :=
  (∏ i, m.unary i (x i)) * ∏ k, m.pair k (x k.succ) (x (m.parent k))

/-- **Parent of the last vertex.** In a pairwise tree model on the vertices $0, \dots, n + 1$, this
is the parent of the last vertex $n + 1$, regarded as one of the vertices $0, \dots, n$ of the tree
with the last vertex removed. -/
def lastParent (m : TreeModel α (n + 1)) : Fin (n + 1) :=
  ⟨m.par (Fin.last n), by have := (m.par (Fin.last n)).2; simp at this; omega⟩

/-- **Message from the last vertex.** Let $\alpha$ be finite and consider a pairwise tree model on
the vertices $0, \dots, n + 1$ with unary factors $\varphi_i$ and pairwise factors $\psi_k$. The
message from the last vertex $n + 1$ to its parent is the function $\mu : \alpha \to \mathbb{R}$
given by $\mu(a) = \sum_{b \in \alpha} \psi_n(b, a) \, \varphi_{n+1}(b)$, where $\psi_n$ is the
factor of the edge between vertex $n + 1$ and its parent. -/
noncomputable def message [Fintype α] (m : TreeModel α (n + 1)) (a : α) : ℝ :=
  ∑ b, m.pair (Fin.last n) b a * m.unary (Fin.last (n + 1)) b

/-- **Eliminating the last vertex of a tree model.** Let $\alpha$ be finite, let $m$ be a pairwise
tree model on the vertices $0, \dots, n + 1$ with parents $p$, unary factors $\varphi_i$ and
pairwise factors $\psi_k$, and let $\mu$ be the message from the last vertex $n + 1$ to its
parent $q = p(n + 1)$. Eliminating the last vertex gives the pairwise tree model on the vertices
$0, \dots, n$ in which vertex $k + 1$ has parent $p(k + 1)$ and edge factor $\psi_k$ for each
$k < n$, and whose unary factors are $\varphi'_q(a) = \varphi_q(a) \, \mu(a)$ and
$\varphi'_i = \varphi_i$ for every vertex $i \le n$ with $i \ne q$. -/
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

/-- **One step of variable elimination.** Let $\alpha$ be finite, let $m$ be a pairwise tree model
on the vertices $0, \dots, n + 1$ with weight $w$, and let $m'$ be the model on the vertices
$0, \dots, n$ obtained from $m$ by eliminating the last vertex, with weight $w'$. Then for every
function $g : \alpha \to \mathbb{R}$ we have $\sum_x w(x) \, g(x_0) = \sum_y w'(y) \, g(y_0)$,
where $x$ ranges over all assignments $\{0, \dots, n + 1\} \to \alpha$ and $y$ over all
assignments $\{0, \dots, n\} \to \alpha$. -/
theorem sum_weight_mul_eliminate [Fintype α] (m : TreeModel α (n + 1)) (g : α → ℝ) :
    ∑ x, m.weight x * g (x 0) = ∑ y, m.eliminate.weight y * g (y 0) := by
  rw [sum_snoc]
  refine sum_congr rfl fun y _ => ?_
  have hroot : ∀ b, (Fin.snoc y b : Fin (n + 2) → α) 0 = y 0 := fun b =>
    Fin.snoc_castSucc (α := fun _ => α) b y 0
  simp only [hroot, ← sum_mul, weight_snoc, ← mul_sum, eliminate_weight, message]

/-- **Root message of a tree model.** Let $\alpha$ be finite. The root message of a pairwise tree
model $m$ on the vertices $0, \dots, n$ is the function $r_m : \alpha \to \mathbb{R}$ defined by
recursion on $n$: if $n = 0$, it is the unary factor of the root $0$; if $m$ is a model on the
vertices $0, \dots, n + 1$, it is $r_{m'}$, where $m'$ is the model on the vertices $0, \dots, n$
obtained from $m$ by eliminating the last vertex.

By variable elimination, $r_m(a)$ is the unnormalized marginal of the root at $a$. -/
noncomputable def rootMessage [Fintype α] : {n : ℕ} → TreeModel α n → α → ℝ
  | 0, m => m.unary 0
  | _ + 1, m => rootMessage m.eliminate

/-- **Variable elimination is exact.** Let $\alpha$ be finite and let $m$ be a pairwise tree model
on the vertices $0, \dots, n$ with weight $w$ and root message $r : \alpha \to \mathbb{R}$. Then
for every function $g : \alpha \to \mathbb{R}$ of the root value,
$\sum_x w(x) \, g(x_0) = \sum_{a \in \alpha} r(a) \, g(a)$, where $x$ ranges over all assignments
$\{0, \dots, n\} \to \alpha$. -/
theorem sum_weight_mul_eq [Fintype α] :
    ∀ {n : ℕ} (m : TreeModel α n) (g : α → ℝ),
      ∑ x, m.weight x * g (x 0) = ∑ a, m.rootMessage a * g a
  | 0, m, g => by
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp [weight, rootMessage]
  | _ + 1, m, g => by
    rw [sum_weight_mul_eliminate, sum_weight_mul_eq m.eliminate g]
    rfl

/-- **Variable elimination computes the partition function.** Let $\alpha$ be finite and let $m$
be a pairwise tree model on the vertices $0, \dots, n$ with weight $w$ and root message
$r : \alpha \to \mathbb{R}$. Then the partition function of $m$ is the total root message:
$\sum_x w(x) = \sum_{a \in \alpha} r(a)$, where $x$ ranges over all assignments
$\{0, \dots, n\} \to \alpha$. -/
theorem partition_eq [Fintype α] {n : ℕ} (m : TreeModel α n) :
    ∑ x, m.weight x = ∑ a, m.rootMessage a := by
  simpa using m.sum_weight_mul_eq fun _ => 1

/-- **Variable elimination computes the unnormalized root marginal.** Let $\alpha$ be finite and
let $m$ be a pairwise tree model on the vertices $0, \dots, n$ with weight $w$ and root message
$r : \alpha \to \mathbb{R}$. Then for every $a \in \alpha$ the unnormalized marginal of the root
at $a$ equals $r(a)$, that is, $\sum_x w(x) = r(a)$, where $x$ ranges over the assignments
$\{0, \dots, n\} \to \alpha$ with $x_0 = a$. -/
theorem rootMarginal_eq [Fintype α] [DecidableEq α] {n : ℕ} (m : TreeModel α n) (a : α) :
    ∑ x with x 0 = a, m.weight x = m.rootMessage a := by
  have h := m.sum_weight_mul_eq fun b => if b = a then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, sum_filter]

end TreeModel

end Cslib.MachineLearning.GraphicalModels
