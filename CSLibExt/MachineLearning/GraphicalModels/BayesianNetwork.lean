/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bayesian networks: the chain rule and factorization along a topological order

Random variables `X 0, …, X (n - 1)` take values in a finite type `α` and are listed in a
topological order of a directed acyclic graph. A `Chain` gives, for each `k`, the conditional
distribution of `X k` given the earlier variables `X 0, …, X (k - 1)` (a point of Mathlib's
standard simplex `Convexity.StdSimplex`). Its joint distribution is defined by the chain rule:
`joint (k + 1) (x₀, …, x_k) = joint k (x₀, …, x_{k-1}) * p_k (x_k | x₀, …, x_{k-1})`.

## Main results

* `sum_joint`: the joint is a probability distribution; `sum_joint_snoc`: summing out the last
  variable gives the joint of the earlier ones, so `joint k` is the marginal of the first `k`
  variables; `cond_eq_div`: the conditional of the joint is the given conditional distribution.
* `joint_eq_prod`: the joint is the product of the conditionals along the order.
* `exists_chain`: **the chain rule**: every probability distribution of `n` variables is the
  joint of a chain, that is, factorizes as a product of conditionals along any order.
* Bayesian networks: `BayesNet` gives each node `k` a set of parents among `0, …, k - 1` and a
  conditional probability table depending only on the parents. `BayesNet.joint_eq_prod`: its
  joint is `∏ k, p_k (x_k | x_{pa k})`; `BayesNet.sum_joint`: it is a probability distribution;
  `BayesNet.cond_eq_cpt`: the conditional distribution of each node given all earlier nodes (with
  positive probability) is its table, so it depends only on the parents (the ordered Markov
  property).

Sequential models with a hidden chain (hidden Markov models) are in
`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-- **Splitting a sum over $\alpha^{n+1}$ at the last coordinate.** Let $\alpha$ be a finite
type, $M$ an additive commutative monoid, $n$ a natural number and $f : \alpha^{n+1} \to M$.
Then $\sum_{x \in \alpha^{n+1}} f(x) =
\sum_{y \in \alpha^n} \sum_{a \in \alpha} f(y_0, \dots, y_{n-1}, a)$, where
$y = (y_0, \dots, y_{n-1})$. -/
theorem sum_snoc [Fintype α] {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ y : Fin n → α, ∑ a, f (Fin.snoc y a) := by
  rw [← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- **Chain of conditional distributions.** A chain of conditional distributions with values in
a type $\alpha$ assigns to every $k \in \mathbb{N}$ and every assignment $(x_0, \dots, x_{k-1})$
of values in $\alpha$ to the variables $0, \dots, k - 1$ a finitely supported probability
distribution $p_k(\cdot \mid x_0, \dots, x_{k-1})$ on $\alpha$, the conditional distribution of
variable $k$ given the earlier ones. -/
structure Chain (α : Type*) where
  /-- The distribution of variable `k` given the values of variables `0, …, k - 1`. -/
  cond : (k : ℕ) → (Fin k → α) → StdSimplex ℝ α

namespace Chain

variable (c : Chain α)

/-- **Joint distribution of a chain.** For a chain of conditional distributions with values in
a type $\alpha$, write $p_k(\cdot \mid x_0, \dots, x_{k-1})$ for the conditional distribution of
variable $k$ given the earlier ones. The joint distribution $P_n : \alpha^n \to \mathbb{R}$ of
the first $n$ variables is defined by the chain rule: $P_0 = 1$ and
$P_{n+1}(x_0, \dots, x_n) = P_n(x_0, \dots, x_{n-1}) \, p_n(x_n \mid x_0, \dots, x_{n-1})$. -/
noncomputable def joint : (n : ℕ) → (Fin n → α) → ℝ
  | 0, _ => 1
  | n + 1, x => joint n (Fin.init x) * (c.cond n (Fin.init x)).weights (x (Fin.last n))

theorem joint_zero (x : Fin 0 → α) : c.joint 0 x = 1 :=
  rfl

theorem joint_snoc (n : ℕ) (y : Fin n → α) (a : α) :
    c.joint (n + 1) (Fin.snoc y a) = c.joint n y * (c.cond n y).weights a := by
  simp [joint, Fin.init_snoc, Fin.snoc_last]

theorem joint_nonneg : ∀ (n : ℕ) (x : Fin n → α), 0 ≤ c.joint n x
  | 0, _ => zero_le_one
  | n + 1, _ => mul_nonneg (joint_nonneg n _) ((c.cond n _).nonneg _)

/-- **Marginalizing the last variable of a chain.** Let $c$ be a chain of conditional
distributions with values in a finite type $\alpha$, and write $P_k$ for its joint distribution
of the first $k$ variables. For every $n$ and every $y = (y_0, \dots, y_{n-1}) \in \alpha^n$,
$\sum_{a \in \alpha} P_{n+1}(y_0, \dots, y_{n-1}, a) = P_n(y)$. -/
theorem sum_joint_snoc [Fintype α] (n : ℕ) (y : Fin n → α) :
    ∑ a, c.joint (n + 1) (Fin.snoc y a) = c.joint n y := by
  simp only [joint_snoc, ← mul_sum, (c.cond n y).total_of_fintype, mul_one]

/-- **The joint distribution of a chain sums to one.** Let $c$ be a chain of conditional
distributions with values in a finite type $\alpha$, and write $P_n$ for its joint distribution
of the first $n$ variables. For every $n$, $\sum_{x \in \alpha^n} P_n(x) = 1$. -/
theorem sum_joint [Fintype α] : ∀ n : ℕ, ∑ x, c.joint n x = 1
  | 0 => by simp [joint]
  | n + 1 => by
    rw [sum_snoc]
    simp only [sum_joint_snoc]
    exact sum_joint n

/-- **Conditionals of the joint of a chain.** Let $c$ be a chain of conditional distributions
with values in a type $\alpha$, let $P_m$ be its joint distribution of the first $m$ variables,
and let $p_n(\cdot \mid y)$ be its conditional distribution of variable $n$ given values
$y \in \alpha^n$ of the earlier ones. For every $n$, every $y \in \alpha^n$ with $P_n(y) \ne 0$
and every $a \in \alpha$, we have $P_{n+1}(y, a) / P_n(y) = p_n(a \mid y)$, where
$(y, a) \in \alpha^{n+1}$ extends $y$ by the value $a$. -/
theorem cond_eq_div {n : ℕ} {y : Fin n → α} (hy : c.joint n y ≠ 0) (a : α) :
    c.joint (n + 1) (Fin.snoc y a) / c.joint n y = (c.cond n y).weights a := by
  rw [joint_snoc, mul_div_cancel_left₀ _ hy]

/-- **Factorization of the joint of a chain.** For a chain of conditional distributions with
values in a type $\alpha$, write $p_k(\cdot \mid x_0, \dots, x_{k-1})$ for the conditional
distribution of variable $k$ given the earlier ones and $P_n$ for the joint distribution of
the first $n$ variables. Then for every $n$ and every $x \in \alpha^n$ we have
$P_n(x) = \prod_{k < n} p_k(x_k \mid x_0, \dots, x_{k-1})$. -/
theorem joint_eq_prod : ∀ (n : ℕ) (x : Fin n → α),
    c.joint n x = ∏ k : Fin n, (c.cond k fun j => x (Fin.castLE k.2.le j)).weights (x k)
  | 0, _ => by simp [joint]
  | n + 1, x => by
    rw [joint, joint_eq_prod n, Fin.prod_univ_castSucc]
    rfl

/-- **Joint distribution determined by the first conditionals.** Let $n \in \mathbb{N}$. If two
chains of conditional distributions $c$ and $c'$ with values in a type $\alpha$ have the same
conditional distribution of variable $k$ given the earlier variables for every $k < n$, then
they have the same joint distribution of the first $n$ variables. -/
theorem joint_congr {c' : Chain α} : ∀ {n : ℕ}, (∀ k < n, c.cond k = c'.cond k) →
    c.joint n = c'.joint n
  | 0, _ => rfl
  | n + 1, h => by
    funext x
    rw [joint, joint, joint_congr fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)]

/-- **Replacing one conditional of a chain.** Given a chain $c$ of conditional distributions with
values in $\alpha$, an index $n$ and a family $f$ assigning to each $y \in \alpha^n$ a
probability distribution $f(y)$ on $\alpha$, the updated chain has conditional distribution $f$
for variable $n$ and the same conditional distribution as $c$ for every other variable. -/
def update (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) : Chain α where
  cond k := if h : k = n then h ▸ f else c.cond k

theorem update_cond_self (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) :
    (c.update n f).cond n = f := by
  simp [update]

theorem update_cond_of_ne (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) {k : ℕ} (hk : k ≠ n) :
    (c.update n f).cond k = c.cond k := by
  simp [update, hk]

end Chain

/-- **The chain rule.** Let $\alpha$ be a finite nonempty type and $n \in \mathbb{N}$. For every
function $P : \alpha^n \to \mathbb{R}$ with $P(x) \ge 0$ for all $x$ and $\sum_x P(x) = 1$,
there is a chain of conditional distributions with values in $\alpha$ whose joint distribution
of the first $n$ variables equals $P$. -/
theorem exists_chain [Fintype α] [Nonempty α] : ∀ (n : ℕ) (P : (Fin n → α) → ℝ),
    (∀ x, 0 ≤ P x) → ∑ x, P x = 1 → ∃ c : Chain α, ∀ x, P x = c.joint n x
  | 0, P, _, h1 => ⟨⟨fun _ _ => StdSimplex.single (Classical.arbitrary α)⟩, fun x => by
      rw [Fintype.sum_unique, Subsingleton.elim default x] at h1
      rw [h1, Chain.joint_zero]⟩
  | n + 1, P, h0, h1 => by
    classical
    set Q : (Fin n → α) → ℝ := fun y => ∑ a, P (Fin.snoc y a) with hQ
    have hQ0 : ∀ y, 0 ≤ Q y := fun y => sum_nonneg fun a _ => h0 _
    have hQ1 : ∑ y, Q y = 1 := by rw [← h1, sum_snoc]
    obtain ⟨c', hc'⟩ := exists_chain n Q hQ0 hQ1
    let f : (Fin n → α) → StdSimplex ℝ α := fun y =>
      if hy : Q y = 0 then StdSimplex.single (Classical.arbitrary α) else
        { weights := Finsupp.equivFunOnFinite.symm fun a => P (Fin.snoc y a) / Q y
          nonneg := fun a => by
            simpa using div_nonneg (h0 (Fin.snoc y a)) (hQ0 y)
          total := by
            rw [Finsupp.sum_fintype _ _ fun _ => rfl, ← div_self hy]
            simp [← sum_div, hQ] }
    refine ⟨c'.update n f, fun x => ?_⟩
    have hjoint : (c'.update n f).joint n = c'.joint n :=
      Chain.joint_congr _ fun k hk => Chain.update_cond_of_ne _ _ _ hk.ne
    rw [← Fin.snoc_init_self x, Chain.joint_snoc, hjoint, ← hc', Chain.update_cond_self]
    by_cases hy : Q (Fin.init x) = 0
    · have hzero : P (Fin.snoc (Fin.init x) (x (Fin.last n))) = 0 :=
        (sum_eq_zero_iff_of_nonneg fun a _ => h0 _).1 hy _ (mem_univ _)
      rw [hzero, hy, zero_mul]
    · simp [f, hy, mul_div_cancel₀ _ hy]

/-! ### Bayesian networks -/

/-- **Bayesian network.** A Bayesian network with values in a type $\alpha$ on the nodes
$0, \dots, n - 1$, listed in a topological order, assigns to each node $k$ a finite set of
parents among the earlier nodes $0, \dots, k - 1$, and a conditional probability table: for each
assignment of values in $\alpha$ to the parents of $k$, a finitely supported probability
distribution on $\alpha$ for the value of node $k$. -/
structure BayesNet (α : Type*) (n : ℕ) where
  /-- The parents of node `k`, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The distribution of node `k` given the values of its parents. -/
  cpt : (k : Fin n) → (pa k → α) → StdSimplex ℝ α

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-- **The chain of a Bayesian network.** A Bayesian network $b$ on nodes $0, \dots, n - 1$ with
values in a nonempty type $\alpha$ defines a chain of conditional distributions. For $k < n$,
the conditional distribution of variable $k$ given values $y_0, \dots, y_{k-1}$ of the earlier
variables is the table of node $k$ applied to the values $y_j$ of its parents $j$. For
$k \ge n$ it is the point mass at a fixed arbitrary element of $\alpha$. -/
noncomputable def toChain : Chain α where
  cond k y := if hk : k < n then b.cpt ⟨k, hk⟩ fun j => y j else
    StdSimplex.single (Classical.arbitrary α)

/-- **Joint distribution of a Bayesian network.** Let $B$ be a Bayesian network on the nodes
$0, \dots, n - 1$ with values in a nonempty type $\alpha$. The joint distribution of $B$ is the
function $P : \alpha^n \to \mathbb{R}$ given by $P(x) = P_n(x)$ for $x \in \alpha^n$, where $P_n$
is the joint distribution of the first $n$ variables of the chain of conditional distributions
of $B$. -/
noncomputable def joint (x : Fin n → α) : ℝ :=
  b.toChain.joint n x

/-- **Factorization of a Bayesian network**: the joint is the product over nodes of the
probability of the node's value given the values of its parents. -/
theorem joint_eq_prod (x : Fin n → α) :
    b.joint x = ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
  rw [joint, Chain.joint_eq_prod]
  refine prod_congr rfl fun k _ => ?_
  simp [toChain, k.2]

/-- **The joint distribution of a Bayesian network sums to one.** Let $B$ be a Bayesian network
on the nodes $0, \dots, n - 1$ with values in a finite nonempty type $\alpha$, and let $P$ be its
joint distribution. Then $\sum_{x \in \alpha^n} P(x) = 1$. -/
theorem sum_joint [Fintype α] : ∑ x, b.joint x = 1 :=
  b.toChain.sum_joint n

/-- **The ordered Markov property.** Let $B$ be a Bayesian network on the nodes
$0, \dots, n - 1$ with values in a nonempty type $\alpha$, and let $P_m$ be the joint
distribution of the first $m$ nodes of $B$ viewed as a chain of conditional distributions. For
a node $k < n$, write $p_k(\cdot \mid z)$ for its conditional probability table at values $z$
of its parents. Let $y = (y_0, \dots, y_{k-1}) \in \alpha^k$ with $P_k(y) \ne 0$, and write
$y_{\mathrm{pa}(k)}$ for the values of $y$ at the parents of $k$. Then for every $a \in \alpha$,
$$P_{k+1}(y_0, \dots, y_{k-1}, a) / P_k(y) = p_k(a \mid y_{\mathrm{pa}(k)}).$$
In particular, the conditional distribution of node $k$ given all earlier nodes depends only on
the values of its parents. -/
theorem cond_eq_cpt {k : ℕ} (hk : k < n) {y : Fin k → α} (hy : b.toChain.joint k y ≠ 0)
    (a : α) :
    b.toChain.joint (k + 1) (Fin.snoc y a) / b.toChain.joint k y =
      (b.cpt ⟨k, hk⟩ fun j => y j).weights a := by
  rw [Chain.cond_eq_div _ hy]
  simp [toChain, hk]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
