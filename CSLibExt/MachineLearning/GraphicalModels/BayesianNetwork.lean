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

/-- Sums over `Fin (n + 1) → α` split into the first `n` coordinates and the last one. -/
theorem sum_snoc [Fintype α] {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ y : Fin n → α, ∑ a, f (Fin.snoc y a) := by
  rw [← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Conditional distributions of each variable given all earlier ones. -/
structure Chain (α : Type*) where
  /-- The distribution of variable `k` given the values of variables `0, …, k - 1`. -/
  cond : (k : ℕ) → (Fin k → α) → StdSimplex ℝ α

namespace Chain

variable (c : Chain α)

/-- The joint distribution of the first `n` variables, by the chain rule. -/
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

/-- Summing out the last variable gives the joint of the earlier ones. -/
theorem sum_joint_snoc [Fintype α] (n : ℕ) (y : Fin n → α) :
    ∑ a, c.joint (n + 1) (Fin.snoc y a) = c.joint n y := by
  simp only [joint_snoc, ← mul_sum, (c.cond n y).total_of_fintype, mul_one]

/-- The joint is a probability distribution. -/
theorem sum_joint [Fintype α] : ∀ n : ℕ, ∑ x, c.joint n x = 1
  | 0 => by simp [joint]
  | n + 1 => by
    rw [sum_snoc]
    simp only [sum_joint_snoc]
    exact sum_joint n

/-- The conditional distribution of the last variable given the earlier ones, computed from the
joint, is the given conditional distribution. -/
theorem cond_eq_div {n : ℕ} {y : Fin n → α} (hy : c.joint n y ≠ 0) (a : α) :
    c.joint (n + 1) (Fin.snoc y a) / c.joint n y = (c.cond n y).weights a := by
  rw [joint_snoc, mul_div_cancel_left₀ _ hy]

/-- The joint is the product of the conditionals along the order. -/
theorem joint_eq_prod : ∀ (n : ℕ) (x : Fin n → α),
    c.joint n x = ∏ k : Fin n, (c.cond k fun j => x (Fin.castLE k.2.le j)).weights (x k)
  | 0, _ => by simp [joint]
  | n + 1, x => by
    rw [joint, joint_eq_prod n, Fin.prod_univ_castSucc]
    rfl

/-- Two chains that agree on the conditionals of the first `n` variables have the same joint
distribution of these variables. -/
theorem joint_congr {c' : Chain α} : ∀ {n : ℕ}, (∀ k < n, c.cond k = c'.cond k) →
    c.joint n = c'.joint n
  | 0, _ => rfl
  | n + 1, h => by
    funext x
    rw [joint, joint, joint_congr fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)]

/-- Replace the conditional distribution of variable `n`. -/
def update (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) : Chain α where
  cond k := if h : k = n then h ▸ f else c.cond k

theorem update_cond_self (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) :
    (c.update n f).cond n = f := by
  simp [update]

theorem update_cond_of_ne (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) {k : ℕ} (hk : k ≠ n) :
    (c.update n f).cond k = c.cond k := by
  simp [update, hk]

end Chain

/-- **The chain rule**: every probability distribution of `n` variables is the joint of a chain
of conditional distributions. -/
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

/-- A Bayesian network on nodes `0, …, n - 1` in topological order: each node has parents among
the earlier nodes and a conditional probability table given the values of its parents. -/
structure BayesNet (α : Type*) (n : ℕ) where
  /-- The parents of node `k`, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The distribution of node `k` given the values of its parents. -/
  cpt : (k : Fin n) → (pa k → α) → StdSimplex ℝ α

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-- The network as a chain: the conditional of node `k` given the earlier nodes is its table
applied to the values of its parents. -/
noncomputable def toChain : Chain α where
  cond k y := if hk : k < n then b.cpt ⟨k, hk⟩ fun j => y j else
    StdSimplex.single (Classical.arbitrary α)

/-- The joint distribution of the network. -/
noncomputable def joint (x : Fin n → α) : ℝ :=
  b.toChain.joint n x

/-- **Factorization of a Bayesian network**: the joint is the product over nodes of the
probability of the node's value given the values of its parents. -/
theorem joint_eq_prod (x : Fin n → α) :
    b.joint x = ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
  rw [joint, Chain.joint_eq_prod]
  refine prod_congr rfl fun k _ => ?_
  simp [toChain, k.2]

/-- The joint of a Bayesian network is a probability distribution. -/
theorem sum_joint [Fintype α] : ∑ x, b.joint x = 1 :=
  b.toChain.sum_joint n

/-- **The ordered Markov property**: the conditional distribution of node
`k` given all earlier nodes, computed from the joint of the first `k + 1` nodes, is the node's
table at its parents' values. In particular it depends only on the values of the parents. -/
theorem cond_eq_cpt {k : ℕ} (hk : k < n) {y : Fin k → α} (hy : b.toChain.joint k y ≠ 0)
    (a : α) :
    b.toChain.joint (k + 1) (Fin.snoc y a) / b.toChain.joint k y =
      (b.cpt ⟨k, hk⟩ fun j => y j).weights a := by
  rw [Chain.cond_eq_div _ hy]
  simp [toChain, hk]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
