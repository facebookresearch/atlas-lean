/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import MathlibExt.Probability.FiniteWeight
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Causal Bayesian networks: the do-operator and adjustment for the parents

A Bayesian network (`BayesNet`, nodes in a topological order) is read causally: each table
`p_k (x_k | x_{pa k})` is an autonomous mechanism. The intervention `do(X_k = a)` replaces the
mechanism of node `k` by the point mass at `a` and keeps all other mechanisms (Pearl 2009,
Definition 1.3.1 and §3.2.2).

## Main definitions

* `BayesNet.paVal b k x`: the values of the parents of node `k` in a full assignment `x`.
* `BayesNet.intervene b k a`: the network after the intervention `do(X_k = a)`.
* `BayesNet.Edge`, `BayesNet.IsDescendant`, `BayesNet.IsPath`, `BayesNet.PathBlocked`,
  `BayesNet.DSeparated`: the graph of a network, paths of its skeleton, blocking and
  d-separation (Pearl 2009, Definition 1.2.3).

## Main results

* `BayesNet.joint_intervene`: **the truncated factorization** (Pearl 2009, eq. (3.10)): the
  post-intervention joint is `∏_{j ≠ k} p_j (x_j | x_{pa j})` on assignments with `x_k = a`,
  and `0` elsewhere.
* `BayesNet.sum_paVal_intervene`: the intervention does not change the law of the parents of
  the intervened node; `BayesNet.sum_filter_joint_eq_cpt_mul`: the table of a node is its
  conditional law given its parents, `P(X_k = a, pa_k = z) = p_k (a | z) P(pa_k = z)`.
* `BayesNet.sum_intervene_joint_mul`: **adjustment for the direct causes** (Pearl 2009,
  Theorem 3.2.2; the case `Z = pa(X)` of the back-door adjustment, Pearl 1995 and Pearl 2009,
  Theorem 3.3.2): for every function `f` of the variables,
  `E[f | do(X_k = a)] = ∑_z P(pa_k = z) E[f | X_k = a, pa_k = z]`, under positivity of
  `P(X_k = a, pa_k = z)` wherever `P(pa_k = z) > 0`. With `f` the indicator of `{Y = y}` this is
  `P(y | do(x)) = ∑_z P(y | x, z) P(z)`. `BayesNet.sum_intervene_joint_mul_of_cpt_ne_zero`:
  the same when the table of node `k` gives `a` positive probability at every parent value.
* `BayesNet.sum_intervene_joint_mul_of_pred`: **back-door adjustment** (Pearl 2009,
  Theorem 3.3.2) for a set `Z` of nodes preceding the treatment in the topological order that
  contains its parents (such a `Z` meets the back-door criterion), with
  `BayesNet.sum_filter_restrict_joint_eq_cpt_mul` and
  `BayesNet.sum_intervene_joint_mul_of_pred_of_cpt_ne_zero`.
* `BayesNet.DSeparated.symm`: d-separation is symmetric.

The global Markov property (d-separation implies conditional independence), the general
back-door adjustment (any `Z` meeting the back-door criterion, for example one containing
descendants of the parents that are not descendants of the treatment, or nodes after the
treatment in the order) and the front-door adjustment are stated in
`WantedExt/Probability/CausalGraphicalWanted.lean`; the do-calculus is not covered.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.2–1.3, §3.2–3.3.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-- Summing a function of the first `k` variables against the joint of `n ≥ k` variables gives
the sum against the joint of the first `k`. -/
private lemma chain_sum_mul_joint_castLE [Fintype α] (c : Chain α) {k : ℕ}
    (g : (Fin k → α) → ℝ) (n : ℕ) (h : k ≤ n) :
    ∑ x : Fin n → α, g (fun j => x (Fin.castLE h j)) * c.joint n x =
      ∑ y : Fin k → α, g y * c.joint k y := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_snoc]
    have hc : ∀ (y : Fin n → α) (a : α),
        (fun j : Fin k => (Fin.snoc y a : Fin (n + 1) → α) (Fin.castLE (hkn.trans n.le_succ) j)) =
          fun j => y (Fin.castLE hkn j) := by
      intro y a; funext j
      have : Fin.castLE (hkn.trans n.le_succ) j = Fin.castSucc (Fin.castLE hkn j) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hc, Chain.joint_snoc, ← mul_assoc, ← mul_sum, (c.cond n _).total_of_fintype,
      mul_one]
    exact ih
namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-- The values of the parents of node `k` in a full assignment `x`. -/
def paVal (k : Fin n) (x : Fin n → α) : b.pa k → α :=
  fun j => x (Fin.castLE k.2.le j)

/-- **The intervention `do(X_k = a)`**: the mechanism of node `k` is replaced by the point mass
at `a`; every other node keeps its parents and its table. (The parents of `k` are kept as a
`Finset`, but the new table of `k` does not depend on them.) -/
noncomputable def intervene (k : Fin n) (a : α) : BayesNet α n where
  pa := b.pa
  cpt j z := if j = k then StdSimplex.single a else b.cpt j z

/-- **The truncated factorization** (Pearl 2009, eq. (3.10)): after `do(X_k = a)` the joint is
the product of the tables of all nodes other than `k` on assignments with `x_k = a`, and `0`
elsewhere. -/
theorem joint_intervene [DecidableEq α] (k : Fin n) (a : α) (x : Fin n → α) :
    (b.intervene k a).joint x =
      if x k = a then ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) else 0 := by
  rw [joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k)]
  have hrest : ∏ j ∈ univ.erase k, ((b.intervene k a).cpt j
      fun i => x (Fin.castLE j.2.le i)).weights (x j) =
      ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) := by
    refine prod_congr rfl fun j hj => ?_
    simp [intervene, ne_of_mem_erase hj]
    rfl
  rw [hrest]
  simp only [intervene, ite_true]
  split_ifs with h
  · simp [StdSimplex.single, h]
  · simp [StdSimplex.single, Ne.symm h]

private lemma toChain_intervene_joint (k : Fin n) (a : α) :
    (b.intervene k a).toChain.joint k = b.toChain.joint k := by
  refine Chain.joint_congr _ fun j hj => ?_
  funext y
  have hjn : j < n := hj.trans k.2
  have hne : (⟨j, hjn⟩ : Fin n) ≠ k := fun h => (Fin.ext_iff.1 h ▸ hj).false
  simp [toChain, hjn, intervene, hne]

/-- The intervention `do(X_k = a)` does not change the law of the parents of node `k`. -/
theorem sum_paVal_intervene [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (z : b.pa k → α) :
    ∑ x with b.paVal k x = z, (b.intervene k a).joint x = ∑ x with b.paVal k x = z, b.joint x := by
  have hmarg : ∀ b' : BayesNet α n, b'.pa = b.pa →
      ∑ x with b.paVal k x = z, b'.joint x =
        ∑ y : Fin k → α, (if (fun j : b.pa k => y j) = z then 1 else 0) * b'.toChain.joint k y := by
    intro b' _
    rw [← chain_sum_mul_joint_castLE b'.toChain _ n k.2.le, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    change (if b.paVal k x = z then b'.joint x else 0) =
      (if b.paVal k x = z then 1 else 0) * b'.toChain.joint n x
    split_ifs <;> simp [joint]
  rw [hmarg (b.intervene k a) rfl, hmarg b rfl, toChain_intervene_joint]

private lemma joint_eq_intervene_mul (k : Fin n) (a : α) {x : Fin n → α}
    (hx : x k = a) :
    b.joint x = (b.intervene k a).joint x * (b.cpt k (b.paVal k x)).weights a := by
  classical
  rw [joint_intervene]
  simp only [hx, ↓reduceIte]
  rw [joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k),
    mul_comm, hx]
  rfl

private lemma sum_filter_joint_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ) (z : b.pa k → α) :
    ∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x =
      (b.cpt k z).weights a * ∑ x with b.paVal k x = z, (b.intervene k a).joint x * f x := by
  rw [sum_filter, sum_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hk : x k = a
  · by_cases hz : b.paVal k x = z
    · simp only [hk, hz, and_self, ↓reduceIte]
      rw [joint_eq_intervene_mul b k a hk, hz]
      ring
    · simp [hz]
  · rw [joint_intervene]
    simp [hk]

/-- **Adjustment for the direct causes** (Pearl 2009, Theorem 3.2.2; the case `Z = pa(X)` of
the back-door adjustment): for every function `f` of the variables,
`E[f | do(X_k = a)] = ∑_z P(pa_k = z) E[f | X_k = a, pa_k = z]`, assuming
`P(X_k = a, pa_k = z) > 0` whenever `P(pa_k = z) > 0`. -/
theorem sum_intervene_joint_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ)
    (hpos : ∀ z : b.pa k → α, ∑ x with b.paVal k x = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ b.paVal k x = z, b.joint x ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : b.pa k → α, (∑ x with b.paVal k x = z, b.joint x) *
        ((∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x) /
          ∑ x with x k = a ∧ b.paVal k x = z, b.joint x) := by
  rw [← sum_fiberwise univ (b.paVal k) fun x => (b.intervene k a).joint x * f x]
  refine sum_congr rfl fun z _ => ?_
  have hQ := sum_filter_joint_mul b k a (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [sum_paVal_intervene] at hQ
  rw [sum_filter_joint_mul b k a f z, hQ]
  by_cases hP : ∑ x with b.paVal k x = z, b.joint x = 0
  · rw [hP, zero_mul]
    have hPdo : ∑ x with b.paVal k x = z, (b.intervene k a).joint x = 0 := by
      rw [sum_paVal_intervene, hP]
    rw [sum_eq_zero_iff_of_nonneg (f := fun x => (b.intervene k a).joint x)
      fun x _ => (b.intervene k a).toChain.joint_nonneg n x] at hPdo
    exact sum_eq_zero fun x hx => by
      change (b.intervene k a).joint x * f x = 0
      rw [hPdo x hx, zero_mul]
  · have hw : (b.cpt k z).weights a ≠ 0 := by
      intro hw; apply hpos z hP; rw [hQ, hw, zero_mul]
    field_simp

/-- The table of node `k` is the conditional law of `X_k` given its parents:
`P(X_k = a, pa_k = z) = p_k (a | z) P(pa_k = z)`. -/
theorem sum_filter_joint_eq_cpt_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (z : b.pa k → α) :
    ∑ x with x k = a ∧ b.paVal k x = z, b.joint x =
      (b.cpt k z).weights a * ∑ x with b.paVal k x = z, b.joint x := by
  have hQ := sum_filter_joint_mul b k a (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [hQ, sum_paVal_intervene]

/-- Adjustment for the direct causes when the table of node `k` gives the value `a` positive
probability at every value of the parents. -/
theorem sum_intervene_joint_mul_of_cpt_ne_zero [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ) (hpos : ∀ z, (b.cpt k z).weights a ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : b.pa k → α, (∑ x with b.paVal k x = z, b.joint x) *
        ((∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x) /
          ∑ x with x k = a ∧ b.paVal k x = z, b.joint x) :=
  b.sum_intervene_joint_mul k a f fun z hz => by
    rw [sum_filter_joint_eq_cpt_mul]
    exact mul_ne_zero (hpos z) hz

/-- The intervention `do(X_k = a)` does not change the law of any set `Z` of nodes preceding `k`
in the topological order. -/
private lemma sum_restrict_intervene [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k) (z : Z → α) :
    ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x =
      ∑ x with (fun i : Z => x i) = z, b.joint x := by
  let g : (Fin k → α) → ℝ := fun y =>
    if (fun i : Z => y ⟨i.1.val, hZk i.1 i.2⟩) = z then 1 else 0
  have hmarg : ∀ b' : BayesNet α n,
      ∑ x with (fun i : Z => x i) = z, b'.joint x = ∑ y, g y * b'.toChain.joint k y := by
    intro b'
    rw [← chain_sum_mul_joint_castLE b'.toChain g n k.2.le, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    change (if (fun i : Z => x i) = z then b'.joint x else 0) =
      (if (fun i : Z => x i) = z then 1 else 0) * b'.toChain.joint n x
    split_ifs <;> simp [joint]
  rw [hmarg, hmarg, toChain_intervene_joint]

/-- **Back-door adjustment for a set of predecessors containing the parents**: let `Z` be a set
of nodes preceding `k` in the topological order (so `Z` contains no descendant of `k`) that
contains the parents of `k`. Then `Z` meets the back-door criterion for every outcome node
`y ∉ Z` (a path from `k` to `y` that starts with an arrow into `k` starts `k ← p` with
`p ∈ pa(k) ⊆ Z`, an interior non-collider, so it is blocked), and for every function `f` of the
variables
`E[f | do(X_k = a)] = ∑_z P(Z = z) E[f | X_k = a, Z = z]`, assuming `P(X_k = a, Z = z) > 0`
whenever `P(Z = z) > 0` (Pearl 2009, Theorem 3.3.2, in this case). -/
theorem sum_intervene_joint_mul_of_pred [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k)
    (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z) (f : (Fin n → α) → ℝ)
    (hpos : ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * f x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) := by
  -- the parents' values as a function of the values on `Z`
  let π : (Z → α) → (b.pa k → α) := fun z j => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩
  have hπ : ∀ x z, (fun i : Z => x i) = z → b.paVal k x = π z := by
    intro x z hz
    funext j
    exact congrFun hz ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩
  have hR : ∀ (g : (Fin n → α) → ℝ) (z : Z → α),
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * g x =
        (b.cpt k (π z)).weights a *
          ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x * g x := by
    intro g z
    rw [sum_filter, sum_filter, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    by_cases hk : x k = a
    · by_cases hz : (fun i : Z => x i) = z
      · simp only [hk, hz, and_self, ↓reduceIte]
        rw [joint_eq_intervene_mul b k a hk, hπ x z hz]
        ring
      · simp [hz]
    · rw [joint_intervene]
      simp [hk]
  rw [← sum_fiberwise univ (fun x : Fin n → α => fun i : Z => x i)
    fun x => (b.intervene k a).joint x * f x]
  refine sum_congr rfl fun z _ => ?_
  have hQ := hR (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [sum_restrict_intervene b k a Z hZk] at hQ
  rw [hR f z, hQ]
  by_cases hP : ∑ x with (fun i : Z => x i) = z, b.joint x = 0
  · rw [hP, zero_mul]
    have hPdo : ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x = 0 := by
      rw [sum_restrict_intervene b k a Z hZk, hP]
    rw [sum_eq_zero_iff_of_nonneg (f := fun x => (b.intervene k a).joint x)
      fun x _ => (b.intervene k a).toChain.joint_nonneg n x] at hPdo
    exact sum_eq_zero fun x hx => by
      change (b.intervene k a).joint x * f x = 0
      rw [hPdo x hx, zero_mul]
  · have hw : (b.cpt k (π z)).weights a ≠ 0 := by
      intro hw; apply hpos z hP; rw [hQ, hw, zero_mul]
    field_simp

/-- For a set `Z` of predecessors of `k` containing its parents, the table of `k` is its
conditional law given `Z`: `P(X_k = a, Z = z) = p_k (a | z_{pa k}) P(Z = z)`. -/
theorem sum_filter_restrict_joint_eq_cpt_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k) (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z)
    (z : Z → α) :
    ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x =
      (b.cpt k fun j => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩).weights a *
        ∑ x with (fun i : Z => x i) = z, b.joint x := by
  rw [← sum_restrict_intervene b k a Z hZk, mul_sum, sum_filter, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hk : x k = a
  · by_cases hz : (fun i : Z => x i) = z
    · simp only [hk, hz, and_self, ↓reduceIte]
      rw [joint_eq_intervene_mul b k a hk, mul_comm,
        show b.paVal k x = fun j : b.pa k => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩ from
          funext fun j : b.pa k => congrFun hz ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩]
    · simp [hz]
  · rw [joint_intervene]
    simp [hk]

/-- Back-door adjustment for a set of predecessors containing the parents, when the table of
node `k` gives the value `a` positive probability at every value of the parents. -/
theorem sum_intervene_joint_mul_of_pred_of_cpt_ne_zero [Fintype α] [DecidableEq α] (k : Fin n)
    (a : α) (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k)
    (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z) (f : (Fin n → α) → ℝ)
    (hcpt : ∀ u, (b.cpt k u).weights a ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * f x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) :=
  b.sum_intervene_joint_mul_of_pred k a Z hZk hpaZ f fun z hz => by
    rw [sum_filter_restrict_joint_eq_cpt_mul b k a Z hZk hpaZ]
    exact mul_ne_zero (hcpt _) hz

end BayesNet

namespace BayesNet

variable {n : ℕ} (b : BayesNet α n)

/-! ### The graph of a network and d-separation -/

/-- The edge `i → j` of the network's graph: `i` is a parent of `j`. -/
def Edge (i j : Fin n) : Prop :=
  ∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ b.pa j

/-- `j` is a descendant of `i` (every node is its own descendant). -/
def IsDescendant (i j : Fin n) : Prop :=
  Relation.ReflTransGen b.Edge i j

/-- `i` and `j` are adjacent in the skeleton of the graph. -/
def Adj (i j : Fin n) : Prop :=
  b.Edge i j ∨ b.Edge j i

/-- A path of the skeleton from `x` to `y`: a list of distinct nodes, consecutive ones
adjacent, starting at `x` and ending at `y`. -/
def IsPath (x y : Fin n) (p : List (Fin n)) : Prop :=
  p.Nodup ∧ p.IsChain b.Adj ∧ p.head? = some x ∧ p.getLast? = some y

/-- The consecutive nodes `u, m, w` of a path are blocked by `Z` (Pearl 2009, Definition
1.2.3): either `m` is a collider `u → m ← w` none of whose descendants is in `Z`, or `m` is not
a collider (a chain or a fork) and `m ∈ Z`. -/
def BlockedAt (Z : Set (Fin n)) (u m w : Fin n) : Prop :=
  (b.Edge u m ∧ b.Edge w m ∧ ∀ d, b.IsDescendant m d → d ∉ Z) ∨
    (¬(b.Edge u m ∧ b.Edge w m) ∧ m ∈ Z)

/-- A path is blocked by `Z` if some three consecutive nodes of it are. -/
def PathBlocked (Z : Set (Fin n)) (p : List (Fin n)) : Prop :=
  ∃ (i : ℕ) (h : i + 2 < p.length), b.BlockedAt Z p[i] p[i + 1] p[i + 2]

/-- **d-separation** (Pearl 1988; Pearl 2009, Definition 1.2.3): `Z` d-separates `X` from `Y`
if every path between a node of `X` and a node of `Y` is blocked by `Z`. -/
def DSeparated (X Y Z : Set (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ p, b.IsPath x y p → b.PathBlocked Z p

/-- Blocking at a node does not depend on the direction in which the path is read. -/
theorem blockedAt_comm {Z : Set (Fin n)} {u m w : Fin n} :
    b.BlockedAt Z u m w ↔ b.BlockedAt Z w m u := by
  unfold BlockedAt
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩

/-- The reverse of a path from `x` to `y` is a path from `y` to `x`. -/
theorem isPath_reverse {x y : Fin n} {p : List (Fin n)} (h : b.IsPath x y p) :
    b.IsPath y x p.reverse := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨List.nodup_reverse.2 h1, ?_, by simpa using h4, by simpa using h3⟩
  rw [List.isChain_reverse]
  exact h2.imp fun a b hab => hab.symm

/-- If a path is blocked by `Z`, so is its reverse. -/
theorem pathBlocked_reverse {Z : Set (Fin n)} {p : List (Fin n)} (h : b.PathBlocked Z p) :
    b.PathBlocked Z p.reverse := by
  obtain ⟨i, hi, hb⟩ := h
  refine ⟨p.length - 3 - i, by simp; omega, ?_⟩
  rw [blockedAt_comm]
  simp only [List.getElem_reverse]
  convert hb using 3 <;> omega

/-- d-separation is symmetric. -/
theorem DSeparated.symm {X Y Z : Set (Fin n)} (h : b.DSeparated X Y Z) : b.DSeparated Y X Z :=
  fun y hy x hx p hp => by
    simpa using b.pathBlocked_reverse (h x hx y hy p.reverse (b.isPath_reverse hp))

end BayesNet

end Cslib.MachineLearning.GraphicalModels
