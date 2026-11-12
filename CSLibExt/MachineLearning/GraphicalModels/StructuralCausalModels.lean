/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs

/-!
# Finite structural causal models: structural equations and unique solutions

A finite recursive structural causal model (SCM) lists its endogenous variables
`X 0, …, X (n - 1)` in a topological order. Node `k` has an exogenous noise variable of type
`U k`, parents among the earlier nodes `0, …, k - 1`, and a structural equation
`x_k = f_k (x_{pa k}, u_k)` (Pearl, Glymour and Jewell 2016, §1.5; Pearl 2009, Definition 7.1.1,
recursive case; the linear-Gaussian case is Evans, *Graphical Models*, §8.6, eq. (8.1)).

## Main definitions

* `FiniteSCM α n U`: parents (the convention of `BayesNet`) and structural functions. The
  exogenous law is not part of the structure; independence of the noises is an extra assumption
  of the statements that use a law.
* `FiniteSCM.IsSolution M u x`: `x` satisfies every structural equation at the noise value `u`.
* `FiniteSCM.solve M u`: the solution map, computed by recursion along the order.
* `FiniteSCM.inducedLaw M μ`: the observational law under independent noises with laws `μ k`,
  the push-forward of the product noise law under `solve`.
* `FiniteSCM.inducedBayesNet M μ`: the Bayesian network with the model's parents whose table at
  node `k` is the push-forward of `μ k` under the structural function `f_k (z, ·)`.
* `FiniteSCM.doNode M k a`, `FiniteSCM.doSet M W w`: **surgery**: the structural equation of node
  `k` (of every node of `W`) is replaced by a constant and its parents are deleted.
* `FiniteSCM.counterfactual M k a u`: the **counterfactual** solution had node `k` been set to
  `a`, at the same noise value `u`. `FiniteSCM.counterfactualProb M μ E k a F`: the conditional
  counterfactual probability `P(X_{k ← a} ∈ F | E)` for factual evidence `E`;
  `FiniteSCM.posteriorWeight`: the posterior of the noise given the evidence. Both are
  genuine probabilities only when the evidence has positive probability; for
  zero-probability evidence they are `0` by the totalized-division convention.

## Main results

* `FiniteSCM.solve_isSolution`, `FiniteSCM.IsSolution.eq_solve`,
  `FiniteSCM.existsUnique_isSolution`: **unique solvability**: for every noise value the
  structural equations have exactly one solution, `solve u`.
* `FiniteSCM.solve_congr_of_ancestral`: on a parent-closed (ancestral) set of nodes the solution
  depends only on the noise on that set; in particular a node's value depends only on its own and
  its ancestors' noise.
* `FiniteSCM.inducedLaw_eq_joint`: **a Markovian SCM induces its Bayesian network**: under
  independent noises the law of the solution is the joint of `inducedBayesNet` (Pearl 2009,
  Theorem 1.4.1), so it factorizes along the graph (`BayesNet.joint_eq_prod`). Dependent noises
  are not covered: they need explicit latent nodes.
* `BayesNet.responseSCM_inducedLaw`: **every finite Bayesian network has a Markovian SCM
  realization**: the response-function SCM (`BayesNet.responseSCM`, noise of node `k` a function
  from parent values to values) with independent response noises (`BayesNet.responseLaw`, rows of
  the tables drawn independently) has the network's joint as its law. The coupling of responses
  at different parent values is one choice among many; it is not identified by the network.
* `FiniteSCM.inducedLaw_doNode`, `FiniteSCM.inducedLaw_doSet`: **surgery commutes with the
  do-operator**: the law of the model after surgery is the joint of the induced Bayesian network
  after `BayesNet.intervene` (resp. `BayesNet.mutilateSet`), the causal Bayesian-network reading
  of interventions (Pearl 2009, §3.2 and Definition 7.1.2).
* `FiniteSCM.solve_doNode_of_ancestral`: on a parent-closed set not containing `k` (for example
  the non-descendants of `k`), surgery on `k` does not change the solution.
* `FiniteSCM.counterfactualProb_eq_sum_posteriorWeight`: **abduction, action, prediction**
  (Pearl 2009, Theorem 7.1.7): for evidence of positive probability, the counterfactual
  probability is the posterior weight of the noise values whose counterfactual solution lies in
  `F`; `FiniteSCM.sum_posteriorWeight`: the posterior is a probability distribution;
  `FiniteSCM.counterfactualProb_true`: without evidence the counterfactual probability is the
  interventional one, computed by `BayesNet.intervene`.

Cyclic systems (where a solution may fail to exist or be unique) are not expressible: parents
always precede their child.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §1.5.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.4, §7.1.
* R. Evans, *Graphical Models*, lecture notes, University of Oxford, §8.6.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

/-- A finite recursive (acyclic) structural causal model on endogenous nodes `0, …, n - 1`
listed in a topological order, with values in `α` and exogenous noise of type `U k` at node `k`.
Node `k` has parents among the earlier nodes `0, …, k - 1` (the parent convention of
`BayesNet`) and a structural equation `x_k = f_k (x_{pa k}, u_k)`. The exogenous law is not part
of the structure: it is supplied where a probabilistic statement needs it, and independence of
the noises (the Markovian case) is an extra assumption of those statements. Shared or dependent
noise is modelled by explicit latent endogenous nodes. -/
structure FiniteSCM (α : Type*) (n : ℕ) (U : Fin n → Type*) where
  /-- The parents of node `k`, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The structural function of node `k`: its value from the values of its parents and its
  own exogenous noise. -/
  f : (k : Fin n) → (pa k → α) → U k → α

namespace FiniteSCM

/-- The values of the parents of node `k` in a full assignment `x`. -/
def paVal {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (k : Fin n)
    (x : Fin n → α) : M.pa k → α :=
  fun j => x (Fin.castLE k.2.le j)

/-- `x` satisfies every structural equation `x_k = f_k (x_{pa k}, u_k)` at the noise value
`u`. -/
def IsSolution {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (u : (k : Fin n) → U k) (x : Fin n → α) : Prop :=
  ∀ k, x k = M.f k (M.paVal k x) (u k)

/-- The values of the first `m` nodes at the noise value `u`, computed by recursion along the
topological order. -/
def solvePrefix {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (u : (k : Fin n) → U k) : (m : ℕ) → m ≤ n → Fin m → α
  | 0, _ => Fin.elim0
  | m + 1, h => Fin.snoc (M.solvePrefix u m (Nat.le_of_succ_le h))
      (M.f ⟨m, h⟩ (fun j => M.solvePrefix u m (Nat.le_of_succ_le h) j) (u ⟨m, h⟩))

/-- The solution map of the model: the values of all nodes at the noise value `u`. -/
def solve {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (u : (k : Fin n) → U k) : Fin n → α :=
  M.solvePrefix u n le_rfl

/-- Extending the prefix by one node does not change the earlier values. -/
theorem solvePrefix_castSucc {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (u : (k : Fin n) → U k) (m : ℕ) (h : m + 1 ≤ n)
    (i : Fin m) :
    M.solvePrefix u (m+1) h i.castSucc = M.solvePrefix u m (Nat.le_of_succ_le h) i := by
  simp only [solvePrefix, Fin.snoc_castSucc]

/-- The new value in a prefix of length `m + 1` is given by the structural equation of node `m`. -/
theorem solvePrefix_last {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (u : (k : Fin n) → U k) (m : ℕ) (h : m + 1 ≤ n) :
    M.solvePrefix u (m+1) h (Fin.last m) =
      M.f ⟨m, h⟩ (fun j => M.solvePrefix u m (Nat.le_of_succ_le h) j) (u ⟨m, h⟩) := by
  simp only [solvePrefix, Fin.snoc_last]

/-- A longer prefix agrees with a shorter one on the shorter one's nodes. -/
private theorem solvePrefix_castLE_aux {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (u : (k : Fin n) → U k) (m : ℕ)
    (k : ℕ) (hmk : m ≤ k) (hk : k ≤ n) (hm : m ≤ n) (i : Fin m) :
      M.solvePrefix u k hk (Fin.castLE hmk i) = M.solvePrefix u m hm i := by
  induction k, hmk using Nat.le_induction with
  | base =>
    have hcast : Fin.castLE (le_refl m) i = i := Fin.castLE_refl _ i
    simp only [hcast]
  | succ k hmn ih =>
    have h1 : ∀ (h : m ≤ k + 1), Fin.castLE h i = (Fin.castLE hmn i).castSucc := by
      intro h
      apply Fin.ext
      simp [Fin.val_castLE]
    rw [h1 _]
    rw [M.solvePrefix_castSucc u k hk]
    exact ih (Nat.le_of_succ_le hk)

/-- Every prefix is a restriction of the solution map. -/
theorem solvePrefix_eq_solve {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (u : (k : Fin n) → U k) (m : ℕ) (h : m ≤ n) (i : Fin m) :
    M.solvePrefix u m h i = M.solve u (Fin.castLE h i) := by
  unfold solve
  exact (M.solvePrefix_castLE_aux u m n h le_rfl h i).symm

/-- A solution of the structural equations agrees with every prefix. -/
theorem isSolution_prefix {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) {u : (k : Fin n) → U k} {x : Fin n → α}
    (hx : M.IsSolution u x) (m : ℕ) (h : m ≤ n) (i : Fin m) :
    x (Fin.castLE h i) = M.solvePrefix u m h i := by
  induction m with
  | zero =>
    exact Fin.elim0 i
  | succ m ih =>
    refine Fin.lastCases ?_ ?_ i
    · have h_cast : Fin.castLE h (Fin.last m) = (⟨m, h⟩ : Fin n) := by
        apply Fin.ext
        simp [Fin.val_castLE, Fin.val_last]
      rw [h_cast]
      have hx_m := hx ⟨m, h⟩
      have h_last := M.solvePrefix_last u m h
      rw [hx_m, h_last]
      congr 1
      funext j
      simp only [paVal]
      exact ih (Nat.le_of_succ_le h) (↑j : Fin m)
    · intro j
      have h_rhs := M.solvePrefix_castSucc u m h j
      rw [h_rhs]
      exact ih (Nat.le_of_succ_le h) j

/-- On a parent-closed set, prefixes depend only on the noise on that set. -/
theorem solvePrefix_ancestral {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) {S : Set (Fin n)}
    (hS : ∀ k ∈ S, ∀ j ∈ M.pa k, Fin.castLE k.2.le j ∈ S)
    {u u' : (k : Fin n) → U k} (hu : ∀ k ∈ S, u k = u' k)
    (m : ℕ) (h : m ≤ n) (i : Fin m) (hmem : Fin.castLE h i ∈ S) :
    M.solvePrefix u m h i = M.solvePrefix u' m h i := by
  induction m with
  | zero =>
    exact Fin.elim0 i
  | succ m ih =>
    revert hmem
    refine Fin.lastCases ?_ ?_ i
    · intro hmem_last
      have h_cast : Fin.castLE h (Fin.last m) = (⟨m, h⟩ : Fin n) := by
        apply Fin.ext
        simp [Fin.val_castLE, Fin.val_last]
      have h_mem : (⟨m, h⟩ : Fin n) ∈ S := by
        rw [← h_cast]
        exact hmem_last
      have h_last_u := M.solvePrefix_last u m h
      have h_last_u' := M.solvePrefix_last u' m h
      rw [h_last_u, h_last_u']
      have hu_m : u ⟨m, h⟩ = u' ⟨m, h⟩ := hu ⟨m, h⟩ h_mem
      rw [hu_m]
      congr 1
      funext j
      apply ih (Nat.le_of_succ_le h) (↑j : Fin m)
      have hj_mem : (↑j : Fin (⟨m, h⟩ : Fin n)) ∈ M.pa ⟨m, h⟩ := j.property
      have hpar := hS ⟨m, h⟩ h_mem (↑j) hj_mem
      exact hpar
    · intro j hmem_succ
      have h_rhs_u := M.solvePrefix_castSucc u m h j
      have h_rhs_u' := M.solvePrefix_castSucc u' m h j
      rw [h_rhs_u, h_rhs_u']
      apply ih (Nat.le_of_succ_le h) j
      exact hmem_succ

/-- The solution map solves every structural equation. -/
theorem solve_isSolution {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (u : (k : Fin n) → U k) : M.IsSolution u (M.solve u) := by
  intro k
  obtain ⟨m, hm⟩ := k
  have hm1 : m + 1 ≤ n := hm
  have h_last_cast : Fin.castLE hm1 (Fin.last m) = (⟨m, hm⟩ : Fin n) := by
    apply Fin.ext
    simp [Fin.val_castLE, Fin.val_last]
  have h_prefix : M.solvePrefix u (m+1) hm1 (Fin.last m) = M.solve u ⟨m, hm⟩ := by
    have h := M.solvePrefix_eq_solve u (m+1) hm1 (Fin.last m)
    rw [h_last_cast] at h
    exact h
  have h_last_eq := M.solvePrefix_last u m hm1
  rw [← h_prefix, h_last_eq]
  have hfun : (fun (j : M.pa ⟨m, hm1⟩) => M.solvePrefix u m (Nat.le_of_succ_le hm1) (↑j : Fin m)) =
      M.paVal ⟨m, hm⟩ (M.solve u) := by
    funext j
    simp only [paVal]
    exact M.solvePrefix_eq_solve u m (Nat.le_of_succ_le hm1) (↑j : Fin m)
  rw [hfun]

/-- Every solution of the structural equations is the solution map's value. -/
theorem IsSolution.eq_solve {α : Type*} {n : ℕ} {U : Fin n → Type*} {M : FiniteSCM α n U}
    {u : (k : Fin n) → U k} {x : Fin n → α} (hx : M.IsSolution u x) : x = M.solve u := by
  funext k
  have h := M.isSolution_prefix hx n le_rfl k
  have hcast : Fin.castLE le_rfl k = k := Fin.castLE_refl le_rfl k
  rw [hcast] at h
  exact h

/-- **Unique solvability of a recursive SCM**: for every noise value `u` the structural
equations have exactly one solution. -/
theorem existsUnique_isSolution {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (u : (k : Fin n) → U k) : ∃! x, M.IsSolution u x := by
  refine ⟨M.solve u, M.solve_isSolution u, ?_⟩
  intro y hy
  exact IsSolution.eq_solve hy

/-- On a set `S` of nodes closed under taking parents (an ancestral set), the solution depends
only on the noise at the nodes of `S`. In particular the value of node `k` depends only on the
noise at `k` and its ancestors. -/
theorem solve_congr_of_ancestral {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) {S : Set (Fin n)}
    (hS : ∀ k ∈ S, ∀ j ∈ M.pa k, Fin.castLE k.2.le j ∈ S) {u u' : (k : Fin n) → U k}
    (hu : ∀ k ∈ S, u k = u' k) : ∀ k ∈ S, M.solve u k = M.solve u' k := by
  intro k hk
  have hcast : Fin.castLE le_rfl k = k := Fin.castLE_refl le_rfl k
  have hmem : Fin.castLE le_rfl k ∈ S := by
    rw [hcast]
    exact hk
  exact M.solvePrefix_ancestral hS hu n le_rfl k hmem

/-! ### Markovian models and their Bayesian networks -/

section Markovian

open Finset Convexity

/-- The probability of the noise value `u` when the noises of the nodes are independent with
laws `μ k` (the Markovian case): `∏ k, μ_k (u_k)`. -/
noncomputable def noiseWeight {n : ℕ} {U : Fin n → Type*} (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (u : (k : Fin n) → U k) : ℝ :=
  ∏ k, (μ k).weights (u k)

/-- The observational law induced by the model under independent noises with laws `μ k`: the
probability that the solution is `x`, that is, the push-forward of the product noise law under
the solution map. -/
noncomputable def inducedLaw {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) : ℝ :=
  ∑ u with M.solve u = x, noiseWeight μ u

/-- The Bayesian network of the model under independent noises with laws `μ k`: it has the
model's parents, and the table of node `k` at parent values `z` is the law of
`f_k (z, u_k)` for `u_k ∼ μ_k`, the push-forward of `μ_k` under `f_k (z, ·)`. -/
noncomputable def inducedBayesNet {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) : BayesNet α n where
  pa := M.pa
  cpt k z := (μ k).map (M.f k z)

/-- The push-forward weights of a noise law under a structural function are the sums of the
noise weights over the fibers. -/
private theorem map_weights_eq_sum {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) (k : Fin n) :
    ((μ k).map (M.f k (M.paVal k x))).weights (x k)
      = ∑ v, (if M.f k (M.paVal k x) v = x k then (μ k).weights v else 0) := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

/-- **A Markovian SCM induces its Bayesian network**: under independent noises, the law of the
unique solution is the joint distribution of the Bayesian network whose tables are the
push-forwards of the noise laws under the structural functions. -/
theorem inducedLaw_eq_joint {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] [Nonempty α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) : M.inducedLaw μ x = (M.inducedBayesNet μ).joint x := by
  classical
  rw [(M.inducedBayesNet μ).joint_eq_prod x]
  have hfactor : ∀ k : Fin n,
      ((M.inducedBayesNet μ).cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)
        = ∑ v, (if M.f k (M.paVal k x) v = x k then (μ k).weights v else 0) :=
    fun k => map_weights_eq_sum M μ x k
  simp only [hfactor]
  rw [Fintype.prod_sum]
  unfold inducedLaw
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold noiseWeight
  by_cases h : M.solve u = x
  · rw [ite_eq_left h]
    have hsol : M.IsSolution u x := by
      rw [← h]
      exact M.solve_isSolution u
    have hall : ∀ k, M.f k (M.paVal k x) (u k) = x k := fun k => (hsol k).symm
    exact Finset.prod_congr rfl fun k _ => (ite_eq_left (hall k)).symm
  · rw [ite_eq_right h]
    have hnex : ∃ k, x k ≠ M.f k (M.paVal k x) (u k) := by
      by_contra hall
      push Not at hall
      exact h (IsSolution.eq_solve hall).symm
    obtain ⟨k0, hk0⟩ := hnex
    exact (Finset.prod_eq_zero (Finset.mem_univ k0)
      (ite_eq_right (fun hc => hk0 hc.symm))).symm

end Markovian

end FiniteSCM

/-! ### Markovian SCM realization of a Bayesian network -/

namespace BayesNet

open Finset Convexity

/-- The response-function SCM of a Bayesian network: the noise of node `k` is a response
function `r : (pa k → α) → α`, choosing a value of node `k` for every value of its parents, and
the structural equation is `x_k = r (x_{pa k})`. -/
def responseSCM {α : Type*} {n : ℕ} (b : BayesNet α n) :
    FiniteSCM α n (fun k => (b.pa k → α) → α) where
  pa := b.pa
  f _ z r := r z

/-- The weight of a response function of node `k`: the response values at different parent
values are drawn independently from the tables, `∏_z p_k (r z | z)`. -/
noncomputable def responseWeight {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : BayesNet α n) (k : Fin n) (r : (b.pa k → α) → α) : ℝ :=
  ∏ z, (b.cpt k z).weights (r z)

/-- Response weights are nonnegative. -/
theorem responseWeight_nonneg {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : BayesNet α n) (k : Fin n) (r : (b.pa k → α) → α) : 0 ≤ b.responseWeight k r := by
  simp only [responseWeight]
  exact Finset.prod_nonneg fun z _ => (b.cpt k z).nonneg _

/-- Response weights sum to one. -/
theorem sum_responseWeight {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : BayesNet α n) (k : Fin n) :
    (Finsupp.equivFunOnFinite.symm (b.responseWeight k)).sum (fun _ w => w) = 1 := by
  classical
  rw [Finsupp.sum_fintype _ _ fun _ => rfl]
  have hpoint : ∀ r : (b.pa k → α) → α,
      (Finsupp.equivFunOnFinite.symm (b.responseWeight k)) r = b.responseWeight k r :=
    fun _ => rfl
  simp only [hpoint, responseWeight]
  rw [← Fintype.prod_sum]
  have htot : ∀ z : b.pa k → α, (∑ a, (b.cpt k z).weights a) = 1 :=
    fun z => (b.cpt k z).total_of_fintype
  simp only [htot, Finset.prod_const_one]

/-- The law of the response function of node `k`. -/
noncomputable def responseLaw {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : BayesNet α n) (k : Fin n) : StdSimplex ℝ ((b.pa k → α) → α) where
  weights := Finsupp.equivFunOnFinite.symm (b.responseWeight k)
  nonneg r := b.responseWeight_nonneg k r
  total := b.sum_responseWeight k

/-- **Every finite Bayesian network is induced by a Markovian SCM**: the response-function SCM
with independent response-function noises has the network's joint as its observational law. -/
theorem responseSCM_inducedLaw {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) (x : Fin n → α) :
    b.responseSCM.inducedLaw b.responseLaw x = b.joint x := by
  classical
  rw [FiniteSCM.inducedLaw_eq_joint]
  simp only [joint_eq_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hfb := FiniteSCM.map_weights_eq_sum b.responseSCM b.responseLaw x k
  change ((b.responseLaw k).map (b.responseSCM.f k (b.responseSCM.paVal k x))).weights (x k)
    = (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)
  rw [hfb]
  have hpoint : ∀ v : (b.pa k → α) → α,
      (if b.responseSCM.f k (b.responseSCM.paVal k x) v = x k then (b.responseLaw k).weights v
        else 0)
        = (if v (b.responseSCM.paVal k x) = x k then ∏ z, (b.cpt k z).weights (v z) else 0) :=
    fun _ => rfl
  simp only [hpoint]
  have hpa : b.responseSCM.paVal k x
      = (fun j : b.pa k => x (Fin.castLE k.2.le (j : Fin k))) := rfl
  rw [hpa]
  set z₀ : b.pa k → α := (fun j => x (Fin.castLE k.2.le (j : Fin k))) with hz₀
  set a₀ := x k with ha₀
  let g : (b.pa k → α) → α → ℝ := fun z a =>
    if z = z₀ then (if a = a₀ then (b.cpt k z).weights a else 0) else (b.cpt k z).weights a
  have hg : ∀ z a, g z a
      = (if z = z₀ then (if a = a₀ then (b.cpt k z).weights a else 0)
        else (b.cpt k z).weights a) :=
    fun _ _ => rfl
  have hpoint_g : ∀ v : (b.pa k → α) → α,
      (∏ z, g z (v z)) = (if v z₀ = a₀ then ∏ z, (b.cpt k z).weights (v z) else 0) := by
    intro v
    by_cases h : v z₀ = a₀
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun z _ => ?_
      by_cases hz : z = z₀
      · simp [hg, hz, h]
      · simp [hg, hz]
    · rw [ite_eq_right h]
      have hz0 : g z₀ (v z₀) = 0 := by simp [hg, h]
      exact Finset.prod_eq_zero (Finset.mem_univ z₀) hz0
  have hsum_eq : (∑ v : (b.pa k → α) → α, ∏ z : b.pa k → α, g z (v z))
      = ∑ v : (b.pa k → α) → α,
        (if v z₀ = a₀ then ∏ z : b.pa k → α, (b.cpt k z).weights (v z) else 0) :=
    Finset.sum_congr rfl fun v _ => hpoint_g v
  have hprod_g : (∏ z : b.pa k → α, ∑ a : α, g z a) = (b.cpt k z₀).weights a₀ := by
    have hfactor : ∀ z : b.pa k → α,
        (∑ a : α, g z a) = (if z = z₀ then (b.cpt k z₀).weights a₀ else 1) := by
      intro z
      by_cases hz : z = z₀
      · subst hz
        rw [ite_eq_left rfl]
        have hgg : ∀ a, g z₀ a = (if a = a₀ then (b.cpt k z₀).weights a else 0) := by
          intro a
          simp [hg]
        simp only [hgg]
        have hW' : (if a₀ = a₀ then (b.cpt k z₀).weights a₀ else (0 : ℝ))
            = (b.cpt k z₀).weights a₀ := ite_eq_left rfl
        have h1' : (∑ a : α, (if a = a₀ then (b.cpt k z₀).weights a else 0))
            = (if a₀ = a₀ then (b.cpt k z₀).weights a₀ else 0) := by
          apply Finset.sum_eq_single a₀
          · intro a _ ha
            simp [ha]
          · intro hmem
            exact absurd (Finset.mem_univ a₀) hmem
        rw [hW'] at h1'
        exact h1'
      · rw [ite_eq_right hz]
        have hgg : ∀ a, g z a = (b.cpt k z).weights a := by
          intro a
          simp [hg, hz]
        simp only [hgg]
        exact (b.cpt k z).total_of_fintype
    simp only [hfactor]
    have hW : (if z₀ = z₀ then (b.cpt k z₀).weights a₀ else (1 : ℝ))
        = (b.cpt k z₀).weights a₀ := ite_eq_left rfl
    have h1 : (∏ z : b.pa k → α, (if z = z₀ then (b.cpt k z₀).weights a₀ else 1))
        = (if z₀ = z₀ then (b.cpt k z₀).weights a₀ else 1) := by
      apply Finset.prod_eq_single z₀
      · intro z _ hz
        simp [hz]
      · intro hmem
        exact absurd (Finset.mem_univ z₀) hmem
    rw [hW] at h1
    exact h1
  calc ∑ v : (b.pa k → α) → α,
          (if v z₀ = a₀ then ∏ z : b.pa k → α, (b.cpt k z).weights (v z) else 0)
      = ∑ v : (b.pa k → α) → α, ∏ z : b.pa k → α, g z (v z) := hsum_eq.symm
    _ = ∏ z : b.pa k → α, ∑ a : α, g z a := by rw [Fintype.prod_sum]
    _ = (b.cpt k z₀).weights a₀ := hprod_g

end BayesNet

/-! ### Surgery and the do-operator -/

namespace BayesNet

open Finset Convexity

/-- Helper: away from the intervened node, `intervene` keeps the parents. (Atlas's
`BayesNet.intervene_pa_of_ne` carries an unused `[Nonempty α]` section variable, so it does not
apply in the `Nonempty`-free helpers below.) -/
private theorem intervene_pa_of_ne' {α : Type*} {n : ℕ} (b : BayesNet α n) (k : Fin n) (a : α)
    {j : Fin n} (hjk : j ≠ k) : (b.intervene k a).pa j = b.pa j := by
  simp [intervene, hjk]

/-- Helper: at the intervened node, the table is the point mass. -/
private theorem intervene_cpt_of_eq {α : Type*} {n : ℕ} (b : BayesNet α n) (k : Fin n) (a : α)
    (z : (b.intervene k a).pa k → α) :
    (b.intervene k a).cpt k z = StdSimplex.single a := by
  simp [intervene]

/-- Helper: away from the intervened node, the table is the original one transported. -/
private theorem intervene_cpt_of_ne {α : Type*} {n : ℕ} (b : BayesNet α n) (k : Fin n) (a : α)
    {j : Fin n} (hjk : j ≠ k) (z : (b.intervene k a).pa j → α) :
    (b.intervene k a).cpt j z
      = b.cpt j (fun i => z ⟨i.1, by rw [b.intervene_pa_of_ne' k a hjk]; exact i.2⟩) := by
  simp [intervene, hjk]

/-- Helper: away from the mutilated set, `mutilateSet` keeps the parents. -/
private theorem mutilateSet_pa_of_not_mem {α : Type*} {n : ℕ} (b : BayesNet α n)
    (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∉ W) :
    (b.mutilateSet W w).pa j = b.pa j := by
  simp [mutilateSet, hjW]

/-- Helper: on the mutilated set, the table is the point mass. -/
private theorem mutilateSet_cpt_of_mem {α : Type*} {n : ℕ} (b : BayesNet α n)
    (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∈ W)
    (z : (b.mutilateSet W w).pa j → α) :
    (b.mutilateSet W w).cpt j z = StdSimplex.single (w j) := by
  simp [mutilateSet, hjW]

/-- Helper: away from the mutilated set, the table is the original one transported. -/
private theorem mutilateSet_cpt_of_not_mem {α : Type*} {n : ℕ} (b : BayesNet α n)
    (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∉ W)
    (z : (b.mutilateSet W w).pa j → α) :
    (b.mutilateSet W w).cpt j z
      = b.cpt j (fun i => z ⟨i, by rw [b.mutilateSet_pa_of_not_mem W w hjW]; exact i.2⟩) := by
  simp [mutilateSet, hjW]

end BayesNet

namespace FiniteSCM

open Finset Convexity

/-- **Surgery** `do(X_k = a)` on a structural causal model: the structural equation of node `k`
is replaced by the constant `a` and its parents are deleted; every other node keeps its parents,
its noise and its structural function. -/
def doNode {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (k : Fin n) (a : α) :
    FiniteSCM α n U where
  pa j := if j = k then ∅ else M.pa j
  f j z u := if h : j = k then a
    else M.f j (fun i => z ⟨i, by simp [h]⟩) u

/-- Surgery `do(X_W = w)` on a set `W` of nodes: each structural equation of a node `j ∈ W` is
replaced by the constant `w j` and its parents are deleted. -/
def doSet {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (W : Finset (Fin n))
    (w : Fin n → α) : FiniteSCM α n U where
  pa j := if j ∈ W then ∅ else M.pa j
  f j z u := if h : j ∈ W then w j
    else M.f j (fun i => z ⟨i, by simp [h]⟩) u

/-- Helper: the induced-network factor at the parent values from `x`, in push-forward form. -/
private theorem inducedBayesNet_cpt_apply {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) (j : Fin n) :
    (M.inducedBayesNet μ).cpt j (fun t => x (Fin.castLE j.2.le ↑t))
      = (μ j).map (M.f j (fun t => x (Fin.castLE j.2.le ↑t))) := rfl

/-- Helper: the intervened induced-network table away from `k`, in push-forward form. -/
private theorem inducedBayesNet_intervene_cpt_of_ne {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (k : Fin n) (a : α) {j : Fin n} (hjk : j ≠ k)
    (z : ((M.inducedBayesNet μ).intervene k a).pa j → α) :
    ((M.inducedBayesNet μ).intervene k a).cpt j z
      = (μ j).map (M.f j (fun i => z ⟨i.1, by
        rw [(M.inducedBayesNet μ).intervene_pa_of_ne' k a hjk]; exact i.2⟩)) := by
  rw [(M.inducedBayesNet μ).intervene_cpt_of_ne k a hjk]
  rfl

/-- Helper: the mutilated induced-network table away from `W`, in push-forward form. -/
private theorem inducedBayesNet_mutilateSet_cpt_of_not_mem {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∉ W)
    (z : ((M.inducedBayesNet μ).mutilateSet W w).pa j → α) :
    ((M.inducedBayesNet μ).mutilateSet W w).cpt j z
      = (μ j).map (M.f j (fun i => z ⟨i, by
        rw [(M.inducedBayesNet μ).mutilateSet_pa_of_not_mem W w hjW]; exact i.2⟩)) := by
  rw [(M.inducedBayesNet μ).mutilateSet_cpt_of_not_mem W w hjW]
  rfl

/-- Helper: away from the surgery node, `doNode` keeps the parents. -/
theorem doNode_pa_of_ne {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (k : Fin n) (a : α) {j : Fin n} (hjk : j ≠ k) :
    (M.doNode k a).pa j = M.pa j := by
  simp [doNode, hjk]

/-- Helper: at the surgery node, the structural map is constant. -/
theorem doNode_f_of_eq {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (k : Fin n) (a : α) (z : (M.doNode k a).pa k → α) :
    (M.doNode k a).f k z = fun _ => a := by
  funext v
  simp [doNode]

/-- Helper: away from the surgery node, the structural map is the original one transported. -/
theorem doNode_f_of_ne {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (k : Fin n) (a : α) {j : Fin n} (hjk : j ≠ k)
    (z : (M.doNode k a).pa j → α) :
    (M.doNode k a).f j z
      = M.f j (fun i => z ⟨↑i, by rw [M.doNode_pa_of_ne k a hjk]; exact i.2⟩) := by
  funext v
  simp [doNode, hjk]

/-- Helper: away from the surgery set, `doSet` keeps the parents. -/
theorem doSet_pa_of_not_mem {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∉ W) :
    (M.doSet W w).pa j = M.pa j := by
  simp [doSet, hjW]

/-- Helper: on the surgery set, the structural map is constant. -/
theorem doSet_f_of_mem {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∈ W)
    (z : (M.doSet W w).pa j → α) :
    (M.doSet W w).f j z = fun _ => w j := by
  funext v
  simp [doSet, hjW]

/-- Helper: away from the surgery set, the structural map is the original one transported. -/
theorem doSet_f_of_not_mem {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (W : Finset (Fin n)) (w : Fin n → α) {j : Fin n} (hjW : j ∉ W)
    (z : (M.doSet W w).pa j → α) :
    (M.doSet W w).f j z
      = M.f j (fun i => z ⟨i, by rw [M.doSet_pa_of_not_mem W w hjW]; exact i.2⟩) := by
  funext v
  simp [doSet, hjW]

/-- On a parent-closed set of nodes not containing `k`, surgery on `k` does not change the
solution. -/
theorem solve_doNode_of_ancestral {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (k : Fin n) (a : α) {S : Set (Fin n)}
    (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S) (hk : k ∉ S)
    (u : (j : Fin n) → U j) : ∀ j ∈ S, (M.doNode k a).solve u j = M.solve u j := by
  suffices h : ∀ m j (_ : j ∈ S) (_ : j.val < m), (M.doNode k a).solve u j = M.solve u j by
    intro j hj
    exact h (j.val + 1) j hj (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero =>
    intro j _ hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj hm
    have hjk : j ≠ k := fun heq => hk (heq ▸ hj)
    have hsolD := (M.doNode k a).solve_isSolution u j
    have hsolM := M.solve_isSolution u j
    rw [hsolD, M.doNode_f_of_ne k a hjk, hsolM]
    congr 1
    funext i
    change (M.doNode k a).solve u (Fin.castLE j.2.le ↑i)
      = M.solve u (Fin.castLE j.2.le ↑i)
    exact ih _ (hS j hj _ i.2) (Nat.lt_of_lt_of_le (i.1).isLt (Nat.le_of_lt_succ hm))

/-- **Surgery commutes with the do-operator**: under independent noises, the law of the model
after `do(X_k = a)` is the joint of the induced Bayesian network after the intervention
`do(X_k = a)`. -/
theorem inducedLaw_doNode {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] [Nonempty α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (k : Fin n) (a : α) (x : Fin n → α) :
    (M.doNode k a).inducedLaw μ x = ((M.inducedBayesNet μ).intervene k a).joint x := by
  rw [(M.doNode k a).inducedLaw_eq_joint μ x,
    ((M.doNode k a).inducedBayesNet μ).joint_eq_prod x,
    ((M.inducedBayesNet μ).intervene k a).joint_eq_prod x]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjk : j = k
  · subst hjk
    rw [(M.doNode j a).inducedBayesNet_cpt_apply μ x j, M.doNode_f_of_eq j a,
      StdSimplex.map_const, (M.inducedBayesNet μ).intervene_cpt_of_eq j a]
  · rw [(M.doNode k a).inducedBayesNet_cpt_apply μ x j, M.doNode_f_of_ne k a hjk,
      M.inducedBayesNet_intervene_cpt_of_ne μ k a hjk]

/-- Surgery on a set of nodes commutes with the do-operator for that set. -/
theorem inducedLaw_doSet {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] [Nonempty α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (W : Finset (Fin n)) (w x : Fin n → α) :
    (M.doSet W w).inducedLaw μ x = ((M.inducedBayesNet μ).mutilateSet W w).joint x := by
  rw [(M.doSet W w).inducedLaw_eq_joint μ x,
    ((M.doSet W w).inducedBayesNet μ).joint_eq_prod x,
    ((M.inducedBayesNet μ).mutilateSet W w).joint_eq_prod x]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjW : j ∈ W
  · rw [(M.doSet W w).inducedBayesNet_cpt_apply μ x j, M.doSet_f_of_mem W w hjW,
      StdSimplex.map_const, (M.inducedBayesNet μ).mutilateSet_cpt_of_mem W w hjW]
  · rw [(M.doSet W w).inducedBayesNet_cpt_apply μ x j, M.doSet_f_of_not_mem W w hjW,
      M.inducedBayesNet_mutilateSet_cpt_of_not_mem μ W w hjW]

end FiniteSCM

/-! ### Counterfactuals -/

namespace FiniteSCM

open Finset Convexity

/-- The **counterfactual** `X_{k ← a}(u)`: the values of all nodes in the unit with noise value
`u` had node `k` been set to `a`. The same noise value `u` is used in the model after surgery
(a fresh noise draw would be an interventional, not a counterfactual, quantity). -/
def counterfactual {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (k : Fin n)
    (a : α) (u : (j : Fin n) → U j) : Fin n → α :=
  (M.doNode k a).solve u

/-- The probability, under independent noises with laws `μ`, of factual evidence `E` about the
solution of the model. -/
noncomputable def evidenceProb {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] : ℝ :=
  ∑ u with E (M.solve u), noiseWeight μ u

/-- The conditional counterfactual probability `P(X_{k ← a} ∈ F | E)`: the probability that the
factual solution satisfies the evidence `E` and the counterfactual solution, at the same noise
value, satisfies `F`, divided by the probability of `E`. This is a genuine conditional
probability only when `M.evidenceProb μ E ≠ 0`; when the evidence has probability zero,
Lean's totalized real division makes the result `0` by convention, not a conditional
probability. -/
noncomputable def counterfactualProb {α : Type*} {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : (Fin n → α) → Prop) [DecidablePred E] (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] : ℝ :=
  (∑ u with E (M.solve u) ∧ F (M.counterfactual k a u), noiseWeight μ u) / M.evidenceProb μ E

/-- **Abduction**: the posterior weight of the noise value `u` given the factual evidence `E`.
These are genuine posterior weights only when `M.evidenceProb μ E ≠ 0`; when the evidence
has probability zero, Lean's totalized real division makes every weight `0` by convention,
so they do not form a posterior distribution in that case. -/
noncomputable def posteriorWeight {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] (u : (k : Fin n) → U k) : ℝ :=
  if E (M.solve u) then noiseWeight μ u / M.evidenceProb μ E else 0

/-- The noise weights sum to `1`: the product noise law is a probability distribution. -/
theorem sum_noiseWeight_eq_one {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) :
    ∑ u, noiseWeight μ u = 1 := by
  have h : ∏ k, ∑ v, (μ k).weights v
      = ∑ u : (k : Fin n) → U k, ∏ k, (μ k).weights (u k) :=
    Fintype.prod_sum _
  unfold noiseWeight
  rw [← h]
  simp only [StdSimplex.total_of_fintype, Finset.prod_const_one]

/-- Splitting a filtered noise sum by the value of the counterfactual solution. -/
private theorem sum_filter_counterfactual_fiber {α : Type*} {n : ℕ} {U : Fin n → Type*} [Fintype α]
    [∀ k, Fintype (U k)] [DecidableEq α] (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (k : Fin n) (a : α)
    (F : (Fin n → α) → Prop) [DecidablePred F] :
    ∑ u with F (M.counterfactual k a u), noiseWeight μ u =
      ∑ x with F x, ∑ u with M.counterfactual k a u = x, noiseWeight μ u := by
  have hmaps : ∀ u ∈ Finset.univ.filter (fun u => F (M.counterfactual k a u)),
      M.counterfactual k a u ∈ Finset.univ.filter F := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨Finset.mem_univ _, hu.2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun u => F (M.counterfactual k a u)))
    (t := Finset.univ.filter F) (g := fun u => M.counterfactual k a u) hmaps
    (f := fun u => noiseWeight μ u)
  rw [← hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hFx : F x := (Finset.mem_filter.1 hx).2
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun u _ => rfl
  exact Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨by rwa [h], h⟩⟩

/-- The posterior weights given evidence of positive probability form a probability
distribution on the noise values. -/
theorem sum_posteriorWeight {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] (hE : M.evidenceProb μ E ≠ 0) :
    (∀ u, 0 ≤ M.posteriorWeight μ E u) ∧ ∑ u, M.posteriorWeight μ E u = 1 := by
  have hnoise : ∀ u, 0 ≤ noiseWeight μ u := by
    intro u
    unfold noiseWeight
    exact Finset.prod_nonneg fun k _ => (μ k).nonneg _
  have hEpos : 0 < M.evidenceProb μ E := by
    unfold evidenceProb
    exact lt_of_le_of_ne (Finset.sum_nonneg fun u _ => hnoise u) (Ne.symm hE)
  constructor
  · intro u
    unfold posteriorWeight
    split_ifs with h
    · exact div_nonneg (hnoise u) hEpos.le
    · exact le_rfl
  · simp only [posteriorWeight, ← Finset.sum_filter, ← Finset.sum_div]
    exact div_self hE

/-- **Abduction, action, prediction**: for evidence of positive probability, the conditional
counterfactual probability is obtained by weighting the noise values by their posterior given
the evidence (abduction), solving the model after surgery `do(X_k = a)` at each noise value
(action), and adding the posterior weights of the noise values whose counterfactual solution lies
in `F` (prediction). (For evidence of probability zero both sides are `0`.) -/
theorem counterfactualProb_eq_sum_posteriorWeight {α : Type*} {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : (Fin n → α) → Prop) [DecidablePred E] (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] :
    M.counterfactualProb μ E k a F =
      ∑ u with F (M.counterfactual k a u), M.posteriorWeight μ E u := by
  simp only [counterfactualProb, posteriorWeight, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hE' : E (M.solve u) <;> by_cases hF : F (M.counterfactual k a u) <;> simp [hE', hF]

/-- Without evidence, the counterfactual probability is the interventional probability: the
mass of `F` under the joint of the induced Bayesian network after `do(X_k = a)`. The
`Nonempty α` instance that `BayesNet.joint` requires is supplied from `a` itself, so
callers need not provide a separate instance. -/
theorem counterfactualProb_true {α : Type*} [Fintype α] {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] :
    M.counterfactualProb μ (fun _ => True) k a F =
      ∑ x with F x, (@BayesNet.joint α _ ⟨a⟩
        ((M.inducedBayesNet μ).intervene k a) x) := by
  classical
  have _nonempty : Nonempty α := ⟨a⟩
  have hsum1 : ∑ u, noiseWeight μ u = 1 := sum_noiseWeight_eq_one μ
  have hE1 : M.evidenceProb μ (fun _ => True) = 1 := by
    simp only [evidenceProb, Finset.filter_true]
    exact hsum1
  unfold counterfactualProb
  rw [hE1, div_one]
  simp only [true_and]
  rw [sum_filter_counterfactual_fiber M μ k a F]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← M.inducedLaw_doNode μ k a x]
  rfl

end FiniteSCM

end Cslib.MachineLearning.GraphicalModels
