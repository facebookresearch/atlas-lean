/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
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

end Cslib.MachineLearning.GraphicalModels
