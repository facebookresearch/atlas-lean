/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import MathlibExt.Probability.Causality.CausalIdentification
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
* `FiniteSCM.counterfactual_self`, `FiniteSCM.counterfactual_eq_solve`,
  `FiniteSCM.solve_doNode_doNode_of_counterfactual`: **effectiveness, consistency and
  composition** (Pearl 2009, Theorem 7.3.3), derived from unique solvability: setting a node
  makes it take the set value; setting a node to its factual value changes nothing; and,
  for compatible nested interventions, adding the intervention on a value the counterfactual
  already takes changes nothing.

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
  | m + 1, h =>
    let prev := M.solvePrefix u m (Nat.le_of_succ_le h)
    Fin.snoc prev (M.f ⟨m, h⟩ (fun j => prev j) (u ⟨m, h⟩))

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

open Classical in
/-- The observational law induced by the model under independent noises with laws `μ k`: the
probability that the solution is `x`, that is, the push-forward of the product noise law under
the solution map. The sum runs over the product of the supports of the noise laws, so the
noise types need not be finite: a finitely supported law on an infinite type, such as
`U k = ℕ`, is covered. Equality is decided classically, so no `DecidableEq α` is required. -/
noncomputable def inducedLaw {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) : ℝ :=
  ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
    if M.solve u = x then noiseWeight μ u else 0

/-- The Bayesian network of the model under independent noises with laws `μ k`: it has the
model's parents, and the table of node `k` at parent values `z` is the law of
`f_k (z, u_k)` for `u_k ∼ μ_k`, the push-forward of `μ_k` under `f_k (z, ·)`. -/
noncomputable def inducedBayesNet {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) : BayesNet α n where
  pa := M.pa
  cpt k z := (μ k).map (M.f k z)

theorem map_weights_eq {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [DecidableEq α] (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t : Fin n) (w : M.pa t → α) (a₁ : α) :
    ((μ t).map (M.f t w)).weights a₁
      = ∑ v, (if M.f t w v = a₁ then (μ t).weights v else 0) := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

open Classical in
/-- The push-forward weights of a noise law under a structural function are the sums of the
noise weights over the fibers. The sum runs over the support of the noise law, so no
finiteness of the noise type is needed. -/
private theorem map_weights_eq_sum {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) (k : Fin n) :
    ((μ k).map (M.f k (M.paVal k x))).weights (x k)
      = ∑ v ∈ (μ k).weights.support,
        (if M.f k (M.paVal k x) v = x k then (μ k).weights v else 0) := by
  classical
  rw [StdSimplex.weights_map]
  simp only [Finsupp.mapDomain_apply, Finsupp.sum, Finsupp.single_apply]

/-- **A Markovian SCM induces its Bayesian network**: under independent noises, the law of the
unique solution is the joint distribution of the Bayesian network whose tables are the
push-forwards of the noise laws under the structural functions. -/
theorem inducedLaw_eq_joint {α : Type*} {n : ℕ} {U : Fin n → Type*} [Nonempty α]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (x : Fin n → α) : M.inducedLaw μ x = (M.inducedBayesNet μ).joint x := by
  classical
  rw [(M.inducedBayesNet μ).joint_eq_prod x]
  have hfactor : ∀ k : Fin n,
      ((M.inducedBayesNet μ).cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)
        = ∑ v ∈ (μ k).weights.support,
          (if M.f k (M.paVal k x) v = x k then (μ k).weights v else 0) :=
    fun k => map_weights_eq_sum M μ x k
  simp only [hfactor]
  rw [Finset.prod_univ_sum]
  unfold inducedLaw
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
  have hfb : ((b.responseLaw k).map (b.responseSCM.f k (b.responseSCM.paVal k x))).weights (x k)
      = ∑ v, (if b.responseSCM.f k (b.responseSCM.paVal k x) v = x k then
          (b.responseLaw k).weights v else 0) := by
    rw [FiniteSCM.map_weights_eq_sum b.responseSCM b.responseLaw x k]
    refine (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_).trans
      (Finset.sum_congr rfl fun v _ => by split_ifs <;> rfl)
    simp [Finsupp.notMem_support_iff.mp hv]
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
theorem inducedLaw_doNode {α : Type*} {n : ℕ} {U : Fin n → Type*} [Nonempty α]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
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
theorem inducedLaw_doSet {α : Type*} {n : ℕ} {U : Fin n → Type*} [Nonempty α]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
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
solution of the model. As in `inducedLaw`, the sum runs over the product of the supports of the
noise laws, so the noise types need not be finite. -/
noncomputable def evidenceProb {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] : ℝ :=
  ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with E (M.solve u), noiseWeight μ u

/-- The conditional counterfactual probability `P(X_{k ← a} ∈ F | E)`: the probability that the
factual solution satisfies the evidence `E` and the counterfactual solution, at the same noise
value, satisfies `F`, divided by the probability of `E`. The sum runs over the product of the
supports of the noise laws, so the noise types need not be finite. This is a genuine conditional
probability only when `M.evidenceProb μ E ≠ 0`; when the evidence has probability zero,
Lean's totalized real division makes the result `0` by convention, not a conditional
probability. -/
noncomputable def counterfactualProb {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : (Fin n → α) → Prop) [DecidablePred E] (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] : ℝ :=
  (∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with
      E (M.solve u) ∧ F (M.counterfactual k a u), noiseWeight μ u) / M.evidenceProb μ E

/-- **Abduction**: the posterior weight of the noise value `u` given the factual evidence `E`.
These are genuine posterior weights only when `M.evidenceProb μ E ≠ 0`; when the evidence
has probability zero, Lean's totalized real division makes every weight `0` by convention,
so they do not form a posterior distribution in that case. -/
noncomputable def posteriorWeight {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] (u : (k : Fin n) → U k) : ℝ :=
  if E (M.solve u) then noiseWeight μ u / M.evidenceProb μ E else 0

/-- The noise weights sum to `1` over the product of the supports of the noise laws: the
product noise law is a probability distribution. No finiteness of the noise types is needed. -/
theorem sum_noiseWeight_eq_one {n : ℕ} {U : Fin n → Type*}
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) :
    ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support), noiseWeight μ u = 1 := by
  unfold noiseWeight
  rw [← Finset.prod_univ_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  have h := (μ k).total
  rwa [Finsupp.sum] at h

/-- Splitting a filtered noise sum by the value of the counterfactual solution. -/
private theorem sum_filter_counterfactual_fiber {α : Type*} {n : ℕ} {U : Fin n → Type*} [Fintype α]
    [DecidableEq α] (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (k : Fin n) (a : α)
    (F : (Fin n → α) → Prop) [DecidablePred F] :
    ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with F (M.counterfactual k a u),
        noiseWeight μ u =
      ∑ x with F x, ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with
        M.counterfactual k a u = x, noiseWeight μ u := by
  have hmaps : ∀ u ∈ (Fintype.piFinset (fun j => (μ j).weights.support)).filter
      (fun u => F (M.counterfactual k a u)), M.counterfactual k a u ∈ Finset.univ.filter F := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨Finset.mem_univ _, hu.2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Fintype.piFinset (fun j => (μ j).weights.support)).filter
      (fun u => F (M.counterfactual k a u)))
    (t := Finset.univ.filter F) (g := fun u => M.counterfactual k a u) hmaps
    (f := fun u => noiseWeight μ u)
  rw [← hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hFx : F x := (Finset.mem_filter.1 hx).2
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun u _ => rfl
  exact Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨by rwa [h], h⟩⟩

/-- The posterior weights given evidence of positive probability form a probability
distribution on the noise values in the product of the supports of the noise laws. -/
theorem sum_posteriorWeight {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (E : (Fin n → α) → Prop)
    [DecidablePred E] (hE : M.evidenceProb μ E ≠ 0) :
    (∀ u, 0 ≤ M.posteriorWeight μ E u) ∧
      ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support), M.posteriorWeight μ E u = 1 := by
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
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : (Fin n → α) → Prop) [DecidablePred E] (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] :
    M.counterfactualProb μ E k a F =
      ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with F (M.counterfactual k a u),
        M.posteriorWeight μ E u := by
  simp only [counterfactualProb, posteriorWeight, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hE' : E (M.solve u) <;> by_cases hF : F (M.counterfactual k a u) <;> simp [hE', hF]

/-- Without evidence, the counterfactual probability is the interventional probability: the
mass of `F` under the joint of the induced Bayesian network after `do(X_k = a)`. The
`Nonempty α` instance that `BayesNet.joint` requires is supplied from `a` itself, so
callers need not provide a separate instance. -/
theorem counterfactualProb_true {α : Type*} [Fintype α] {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (k : Fin n) (a : α) (F : (Fin n → α) → Prop)
    [DecidablePred F] :
    M.counterfactualProb μ (fun _ => True) k a F =
      ∑ x with F x, (@BayesNet.joint α _ ⟨a⟩
        ((M.inducedBayesNet μ).intervene k a) x) := by
  classical
  have _nonempty : Nonempty α := ⟨a⟩
  have hE1 : M.evidenceProb μ (fun _ => True) = 1 := by
    simp only [evidenceProb, Finset.filter_true]
    exact sum_noiseWeight_eq_one μ
  unfold counterfactualProb
  rw [hE1, div_one]
  simp only [true_and]
  rw [sum_filter_counterfactual_fiber M μ k a F]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← M.inducedLaw_doNode μ k a x]
  unfold inducedLaw
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : (M.doNode k a).solve u = x <;> simp [h, counterfactual]

end FiniteSCM

/-! ### Effectiveness, consistency and composition -/

namespace FiniteSCM

/-- **Effectiveness**: setting node `k` to `a` makes its counterfactual value `a`, whatever the
noise. -/
theorem counterfactual_self {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (k : Fin n) (a : α) (u : (j : Fin n) → U j) : M.counterfactual k a u k = a := by
  unfold counterfactual
  have h := (M.doNode k a).solve_isSolution u k
  rw [M.doNode_f_of_eq] at h
  exact h

/-- **Consistency**: if node `k` already takes the value `a` in the unit with noise `u`, then
setting it to `a` changes nothing: the counterfactual solution is the factual one. -/
theorem counterfactual_eq_solve {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    {k : Fin n} {a : α} {u : (j : Fin n) → U j} (h : M.solve u k = a) :
    M.counterfactual k a u = M.solve u := by
  unfold counterfactual
  symm
  apply IsSolution.eq_solve
  intro j
  by_cases hjk : j = k
  · subst hjk
    rw [M.doNode_f_of_eq]
    exact h
  · rw [M.doNode_f_of_ne k a hjk]
    have hsol := M.solve_isSolution u j
    rw [hsol]
    congr 1

/-- **Composition** for compatible nested interventions: if, after setting node `k` to `a`,
node `j` takes the value `b` in the unit with noise `u`, then additionally setting node `j` to
`b` changes nothing. -/
theorem solve_doNode_doNode_of_counterfactual {α : Type*} {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) {k j : Fin n} {a b : α} {u : (i : Fin n) → U i}
    (h : M.counterfactual k a u j = b) :
    ((M.doNode k a).doNode j b).solve u = M.counterfactual k a u := by
  have h' : (M.doNode k a).solve u j = b := h
  have hc := counterfactual_eq_solve (M := M.doNode k a) (k := j) (a := b) (u := u) h'
  exact hc


/-! ### Potential outcomes from an SCM: consistency and Markovian ignorability -/

open MeasureTheory Convexity MathlibExt.Probability.Causality


/-- The law of the noise under independent noise laws `μ`, as a measure on the finite noise
space: the point mass at each noise value `u` weighted by `∏ k, μ_k (u_k)`. -/
noncomputable def noiseMeasure {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] (μ : (k : Fin n) → StdSimplex ℝ (U k)) :
    Measure ((k : Fin n) → U k) :=
  ∑ u, ENNReal.ofReal (noiseWeight μ u) • Measure.dirac u

/-- The treated event: the noise values at which node `t` takes the treatment value `a₁`. -/
def treated {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (t : Fin n) (a₁ : α) :
    Set ((k : Fin n) → U k) :=
  {u | M.solve u t = a₁}

/-- The potential outcome `Y_a = g (X_y)` after `do(X_t = a)`, a real readout `g` of the value
of node `y` in the counterfactual solution at the same noise value. -/
def potentialOutcome {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U) (t : Fin n)
    (a : α) (y : Fin n) (g : α → ℝ) (u : (k : Fin n) → U k) : ℝ :=
  g (M.counterfactual t a u y)

theorem noiseWeight_nonneg {n : ℕ} {U : Fin n → Type*} (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (u : (k : Fin n) → U k) : 0 ≤ noiseWeight μ u := by
  unfold noiseWeight
  exact Finset.prod_nonneg fun k _ => (μ k).nonneg _

theorem noise_measSet {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (s : Set ((k : Fin n) → U k)) : MeasurableSet s :=
  (Set.toFinite s).measurableSet

theorem noiseMeasure_apply_eq {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (s : Set ((k : Fin n) → U k))
    [DecidablePred fun u => u ∈ s] :
    noiseMeasure μ s
      = ∑ u ∈ Finset.univ.filter (fun u => u ∈ s), ENNReal.ofReal (noiseWeight μ u) := by
  have hterm : ∀ u : (k : Fin n) → U k,
      (ENNReal.ofReal (noiseWeight μ u) • Measure.dirac u) s
        = (if u ∈ s then ENNReal.ofReal (noiseWeight μ u) else 0) := by
    intro u
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases h : u ∈ s
    · rw [ite_eq_left h]
      have h1 : Measure.dirac u s = 1 := by
        exact Measure.dirac_apply_of_mem h
      rw [h1, mul_one]
    · rw [ite_eq_right h]
      have h0 : Measure.dirac u s = 0 := by
        first
          | exact Measure.dirac_apply_of_notMem h
          | rw [Measure.dirac_apply _ (noise_measSet s)]
            exact Set.indicator_of_notMem h 1
          | rw [Measure.dirac_apply' _ (noise_measSet s)]
            exact Set.indicator_of_notMem h 1
      rw [h0, mul_zero]
  have hsum : noiseMeasure μ s
      = ∑ u ∈ Finset.univ, (ENNReal.ofReal (noiseWeight μ u) • Measure.dirac u) s := by
    unfold noiseMeasure
    rw [MeasureTheory.Measure.finsetSum_apply]
  rw [hsum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun u _ => hterm u

theorem noiseMeasure_real_eq {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (s : Set ((k : Fin n) → U k))
    [DecidablePred fun u => u ∈ s] :
    (noiseMeasure μ).real s
      = ∑ u ∈ Finset.univ.filter (fun u => u ∈ s), noiseWeight μ u := by
  rw [measureReal_def, noiseMeasure_apply_eq,
    ENNReal.toReal_sum (fun u _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun u _ => ENNReal.toReal_ofReal (noiseWeight_nonneg μ u)

theorem noiseMeasure_real_univ_eq {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) : (noiseMeasure μ).real Set.univ = 1 := by
  classical
  rw [noiseMeasure_real_eq]; simpa using sum_noiseWeight_eq_one μ

theorem noiseMeasure_lt_top {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (s : Set ((k : Fin n) → U k)) :
    noiseMeasure μ s < ⊤ := by
  classical
  rw [noiseMeasure_apply_eq, ← ENNReal.ofReal_sum_of_nonneg (fun u _ => noiseWeight_nonneg μ u)]
  exact ENNReal.ofReal_lt_top

theorem noiseMeasure_real_ne_zero {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (s : Set ((k : Fin n) → U k))
    (h : noiseMeasure μ s ≠ 0) : (noiseMeasure μ).real s ≠ 0 := by
  rw [measureReal_def]
  have htop : noiseMeasure μ s ≠ ⊤ := ne_of_lt (noiseMeasure_lt_top μ s)
  rw [ENNReal.toReal_ne_zero]; exact ⟨h, htop⟩

noncomputable def restWeight {n : ℕ} {U : Fin n → Type*} (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t : Fin n) (u : (k : Fin n) → U k) : ℝ :=
  ∏ k ∈ Finset.univ.erase t, (μ k).weights (u k)

theorem noiseWeight_split {n : ℕ} {U : Fin n → Type*} (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t : Fin n) (u : (k : Fin n) → U k) :
    noiseWeight μ u = (μ t).weights (u t) * restWeight μ t u := by
  unfold noiseWeight restWeight
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ t)).symm.trans (mul_comm _ _)

theorem paVal_update_congr {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (t : Fin n) (u : (k : Fin n) → U k) (v : U t) :
    M.paVal t (M.solve (Function.update u t v)) = M.paVal t (M.solve u) := by
  have hS : ∀ k ∈ {k : Fin n | k.val < t.val}, ∀ j ∈ M.pa k,
      Fin.castLE k.2.le j ∈ {k : Fin n | k.val < t.val} := by
    intro k hk j hj
    show (Fin.castLE k.2.le j).val < t.val
    rw [Fin.val_castLE]
    exact lt_trans j.2 hk
  have hu : ∀ k ∈ {k : Fin n | k.val < t.val}, Function.update u t v k = u k := by
    intro k hk
    have hkt : k ≠ t := by
      rintro rfl
      simp at hk
    exact Function.update_of_ne hkt v u
  have hcongr := M.solve_congr_of_ancestral hS hu
  funext j
  show M.solve (Function.update u t v) (Fin.castLE t.2.le ↑j)
    = M.solve u (Fin.castLE t.2.le ↑j)
  exact hcongr _ (by
    show (Fin.castLE t.2.le (↑j : Fin t.val)).val < t.val
    rw [Fin.val_castLE]
    exact j.1.2)

theorem doNode_solve_update {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (t : Fin n) (a : α) (u : (k : Fin n) → U k) (v : U t) :
    (M.doNode t a).solve (Function.update u t v) = (M.doNode t a).solve u := by
  symm
  apply IsSolution.eq_solve
  intro j
  by_cases hjk : j = t
  · rw [hjk]
    have ht := (M.doNode t a).solve_isSolution u t
    rw [M.doNode_f_of_eq] at ht
    rw [ht, M.doNode_f_of_eq]
  · have hsol := (M.doNode t a).solve_isSolution u j
    rw [hsol, Function.update_of_ne hjk v u]

theorem treated_inter_fiber {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (t : Fin n) (a₁ : α) (w : M.pa t → α) :
    M.treated t a₁ ∩ (fun u => M.paVal t (M.solve u)) ⁻¹' {w}
      = {u | M.f t w (u t) = a₁} ∩ (fun u => M.paVal t (M.solve u)) ⁻¹' {w} := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨ht, hw⟩ := h
    have ht' : M.solve u t = a₁ := ht
    have hsol := M.solve_isSolution u t
    refine ⟨?_, hw⟩
    show M.f t w (u t) = a₁
    rw [← ht', hsol, hw]
  · intro h
    obtain ⟨hf, hw⟩ := h
    have hf' : M.f t w (u t) = a₁ := hf
    have hsol := M.solve_isSolution u t
    refine ⟨?_, hw⟩
    show M.solve u t = a₁
    rw [hsol, hw]
    exact hf'

theorem fiber_sum_update_congr {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t : Fin n)
    {E : Set ((k : Fin n) → U k)}
    (hE : ∀ u v, Function.update u t v ∈ E ↔ u ∈ E)
    (v v₀ : U t)
    [DecidablePred fun u : (k : Fin n) → U k => u ∈ E]
    [DecidablePred fun u : (k : Fin n) → U k => u t = v]
    [DecidablePred fun u : (k : Fin n) → U k => u t = v₀] :
    ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
        (fun u : (k : Fin n) → U k => u t = v), restWeight μ t u
      = ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
        (fun u : (k : Fin n) → U k => u t = v₀), restWeight μ t u := by
  refine Finset.sum_bij (fun u _ => Function.update u t v₀) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨huE, huv⟩ := hu
    refine ⟨?_, Function.update_self t v₀ u⟩
    exact (hE u v₀).mpr huE
  · intro u₁ hu₁ u₂ hu₂ heq
    have heq' : Function.update u₁ t v₀ = Function.update u₂ t v₀ := heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
    obtain ⟨-, huv₁⟩ := hu₁
    obtain ⟨-, huv₂⟩ := hu₂
    have e1 : u₁ = Function.update (Function.update u₁ t v₀) t v := by
      rw [Function.update_idem, ← huv₁, Function.update_eq_self]
    have e2 : u₂ = Function.update (Function.update u₂ t v₀) t v := by
      rw [Function.update_idem, ← huv₂, Function.update_eq_self]
    rw [e1, e2, heq']
  · intro u' hu'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    obtain ⟨hu'E, hu'v₀⟩ := hu'
    refine ⟨Function.update u' t v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(hE u' v).mpr hu'E, Function.update_self t v u'⟩
    · show Function.update (Function.update u' t v) t v₀ = u'
      rw [Function.update_idem, ← hu'v₀, Function.update_eq_self]
  · intro u hu
    show restWeight μ t u
      = restWeight μ t ((fun u _ => Function.update u t v₀) u hu)
    unfold restWeight
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkne : k ≠ t := Finset.ne_of_mem_erase hk
    show (μ k).weights (u k) = (μ k).weights (Function.update u t v₀ k)
    rw [Function.update_of_ne hkne v₀ u]

theorem real_coord_inter {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t : Fin n) (P : U t → Prop) [DecidablePred P]
    {E : Set ((k : Fin n) → U k)}
    (hE : ∀ u v, Function.update u t v ∈ E ↔ u ∈ E) :
    (noiseMeasure μ).real ({u | P (u t)} ∩ E)
      = (∑ v ∈ Finset.univ.filter P, (μ t).weights v) * (noiseMeasure μ).real E := by
  classical
  by_cases hne : Nonempty (U t)
  · obtain ⟨v₀⟩ := hne
    have hfibw : ∀ (G : Finset ((k : Fin n) → U k)) (f : ((k : Fin n) → U k) → ℝ),
        ∑ u ∈ G, f u
          = ∑ v ∈ Finset.univ, ∑ u ∈ G.filter
            (fun u : (k : Fin n) → U k => u t = v), f u :=
      fun G f => (Finset.sum_fiberwise_of_maps_to (fun u _ => Finset.mem_univ _) f).symm
    have hEeq : (noiseMeasure μ).real E
        = ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
          (fun u : (k : Fin n) → U k => u t = v₀), restWeight μ t u := by
      rw [noiseMeasure_real_eq]
      have hsplit : ∀ u ∈ Finset.univ.filter (fun u => u ∈ E),
          noiseWeight μ u = (μ t).weights (u t) * restWeight μ t u :=
        fun u _ => noiseWeight_split μ t u
      rw [Finset.sum_congr rfl hsplit, hfibw]
      have hinner : ∀ v ∈ Finset.univ,
          ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
              (fun u : (k : Fin n) → U k => u t = v),
            (μ t).weights (u t) * restWeight μ t u
            = (μ t).weights v * ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
              (fun u : (k : Fin n) → U k => u t = v₀), restWeight μ t u := by
        intro v _
        have h1 : ∀ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
            (fun u : (k : Fin n) → U k => u t = v),
            (μ t).weights (u t) * restWeight μ t u
              = (μ t).weights v * restWeight μ t u := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          obtain ⟨-, huv⟩ := hu
          rw [huv]
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
        congr 1
        exact fiber_sum_update_congr μ t hE v v₀
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
      simp
    have hAE : (noiseMeasure μ).real ({u | P (u t)} ∩ E)
        = (∑ v ∈ Finset.univ.filter P, (μ t).weights v)
          * ∑ u ∈ (Finset.univ.filter (fun u => u ∈ E)).filter
            (fun u : (k : Fin n) → U k => u t = v₀), restWeight μ t u := by
      rw [noiseMeasure_real_eq]
      have hsplit : ∀ u ∈ Finset.univ.filter (fun u => u ∈ {u | P (u t)} ∩ E),
          noiseWeight μ u = (μ t).weights (u t) * restWeight μ t u :=
        fun u _ => noiseWeight_split μ t u
      rw [Finset.sum_congr rfl hsplit, hfibw]
      have hinner : ∀ v ∈ Finset.univ,
          ∑ u ∈ (Finset.univ.filter (fun u => u ∈ {u | P (u t)} ∩ E)).filter
              (fun u : (k : Fin n) → U k => u t = v),
            (μ t).weights (u t) * restWeight μ t u
            = (if P v then (μ t).weights v * ∑ u ∈ (Finset.univ.filter
              (fun u => u ∈ E)).filter
              (fun u : (k : Fin n) → U k => u t = v₀), restWeight μ t u else 0) := by
        intro v _
        by_cases hPv : P v
        · rw [ite_eq_left hPv]
          have h1 : ∀ u ∈ (Finset.univ.filter (fun u => u ∈ {u | P (u t)} ∩ E)).filter
              (fun u : (k : Fin n) → U k => u t = v),
              (μ t).weights (u t) * restWeight μ t u
                = (μ t).weights v * restWeight μ t u := by
            intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_inter_iff] at hu
            obtain ⟨⟨-, -⟩, huv⟩ := hu
            rw [huv]
          rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
          congr 1
          refine Finset.sum_bij (fun u _ => Function.update u t v₀) ?_ ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_inter_iff] at hu ⊢
            obtain ⟨⟨-, huE⟩, huv⟩ := hu
            refine ⟨?_, Function.update_self t v₀ u⟩
            exact (hE u v₀).mpr huE
          · intro u₁ hu₁ u₂ hu₂ heq
            have heq' : Function.update u₁ t v₀ = Function.update u₂ t v₀ := heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_inter_iff] at hu₁ hu₂
            obtain ⟨⟨-, -⟩, huv₁⟩ := hu₁
            obtain ⟨⟨-, -⟩, huv₂⟩ := hu₂
            have e1 : u₁ = Function.update (Function.update u₁ t v₀) t v := by
              rw [Function.update_idem, ← huv₁, Function.update_eq_self]
            have e2 : u₂ = Function.update (Function.update u₂ t v₀) t v := by
              rw [Function.update_idem, ← huv₂, Function.update_eq_self]
            rw [e1, e2, heq']
          · intro u' hu'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
            obtain ⟨hu'E, hu'v₀⟩ := hu'
            refine ⟨Function.update u' t v, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Set.mem_inter_iff]
              have hPA : Function.update u' t v ∈ {u | P (u t)} := by
                show P (Function.update u' t v t)
                rw [Function.update_self]
                exact hPv
              refine ⟨⟨hPA, (hE u' v).mpr hu'E⟩, Function.update_self t v u'⟩
            · show Function.update (Function.update u' t v) t v₀ = u'
              rw [Function.update_idem, ← hu'v₀, Function.update_eq_self]
          · intro u hu
            show restWeight μ t u
              = restWeight μ t ((fun u _ => Function.update u t v₀) u hu)
            unfold restWeight
            refine Finset.prod_congr rfl fun k hk => ?_
            have hkne : k ≠ t := Finset.ne_of_mem_erase hk
            show (μ k).weights (u k) = (μ k).weights (Function.update u t v₀ k)
            rw [Function.update_of_ne hkne v₀ u]
        · rw [ite_eq_right hPv]
          have hempty : (Finset.univ.filter (fun u => u ∈ {u | P (u t)} ∩ E)).filter
              (fun u : (k : Fin n) → U k => u t = v) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_inter_iff] at hu
            obtain ⟨⟨huA, -⟩, huv⟩ := hu
            have hPu : P (u t) := huA
            rw [huv] at hPu
            exact hPv hPu
          rw [hempty, Finset.sum_empty]
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, ← Finset.sum_mul]
    rw [hAE, hEeq]
  · have hNoiseEmpty : IsEmpty ((k : Fin n) → U k) := ⟨fun u => hne ⟨u t⟩⟩
    have hUtEmpty : IsEmpty (U t) := ⟨fun v => hne ⟨v⟩⟩
    have huniv : (Finset.univ : Finset ((k : Fin n) → U k)) = ∅ :=
      Finset.univ_eq_empty_iff.mpr hNoiseEmpty
    have hunivUt : (Finset.univ : Finset (U t)) = ∅ :=
      Finset.univ_eq_empty_iff.mpr hUtEmpty
    rw [noiseMeasure_real_eq, huniv]
    simp only [Finset.filter_empty, Finset.sum_empty]
    have hWP : (∑ v ∈ Finset.univ.filter P, (μ t).weights v) = 0 := by
      rw [hunivUt]
      simp only [Finset.filter_empty, Finset.sum_empty]
    rw [hWP, zero_mul]

theorem real_coord_eq {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t : Fin n) (P : U t → Prop) [DecidablePred P] :
    (noiseMeasure μ).real {u | P (u t)}
      = ∑ v ∈ Finset.univ.filter P, (μ t).weights v := by
  classical
  have h := real_coord_inter μ t P (E := Set.univ) (fun u v => Iff.rfl)
  rw [Set.inter_univ, noiseMeasure_real_univ_eq, mul_one] at h
  exact h

theorem factor_real_inter {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t : Fin n) (P : U t → Prop) [DecidablePred P]
    {E : Set ((k : Fin n) → U k)}
    (hE : ∀ u v, Function.update u t v ∈ E ↔ u ∈ E) :
    (noiseMeasure μ).real ({u | P (u t)} ∩ E)
      = (noiseMeasure μ).real {u | P (u t)} * (noiseMeasure μ).real E := by
  classical
  rw [real_coord_inter μ t P hE, real_coord_eq μ t P]

theorem indep_paValFib {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (t : Fin n) (w : M.pa t → α) :
    ∀ u v, Function.update u t v ∈ (fun u => M.paVal t (M.solve u)) ⁻¹' {w}
      ↔ u ∈ (fun u => M.paVal t (M.solve u)) ⁻¹' {w} := by
  intro u v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, paVal_update_congr M t u v]

theorem indep_potOutFib {α : Type*} {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM α n U)
    (t y : Fin n) (a₀ a₁ : α) (g : α → ℝ) (B : Set (ℝ × ℝ)) :
    ∀ u v, Function.update u t v
        ∈ (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B
      ↔ u ∈ (fun u => (M.potentialOutcome t a₀ y g u,
        M.potentialOutcome t a₁ y g u)) ⁻¹' B := by
  intro u v
  have hY0 : M.potentialOutcome t a₀ y g (Function.update u t v)
      = M.potentialOutcome t a₀ y g u := by
    unfold potentialOutcome counterfactual
    rw [doNode_solve_update M t a₀ u v]
  have hY1 : M.potentialOutcome t a₁ y g (Function.update u t v)
      = M.potentialOutcome t a₁ y g u := by
    unfold potentialOutcome counterfactual
    rw [doNode_solve_update M t a₁ u v]
  simp only [Set.mem_preimage, hY0, hY1]

/-- **Consistency of the potential outcomes**: if the treatment node takes only the values `a₀`
and `a₁` on noise values of positive probability, the factual outcome is almost surely the
observed potential outcome. -/
theorem ae_eq_observed {α : Type*} {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)]
    [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)] (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t y : Fin n) (a₀ a₁ : α) (g : α → ℝ)
    (hbin : ∀ u, noiseWeight μ u ≠ 0 → M.solve u t = a₀ ∨ M.solve u t = a₁) :
    (fun u => g (M.solve u y)) =ᵐ[noiseMeasure μ]
      observed (M.treated t a₁) (M.potentialOutcome t a₀ y g) (M.potentialOutcome t a₁ y g) := by
  classical
  show ∀ᵐ u ∂(noiseMeasure μ),
    (fun u => g (M.solve u y)) u
      = observed (M.treated t a₁) (M.potentialOutcome t a₀ y g)
        (M.potentialOutcome t a₁ y g) u
  rw [ae_iff]
  have hZ : noiseMeasure μ {u | noiseWeight μ u = 0} = 0 := by
    rw [noiseMeasure_apply_eq]
    refine Finset.sum_eq_zero fun u hu => ?_
    have huw : noiseWeight μ u = 0 := (Finset.mem_filter.mp hu).2
    rw [huw, ENNReal.ofReal_zero]
  refine measure_mono_null ?_ hZ
  intro u hu
  show noiseWeight μ u = 0
  by_contra hwne
  have hpt : (fun u => g (M.solve u y)) u
      = observed (M.treated t a₁) (M.potentialOutcome t a₀ y g)
        (M.potentialOutcome t a₁ y g) u := by
    by_cases huT : u ∈ M.treated t a₁
    · have h1 : M.solve u t = a₁ := huT
      have hY : M.potentialOutcome t a₁ y g u = g (M.solve u y) := by
        unfold potentialOutcome
        rw [M.counterfactual_eq_solve h1]
      have hnc : u ∉ (M.treated t a₁)ᶜ := fun hc => hc huT
      show g (M.solve u y) = observed (M.treated t a₁)
        (M.potentialOutcome t a₀ y g) (M.potentialOutcome t a₁ y g) u
      unfold observed
      rw [Pi.add_apply, Set.indicator_of_mem huT, Set.indicator_of_notMem hnc, add_zero]
      exact hY.symm
    · have h0 : M.solve u t = a₀ := by
        rcases hbin u hwne with h0 | h1
        · exact h0
        · exact absurd (show u ∈ M.treated t a₁ from h1) huT
      have hY : M.potentialOutcome t a₀ y g u = g (M.solve u y) := by
        unfold potentialOutcome
        rw [M.counterfactual_eq_solve h0]
      have hmc : u ∈ (M.treated t a₁)ᶜ := (Set.mem_compl_iff _ _).mpr huT
      show g (M.solve u y) = observed (M.treated t a₁)
        (M.potentialOutcome t a₀ y g) (M.potentialOutcome t a₁ y g) u
      unfold observed
      rw [Pi.add_apply, Set.indicator_of_notMem huT, Set.indicator_of_mem hmc, zero_add]
      exact hY.symm
  exact hu hpt

/-- **Markovian ignorability**: under independent noises, the treatment is conditionally
independent of the pair of potential outcomes given the values of the treatment's parents. -/
theorem condIndepDiscrete_potentialOutcomes {α : Type*} {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t y : Fin n) (a₀ a₁ : α)
    (g : α → ℝ) :
    CondIndepDiscrete (noiseMeasure μ) (M.treated t a₁)
      (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u))
      (fun u => M.paVal t (M.solve u)) := by
  classical
  intro B hB w
  have hC := indep_paValFib M t w
  have hD := indep_potOutFib M t y a₀ a₁ g B
  have hCD : ∀ u v, Function.update u t v
      ∈ (fun u => M.paVal t (M.solve u)) ⁻¹' {w} ∩
        (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B
      ↔ u ∈ (fun u => M.paVal t (M.solve u)) ⁻¹' {w} ∩
        (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B := by
    intro u v
    simp only [Set.mem_inter_iff, hC u v, hD u v]
  have hTW := treated_inter_fiber M t a₁ w
  have hfact1 : (noiseMeasure μ).real
        ({u | M.f t w (u t) = a₁} ∩ ((fun u => M.paVal t (M.solve u)) ⁻¹' {w} ∩
          (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B))
      = (noiseMeasure μ).real {u | M.f t w (u t) = a₁}
        * (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w} ∩
          (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B) :=
    factor_real_inter μ t (fun v => M.f t w v = a₁) hCD
  have hfact2 : (noiseMeasure μ).real
        ({u | M.f t w (u t) = a₁} ∩ (fun u => M.paVal t (M.solve u)) ⁻¹' {w})
      = (noiseMeasure μ).real {u | M.f t w (u t) = a₁}
        * (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w}) :=
    factor_real_inter μ t (fun v => M.f t w v = a₁) hC
  rw [Set.inter_right_comm, hTW, Set.inter_assoc, hfact1, hfact2]
  have hCD' : (fun u => M.paVal t (M.solve u)) ⁻¹' {w} ∩
      (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B
      = (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u)) ⁻¹' B ∩
        (fun u => M.paVal t (M.solve u)) ⁻¹' {w} :=
    Set.inter_comm _ _
  rw [hCD']
  ring

/-- **Strong ignorability given the parents**: if the treatment mechanism gives the value `a₁`
probability strictly between `0` and `1` at every value of the parents (overlap), the treatment
is strongly ignorable given the parents for the pair of potential outcomes. -/
theorem stronglyIgnorable_potentialOutcomes {α : Type*} {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t y : Fin n)
    (a₀ a₁ : α) (g : α → ℝ)
    (hover : ∀ w : M.pa t → α,
      0 < ((μ t).map (M.f t w)).weights a₁ ∧ ((μ t).map (M.f t w)).weights a₁ < 1) :
    StronglyIgnorable (noiseMeasure μ) (M.treated t a₁)
      (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u))
      (fun u => M.paVal t (M.solve u)) := by
  classical
  constructor
  · exact condIndepDiscrete_potentialOutcomes M μ t y a₀ a₁ g
  · intro w hwpos
    have hC := indep_paValFib M t w
    have hCreal : (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w}) ≠ 0 :=
      noiseMeasure_real_ne_zero μ _ hwpos
    have hTW := treated_inter_fiber M t a₁ w
    have hfact : (noiseMeasure μ).real
          ({u | M.f t w (u t) = a₁} ∩ (fun u => M.paVal t (M.solve u)) ⁻¹' {w})
        = (noiseMeasure μ).real {u | M.f t w (u t) = a₁}
          * (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w}) :=
      factor_real_inter μ t (fun v => M.f t w v = a₁) hC
    have hA : (noiseMeasure μ).real {u | M.f t w (u t) = a₁}
        = ((μ t).map (M.f t w)).weights a₁ := by
      rw [real_coord_eq μ t (fun v => M.f t w v = a₁)]
      rw [Finset.sum_filter]
      exact (map_weights_eq M μ t w a₁).symm
    show 0 < propensity (noiseMeasure μ) (M.treated t a₁)
          (fun u => M.paVal t (M.solve u)) w
        ∧ propensity (noiseMeasure μ) (M.treated t a₁)
          (fun u => M.paVal t (M.solve u)) w < 1
    unfold propensity
    rw [hTW, hfact, hA]
    have hcancel : ∀ a : ℝ,
        a * (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w}) /
          (noiseMeasure μ).real ((fun u => M.paVal t (M.solve u)) ⁻¹' {w}) = a := by
      intro a
      exact mul_div_cancel_right₀ a hCreal
    rw [hcancel]
    exact hover w

/-- **A parentless nondegenerate treatment is ignorable**: if the treatment node has no parents
and gives `a₁` probability strictly between `0` and `1`, it is (unconditionally) strongly
ignorable for the pair of potential outcomes. -/
theorem stronglyIgnorable_of_pa_eq_empty {α : Type*} {n : ℕ} {U : Fin n → Type*}
    [∀ k, Fintype (U k)] [∀ k, MeasurableSpace (U k)] [∀ k, MeasurableSingletonClass (U k)]
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t y : Fin n)
    (a₀ a₁ : α) (g : α → ℝ) (hpa : M.pa t = ∅)
    (hover : ∀ w : M.pa t → α,
      0 < ((μ t).map (M.f t w)).weights a₁ ∧ ((μ t).map (M.f t w)).weights a₁ < 1) :
    StronglyIgnorable (noiseMeasure μ) (M.treated t a₁)
      (fun u => (M.potentialOutcome t a₀ y g u, M.potentialOutcome t a₁ y g u))
      (fun _ => ()) := by
  classical
  have w₀ : M.pa t → α := fun j => by
    have hj := j.2
    exact (Finset.eq_empty_iff_forall_notMem.mp hpa _ hj).elim
  have hpaV : ∀ x : Fin n → α, M.paVal t x = w₀ := by
    intro x
    funext j
    have hj := j.2
    exact (Finset.eq_empty_iff_forall_notMem.mp hpa _ hj).elim
  have hT : M.treated t a₁ = {u | M.f t w₀ (u t) = a₁} := by
    ext u
    show (M.solve u t = a₁) ↔ (M.f t w₀ (u t) = a₁)
    have hsol := M.solve_isSolution u t
    rw [hsol, hpaV]
  have hC : ∀ w : Unit, (fun _ : (k : Fin n) → U k => ()) ⁻¹' {w} = Set.univ :=
    fun w => Set.preimage_const_of_mem (Set.mem_singleton_iff.mpr (Subsingleton.elim () w))
  constructor
  · intro B hB w
    rw [hC w]
    simp only [Set.inter_univ]
    rw [noiseMeasure_real_univ_eq, mul_one, hT]
    exact factor_real_inter μ t (fun v => M.f t w₀ v = a₁)
      (indep_potOutFib M t y a₀ a₁ g B)
  · intro w hwpos
    have hA : (noiseMeasure μ).real {u | M.f t w₀ (u t) = a₁}
        = ((μ t).map (M.f t w₀)).weights a₁ := by
      rw [real_coord_eq μ t (fun v => M.f t w₀ v = a₁)]
      rw [Finset.sum_filter]
      exact (map_weights_eq M μ t w₀ a₁).symm
    show 0 < propensity (noiseMeasure μ) (M.treated t a₁)
          (fun _ : (k : Fin n) → U k => ()) w
        ∧ propensity (noiseMeasure μ) (M.treated t a₁)
          (fun _ : (k : Fin n) → U k => ()) w < 1
    unfold propensity
    rw [hC w, Set.inter_univ, noiseMeasure_real_univ_eq, div_one, hT, hA]
    exact hover w₀
end FiniteSCM

end Cslib.MachineLearning.GraphicalModels
