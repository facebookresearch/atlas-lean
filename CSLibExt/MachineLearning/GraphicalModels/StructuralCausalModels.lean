/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

## Main results

* `FiniteSCM.solve_isSolution`, `FiniteSCM.IsSolution.eq_solve`,
  `FiniteSCM.existsUnique_isSolution`: **unique solvability**: for every noise value the
  structural equations have exactly one solution, `solve u`.
* `FiniteSCM.solve_congr_of_ancestral`: on a parent-closed (ancestral) set of nodes the solution
  depends only on the noise on that set; in particular a node's value depends only on its own and
  its ancestors' noise.

Cyclic systems (where a solution may fail to exist or be unique) are not expressible: parents
always precede their child.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §1.5.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §7.1.
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

end FiniteSCM

end Cslib.MachineLearning.GraphicalModels
