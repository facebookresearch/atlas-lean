/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Hidden Markov models: backward variables and smoothing

The backward half of the forward-backward algorithm (Rabiner, *A tutorial on hidden Markov
models and selected applications in speech recognition*, Proc. IEEE 77, 1989; Bishop, *Pattern
Recognition and Machine Learning*, Section 13.2.2) for the hidden Markov models of
`Sequence/HiddenMarkov.lean`. `backward k t s` is the weight of the observations
`x (t + 1), …, x (t + k)` given the state `s` at time `t`, and `stateMarg t k s` is the joint
weight of `x 0, …, x (t + k)` and the state `s` at time `t`. Like the forward algorithm, the
identities hold over any semiring (multiplication order along a path is kept).

Main results:

* `stateMarg_eq`: **forward-backward**: `stateMarg t k s = forward t s * backward k t s`. The proof
  goes through `bridge` (path weights between two fixed states, built from the end;
  `sum_pathProb_ite_ite`), its front decomposition `bridge_succ_front`, and `sum_bridge`.
* `likelihood_eq_sum_forward_mul_backward`: `likelihood (t + k) = ∑ s, forward t s * backward k t s`
  at every intermediate time.
* `smoothed`, `smoothed_eq`, `sum_smoothed`, `smoothed_nonneg`: **smoothing**: the ratio
  `forward t s * backward k t s / likelihood` is the joint weight of the observations and
  `z t = s` over the likelihood. With nonnegative weights over an ordered field and a positive
  likelihood it is a distribution over states; when the weights are probabilities it is the
  smoothing posterior `P(z t = s | x 0, …, x (t + k))`.
* On `Fin n`, tabulated: `backwardTab` (`backwardTab_get`) and `smoothedTab` (`smoothedTab_get`).

## Cost model

Semiring operations. `backwardTab` takes `O(n²)` per step, and `smoothedTab` takes `O((t + k) n²)`
in total. The untabulated `backward`, `bridge` and `stateMarg` are specifications.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

variable {S O R : Type*} [Fintype S] [Semiring R] (h : HMM S O R) (x : ℕ → O)

/-- The backward variables: `backward k t s` is the weight of the observations
`x (t + 1), …, x (t + k)` given the state `s` at time `t`. -/
def backward : ℕ → ℕ → S → R
  | 0, _, _ => 1
  | k + 1, t, s => ∑ s', h.trans s s' * h.emit s' (x (t + 1)) * backward k (t + 1) s'

/-- The weight of the paths from state `s` at time `t` to state `u` at time `t + k`
(transitions and emissions at times `t + 1, …, t + k`), built from the end. -/
def bridge [DecidableEq S] : ℕ → ℕ → S → S → R
  | 0, _, s, u => if s = u then 1 else 0
  | k + 1, t, s, u => (∑ u', bridge k t s u' * h.trans u' u) * h.emit u (x (t + k + 1))

/-- The joint weight of the observations `x 0, …, x (t + k)` and the state `s` at time `t`. -/
def stateMarg [DecidableEq S] (t k : ℕ) (s : S) : R :=
  ∑ z : Fin (t + k + 1) → S, if z ⟨t, by omega⟩ = s then pathProb h x (t + k) z else 0

/-- The bridge weights, decomposed from the front: the first transition, then a shorter bridge. -/
theorem bridge_succ_front [DecidableEq S] : ∀ (k t : ℕ) (s u : S),
    bridge h x (k + 1) t s u =
      ∑ s', h.trans s s' * h.emit s' (x (t + 1)) * bridge h x k (t + 1) s' u
  | 0, t, s, u => by
      simp only [bridge, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, Nat.add_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  | k + 1, t, s, u => by
      rw [bridge]
      simp only [bridge_succ_front k t s]
      simp only [bridge, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun u' _ => ?_
      rw [show t + (k + 1) + 1 = t + 1 + k + 1 by omega]
      simp only [mul_assoc]

/-- Summing the bridges over their end state gives the backward variable. -/
theorem sum_bridge [DecidableEq S] :
    ∀ (k t : ℕ) (s : S), ∑ u, bridge h x k t s u = backward h x k t s
  | 0, t, s => by simp [bridge, backward]
  | k + 1, t, s => by
      simp only [bridge_succ_front, backward]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [← Finset.mul_sum, sum_bridge k (t + 1) s']

/-- The path sums with fixed states at times `t` and `t + k` factor through the forward variable
and a bridge. -/
theorem sum_pathProb_ite_ite [DecidableEq S] : ∀ (k t : ℕ) (s u : S),
    ∑ z : Fin (t + k + 1) → S,
      (if z ⟨t, by omega⟩ = s ∧ z (Fin.last (t + k)) = u then pathProb h x (t + k) z else 0) =
      forward h x t s * bridge h x k t s u
  | 0, t, s, u => by
      change ∑ z : Fin (t + 1) → S,
          (if z (Fin.last t) = s ∧ z (Fin.last t) = u then pathProb h x t z else 0) =
        forward h x t s * bridge h x 0 t s u
      simp only [bridge, mul_ite, mul_one, mul_zero]
      rw [forward_eq]
      split_ifs with hsu
      · subst hsu
        exact Finset.sum_congr rfl fun z _ => by simp only [and_self]
      · refine Finset.sum_eq_zero fun z _ => ?_
        have : ¬ (z (Fin.last t) = s ∧ z (Fin.last t) = u) := fun ⟨h1, h2⟩ => hsu (h1.symm.trans h2)
        simp only [this, ↓reduceIte]
  | k + 1, t, s, u => by
      have hsn : ∀ (z : Fin (t + k + 1) → S) (v : S),
          (Fin.snoc z v : Fin (t + k + 2) → S) ⟨t, by omega⟩ = z ⟨t, by omega⟩ := by
        intro z v
        rw [show (⟨t, by omega⟩ : Fin (t + k + 2)) = Fin.castSucc ⟨t, by omega⟩ from rfl,
          Fin.snoc_castSucc]
      change ∑ z : Fin (t + k + 2) → S,
          (if z ⟨t, by omega⟩ = s ∧ z (Fin.last (t + k + 1)) = u then pathProb h x (t + k + 1) z
            else 0) = forward h x t s * bridge h x (k + 1) t s u
      rw [sum_snoc]
      simp only [hsn, Fin.snoc_last, pathProb_snoc]
      -- both sides as a sum over the prefix
      have lhs : ∀ z : Fin (t + k + 1) → S,
          (∑ v, if z ⟨t, by omega⟩ = s ∧ v = u then pathProb h x (t + k) z *
            h.trans (z (Fin.last (t + k))) v * h.emit v (x (t + k + 1)) else 0) =
          if z ⟨t, by omega⟩ = s then pathProb h x (t + k) z *
            h.trans (z (Fin.last (t + k))) u * h.emit u (x (t + k + 1)) else 0 := by
        intro z
        by_cases hz : z ⟨t, by omega⟩ = s
        · simp [hz]
        · simp [hz]
      rw [Finset.sum_congr rfl fun z _ => lhs z, bridge, ← mul_assoc, Finset.mul_sum,
        Finset.sum_mul]
      simp only [← mul_assoc, ← sum_pathProb_ite_ite k t s, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z ⟨t, by omega⟩ = s
      · simp only [hz, true_and, ite_mul, zero_mul, ↓reduceIte]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hz]

/-- **Forward-backward**: the joint weight of the observations up to time `t + k` and the state
`s` at time `t` is `forward t s * backward k t s`. -/
theorem stateMarg_eq [DecidableEq S] (t k : ℕ) (s : S) :
    stateMarg h x t k s = forward h x t s * backward h x k t s := by
  rw [← sum_bridge, Finset.mul_sum,
    ← Finset.sum_congr rfl fun u _ => sum_pathProb_ite_ite h x k t s u,
    Finset.sum_comm, stateMarg]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ⟨t, by omega⟩ = s
  · simp [hz]
  · simp [hz]

/-- The likelihood from the forward and backward variables at any intermediate time. -/
theorem likelihood_eq_sum_forward_mul_backward (t k : ℕ) :
    likelihood h x (t + k) = ∑ s, forward h x t s * backward h x k t s := by
  classical
  simp only [← stateMarg_eq, stateMarg]
  rw [Finset.sum_comm, likelihood]
  exact Finset.sum_congr rfl fun z _ => by simp

/-! ## Smoothing weights -/

section Smoothing

variable {K : Type*} [Semifield K] (g : HMM S O K)

/-- The normalized forward-backward weights `forward t s * backward k t s / likelihood`. For a
probabilistic HMM (nonnegative weights with stochastic rows, positive likelihood) this is the
smoothing posterior `P(z t = s | x 0, …, x (t + k))`: `smoothed_eq` writes it as the joint weight of
the observations and `z t = s` over the likelihood. For general semifield weights it is only this
ratio. -/
def smoothed (t k : ℕ) (s : S) : K :=
  forward g x t s * backward g x k t s / likelihood g x (t + k)

/-- **Forward-backward smoothing is a joint-to-likelihood ratio**: `smoothed` is the joint weight
of the observations and `z t = s` divided by the likelihood. When the weights are probabilities
and the likelihood is positive, this ratio is the conditional state marginal. -/
theorem smoothed_eq [DecidableEq S] (t k : ℕ) (s : S) :
    smoothed x g t k s = stateMarg g x t k s / likelihood g x (t + k) := by
  rw [smoothed, stateMarg_eq]

/-- The smoothing weights at each time sum to one when the likelihood is nonzero. -/
theorem sum_smoothed (t k : ℕ) (hL : likelihood g x (t + k) ≠ 0) :
    ∑ s, smoothed x g t k s = 1 := by
  simp only [smoothed, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← likelihood_eq_sum_forward_mul_backward, mul_inv_cancel₀ hL]

/-- With nonnegative weights over an ordered field the smoothing weights are nonnegative, so with
a positive likelihood they form a distribution over states (`sum_smoothed`). -/
theorem smoothed_nonneg [LinearOrder K] [IsStrictOrderedRing K]
    (hn : g.Nonneg) (t k : ℕ) (s : S) : 0 ≤ smoothed x g t k s := by
  classical
  rw [smoothed_eq]
  refine div_nonneg (Finset.sum_nonneg fun z _ => ?_)
    (Finset.sum_nonneg fun z _ => pathProb_nonneg x hn _ z)
  split_ifs
  exacts [pathProb_nonneg x hn _ z, le_rfl]

end Smoothing

/-! ## Tabulated on `Fin n` -/

section Tabulated

variable {n : ℕ}

/-- One backward step on a table of the next step's values. -/
def backwardStep (g : HMM (Fin n) O R) (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => ∑ s', g.trans s s' * g.emit s' (x (t + 1)) * v[s']

/-- The backward variables, tabulated step by step: `O(n²)` operations per step. -/
def backwardTab (g : HMM (Fin n) O R) : ℕ → ℕ → Vector R n
  | 0, _ => Vector.replicate n 1
  | k + 1, t => backwardStep x g (backwardTab g k (t + 1)) t

theorem backwardTab_get (g : HMM (Fin n) O R) :
    ∀ (k t : ℕ) (s : Fin n), (backwardTab x g k t)[s] = backward g x k t s
  | 0, t, s => by simp [backwardTab, backward]
  | k + 1, t, s => by simp [backwardTab, backwardStep, backward, backwardTab_get g k (t + 1)]

/-- Combine the forward and backward tables into the smoothing weights. -/
def smoothStep {K : Type*} [Semifield K] (a b : Vector K n) (L : K) : Vector K n :=
  Vector.ofFn fun s => a[s] * b[s] / L

/-- **Forward-backward smoothing**, tabulated: the smoothing weights `smoothed x g t k s` of all
states at time `t`, in `O((t + k) n²)` operations. -/
def smoothedTab {K : Type*} [Semifield K] (g : HMM (Fin n) O K) (t k : ℕ) : Vector K n :=
  smoothStep (forwardTab x g t) (backwardTab x g k t) (likelihoodTab x g (t + k))

theorem smoothedTab_get {K : Type*} [Semifield K] (g : HMM (Fin n) O K) (t k : ℕ) (s : Fin n) :
    (smoothedTab x g t k)[s] = smoothed x g t k s := by
  have h1 := forwardTab_get x g t s
  have h2 := backwardTab_get x g k t s
  simp only [Fin.getElem_fin] at h1 h2
  simp [smoothedTab, smoothStep, smoothed, h1, h2, likelihoodTab_eq]

end Tabulated

end Cslib.MachineLearning.Sequence.HiddenMarkov
