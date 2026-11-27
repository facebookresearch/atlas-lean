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

/-- **Backward variables of a hidden Markov model.** Let $h$ be a hidden Markov model with finite
state set $S$, transition weights $a$ and emission weights $b$ in a semiring $R$, and let
$x_0, x_1, \dots$ be observations. The backward variables $\beta_k(t, s) \in R$, for
$k, t \in \mathbb{N}$ and $s \in S$, are defined by $\beta_0(t, s) = 1$ and
$$\beta_{k+1}(t, s) = \sum_{s' \in S} a(s, s')\, b(s', x_{t+1})\, \beta_k(t + 1, s').$$
Thus $\beta_k(t, s)$ is the weight of the observations $x_{t+1}, \dots, x_{t+k}$ given the state
$s$ at time $t$. -/
def backward : ℕ → ℕ → S → R
  | 0, _, _ => 1
  | k + 1, t, s => ∑ s', h.trans s s' * h.emit s' (x (t + 1)) * backward k (t + 1) s'

/-- **Bridge weights of a hidden Markov model.** Let $h$ be a hidden Markov model with finite state
set $S$, transition weights $a$ and emission weights $b$ in a semiring $R$, and let
$x_0, x_1, \dots$ be observations. The bridge weights $B_k(t, s, u) \in R$, for
$k, t \in \mathbb{N}$ and $s, u \in S$, are defined from the end by $B_0(t, s, u) = 1$ if $s = u$
and $B_0(t, s, u) = 0$ otherwise, and
$$B_{k+1}(t, s, u) = \left(\sum_{u' \in S} B_k(t, s, u')\, a(u', u)\right) b(u, x_{t+k+1}).$$
Thus $B_k(t, s, u)$ is the total weight of the paths from state $s$ at time $t$ to state $u$ at
time $t + k$, with transitions and emissions at times $t + 1, \dots, t + k$. -/
def bridge [DecidableEq S] : ℕ → ℕ → S → S → R
  | 0, _, s, u => if s = u then 1 else 0
  | k + 1, t, s, u => (∑ u', bridge k t s u' * h.trans u' u) * h.emit u (x (t + k + 1))

/-- **Joint weight of the observations and a state.** For a hidden Markov model with a finite set
of states $S$ and weights in a semiring, observations $x_0, x_1, \dots$, times $t, k \in \mathbb{N}$
and a state $s \in S$, the joint weight of $x_0, \dots, x_{t+k}$ and the state $s$ at time $t$ is
the sum of the path weights $p_{t+k}(z)$ over all state paths $z = (z_0, \dots, z_{t+k})$ in $S$
with $z_t = s$, where $p_{t+k}(z)$ is the joint weight of the path $z$ and the observations
$x_0, \dots, x_{t+k}$. -/
def stateMarg [DecidableEq S] (t k : ℕ) (s : S) : R :=
  ∑ z : Fin (t + k + 1) → S, if z ⟨t, by omega⟩ = s then pathProb h x (t + k) z else 0

/-- **Front decomposition of the bridge weights.** Let $h$ be a hidden Markov model with finite
state set $S$, transition weights $a$ and emission weights $b$ in a semiring, let $x_0, x_1, \dots$
be observations, and write $B_k(t, s, u)$ for the bridge weight of the paths from state $s$ at
time $t$ to state $u$ at time $t + k$. Then for all $k, t \in \mathbb{N}$ and $s, u \in S$,
$$B_{k+1}(t, s, u) = \sum_{s' \in S} a(s, s')\, b(s', x_{t+1})\, B_k(t + 1, s', u).$$ -/
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

/-- **Bridge weights sum to the backward variable.** For a hidden Markov model with a finite set
of states $S$ and weights in a semiring, observations $x_0, x_1, \dots$, all $k, t \in \mathbb{N}$
and every state $s \in S$, the sum over all states $u \in S$ of the bridge weight from state $s$
at time $t$ to state $u$ at time $t + k$ equals the backward variable $\beta_{k,t}(s)$, the
weight of the observations $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$. -/
theorem sum_bridge [DecidableEq S] :
    ∀ (k t : ℕ) (s : S), ∑ u, bridge h x k t s u = backward h x k t s
  | 0, t, s => by simp [bridge, backward]
  | k + 1, t, s => by
      simp only [bridge_succ_front, backward]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [← Finset.mul_sum, sum_bridge k (t + 1) s']

/-- **Paths through two fixed states.** For a hidden Markov model with a finite set of states $S$
and weights in a semiring, observations $x_0, x_1, \dots$, all $k, t \in \mathbb{N}$ and states
$s, u \in S$, the sum of the path weights $p_{t+k}(z)$ over all state paths
$z = (z_0, \dots, z_{t+k})$ in $S$ with $z_t = s$ and $z_{t+k} = u$ equals
$\alpha_t(s)\, b_{k,t}(s, u)$. Here $p_{t+k}(z)$ is the joint weight of the path $z$ and the
observations $x_0, \dots, x_{t+k}$, $\alpha_t(s)$ is the forward variable and $b_{k,t}(s, u)$ is
the bridge weight from state $s$ at time $t$ to state $u$ at time $t + k$. -/
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

/-- **Forward-backward identity.** For a hidden Markov model with a finite set of states $S$ and
weights in a semiring, observations $x_0, x_1, \dots$, times $t, k \in \mathbb{N}$ and a state
$s \in S$, the joint weight of the observations $x_0, \dots, x_{t+k}$ and the state $s$ at time
$t$ equals $\alpha_t(s)\,\beta_{k,t}(s)$, the forward variable $\alpha_t(s)$ (the weight of
$x_0, \dots, x_t$ with the state at time $t$ equal to $s$) times the backward variable
$\beta_{k,t}(s)$ (the weight of $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$). -/
theorem stateMarg_eq [DecidableEq S] (t k : ℕ) (s : S) :
    stateMarg h x t k s = forward h x t s * backward h x k t s := by
  rw [← sum_bridge, Finset.mul_sum,
    ← Finset.sum_congr rfl fun u _ => sum_pathProb_ite_ite h x k t s u,
    Finset.sum_comm, stateMarg]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ⟨t, by omega⟩ = s
  · simp [hz]
  · simp [hz]

/-- **The likelihood from the forward and backward variables.** Let $h$ be a hidden Markov model
with finite state set $S$ and weights in a semiring, and let $x_0, x_1, \dots$ be observations.
Write $\alpha_t(s)$ for the forward variable (the weight of $x_0, \dots, x_t$ with the state at
time $t$ equal to $s$) and $\beta_k(t, s)$ for the backward variable. Then for all
$t, k \in \mathbb{N}$, the likelihood of $x_0, \dots, x_{t+k}$ equals
$$\sum_{s \in S} \alpha_t(s)\, \beta_k(t, s).$$ -/
theorem likelihood_eq_sum_forward_mul_backward (t k : ℕ) :
    likelihood h x (t + k) = ∑ s, forward h x t s * backward h x k t s := by
  classical
  simp only [← stateMarg_eq, stateMarg]
  rw [Finset.sum_comm, likelihood]
  exact Finset.sum_congr rfl fun z _ => by simp

/-! ## Smoothing weights -/

section Smoothing

variable {K : Type*} [Semifield K] (g : HMM S O K)

/-- **Smoothed state weights.** For a hidden Markov model with a finite set of states $S$ and
weights in a semifield $K$, observations $x_0, x_1, \dots$, times $t, k \in \mathbb{N}$ and a
state $s \in S$, the smoothed weight of $s$ at time $t$ is
$$\gamma_{t,k}(s) = \frac{\alpha_t(s)\,\beta_{k,t}(s)}{L_{t+k}},$$
where $\alpha_t(s)$ is the forward variable, $\beta_{k,t}(s)$ is the backward variable (the weight
of $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$) and $L_{t+k}$ is the likelihood of
$x_0, \dots, x_{t+k}$. Division is that of $K$, so $\gamma_{t,k}(s) = 0$ when $L_{t+k} = 0$.

For nonnegative weights with stochastic rows and a positive likelihood this is the smoothing
posterior $P(z_t = s \mid x_0, \dots, x_{t+k})$ that the hidden state $z_t$ at time $t$ is $s$; for
general semifield weights it is only this ratio. -/
def smoothed (t k : ℕ) (s : S) : K :=
  forward g x t s * backward g x k t s / likelihood g x (t + k)

/-- **Forward-backward smoothing is a joint-to-likelihood ratio.** Let $g$ be a hidden Markov model
with finite state set $S$ and weights in a semifield, and let $x_0, x_1, \dots$ be observations.
For all $t, k \in \mathbb{N}$ and $s \in S$, the smoothing weight
$\alpha_t(s)\, \beta_k(t, s) / L_{t+k}$, where $\alpha$ and $\beta$ are the forward and backward
variables and $L_{t+k}$ is the likelihood of $x_0, \dots, x_{t+k}$, equals the joint weight of
$x_0, \dots, x_{t+k}$ and the state $s$ at time $t$, divided by $L_{t+k}$.

When the weights are probabilities and the likelihood is positive, this ratio is the conditional
state marginal. -/
theorem smoothed_eq [DecidableEq S] (t k : ℕ) (s : S) :
    smoothed x g t k s = stateMarg g x t k s / likelihood g x (t + k) := by
  rw [smoothed, stateMarg_eq]

/-- **Smoothed weights sum to one.** For a hidden Markov model with a finite set of states $S$ and
weights in a semifield, observations $x_0, x_1, \dots$ and times $t, k \in \mathbb{N}$, if the
likelihood $L_{t+k}$ of $x_0, \dots, x_{t+k}$ is nonzero, then the smoothed weights
$\gamma_{t,k}(s) = \alpha_t(s)\,\beta_{k,t}(s) / L_{t+k}$, with $\alpha$ the forward and $\beta$
the backward variables, sum to $1$ over all states $s \in S$. -/
theorem sum_smoothed (t k : ℕ) (hL : likelihood g x (t + k) ≠ 0) :
    ∑ s, smoothed x g t k s = 1 := by
  simp only [smoothed, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← likelihood_eq_sum_forward_mul_backward, mul_inv_cancel₀ hL]

/-- **Smoothing weights are nonnegative.** Let $g$ be a hidden Markov model with finite state set
$S$ whose initial, transition and emission weights are nonnegative elements of a linearly ordered
semifield $K$, and let $x_0, x_1, \dots$ be observations. For all $t, k \in \mathbb{N}$ and
$s \in S$, the smoothing weight $\alpha_t(s)\, \beta_k(t, s) / L_{t+k}$ is nonnegative, where
$\alpha$ and $\beta$ are the forward and backward variables and $L_{t+k}$ is the likelihood of
$x_0, \dots, x_{t+k}$.

Since the smoothing weights at each time sum to one when the likelihood is nonzero, with a
positive likelihood they form a probability distribution over the states. -/
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

/-- **One step of the tabulated backward algorithm.** For a hidden Markov model $g$ with states
$\{0, \dots, n - 1\}$, transition weights $a$ and emission weights $b$ in a semiring $R$, an
observation sequence $x_0, x_1, \dots$, a vector $v \in R^n$ and a time $t$, this is the vector in
$R^n$ whose entry at state $s$ is $\sum_{s'} a(s, s')\, b(s', x_{t+1})\, v_{s'}$. -/
def backwardStep (g : HMM (Fin n) O R) (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => ∑ s', g.trans s s' * g.emit s' (x (t + 1)) * v[s']

/-- **The tabulated backward algorithm.** For a hidden Markov model $g$ with states
$\{0, \dots, n - 1\}$, transition weights $a$ and emission weights $b$ in a semiring $R$, and an
observation sequence $x_0, x_1, \dots$, the tables $\beta^{(k)}_t \in R^n$ for $k, t \in \mathbb{N}$
are defined by recursion on $k$: $\beta^{(0)}_t$ is the all-ones vector, and $\beta^{(k+1)}_t$ is
one backward step at time $t$ applied to $\beta^{(k)}_{t+1}$, that is, its entry at state $s$ is
$\sum_{s'} a(s, s')\, b(s', x_{t+1})\, \beta^{(k)}_{t+1}(s')$.

The entries of $\beta^{(k)}_t$ are the backward variables; each step takes $O(n^2)$ operations. -/
def backwardTab (g : HMM (Fin n) O R) : ℕ → ℕ → Vector R n
  | 0, _ => Vector.replicate n 1
  | k + 1, t => backwardStep x g (backwardTab g k (t + 1)) t

theorem backwardTab_get (g : HMM (Fin n) O R) :
    ∀ (k t : ℕ) (s : Fin n), (backwardTab x g k t)[s] = backward g x k t s
  | 0, t, s => by simp [backwardTab, backward]
  | k + 1, t, s => by simp [backwardTab, backwardStep, backward, backwardTab_get g k (t + 1)]

/-- **Smoothing step on tables.** For a semifield $K$, vectors $a, b \in K^n$ and $L \in K$, this is
the vector in $K^n$ whose entry at $s$ is $a_s b_s / L$.

It combines the forward and backward tables into the smoothing weights. -/
def smoothStep {K : Type*} [Semifield K] (a b : Vector K n) (L : K) : Vector K n :=
  Vector.ofFn fun s => a[s] * b[s] / L

/-- **Tabulated forward-backward smoothing.** Let $g$ be a hidden Markov model with states
$\{0, \dots, n - 1\}$ and weights in a semifield $K$, and let $x_0, x_1, \dots$ be observations.
For $t, k \in \mathbb{N}$, this is the vector in $K^n$ whose entry at state $s$ is
$\alpha_t(s)\, \beta_k(t, s) / L_{t+k}$, where $\alpha_t$ is the tabulated forward vector at time
$t$, $\beta_k(t, \cdot)$ is the tabulated backward vector for $k$ steps from time $t$, and $L_{t+k}$
is the tabulated likelihood of $x_0, \dots, x_{t+k}$.

Its entries are the smoothing weights of all states at time $t$, computed in $O((t + k) n^2)$
operations. -/
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
