/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.ForwardBackward
public import CSLibExt.MachineLearning.Sequence.BaumWelch
import Mathlib.Algebra.BigOperators.Field

/-!
# Baum-Welch expected counts from forward-backward variables

The Baum-Welch update of `Sequence/BaumWelch.lean` is defined from expected counts, which are
posterior sums over all state paths. This module computes them, as Rabiner does (*A tutorial on
hidden Markov models and selected applications in speech recognition*, Proc. IEEE 77, 1989,
`γ` and `ξ`), from the forward and backward variables of `Sequence/HiddenMarkov.lean` and
`Sequence/ForwardBackward.lean`.

Main results:

* `sum_pathProb_ite_pair`, `pairMarg`, `pairMarg_eq`: **pairwise forward-backward**: the joint
  weight of the observations and a transition `s → s'` at time `t` is
  `forward t s * trans s s' * emit s' (x (t + 1)) * backward k (t + 1) s'`.
* `initCount_eq`: `initCount s = ∑ n, α₀(s) β_T(s) / L_n` (starts, Rabiner's `γ₁`).
* `emitCount_eq`: `emitCount s o = ∑ n, ∑_{t ≤ T, xₙ(t) = o} αₜ(s) β_{T-t}(s) / L_n` (`γ`).
* `transCount_eq`: `transCount s s' = ∑ n, ∑_{t < T} αₜ(s) a(s, s') b(s', xₙ(t + 1))
  β_{T-t-1}(s') / L_n` (`ξ`).

Here `L_n = likelihood (xs n) T`, and `backward k t s` is indexed by the number `k` of remaining
steps. The forward and backward variables have tabulated versions (`forwardTab_get`,
`backwardTab_get`), which compute them in `O(T n²)` operations per sequence.

## Cost model

None: identities over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

variable {S O R : Type*} [Fintype S] [DecidableEq S] [Semiring R] (h : HMM S O R) (x : ℕ → O)

/-- **Pairwise path sums with a fixed endpoint.** Let $h$ be a hidden Markov model with finite
state set $S$, transition weights $a$ and emission weights $b$ in a semiring, and let $x$ be an
observation sequence. For all $k, t \in \mathbb{N}$ and states $s, s', u$, the sum of the path
weights of the state paths $z_0, \dots, z_{t + 1 + k}$ with $z_t = s$, $z_{t + 1} = s'$ and
$z_{t + 1 + k} = u$ equals $\alpha_t(s)\, a(s, s')\, b(s', x(t + 1))\, B_{k, t + 1}(s', u)$, where
$\alpha_t(s)$ is the forward variable and $B_{k, t + 1}(s', u)$ is the bridge weight of the paths
from the state $s'$ at time $t + 1$ to the state $u$ at time $t + 1 + k$. -/
theorem sum_pathProb_ite_pair : ∀ (k t : ℕ) (s s' u : S),
    ∑ z : Fin (t + 1 + k + 1) → S,
      (if z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧ z (Fin.last (t + 1 + k)) = u then
        pathProb h x (t + 1 + k) z else 0) =
      forward h x t s * h.trans s s' * h.emit s' (x (t + 1)) * bridge h x k (t + 1) s' u
  | 0, t, s, s', u => by
      change ∑ z : Fin (t + 2) → S,
          (if z ⟨t, by omega⟩ = s ∧ z (Fin.last (t + 1)) = s' ∧ z (Fin.last (t + 1)) = u then
            pathProb h x (t + 1) z else 0) = _
      rw [sum_snoc]
      have hc : ∀ (z : Fin (t + 1) → S) (v : S),
          (Fin.snoc z v : Fin (t + 2) → S) ⟨t, by omega⟩ = z (Fin.last t) := fun z v => by
        rw [show (⟨t, by omega⟩ : Fin (t + 2)) = (Fin.last t).castSucc from rfl, Fin.snoc_castSucc]
      simp only [hc, Fin.snoc_last, pathProb_snoc, bridge]
      by_cases hsu : s' = u
      · subst hsu
        simp only [and_self, ↓reduceIte, mul_one]
        rw [forward_eq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single s']
        · by_cases hz : z (Fin.last t) = s
          · simp [hz]
          · simp [hz]
        · intro v _ hv; simp [hv]
        · simp
      · simp only [hsu, ↓reduceIte, mul_zero]
        refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun v _ => ?_
        have : ¬ (z (Fin.last t) = s ∧ v = s' ∧ v = u) := fun ⟨_, h1, h2⟩ => hsu (h1 ▸ h2)
        simp only [this, ↓reduceIte]
  | k + 1, t, s, s', u => by
      have hc : ∀ (z : Fin (t + 1 + k + 1) → S) (v : S) (i : ℕ) (hi : i < t + 1 + k + 1),
          (Fin.snoc z v : Fin (t + 1 + k + 2) → S) ⟨i, by omega⟩ = z ⟨i, hi⟩ := fun z v i hi => by
        rw [show (⟨i, by omega⟩ : Fin (t + 1 + k + 2)) = Fin.castSucc ⟨i, hi⟩ from rfl,
          Fin.snoc_castSucc]
      change ∑ z : Fin (t + 1 + k + 2) → S,
          (if z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧ z (Fin.last (t + 1 + k + 1)) = u
            then pathProb h x (t + 1 + k + 1) z else 0) = _
      rw [sum_snoc]
      simp only [hc _ _ t (by omega), hc _ _ (t + 1) (by omega), Fin.snoc_last, pathProb_snoc]
      have lhs : ∀ z : Fin (t + 1 + k + 1) → S,
          (∑ v, if z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧ v = u then
            pathProb h x (t + 1 + k) z * h.trans (z (Fin.last (t + 1 + k))) v *
              h.emit v (x (t + 1 + k + 1)) else 0) =
          if z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' then pathProb h x (t + 1 + k) z *
            h.trans (z (Fin.last (t + 1 + k))) u * h.emit u (x (t + 1 + k + 1)) else 0 := by
        intro z
        by_cases hz : z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s'
        · simp [hz]
        · have hv : ∀ v, ¬ (z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧ v = u) :=
            fun v hv => hz ⟨hv.1, hv.2.1⟩
          simp only [hv, hz, ↓reduceIte, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl fun z _ => lhs z, bridge, ← mul_assoc, Finset.mul_sum,
        Finset.sum_mul]
      simp only [← mul_assoc, ← sum_pathProb_ite_pair k t s s', Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s'
      · simp only [hz, true_and, ite_mul, zero_mul, ↓reduceIte]
        rw [Finset.sum_ite_eq]
        simp
      · have hu : ∀ u', ¬ (z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧
            z (Fin.last (t + 1 + k)) = u') := fun u' hu => hz ⟨hu.1, hu.2.1⟩
        simp only [hz, hu, ↓reduceIte, zero_mul, Finset.sum_const_zero]

/-- **Pairwise state marginal of a hidden Markov model.** For a hidden Markov model with finite
state set $S$, an observation sequence $x$, times $t, k \in \mathbb{N}$ and states $s, s'$, the
pairwise marginal is the joint weight of the observations $x(0), \dots, x(t + 1 + k)$ and the
transition $s \to s'$ from time $t$ to time $t + 1$: the sum of the path weights of all state
paths $z_0, \dots, z_{t + 1 + k}$ with $z_t = s$ and $z_{t + 1} = s'$. -/
def pairMarg (t k : ℕ) (s s' : S) : R :=
  ∑ z : Fin (t + 1 + k + 1) → S,
    if z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' then pathProb h x (t + 1 + k) z else 0

/-- **Pairwise forward-backward.** Let $h$ be a hidden Markov model with finite state set $S$,
transition weights $a$ and emission weights $b$ in a semiring, and let $x$ be an observation
sequence. For all $t, k \in \mathbb{N}$ and states $s, s'$, the joint weight of the observations
$x(0), \dots, x(t + 1 + k)$ and the transition $s \to s'$ from time $t$ to time $t + 1$ equals
$\alpha_t(s)\, a(s, s')\, b(s', x(t + 1))\, \beta_{k, t + 1}(s')$, where $\alpha_t(s)$ is the
forward variable and $\beta_{k, t + 1}(s')$ is the backward variable, the weight of the
observations $x(t + 2), \dots, x(t + 1 + k)$ given the state $s'$ at time $t + 1$. -/
theorem pairMarg_eq (t k : ℕ) (s s' : S) :
    pairMarg h x t k s s' =
      forward h x t s * h.trans s s' * h.emit s' (x (t + 1)) * backward h x k (t + 1) s' := by
  rw [← sum_bridge, Finset.mul_sum,
    ← Finset.sum_congr rfl fun u _ => sum_pathProb_ite_pair h x k t s s' u, Finset.sum_comm,
    pairMarg]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s'
  · simp only [hz, true_and, ↓reduceIte]
    rw [Finset.sum_ite_eq]
    simp
  · have hu : ∀ u', ¬ (z ⟨t, by omega⟩ = s ∧ z ⟨t + 1, by omega⟩ = s' ∧
        z (Fin.last (t + 1 + k)) = u') := fun u' hu => hz ⟨hu.1, hu.2.1⟩
    simp only [hz, hu, ↓reduceIte, Finset.sum_const_zero]

theorem sum_ite_eq_stateMarg {T : ℕ} (t k : ℕ) (hT : t + k = T) (s : S) (ht : t < T + 1) :
    ∑ z : Fin (T + 1) → S, (if z ⟨t, ht⟩ = s then pathProb h x T z else 0) =
      stateMarg h x t k s := by
  subst hT; rfl

theorem sum_ite_eq_pairMarg {T : ℕ} (t k : ℕ) (hT : t + 1 + k = T) (s s' : S) (ht : t < T + 1)
    (ht' : t + 1 < T + 1) :
    ∑ z : Fin (T + 1) → S,
      (if z ⟨t, ht⟩ = s ∧ z ⟨t + 1, ht'⟩ = s' then pathProb h x T z else 0) =
      pairMarg h x t k s s' := by
  subst hT; rfl

end Cslib.MachineLearning.Sequence.HiddenMarkov

namespace Cslib.MachineLearning.Sequence.BaumWelch

open Real
open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

variable {S O : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] {T N : ℕ}
  (xs : Fin N → ℕ → O)

omit [DecidableEq S] [DecidableEq O] in
theorem sum_post_mul_ite (h : ValidHMM S O) (n : Fin N) (C : (Fin (T + 1) → S) → Prop)
    [DecidablePred C] :
    ∑ z, post T xs h n z * (if C z then 1 else 0) =
      (∑ z, if C z then pathProb h.1 (xs n) T z else 0) / likelihood h.1 (xs n) T := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs
  · simp only [post, posterior, marginal_joint, joint, mul_one]
  · simp only [mul_zero, zero_div]

omit [DecidableEq O] in
/-- **The expected starts from forward-backward.** Let $h$ be a valid hidden Markov model with
finite state set $S$ and finite observation set $O$, let $T \in \mathbb{N}$, and let
$x_0, \dots, x_{N-1}$ be observation sequences. For a sequence $x_n$ write $\alpha^n_0(s)$ for its
forward variable at time $0$ and state $s$, $\beta^n_{T,0}(s)$ for its backward variable from
time $0$ with $T$ remaining steps (the weight of the observations $x_n(1), \dots, x_n(T)$ given the
state $s$ at time $0$), and $L_n$ for the likelihood of $x_n(0), \dots, x_n(T)$. Then for every
state $s$, the expected number of sequences whose state path of length $T + 1$ starts in $s$,
under the posterior of $h$, is $\sum_{n < N} \alpha^n_0(s)\, \beta^n_{T,0}(s) / L_n$. -/
theorem initCount_eq (h : ValidHMM S O) (s : S) :
    initCount T xs h s =
      ∑ n, forward h.1 (xs n) 0 s * backward h.1 (xs n) T 0 s / likelihood h.1 (xs n) T := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (∑ z, post T xs h n z * pInit T z s) = _ from sum_post_mul_ite xs h n fun z => z 0 = s,
    ← stateMarg_eq]
  congr 1
  rw [← sum_ite_eq_stateMarg h.1 (xs n) 0 T (Nat.zero_add T) s (Nat.succ_pos T)]
  rfl

/-- **The expected emissions from forward-backward.** Let $h$ be a valid hidden Markov model with
finite state set $S$ and finite observation set $O$, let $T \in \mathbb{N}$, and let
$x_0, \dots, x_{N-1}$ be observation sequences. For a sequence $x_n$ write $\alpha^n_t(s)$ for its
forward variable at time $t$ and state $s$, $\beta^n_{k,t}(s)$ for its backward variable (the
weight of the observations $x_n(t + 1), \dots, x_n(t + k)$ given the state $s$ at time $t$), and
$L_n$ for the likelihood of $x_n(0), \dots, x_n(T)$. Then for every state $s$ and observation $o$,
the expected number of emissions of $o$ from $s$ along state paths of length $T + 1$, summed over
the sequences under the posterior of $h$, is
$\sum_{n < N} \sum_{t \le T,\ x_n(t) = o} \alpha^n_t(s)\, \beta^n_{T - t, t}(s) / L_n$. -/
theorem emitCount_eq (h : ValidHMM S O) (s : S) (o : O) :
    emitCount T xs h s o = ∑ n, ∑ t : Fin (T + 1), if xs n t = o then
      forward h.1 (xs n) t s * backward h.1 (xs n) (T - t) t s / likelihood h.1 (xs n) T
      else 0 := by
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [pEmit, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_post_mul_ite xs h n fun z => z t = s ∧ xs n t = o]
  by_cases ho : xs n t = o
  · simp only [ho, and_true, ↓reduceIte]
    rw [← stateMarg_eq, ← sum_ite_eq_stateMarg h.1 (xs n) t (T - t) (by omega) s t.2]
  · simp [ho]

omit [DecidableEq O] in
/-- **The expected transitions from forward-backward.** Let $h$ be a valid hidden Markov model
with finite state set $S$, finite observation set $O$, transition weights $a$ and emission
weights $b$, let $T \in \mathbb{N}$, and let $x_0, \dots, x_{N-1}$ be observation sequences. For a
sequence $x_n$ write $\alpha^n_t(s)$ for its forward variable at time $t$ and state $s$,
$\beta^n_{k,t}(s)$ for its backward variable (the weight of the observations
$x_n(t + 1), \dots, x_n(t + k)$ given the state $s$ at time $t$), and $L_n$ for the likelihood of
$x_n(0), \dots, x_n(T)$. Then for all states $s, s'$, the expected number of transitions
$s \to s'$ along state paths of length $T + 1$, summed over the sequences under the posterior of
$h$, is
$\sum_{n < N} \sum_{t < T} \alpha^n_t(s)\, a(s, s')\, b(s', x_n(t + 1))\,
\beta^n_{T - t - 1, t + 1}(s') / L_n$.

Each summand is Rabiner's $\xi_t(s, s')$ for the sequence $x_n$. -/
theorem transCount_eq (h : ValidHMM S O) (s s' : S) :
    transCount T xs h s s' = ∑ n, ∑ t : Fin T,
      forward h.1 (xs n) t s * h.1.trans s s' * h.1.emit s' (xs n (t + 1)) *
        backward h.1 (xs n) (T - t - 1) (t + 1) s' / likelihood h.1 (xs n) T := by
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [pTrans, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_post_mul_ite xs h n fun z => z t.castSucc = s ∧ z t.succ = s', ← pairMarg_eq,
    ← sum_ite_eq_pairMarg h.1 (xs n) (T := T) t (T - t - 1) (by have := t.2; omega) s s'
      (by have := t.2; omega) (by have := t.2; omega)]
  rfl

end Cslib.MachineLearning.Sequence.BaumWelch
