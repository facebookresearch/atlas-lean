/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Baum-Welch is EM for hidden Markov models

The Baum-Welch algorithm (Rabiner, *A tutorial on hidden Markov models and selected applications
in speech recognition*, Proc. IEEE 77, 1989; Bishop, *Pattern Recognition and Machine Learning*,
Section 13.2.1) as an instance of the generic EM of
`LatentVariable/ExpectationMaximization.lean`. The latent variable is the state path of length
`T + 1`, the data are `N` observation sequences, and the joint is the path weight of
`Sequence/HiddenMarkov.lean` (`marginal_joint`, `logLik_eq`: the EM likelihood is the HMM
likelihood).

Main results:

* `pathProb_eq_prod`, `log_joint`: the path weight factorizes, and its log is linear in the path's
  counts (`pInit`, `pTrans`, `pEmit`).
* `initCount`, `transCount`, `emitCount`: expected counts under the posterior over paths;
  `emQ_eq`: **`Q(h' | h)` is linear in the expected counts**.
* `mStep`: **the Baum-Welch update** (normalized expected counts), valid on data with a sequence,
  at least one transition, and every symbol observed (`Rich`, `mStep_valid`, `emStep`).
* `emQ_le_emStep`: **the update maximizes `Q(· | h)`** over all valid HMMs;
  `logLik_le_emStep`, `logLik_iterate_emStep_monotone`: **Baum-Welch never decreases the
  likelihood**.

The expected counts are defined here as posterior sums over paths, the specification. Computing
them with forward-backward variables (Rabiner's `γ` and `ξ`) is not formalized in this module.

## Cost model

None: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.BaumWelch

open Real
open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.LatentVariable.BernoulliMixture (sum_mul_log_le_sum_mul_log_div)

variable {S O R : Type*}

/-- **Path weight as a product.** Let $h$ be an HMM with weights in a commutative semiring, with
initial weights $\pi$, transition weights $a$ and emission weights $b$, and let $x_0, x_1, \dots$
be observations. For every $T$ and every state path $z = (z_0, \dots, z_T)$, the path weight of
$z$ and $x_0, \dots, x_T$ is
$$\pi(z_0) \prod_{t=0}^{T-1} a(z_t, z_{t+1}) \prod_{t=0}^{T} b(z_t, x_t).$$
-/
theorem pathProb_eq_prod [CommSemiring R] (h : HMM S O R) (x : ℕ → O) :
    ∀ (T : ℕ) (z : Fin (T + 1) → S), pathProb h x T z =
      h.init (z 0) * (∏ t : Fin T, h.trans (z t.castSucc) (z t.succ)) *
        ∏ t : Fin (T + 1), h.emit (z t) (x t)
  | 0, z => by simp [pathProb]
  | T + 1, z => by
      rw [Fin.prod_univ_castSucc (f := fun t : Fin (T + 1) => h.trans (z t.castSucc) (z t.succ)),
        Fin.prod_univ_castSucc (f := fun t : Fin (T + 2) => h.emit (z t) (x t)), pathProb,
        pathProb_eq_prod h x T]
      simp only [Fin.init, Fin.succ_castSucc, Fin.val_castSucc, Fin.castSucc_zero, Fin.succ_last,
        Fin.val_last]
      ring

/-! ## The EM model of an HMM -/

variable [Fintype S] [Fintype O]

/-- **Valid hidden Markov model parameters.** A hidden Markov model with finite state set $S$,
finite observation set $O$ and real initial weights $\pi$, transition weights $a$ and emission
weights $b$ is valid when all its weights are strictly positive and form probability
distributions: $\pi(s) > 0$ for every $s$ and $\sum_{s} \pi(s) = 1$; $a(s, s') > 0$ for all
$s, s'$ and $\sum_{s'} a(s, s') = 1$ for every $s$; and $b(s, o) > 0$ for all $s, o$ and
$\sum_{o} b(s, o) = 1$ for every $s$. -/
structure Valid (h : HMM S O ℝ) : Prop where
  init_pos : ∀ s, 0 < h.init s
  init_sum : ∑ s, h.init s = 1
  trans_pos : ∀ s s', 0 < h.trans s s'
  trans_sum : ∀ s, ∑ s', h.trans s s' = 1
  emit_pos : ∀ s o, 0 < h.emit s o
  emit_sum : ∀ s, ∑ o, h.emit s o = 1

/-- **Valid HMMs.** For finite sets $S$ of states and $O$ of observations, the valid HMMs are the
HMMs with states $S$, observations $O$ and real weights whose initial weights are positive and sum
to $1$, whose transition weights out of each state are positive and sum to $1$, and whose emission
weights from each state are positive and sum to $1$. They form the parameter space of
Baum-Welch. -/
abbrev ValidHMM (S O : Type*) [Fintype S] [Fintype O] := {h : HMM S O ℝ // Valid h}

variable (T : ℕ)

/-- **The EM model of a hidden Markov model.** Let $S$ and $O$ be finite sets and let $T$ be a
natural number. Let $h$ be a valid hidden Markov model on states $S$ and observations $O$, with
positive initial probabilities $\pi_s$, transition probabilities $a_{ss'}$ and emission
probabilities $b_{so}$, each distribution summing to one. The joint of its EM model at an
observation sequence $x = (x_0, x_1, \dots)$ in $O$ and a state path $z = (z_0, \dots, z_T)$ in $S$
is the path weight $p_h(x, z) = \pi_{z_0} b_{z_0 x_0} \prod_{t=1}^{T} a_{z_{t-1} z_t} b_{z_t x_t}$.
-/
noncomputable def joint (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) : ℝ :=
  pathProb h.1 x T z

theorem joint_pos (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) : 0 < joint T h x z := by
  rw [joint, pathProb_eq_prod]
  exact mul_pos (mul_pos (h.2.init_pos _) (Finset.prod_pos fun t _ => h.2.trans_pos _ _))
    (Finset.prod_pos fun t _ => h.2.emit_pos _ _)

/-- **The EM marginal of an HMM is its likelihood.** For every $T$, every valid HMM $h$ and every
observation sequence $x$, the marginal at $h$ and $x$ of the EM model of HMMs with state paths
$(z_0, \dots, z_T)$, that is the sum over all such paths of the path weight of $z$ and $x$, equals
the likelihood under $h$ of the observations $x_0, \dots, x_T$. -/
theorem marginal_joint (h : ValidHMM S O) (x : ℕ → O) :
    marginal (joint T) h x = likelihood h.1 x T := rfl

theorem nonempty_of_valid (h : ValidHMM S O) : Nonempty S := by
  by_contra hS
  have : IsEmpty S := not_nonempty_iff.1 hS
  have := h.2.init_sum
  simp at this

variable [DecidableEq S] [DecidableEq O]

/-- **Initial-state indicator of a state path.** For a state path $z = (z_0, \dots, z_T)$ and a
state $s$, the initial-state indicator is the real number $1$ if $z_0 = s$ and $0$ otherwise. -/
def pInit (z : Fin (T + 1) → S) (s : S) : ℝ := if z 0 = s then 1 else 0

/-- **Transition count of a state path.** For a state path $z = (z_0, \dots, z_T)$ and states
$s, s'$, the transition count is the number of $t \in \{0, \dots, T - 1\}$ with $z_t = s$ and
$z_{t+1} = s'$, as a real number. -/
def pTrans (z : Fin (T + 1) → S) (s s' : S) : ℝ :=
  ∑ t : Fin T, if z t.castSucc = s ∧ z t.succ = s' then 1 else 0

/-- **Emission count of a state path.** For a state path $z = (z_0, \dots, z_T)$, observations
$x_0, x_1, \dots$, a state $s$ and a symbol $o$, the emission count is the number of times
$t \in \{0, \dots, T\}$ with $z_t = s$ and $x_t = o$, as a real number. -/
def pEmit (x : ℕ → O) (z : Fin (T + 1) → S) (s : S) (o : O) : ℝ :=
  ∑ t : Fin (T + 1), if z t = s ∧ x t = o then 1 else 0

private theorem sum_sum_ite_and {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (a : α) (b : β) (f : α → β → ℝ) :
    ∑ s, ∑ s', (if a = s ∧ b = s' then (1 : ℝ) else 0) * f s s' = f a b := by
  simp only [ite_and, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

/-- **The log path weight is linear in the path's counts.** Let $S$ and $O$ be finite sets, let
$T$ be a natural number, and let $h$ be a valid hidden Markov model on states $S$ and observations
$O$, with positive initial probabilities $\pi_s$, transition probabilities $a_{ss'}$ and emission
probabilities $b_{so}$, each distribution summing to one. For every observation sequence
$x = (x_0, x_1, \dots)$ in $O$ and every state path $z = (z_0, \dots, z_T)$ in $S$, the path
weight $p_h(x, z) = \pi_{z_0} b_{z_0 x_0} \prod_{t=1}^{T} a_{z_{t-1} z_t} b_{z_t x_t}$ satisfies
$\log p_h(x, z) = \sum_{s} [z_0 = s] \log \pi_s + \sum_{s, s'} n_{ss'} \log a_{ss'} +
\sum_{s, o} m_{so} \log b_{so}$, where $[z_0 = s]$ is $1$ if $z_0 = s$ and $0$ otherwise,
$n_{ss'} = \#\{t < T : z_t = s,\ z_{t+1} = s'\}$ and $m_{so} = \#\{t \le T : z_t = s,\ x_t = o\}$.
-/
theorem log_joint (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) :
    log (joint T h x z) = ∑ s, pInit T z s * log (h.1.init s) +
      ∑ s, ∑ s', pTrans T z s s' * log (h.1.trans s s') +
      ∑ s, ∑ o, pEmit T x z s o * log (h.1.emit s o) := by
  rw [joint, pathProb_eq_prod, log_mul (mul_pos (h.2.init_pos _)
      (Finset.prod_pos fun t _ => h.2.trans_pos _ _)).ne'
      (Finset.prod_pos fun t _ => h.2.emit_pos _ _).ne',
    log_mul (h.2.init_pos _).ne' (Finset.prod_pos fun t _ => h.2.trans_pos _ _).ne',
    log_prod fun t _ => (h.2.trans_pos _ _).ne', log_prod fun t _ => (h.2.emit_pos _ _).ne']
  congr 1
  · congr 1
    · simp [pInit]
    · simp only [pTrans, Finset.sum_mul]
      conv_rhs => enter [2, s]; rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ =>
        (sum_sum_ite_and _ _ fun s s' => log (h.1.trans s s')).symm
  · simp only [pEmit, Finset.sum_mul]
    conv_rhs => enter [2, s]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (sum_sum_ite_and _ _ fun s o => log (h.1.emit s o)).symm

omit [Fintype S] [Fintype O] in
theorem pInit_nonneg (z : Fin (T + 1) → S) (s : S) : 0 ≤ pInit T z s := by
  unfold pInit; split_ifs <;> norm_num

omit [Fintype S] [Fintype O] in
theorem pTrans_nonneg (z : Fin (T + 1) → S) (s s' : S) : 0 ≤ pTrans T z s s' :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num

omit [Fintype S] [Fintype O] in
theorem pEmit_nonneg (x : ℕ → O) (z : Fin (T + 1) → S) (s : S) (o : O) : 0 ≤ pEmit T x z s o :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num

/-! ## Expected counts and the M-step -/

variable {N : ℕ} (xs : Fin N → ℕ → O)

/-- **Posterior weight of a state path.** For a valid HMM $h$, observation sequences
$x_0, \dots, x_{N-1}$, an index $n < N$ and a state path $z = (z_0, \dots, z_T)$, the posterior
weight of $z$ is the posterior of $z$ given $x_n$ at $h$ in the EM model of HMMs: the path weight
of $z$ and $x_n$ divided by the sum of the path weights of $z'$ and $x_n$ over all state paths
$z' = (z'_0, \dots, z'_T)$. -/
noncomputable def post (h : ValidHMM S O) (n : Fin N) (z : Fin (T + 1) → S) : ℝ :=
  posterior (joint T) h (xs n) z

/-- **Expected initial-state counts.** Let $S$ and $O$ be finite sets, let $T$ be a natural
number, and let $x_1, \dots, x_N$ be sequences of observations in $O$. For a valid hidden Markov
model $h$ on states $S$ and observations $O$ and a state $s$, the expected number of sequences
starting in $s$ is
$$I_s = \sum_{n=1}^{N} \sum_{z \,:\, z_0 = s} p_h(z \mid x_n),$$
where $z$ ranges over the state paths $(z_0, \dots, z_T)$ in $S$ and $p_h(z \mid x_n)$ is the
posterior of $z$ given $x_n$: the path weight of $z$ and $x_n$ under $h$ divided by the total
weight of all such paths. -/
noncomputable def initCount (h : ValidHMM S O) (s : S) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pInit T z s

/-- **Expected transition count.** For a valid HMM $h$, observation sequences
$x_0, \dots, x_{N-1}$ and states $s, s'$, the expected transition count is
$\sum_{n < N} \sum_{z} p_h(z \mid x_n) \, c_{s s'}(z)$, where $z$ ranges over the state paths
$(z_0, \dots, z_T)$, $p_h(z \mid x_n)$ is the posterior weight of $z$ for $x_n$, and $c_{s s'}(z)$
is the number of $t < T$ with $z_t = s$ and $z_{t+1} = s'$. -/
noncomputable def transCount (h : ValidHMM S O) (s s' : S) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pTrans T z s s'

/-- **Expected emission counts.** Let $S$ and $O$ be finite sets, let $T$ be a natural number,
and let $x_1, \dots, x_N$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$.
For a valid hidden Markov model $h$ on states $S$ and observations $O$, a state $s$ and an
observation $o$, the expected number of emissions of $o$ from $s$ is
$$E_{so} = \sum_{n=1}^{N} \sum_{z} p_h(z \mid x_n) \, \#\{t \le T : z_t = s,\ x_{n,t} = o\},$$
where $z$ ranges over the state paths $(z_0, \dots, z_T)$ in $S$ and $p_h(z \mid x_n)$ is the
posterior of $z$ given $x_n$: the path weight of $z$ and $x_n$ under $h$ divided by the total
weight of all such paths. -/
noncomputable def emitCount (h : ValidHMM S O) (s : S) (o : O) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pEmit T (xs n) z s o

/-- **The Baum-Welch M-step.** Let $h$ be a valid HMM with finite state set $S$ and finite
observation set $O$, let $x_0, \dots, x_{N-1}$ be observation sequences, and consider state paths
$(z_0, \dots, z_T)$. Write $I(s)$, $A(s, s')$ and $E(s, o)$ for the expected numbers, under the
posterior of $h$ and summed over the sequences, of sequences starting in $s$, of transitions
$s \to s'$ and of emissions of $o$ from $s$. The M-step is the HMM with real weights whose initial
weight of $s$ is $I(s) / N$, whose transition weight from $s$ to $s'$ is
$A(s, s') / \sum_{s''} A(s, s'')$, and whose emission weight of $o$ from $s$ is
$E(s, o) / \sum_{o'} E(s, o')$ (a quotient by $0$ is read as $0$). -/
noncomputable def mStep (h : ValidHMM S O) : HMM S O ℝ where
  init s := initCount T xs h s / N
  trans s s' := transCount T xs h s s' / ∑ s'', transCount T xs h s s''
  emit s o := emitCount T xs h s o / ∑ o', emitCount T xs h s o'

private theorem sum_sum_mul_sum {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    (r : ι → κ → ℝ) (g : ι → κ → σ → ℝ) :
    ∑ n, ∑ z, r n z * ∑ s, g n z s = ∑ s, ∑ n, ∑ z, r n z * g n z s := by
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_comm

private theorem sum_sum_mul_mul {ι κ : Type*} [Fintype ι] [Fintype κ] (r c : ι → κ → ℝ) (L : ℝ) :
    ∑ n, ∑ z, r n z * (c n z * L) = (∑ n, ∑ z, r n z * c n z) * L := by
  simp only [Finset.sum_mul, mul_assoc]

/-- **The Baum-Welch objective in terms of expected counts.** Let $S$ and $O$ be finite sets, let
$T$ be a natural number, and let $x_1, \dots, x_N$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$ of
observations in $O$. For a valid hidden Markov model $h$ on states $S$ and observations $O$
(positive initial, transition and emission probabilities, each distribution summing to one), write
$p_h(x, z)$ for the path weight of the observations $x$ and a state path $z = (z_0, \dots, z_T)$
(the joint of the EM model of $h$) and $p_h(z \mid x) = p_h(x, z) / \sum_{z'} p_h(x, z')$ for the
posterior of the path, the sums ranging over all paths $z : \{0, \dots, T\} \to S$. Let
$I_s = \sum_n \sum_{z \,:\, z_0 = s} p_h(z \mid x_n)$,
$A_{ss'} = \sum_n \sum_z p_h(z \mid x_n) \, \#\{t < T : z_t = s,\ z_{t+1} = s'\}$ and
$E_{so} = \sum_n \sum_z p_h(z \mid x_n) \, \#\{t \le T : z_t = s,\ x_{n,t} = o\}$ be the expected
counts of initial states, transitions and emissions. Then for every valid hidden Markov model $h'$
with initial probabilities $\pi'_s$, transition probabilities $a'_{ss'}$ and emission
probabilities $b'_{so}$, the EM objective
$Q(h' \mid h) = \sum_n \sum_z p_h(z \mid x_n) \log p_{h'}(x_n, z)$ equals
$\sum_{s} I_s \log \pi'_s + \sum_{s, s'} A_{ss'} \log a'_{ss'} +
\sum_{s, o} E_{so} \log b'_{so}$. -/
theorem emQ_eq (h' h : ValidHMM S O) :
    emQ (joint T) xs h' h = ∑ s, initCount T xs h s * log (h'.1.init s) +
      ∑ s, ∑ s', transCount T xs h s s' * log (h'.1.trans s s') +
      ∑ s, ∑ o, emitCount T xs h s o * log (h'.1.emit s o) := by
  simp only [emQ, log_joint, mul_add, Finset.sum_add_distrib]
  simp only [sum_sum_mul_sum, sum_sum_mul_mul, initCount, transCount, emitCount, post]

/-- **Data rich enough for the Baum-Welch M-step.** Observation sequences $x_0, \dots, x_{N-1}$
over a symbol set $O$ are rich for state paths $(z_0, \dots, z_T)$ when $N > 0$, $T > 0$, and
every symbol $o \in O$ is observed, that is $x_n(t) = o$ for some $n < N$ and some $t \le T$.

These are the data on which the M-step gives a valid HMM. -/
structure Rich (xs : Fin N → ℕ → O) : Prop where
  pos : 0 < N
  len : 0 < T
  covers : ∀ o, ∃ n, ∃ t : Fin (T + 1), xs n t = o

variable {T xs}

omit [DecidableEq S] [DecidableEq O] in
theorem post_pos (h : ValidHMM S O) (n : Fin N) (z : Fin (T + 1) → S) : 0 < post T xs h n z :=
  div_pos (joint_pos T h _ z) (Finset.sum_pos (fun z _ => joint_pos T h _ z) ⟨z, Finset.mem_univ z⟩)

private theorem sum_sum_pos {ι κ : Type*} [Fintype ι] [Fintype κ] {f : ι → κ → ℝ}
    (hf : ∀ n z, 0 ≤ f n z) (n₀ : ι) (z₀ : κ) (h₀ : 0 < f n₀ z₀) : 0 < ∑ n, ∑ z, f n z :=
  lt_of_lt_of_le h₀ <| le_trans (Finset.single_le_sum (fun z _ => hf n₀ z) (Finset.mem_univ z₀))
    (Finset.single_le_sum (f := fun n => ∑ z, f n z)
      (fun n _ => Finset.sum_nonneg fun z _ => hf n z) (Finset.mem_univ n₀))

omit [DecidableEq O] in
theorem initCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s : S) : 0 < initCount T xs h s := by
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pInit_nonneg T z s))
    ⟨0, hx.pos⟩ (fun _ => s) (mul_pos (post_pos h _ _) ?_)
  simp [pInit]

omit [DecidableEq O] in
theorem transCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s s' : S) :
    0 < transCount T xs h s s' := by
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pTrans_nonneg T z s s'))
    ⟨0, hx.pos⟩ (fun i => if i = 0 then s else s') (mul_pos (post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun t : Fin T =>
    if (fun i : Fin (T + 1) => if i = 0 then s else s') t.castSucc = s ∧
      (fun i : Fin (T + 1) => if i = 0 then s else s') t.succ = s' then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ ⟨0, hx.len⟩))
  simp

theorem emitCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s : S) (o : O) :
    0 < emitCount T xs h s o := by
  obtain ⟨n, t, ht⟩ := hx.covers o
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pEmit_nonneg T _ z s o))
    n (fun _ => s) (mul_pos (post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun t : Fin (T + 1) =>
    if (fun _ : Fin (T + 1) => s) t = s ∧ xs n t = o then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
  simp [ht]

omit [DecidableEq O] in
theorem sum_initCount (h : ValidHMM S O) : ∑ s, initCount T xs h s = N := by
  have := nonempty_of_valid h
  simp only [initCount]
  rw [← sum_sum_mul_sum]
  have hp : ∀ z : Fin (T + 1) → S, ∑ s, pInit T z s = 1 := fun z => by simp [pInit]
  simp only [hp, mul_one, post]
  simp [(isDist_posterior (fun h x z => joint_pos T h x z) h _).2]

theorem mStep_valid (hx : Rich T xs) (h : ValidHMM S O) : Valid (mStep T xs h) where
  init_pos s := div_pos (initCount_pos hx h s) (by exact_mod_cast hx.pos)
  init_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_initCount, div_self (by exact_mod_cast hx.pos.ne')]
  trans_pos s s' := div_pos (transCount_pos hx h s s')
    (Finset.sum_pos (fun s' _ => transCount_pos hx h s s') ⟨s', Finset.mem_univ _⟩)
  trans_sum s := by
    simp only [mStep]
    rw [← Finset.sum_div, div_self (Finset.sum_pos (fun s' _ => transCount_pos hx h s s')
      ⟨s, Finset.mem_univ _⟩).ne']
  emit_pos s o := div_pos (emitCount_pos hx h s o)
    (Finset.sum_pos (fun o _ => emitCount_pos hx h s o) ⟨o, Finset.mem_univ _⟩)
  emit_sum s := by
    obtain ⟨o⟩ : Nonempty O := by
      obtain ⟨n, t, _⟩ := hx.covers (xs ⟨0, hx.pos⟩ 0)
      exact ⟨xs n t⟩
    simp only [mStep]
    rw [← Finset.sum_div, div_self (Finset.sum_pos (fun o _ => emitCount_pos hx h s o)
      ⟨o, Finset.mem_univ _⟩).ne']

variable (T xs) in
/-- **One Baum-Welch step.** Let $S$ and $O$ be finite sets, let $T \ge 1$, and let
$x_1, \dots, x_N$ with $N \ge 1$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in
$O$ such that every $o \in O$ equals $x_{n,t}$ for some $n$ and some $t \le T$. For a valid hidden
Markov model $h$ on states $S$ and observations $O$ (positive initial, transition and emission
probabilities, each distribution summing to one), the Baum-Welch step maps $h$ to the hidden Markov
model with initial probabilities $I_s / N$, transition probabilities
$A_{ss'} / \sum_{s''} A_{ss''}$ and emission probabilities $E_{so} / \sum_{o'} E_{so'}$. Here
$I_s$, $A_{ss'}$ and $E_{so}$ are the expected numbers of initial states equal to $s$, of
transitions from $s$ to $s'$ at times $t < T$, and of emissions of $o$ from $s$ at times $t \le T$,
summed over $n$ under the posterior of $h$ over state paths $(z_0, \dots, z_T)$ given $x_n$. On
such data this hidden Markov model is again valid. -/
noncomputable def emStep (hx : Rich T xs) (h : ValidHMM S O) : ValidHMM S O :=
  ⟨mStep T xs h, mStep_valid hx h⟩

/-! ## Baum-Welch is an EM algorithm -/

variable (T xs) in
/-- **The Baum-Welch update maximizes the EM objective.** Let $S$ and $O$ be finite sets, let
$T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$
of observations in $O$ such that every $o \in O$ equals $x_{n,t}$ for some $n$ and some $t \le T$.
Consider the EM model of a hidden Markov model on states $S$ and observations $O$ whose latent
variable is the state path $z = (z_0, \dots, z_T)$ and whose joint $p_h(x, z)$ is the path weight,
with EM objective $Q(h' \mid h) = \sum_n \sum_z p_h(z \mid x_n) \log p_{h'}(x_n, z)$, where
$p_h(z \mid x) = p_h(x, z) / \sum_{z'} p_h(x, z')$ is the posterior of the path. Then for all valid
hidden Markov models $h$ and $h'$ (positive initial, transition and emission probabilities, each
distribution summing to one), $Q(h' \mid h) \le Q(\bar h \mid h)$, where $\bar h$ is the
Baum-Welch step applied to $h$ on these data. -/
theorem emQ_le_emStep (hx : Rich T xs) (h' h : ValidHMM S O) :
    emQ (joint T) xs h' h ≤ emQ (joint T) xs (emStep T xs hx h) h := by
  rw [emQ_eq, emQ_eq]
  have hN : (0 : ℝ) < N := by exact_mod_cast hx.pos
  refine add_le_add (add_le_add ?_ (Finset.sum_le_sum fun s _ => ?_))
    (Finset.sum_le_sum fun s _ => ?_)
  · have hg := sum_mul_log_le_sum_mul_log_div
      (fun s => (initCount_pos hx h s).le) (by rw [sum_initCount]; exact hN) h'.2.init_pos
      h'.2.init_sum
    rw [sum_initCount] at hg
    exact hg
  · exact sum_mul_log_le_sum_mul_log_div (fun s' => (transCount_pos hx h s s').le)
      (Finset.sum_pos (fun s' _ => transCount_pos hx h s s') ⟨s, Finset.mem_univ _⟩)
      (h'.2.trans_pos s) (h'.2.trans_sum s)
  · obtain ⟨o⟩ : Nonempty O := by
      obtain ⟨n, t, _⟩ := hx.covers (xs ⟨0, hx.pos⟩ 0)
      exact ⟨xs n t⟩
    exact sum_mul_log_le_sum_mul_log_div (fun o => (emitCount_pos hx h s o).le)
      (Finset.sum_pos (fun o _ => emitCount_pos hx h s o) ⟨o, Finset.mem_univ _⟩)
      (h'.2.emit_pos s) (h'.2.emit_sum s)

variable (T xs) in
/-- **Each Baum-Welch step does not decrease the log-likelihood.** Let $S$ and $O$ be finite
sets, let $T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$ such that every $o \in O$ equals $x_{n,t}$
for some $n$ and some $t \le T$. For every valid hidden Markov model $h$ on states $S$ and
observations $O$, $\ell(h) \le \ell(\bar h)$, where $\bar h$ is the Baum-Welch step applied to $h$
on these data and $\ell(h) = \sum_{n=1}^{N} \log \sum_z p_h(x_n, z)$ is the log-likelihood of the
EM model of $h$, the sum ranging over state paths $z = (z_0, \dots, z_T)$ and $p_h(x, z)$ being the
path weight. -/
theorem logLik_le_emStep (hx : Rich T xs) (h : ValidHMM S O) :
    logLik (joint T) xs h ≤ logLik (joint T) xs (emStep T xs hx h) := by
  have := nonempty_of_valid h
  exact logLik_le_of_emQ_le (fun h x z => joint_pos T h x z) xs (emQ_le_emStep T xs hx h h)

variable (T xs) in
/-- **The log-likelihood is monotone along the Baum-Welch iterates.** Let $S$ and $O$ be finite
sets, let $T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$ such that every $o \in O$ equals $x_{n,t}$
for some $n$ and some $t \le T$. Let $h_0$ be a valid hidden Markov model on states $S$ and
observations $O$ and let $h_t$ be the result of $t$ Baum-Welch steps from $h_0$ on these data.
Then $t \mapsto \ell(h_t)$ is monotone (nondecreasing in $t \in \mathbb{N}$), where
$\ell(h) = \sum_{n=1}^{N} \log \sum_z p_h(x_n, z)$ is the log-likelihood of the EM model of $h$,
the sum ranging over state paths $z = (z_0, \dots, z_T)$ and $p_h(x, z)$ being the path weight. -/
theorem logLik_iterate_emStep_monotone (hx : Rich T xs) (h₀ : ValidHMM S O) :
    Monotone fun t => logLik (joint T) xs ((emStep T xs hx)^[t] h₀) := by
  have := nonempty_of_valid h₀
  exact logLik_iterate_monotone (fun h x z => joint_pos T h x z) xs
    (fun h => emQ_le_emStep T xs hx h h) h₀

omit [DecidableEq S] [DecidableEq O] in
/-- **The Baum-Welch log-likelihood is the HMM log-likelihood.** Let $S$ and $O$ be finite sets,
let $T$ be a natural number, and let $x_1, \dots, x_N$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$. For every valid hidden Markov model $h$
on states $S$ and observations $O$, the log-likelihood of its EM model (latent state paths
$(z_0, \dots, z_T)$, joint the path weight) on these data equals $\sum_{n=1}^{N} \log L_h(x_n)$,
where $L_h(x_n)$ is the likelihood of the observations $x_{n,0}, \dots, x_{n,T}$ under $h$: the
total path weight over all state paths $(z_0, \dots, z_T)$. -/
theorem logLik_eq (h : ValidHMM S O) :
    logLik (joint T) xs h = ∑ n, log (likelihood h.1 (xs n) T) := rfl

end Cslib.MachineLearning.Sequence.BaumWelch
