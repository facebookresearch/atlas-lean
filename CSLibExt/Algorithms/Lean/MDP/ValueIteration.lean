/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Value iteration for finite discounted Markov decision processes

A finite Markov decision process (`MDP S A K`) has finitely many states `S` and actions `A`, a
reward `reward s a` and transition probabilities `prob s a s'` (`Stochastic`: nonnegative, each
row summing to `1`), with values in an ordered field `K`. For a discount factor `γ`, the Bellman
optimality operator is

  `bellman M γ V s = max_a (reward s a + γ * ∑ s', prob s a s' * V s')`,

and value iteration applies it repeatedly (`valueIteration M γ n V = (bellman M γ)^[n] V`, the
mathematical iterate; `valueIterationVec` is the tabulated program on `Fin m` states, equal to it by
`valueIterationVec_get`). For a
deterministic stationary policy `π : S → A`, `policyBellman M γ π` evaluates `π` instead of
maximizing.

Main results, for `0 ≤ γ < 1` and real values (Puterman, *Markov Decision Processes*,
Section 6.3; Bellman 1957):

* `abs_bellman_sub_le` (any ordered field): if `|V s - W s| ≤ d` for all `s`, then
  `|bellman M γ V s - bellman M γ W s| ≤ γ * d`; so `bellman_contracting`: the operator is
  `ContractingWith γ.toNNReal` in the sup metric on `S → ℝ`, and has a unique fixed point
  `optimalValue` (`bellman_optimalValue`, `eq_optimalValue_of_bellman_eq`).
* `tendsto_valueIteration`: value iteration converges to `optimalValue` from any start, with the
  a priori bound `dist (valueIteration M γ n V) (optimalValue ..) ≤ dist V (bellman M γ V) * γ ^ n
  / (1 - γ)` (`dist_valueIteration_le`) and the stopping test `dist_optimalValue_le`.
* The value of a policy, `policyValue`, is the unique fixed point of `policyBellman`
  (`policyBellman_policyValue`, `eq_policyValue_of_policyBellman_eq`); no policy beats
  `optimalValue` (`policyValue_le_optimalValue`), and a policy greedy with respect to
  `optimalValue` attains it (`policyValue_greedy`).

Values are defined by their Bellman equations; their identification with expected discounted
returns of the induced Markov chain (Puterman, Theorem 6.1.1) is not formalized here.

## Cost model

No `TimeM` cost model: these are mathematical statements about the operators.
`valueIterationVec` stores each update, so one update reads `|S| |A| |S|` stored values (one
multiplication each), and `dist_valueIteration_le` bounds how many updates reach a given accuracy.
`valueIteration` itself is the mathematical iterate: evaluating it directly recomputes earlier
iterates and takes exponential time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

/-- **Markov decision process.** A Markov decision process with states in $S$, actions in $A$ and
values in $K$ consists of a reward $r(s, a) \in K$ for taking action $a$ in state $s$ and, for all
states $s, s'$ and actions $a$, a value $p(s, a, s') \in K$, the probability of moving from $s$ to
$s'$ under action $a$.

No condition is imposed here: finiteness of the states and actions, an order on $K$ and the
stochasticity of $p$ are hypotheses of the results that use them. -/
structure MDP (S A K : Type*) where
  /-- The reward for taking action `a` in state `s`. -/
  reward : S → A → K
  /-- The probability of moving from `s` to `s'` under action `a`. -/
  prob : S → A → S → K

variable {S A K : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Stochastic Markov decision process.** A Markov decision process with finitely many states
and transition probabilities $P(s,a,s')$ in a field $K$ with a linear order is stochastic when
$0 \le P(s,a,s')$ for all states $s, s'$ and actions $a$, and
$\sum_{s'} P(s,a,s') = 1$ for every state $s$ and action $a$. -/
def MDP.Stochastic (M : MDP S A K) : Prop :=
  (∀ s a s', 0 ≤ M.prob s a s') ∧ ∀ s a, ∑ s', M.prob s a s' = 1

/-- **Q-value of an action.** Let $M$ be a Markov decision process with a finite set of states
$S$ and with rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ in a field $K$, and let
$\gamma \in K$. The Q-value of action $a$ in state $s$ against a value estimate
$V : S \to K$ is $r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V(s')$. -/
def qValue (M : MDP S A K) (γ : K) (V : S → K) (s : S) (a : A) : K :=
  M.reward s a + γ * ∑ s', M.prob s a s' * V s'

/-- **Bellman optimality operator.** Let $M$ be a Markov decision process with finitely many
states $s$, a nonempty finite set of actions $a$, rewards $r(s, a)$ and transition probabilities
$p(s, a, s')$ in a field $K$ carrying a linear order, and let $\gamma \in K$ be a discount factor.
The Bellman optimality operator $T$ sends a function $V$ from states to $K$ to the function
$$(TV)(s) = \max_a \Big( r(s, a) + \gamma \sum_{s'} p(s, a, s') V(s') \Big),$$
the largest action value in state $s$. -/
def bellman (M : MDP S A K) (γ : K) (V : S → K) : S → K :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (qValue M γ V s)

/-- **Bellman operator of a policy.** Let $M$ be a Markov decision process with a finite set of
states $S$, a set of actions $A$, and rewards $r(s,a)$ and transition probabilities $P(s,a,s')$
in a field $K$, let $\gamma \in K$ be a discount factor, and let $\pi : S \to A$ be a
deterministic stationary policy. The Bellman operator of $\pi$ sends a value estimate
$V : S \to K$ to the function
$s \mapsto r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V(s')$. -/
def policyBellman (M : MDP S A K) (γ : K) (π : S → A) (V : S → K) : S → K :=
  fun s => qValue M γ V s (π s)

/-- **Value iteration.** Let $M$ be a Markov decision process with finitely many states, a
nonempty finite set of actions, and rewards and transition probabilities in a field $K$ carrying
a linear order, let $\gamma \in K$, and let $T$ be the Bellman optimality operator of $M$ with
discount $\gamma$. For $n \in \mathbb{N}$ and a function $V$ from states to $K$, $n$ steps of
value iteration from $V$ give the $n$-fold iterate $T^n V$, where $T^0 V = V$.

Evaluated directly, this definition recomputes earlier iterates; tabulated value iteration
stores each update instead. -/
def valueIteration (M : MDP S A K) (γ : K) (n : ℕ) (V : S → K) : S → K :=
  (bellman M γ)^[n] V

/-- **Tabulated value iteration.** Let $M$ be a Markov decision process with states
$\{0, \dots, m-1\}$, a nonempty finite set of actions, and rewards and transition probabilities
in a field $K$ carrying a linear order, let $\gamma \in K$, and let $T$ be the Bellman optimality
operator of $M$ with discount $\gamma$. Tabulated value iteration takes a number of steps
$n \in \mathbb{N}$ and a vector $v \in K^m$, read as a function on states: with $0$ steps it
returns $v$, and with $k + 1$ steps it computes the vector $\bigl((Tv)(0), \dots, (Tv)(m-1)\bigr)$
and then runs $k$ steps from that vector.

Each update is stored as a vector, so update $k + 1$ reads the stored values of update $k$. -/
def valueIterationVec {m : ℕ} (M : MDP (Fin m) A K) (γ : K) : ℕ → Vector K m → Vector K m
  | 0, v => v
  | k + 1, v => valueIterationVec M γ k (Vector.ofFn (bellman M γ fun s => v.get s))

/-- **Greedy policy.** Let $M$ be a Markov decision process with finitely many states, a nonempty
finite set of actions, and rewards $r(s, a)$ and transition probabilities $p(s, a, s')$ in a field
$K$ carrying a linear order, let $\gamma \in K$, and let $V$ be a function from states to $K$. The
greedy policy for $V$ chooses in each state $s$ an action $a$ maximizing the action value
$r(s, a) + \gamma \sum_{s'} p(s, a, s') V(s')$; when several actions attain the maximum, one of
them is fixed by choice. -/
noncomputable def greedy (M : MDP S A K) (γ : K) (V : S → K) (s : S) : A :=
  (Finset.univ.exists_max_image (qValue M γ V s) Finset.univ_nonempty).choose

variable {M : MDP S A K} {γ : K}

omit [Fintype S] [IsStrictOrderedRing K] in
/-- **Tabulated value iteration is correct.** Let $M$ be a Markov decision process with states
$\{0, \dots, m-1\}$, a nonempty finite set of actions and values in a field $K$ with a linear
order, let $\gamma \in K$, and let $T$ be the Bellman optimality operator of $M$ with discount
$\gamma$. For every $n \in \mathbb{N}$, every vector $v \in K^m$ and every state $s$, entry $s$ of
the vector computed by $n$ steps of tabulated value iteration from $v$ equals $(T^n v)(s)$, where
$v$ is read as a function on states. -/
theorem valueIterationVec_get {m : ℕ} (M : MDP (Fin m) A K) (γ : K) :
    ∀ (n : ℕ) (v : Vector K m) (s : Fin m),
      (valueIterationVec M γ n v).get s = valueIteration M γ n (fun s => v.get s) s
  | 0, _, _ => rfl
  | n + 1, v, s => by
      have h : (fun s => (Vector.ofFn (bellman M γ fun s => v.get s)).get s) =
          bellman M γ fun s => v.get s := by
        funext s'
        change (Vector.ofFn _)[s'.val] = _
        rw [Vector.getElem_ofFn]
      rw [valueIterationVec, valueIterationVec_get M γ n, valueIteration, valueIteration,
        Function.iterate_succ_apply, h]

/-! ## Order and contraction facts, in any ordered field -/

omit [Fintype A] [Nonempty A] in
theorem qValue_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} (h : V ≤ W) (s : S) (a : A) :
    qValue M γ V s a ≤ qValue M γ W s a := by
  unfold qValue
  gcongr with s'
  all_goals first | exact hM.1 s a s' | exact h s'

theorem bellman_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} (h : V ≤ W) :
    bellman M γ V ≤ bellman M γ W := fun s =>
  Finset.sup'_le _ _ fun a _ => (qValue_mono hM hγ h s a).trans (Finset.le_sup' _ (by simp))

omit [Fintype A] [Nonempty A] in
theorem policyBellman_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : S → A) {V W : S → K}
    (h : V ≤ W) : policyBellman M γ π V ≤ policyBellman M γ π W := fun s =>
  qValue_mono hM hγ h s (π s)

omit [IsStrictOrderedRing K] in
/-- **A policy's Bellman update is at most the optimal one.** Let $M$ be a Markov decision
process with a finite set of states $S$, a finite nonempty set of actions $A$, and rewards
$r(s,a)$ and transition probabilities $P(s,a,s')$ in a field $K$ with a linear order, let
$\gamma \in K$, and let $\pi : S \to A$ be a deterministic stationary policy. For every
$V : S \to K$ and every state $s$, the Bellman operator of $\pi$ applied to $V$ is at most the
Bellman optimality operator applied to $V$ at $s$:
$r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V(s') \le
\max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V(s')\bigr)$. -/
theorem policyBellman_le_bellman (π : S → A) (V : S → K) :
    policyBellman M γ π V ≤ bellman M γ V := fun s =>
  Finset.le_sup' (qValue M γ V s) (Finset.mem_univ (π s))

omit [IsStrictOrderedRing K] in
/-- **The greedy action attains the Bellman maximum.** Let $M$ be a Markov decision process
with a finite set of states $S$, a finite nonempty set of actions, and rewards $r(s,a)$ and
transition probabilities $P(s,a,s')$ in a field $K$ with a linear order, and let $\gamma \in K$.
For every $V : S \to K$ and every state $s$, the action $g$ that the greedy policy for $V$
chooses in $s$ satisfies
$r(s,g) + \gamma \sum_{s'} P(s,g,s') \, V(s') =
\max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V(s')\bigr)$, so its action value equals
the value of the Bellman optimality operator applied to $V$ at $s$. -/
theorem qValue_greedy (V : S → K) (s : S) :
    qValue M γ V s (greedy M γ V s) = bellman M γ V s := by
  have h := (Finset.univ.exists_max_image (qValue M γ V s) Finset.univ_nonempty).choose_spec
  exact le_antisymm (Finset.le_sup' _ h.1) (Finset.sup'_le _ _ fun a ha => h.2 a ha)

omit [IsStrictOrderedRing K] in
theorem policyBellman_greedy (V : S → K) : policyBellman M γ (greedy M γ V) V = bellman M γ V :=
  funext fun s => qValue_greedy V s

omit [Fintype A] [Nonempty A] in
theorem abs_qValue_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} {d : K}
    (h : ∀ s, |V s - W s| ≤ d) (s : S) (a : A) :
    |qValue M γ V s a - qValue M γ W s a| ≤ γ * d := by
  have e : qValue M γ V s a - qValue M γ W s a = γ * ∑ s', M.prob s a s' * (V s' - W s') := by
    simp only [qValue, mul_sub, Finset.sum_sub_distrib]; ring
  rw [e, abs_mul, abs_of_nonneg hγ]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  calc |∑ s', M.prob s a s' * (V s' - W s')|
      ≤ ∑ s', |M.prob s a s' * (V s' - W s')| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', M.prob s a s' * |V s' - W s'| := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (hM.1 s a s')]
    _ ≤ ∑ s', M.prob s a s' * d :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') (hM.1 s a s')
    _ = d := by rw [← Finset.sum_mul, hM.2 s a, one_mul]

/-- **The Bellman operator contracts by $\gamma$.** Let $M$ be a Markov decision process with
finitely many states, a nonempty finite set of actions, and rewards and stochastic transition
probabilities in a linearly ordered field $K$, let $\gamma \ge 0$ in $K$, and let $T$ be the
Bellman optimality operator of $M$ with discount $\gamma$. If two functions $V, W$ from states
to $K$ satisfy $|V(s) - W(s)| \le d$ for every state $s$, where $d \in K$, then
$|(TV)(s) - (TW)(s)| \le \gamma d$ for every state $s$. -/
theorem abs_bellman_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} {d : K}
    (h : ∀ s, |V s - W s| ≤ d) (s : S) : |bellman M γ V s - bellman M γ W s| ≤ γ * d := by
  have hq := abs_qValue_sub_le hM hγ h s
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have := (abs_sub_le_iff.1 (hq a)).1
    have := Finset.le_sup' (qValue M γ W s) (Finset.mem_univ a)
    unfold bellman; linarith
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have := (abs_sub_le_iff.1 (hq a)).2
    have := Finset.le_sup' (qValue M γ V s) (Finset.mem_univ a)
    unfold bellman; linarith

omit [Fintype A] [Nonempty A] in
theorem abs_policyBellman_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : S → A) {V W : S → K}
    {d : K} (h : ∀ s, |V s - W s| ≤ d) (s : S) :
    |policyBellman M γ π V s - policyBellman M γ π W s| ≤ γ * d :=
  abs_qValue_sub_le hM hγ h s (π s)

/-! ## Real values: contraction, value iteration, optimality -/

variable {M : MDP S A ℝ} {γ : ℝ}

/-- A pointwise `γ`-contraction in absolute value is `ContractingWith γ` in the sup metric. -/
private theorem contractingWith_of_abs_le {T : (S → ℝ) → S → ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hT : ∀ (V W : S → ℝ) (d : ℝ), (∀ s, |V s - W s| ≤ d) → ∀ s, |T V s - T W s| ≤ γ * d) :
    ContractingWith γ.toNNReal T := by
  refine ⟨Real.toNNReal_lt_one.2 hγ1, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
  rw [Real.coe_toNNReal γ hγ0, dist_pi_le_iff (by positivity)]
  intro s
  rw [Real.dist_eq]
  exact hT V W _ (fun s' => by rw [← Real.dist_eq]; exact dist_le_pi_dist V W s') s

/-- **Bellman's operator is a contraction.** Let $M$ be a Markov decision process with finitely
many states, a nonempty finite set of actions, real rewards and stochastic transition
probabilities, and let $0 \le \gamma < 1$. Then the Bellman optimality operator $T$ of $M$ with
discount $\gamma$, acting on real-valued functions on the states with the sup metric, is a
contraction with constant $\gamma$: for all such functions $V$ and $W$,
$\|TV - TW\|_\infty \le \gamma \|V - W\|_\infty$.

Source: Puterman, Theorem 6.2.3. -/
theorem bellman_contracting (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith γ.toNNReal (bellman M γ) :=
  contractingWith_of_abs_le hγ0 hγ1 fun _ _ _ h => abs_bellman_sub_le hM hγ0 h

omit [Fintype A] [Nonempty A] in
theorem policyBellman_contracting (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A) : ContractingWith γ.toNNReal (policyBellman M γ π) :=
  contractingWith_of_abs_le hγ0 hγ1 fun _ _ _ h => abs_policyBellman_sub_le hM hγ0 π h

/-- **Optimal value of a discounted Markov decision process.** Let $M$ be a Markov decision
process with finitely many states $S$, finitely many actions (at least one), real rewards
$r(s,a)$, and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over
$s'$, and let $0 \le \gamma < 1$. The optimal value of $M$ with discount $\gamma$ is the unique
function $V^* : S \to \mathbb{R}$ that is a fixed point of the Bellman optimality operator, that
is, $V^*(s) = \max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V^*(s')\bigr)$ for every
state $s$. It exists and is unique because this operator is a $\gamma$-contraction in the sup
metric. -/
noncomputable def optimalValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) : S → ℝ :=
  ContractingWith.fixedPoint _ (bellman_contracting hM hγ0 hγ1)

/-- **Value of a policy.** Let $M$ be a Markov decision process with a finite set of states $S$,
a set of actions $A$, real rewards $r(s,a)$, and transition probabilities $P(s,a,s')$ that are
nonnegative and sum to $1$ over $s'$, let $0 \le \gamma < 1$, and let $\pi : S \to A$ be a
deterministic stationary policy. The value of $\pi$ is the unique function
$V^\pi : S \to \mathbb{R}$ that is a fixed point of the Bellman operator of $\pi$, that is,
$V^\pi(s) = r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V^\pi(s')$ for every state $s$.
It exists and is unique because this operator is a $\gamma$-contraction in the sup metric. -/
noncomputable def policyValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) : S → ℝ :=
  ContractingWith.fixedPoint _ (policyBellman_contracting hM hγ0 hγ1 π)

variable (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hM hγ0 hγ1

/-- **The optimal value solves the Bellman optimality equation.** Let $M$ be a Markov decision
process with finitely many states, a nonempty finite set of actions, real rewards and stochastic
transition probabilities, and let $0 \le \gamma < 1$. Then the optimal value $V^*$ of $M$ with
discount $\gamma$ is a fixed point of the Bellman optimality operator $T$ of $M$ with discount
$\gamma$: $T V^* = V^*$. -/
theorem bellman_optimalValue : bellman M γ (optimalValue M γ hM hγ0 hγ1) =
    optimalValue M γ hM hγ0 hγ1 :=
  ContractingWith.fixedPoint_isFixedPt (bellman_contracting hM hγ0 hγ1)

/-- **Uniqueness of the solution of the Bellman optimality equation.** Let $M$ be a Markov
decision process with finitely many states, a nonempty finite set of actions, real rewards and
stochastic transition probabilities, and let $0 \le \gamma < 1$. If a real-valued function $V$ on
the states satisfies $TV = V$, where $T$ is the Bellman optimality operator of $M$ with discount
$\gamma$, then $V$ is the optimal value of $M$ with discount $\gamma$. -/
theorem eq_optimalValue_of_bellman_eq {V : S → ℝ} (h : bellman M γ V = V) :
    V = optimalValue M γ hM hγ0 hγ1 :=
  ContractingWith.fixedPoint_unique (bellman_contracting hM hγ0 hγ1) h

omit [Fintype A] [Nonempty A] in
/-- **A policy's value satisfies its Bellman equation.** Let $M$ be a Markov decision process
with finitely many states, real rewards $r(s,a)$, and transition probabilities $P(s,a,s')$ that
are nonnegative and sum to $1$ over $s'$, let $0 \le \gamma < 1$, and let $\pi$ be a
deterministic stationary policy with value $V^\pi$. Then $V^\pi$ is a fixed point of the
Bellman operator of $\pi$: for every state $s$,
$V^\pi(s) = r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V^\pi(s')$. -/
theorem policyBellman_policyValue (π : S → A) :
    policyBellman M γ π (policyValue M γ hM hγ0 hγ1 π) = policyValue M γ hM hγ0 hγ1 π :=
  ContractingWith.fixedPoint_isFixedPt (policyBellman_contracting hM hγ0 hγ1 π)

omit [Fintype A] [Nonempty A] in
/-- **Uniqueness of the solution of a policy's Bellman equation.** Let $M$ be a Markov decision
process with finitely many states, real rewards and stochastic transition probabilities, let
$0 \le \gamma < 1$, and let $\pi$ be a deterministic stationary policy, a map from states to
actions. If a real-valued function $V$ on the states satisfies $T_\pi V = V$, where $T_\pi$ is the
Bellman operator of $\pi$ in $M$ with discount $\gamma$, then $V$ is the value of $\pi$. -/
theorem eq_policyValue_of_policyBellman_eq (π : S → A) {V : S → ℝ}
    (h : policyBellman M γ π V = V) : V = policyValue M γ hM hγ0 hγ1 π :=
  ContractingWith.fixedPoint_unique (policyBellman_contracting hM hγ0 hγ1 π) h

/-- **Value iteration converges.** Let $M$ be a Markov decision process with finitely many states
$S$, a nonempty finite set of actions, real rewards and stochastic transition probabilities
(nonnegative, each row summing to $1$), and let $0 \le \gamma < 1$ be a discount factor. Let $T$ be
the Bellman optimality operator of $M$ with discount $\gamma$. Then for every initial value
function $V : S \to \mathbb{R}$, the value iterates $T^n V$ converge to the optimal value of $M$
with discount $\gamma$ as $n \to \infty$. -/
theorem tendsto_valueIteration (V : S → ℝ) :
    Tendsto (fun n => valueIteration M γ n V) atTop (𝓝 (optimalValue M γ hM hγ0 hγ1)) :=
  ContractingWith.tendsto_iterate_fixedPoint (bellman_contracting hM hγ0 hγ1) V

/-- **A priori error bound for value iteration.** Let $M$ be a Markov decision process with
finitely many states, a nonempty finite set of actions, real rewards and stochastic transition
probabilities, let $0 \le \gamma < 1$, and let $T$ be the Bellman optimality operator and $V^*$
the optimal value of $M$ with discount $\gamma$. For every real-valued function $V$ on the states
and every $n \in \mathbb{N}$, the result $T^n V$ of $n$ steps of value iteration from $V$ satisfies
$\|T^n V - V^*\|_\infty \le \|V - TV\|_\infty \, \gamma^n / (1 - \gamma)$, where
$\|\cdot\|_\infty$ is the sup norm. -/
theorem dist_valueIteration_le (V : S → ℝ) (n : ℕ) :
    dist (valueIteration M γ n V) (optimalValue M γ hM hγ0 hγ1) ≤
      dist V (bellman M γ V) * γ ^ n / (1 - γ) := by
  have := ContractingWith.apriori_dist_iterate_fixedPoint_le (bellman_contracting hM hγ0 hγ1) V n
  rwa [Real.coe_toNNReal γ hγ0] at this

/-- **Stopping test.** Let $M$ be a Markov decision process with finitely many states,
a nonempty finite set of actions, real rewards and stochastic transition probabilities, let
$0 \le \gamma < 1$, and let $T$ be the Bellman optimality operator and $V^*$ the optimal value of
$M$ with discount $\gamma$. For every real-valued function $V$ on the states,
$\|V - V^*\|_\infty \le \|V - TV\|_\infty / (1 - \gamma)$, where $\|\cdot\|_\infty$ is the sup
norm. So if one Bellman update moves $V$ by at most $\varepsilon$, then $V$ is within
$\varepsilon / (1 - \gamma)$ of the optimal value. -/
theorem dist_optimalValue_le (V : S → ℝ) :
    dist V (optimalValue M γ hM hγ0 hγ1) ≤ dist V (bellman M γ V) / (1 - γ) := by
  have := ContractingWith.dist_fixedPoint_le (bellman_contracting hM hγ0 hγ1) V
  rwa [Real.coe_toNNReal γ hγ0] at this

/-- **No policy beats the optimal value.** Let $M$ be a Markov decision process with finitely
many states, finitely many actions (at least one), real rewards $r(s,a)$, and transition
probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let
$0 \le \gamma < 1$. For every deterministic stationary policy $\pi$, the value $V^\pi$ of $\pi$
is at most the optimal value $V^*$ in every state: $V^\pi(s) \le V^*(s)$ for all states $s$. -/
theorem policyValue_le_optimalValue (π : S → A) :
    policyValue M γ hM hγ0 hγ1 π ≤ optimalValue M γ hM hγ0 hγ1 := by
  set V := optimalValue M γ hM hγ0 hγ1
  have hle : ∀ n, (policyBellman M γ π)^[n] V ≤ V := by
    intro n
    induction n with
    | zero => exact le_refl V
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc policyBellman M γ π ((policyBellman M γ π)^[n] V)
            ≤ policyBellman M γ π V := policyBellman_mono hM hγ0 π ih
          _ ≤ bellman M γ V := policyBellman_le_bellman π V
          _ = V := bellman_optimalValue hM hγ0 hγ1
  have ht := ContractingWith.tendsto_iterate_fixedPoint (policyBellman_contracting hM hγ0 hγ1 π) V
  intro s
  exact le_of_tendsto' ((continuous_apply s).continuousAt.tendsto.comp ht) fun n => hle n s

/-- **A greedy policy for the optimal value is optimal.** Let $M$ be a Markov decision process
with finitely many states, finitely many actions (at least one), real rewards $r(s,a)$, and
transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, let
$0 \le \gamma < 1$, and let $V^*$ be the optimal value. Let $\pi$ be the greedy policy for
$V^*$, which in each state $s$ chooses an action $a$ maximizing
$r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V^*(s')$. Then the value of $\pi$ equals $V^*$. -/
theorem policyValue_greedy :
    policyValue M γ hM hγ0 hγ1 (greedy M γ (optimalValue M γ hM hγ0 hγ1)) =
      optimalValue M γ hM hγ0 hγ1 := by
  refine (eq_policyValue_of_policyBellman_eq hM hγ0 hγ1 _ ?_).symm
  rw [policyBellman_greedy, bellman_optimalValue hM hγ0 hγ1]

end Cslib.Algorithms.Lean.MarkovDecision
