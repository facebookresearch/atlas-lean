/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Hidden Markov models: the forward algorithm and Viterbi

A hidden Markov model (Rabiner, *A tutorial on hidden Markov models and selected applications in
speech recognition*, Proc. IEEE 77, 1989; Bishop, *Pattern Recognition and Machine Learning*,
Section 13.2) has hidden states `S`, observations `O`, initial weights `init`, transition weights
`trans` and emission weights `emit`. `pathProb t z` is the joint weight of a state path
`z : Fin (t + 1) → S` and the observations `x 0, …, x t`, and `likelihood t` is the total weight
of all paths. The weights live in any semiring for the forward algorithm, which keeps the order of
multiplication along a path (with probabilities in `ℝ` or `ℚ`, `likelihood` is `p(x 0, …, x t)`),
and in a linearly ordered commutative one, nonnegative (`HMM.Nonneg`), for Viterbi.

Main results:

* `forward_eq`: the forward variables are the path sums ending in each state;
  `likelihood_eq_sum_forward`: **the forward algorithm computes the likelihood**.
* `pathProb_le_viterbi`, `exists_pathProb_eq_viterbi`: the Viterbi variables are the largest path
  weights ending in each state; `sup'_viterbi_eq`: **Viterbi computes the MAP value**.
* On `Fin n`, tabulated: `forwardTab`, `likelihoodTab_eq` (`O(t n²)` operations); `viterbiTab`,
  backpointers `back`, `bestPath` (`pathProb_bestPath`), and `viterbiPath` (via `argmaxVec`) with
  `pathProb_le_viterbiPath`: **the backtracked Viterbi path is a most probable path**.

## Cost model

The cost is the number of semiring operations. `forwardTab` and `viterbiTab` do `O(n²)` per step,
`O(t n²)` in total (each step takes the previous table as an argument, so no value is
recomputed). `bestPath` recomputes the table at each backtracking step, `O(t² n²)` in total; a
single forward pass storing the backpointers would give `O(t n²)`. The untabulated `forward`,
`viterbi` and `likelihood` are specifications: evaluating them directly takes exponential time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

variable {S O R : Type*}

/-- **Hidden Markov model.** A hidden Markov model with a set of states $S$, a set of observations
$O$ and weights in $R$ consists of an initial weight $\pi(s) \in R$ for each state $s$, a
transition weight $a(s, s') \in R$ for each pair of states, the weight of a transition from $s$
to $s'$, and an emission weight $e(s, o) \in R$ for each state $s$ and observation $o$, the
weight of emitting $o$ from $s$.

No structure on $R$ and no normalization of the weights is required. -/
structure HMM (S O R : Type*) where
  /-- The initial weight of each state. -/
  init : S → R
  /-- The weight of a transition from the first state to the second. -/
  trans : S → S → R
  /-- The weight of emitting an observation from a state. -/
  emit : S → O → R

section Forward

variable [Fintype S] [Semiring R] (h : HMM S O R) (x : ℕ → O)

/-- **Joint weight of a state path and the observations.** For a hidden Markov model $h$ with
initial weights $\pi$, transition weights $a$ and emission weights $b$ in a semiring, observations
$x_0, x_1, \dots$ and $t \in \mathbb{N}$, the joint weight of a state path $z = (z_0, \dots, z_t)$
and $x_0, \dots, x_t$ is the product, taken from left to right,
$\pi(z_0)\, b(z_0, x_0)\, a(z_0, z_1)\, b(z_1, x_1) \cdots a(z_{t-1}, z_t)\, b(z_t, x_t)$. -/
def pathProb : (t : ℕ) → (Fin (t + 1) → S) → R
  | 0, z => h.init (z 0) * h.emit (z 0) (x 0)
  | t + 1, z => pathProb t (Fin.init z) * h.trans (z (Fin.last t).castSucc) (z (Fin.last (t + 1))) *
      h.emit (z (Fin.last (t + 1))) (x (t + 1))

/-- **Likelihood of the observations.** For a hidden Markov model $h$ with a finite set of states
$S$ and weights in a semiring, observations $x_0, x_1, \dots$ and $t \in \mathbb{N}$, the
likelihood of $x_0, \dots, x_t$ is the sum, over all state paths
$z = (z_0, \dots, z_t) \in S^{t+1}$, of the joint weight of $z$ and $x_0, \dots, x_t$. -/
def likelihood (t : ℕ) : R := ∑ z : Fin (t + 1) → S, pathProb h x t z

/-- **Forward variables of a hidden Markov model.** Let $h$ be a hidden Markov model with a finite
set of states $S$ and weights in a semiring $R$, with initial weights $\pi(s)$, transition weights
$a(s', s)$ from $s'$ to $s$ and emission weights $e(s, o)$ of the observation $o$ from the state
$s$, and let $x$ be an observation sequence. The forward variables are defined by
$\alpha_0(s) = \pi(s) \, e(s, x_0)$ and
$\alpha_{t+1}(s) = \left(\sum_{s'} \alpha_t(s') \, a(s', s)\right) e(s, x_{t+1})$, the sum
running over all states $s'$.

The forward variable $\alpha_t(s)$ is the weight of the observations $x_0, \dots, x_t$ with the
state at time $t$ equal to $s$. -/
def forward : ℕ → S → R
  | 0, s => h.init s * h.emit s (x 0)
  | t + 1, s => (∑ s', forward t s' * h.trans s' s) * h.emit s (x (t + 1))

omit [Fintype S] in
theorem pathProb_snoc (t : ℕ) (z : Fin (t + 1) → S) (s : S) :
    pathProb h x (t + 1) (Fin.snoc z s) = pathProb h x t z * h.trans (z (Fin.last t)) s *
      h.emit s (x (t + 1)) := by
  simp [pathProb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]

theorem sum_snoc {M : Type*} [AddCommMonoid M] {t : ℕ} (f : (Fin (t + 2) → S) → M) :
    ∑ z, f z = ∑ z : Fin (t + 1) → S, ∑ s, f (Fin.snoc z s) := by
  rw [← (Fin.snocEquiv fun _ => S).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- **The forward variables are path sums.** Let $h$ be a hidden Markov model with a finite set of
states $S$ and weights in a semiring $R$, and let $x$ be an observation sequence. For every time
$t$ and every state $s$, the forward variable $\alpha_t(s)$ equals $\sum_z p_t(z)$, the sum
running over the state paths $z = (z_0, \dots, z_t) \in S^{t+1}$ with $z_t = s$, where $p_t(z)$
is the joint weight of $z$ and the observations $x_0, \dots, x_t$. -/
theorem forward_eq [DecidableEq S] : ∀ (t : ℕ) (s : S),
    forward h x t s = ∑ z : Fin (t + 1) → S, if z (Fin.last t) = s then pathProb h x t z else 0
  | 0, s => by
      rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
      simp [forward, pathProb, Fin.last]
  | t + 1, s => by
      rw [sum_snoc]
      simp only [Fin.snoc_last, pathProb_snoc, forward, forward_eq t]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
      simp

/-- **The forward algorithm computes the likelihood.** Let $h$ be a hidden Markov model with a
finite set of states $S$, initial weights $\pi$, transition weights $a$ and emission weights $b$ in
a semiring, and let $x_0, x_1, \dots$ be observations. Let $\alpha$ be the forward variables,
$\alpha_0(s) = \pi(s)\, b(s, x_0)$ and
$\alpha_{t+1}(s) = \bigl(\sum_{s' \in S} \alpha_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. Then for
every $t \in \mathbb{N}$ the likelihood of $x_0, \dots, x_t$ equals $\sum_{s \in S} \alpha_t(s)$. -/
theorem likelihood_eq_sum_forward (t : ℕ) :
    likelihood h x t = ∑ s, forward h x t s := by
  classical
  simp only [forward_eq, likelihood]
  rw [Finset.sum_comm]
  simp

end Forward

/-! ## Viterbi -/

section Viterbi

variable [Fintype S] [Nonempty S] [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
  (h : HMM S O R) (x : ℕ → O)

/-- **The Viterbi variables of a hidden Markov model.** Let $h$ be a hidden Markov model with a
finite nonempty set of states $S$, initial weights $\pi(s)$, transition weights $a(s', s)$ and
emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. The Viterbi variables $V_t(s)$, for
$t \in \mathbb{N}$ and $s \in S$, are defined by $V_0(s) = \pi(s) \, b(s, x_0)$ and

$$V_{t+1}(s) = \Big(\max_{s' \in S} V_t(s') \, a(s', s)\Big) \, b(s, x_{t+1}).$$

When all weights are nonnegative, $V_t(s)$ is the largest joint weight of a state path of length
$t + 1$ ending in $s$ and the observations $x_0, \dots, x_t$. -/
def viterbi : ℕ → S → R
  | 0, s => h.init s * h.emit s (x 0)
  | t + 1, s => Finset.univ.sup' Finset.univ_nonempty (fun s' => viterbi t s' * h.trans s' s) *
      h.emit s (x (t + 1))

/-- **Hidden Markov models with nonnegative weights.** A hidden Markov model $h$ with weights in a
commutative semiring with a linear order has nonnegative weights when all of its initial weights,
transition weights and emission weights are $\ge 0$: for all states $s, s'$ and every observation
$o$, the initial weight of $s$, the weight of the transition from $s$ to $s'$, and the weight of
emitting $o$ from $s$ are nonnegative. -/
structure HMM.Nonneg (h : HMM S O R) : Prop where
  /-- Initial weights are nonnegative. -/
  init : ∀ s, 0 ≤ h.init s
  /-- Transition weights are nonnegative. -/
  trans : ∀ s s', 0 ≤ h.trans s s'
  /-- Emission weights are nonnegative. -/
  emit : ∀ s o, 0 ≤ h.emit s o

variable {h}

omit [Fintype S] [Nonempty S] in
theorem pathProb_nonneg (hn : h.Nonneg) : ∀ (t : ℕ) (z : Fin (t + 1) → S), 0 ≤ pathProb h x t z
  | 0, _ => mul_nonneg (hn.init _) (hn.emit _ _)
  | t + 1, _ => mul_nonneg (mul_nonneg (pathProb_nonneg hn t _) (hn.trans _ _)) (hn.emit _ _)

/-- **Path weights of a hidden Markov model are bounded by the Viterbi variables.** Let $h$ be a
hidden Markov model with a finite nonempty set of states $S$ and initial weights $\pi$, transition
weights $a$ and emission weights $b$ that are nonnegative elements of a linearly ordered
commutative semiring, and let $x_0, x_1, \dots$ be observations. Let $\delta$ be the Viterbi
variables, $\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s' \in S} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$ and every state path $z = (z_0, \dots, z_t) \in S^{t+1}$, the joint weight of
$z$ and $x_0, \dots, x_t$ is at most $\delta_t(z_t)$. -/
theorem pathProb_le_viterbi (hn : h.Nonneg) :
    ∀ (t : ℕ) (z : Fin (t + 1) → S), pathProb h x t z ≤ viterbi h x t (z (Fin.last t))
  | 0, z => le_of_eq (by simp [pathProb, viterbi, Fin.last])
  | t + 1, z => by
      simp only [pathProb, viterbi]
      refine mul_le_mul_of_nonneg_right ?_ (hn.emit _ _)
      refine le_trans (mul_le_mul_of_nonneg_right (pathProb_le_viterbi hn t _) (hn.trans _ _)) ?_
      exact Finset.le_sup' (fun s' => viterbi h x t s' * h.trans s' (z (Fin.last (t + 1))))
        (Finset.mem_univ _)

omit [IsOrderedRing R] in
/-- **The Viterbi variables are attained.** Let $h$ be a hidden Markov model with a finite
nonempty set of states $S$ and weights in a commutative semiring $R$ with a linear order, and let
$x$ be an observation sequence. For every time $t$ and every state $s$, there is a state path
$z = (z_0, \dots, z_t)$ with $z_t = s$ whose joint weight with the observations
$x_0, \dots, x_t$ equals the Viterbi variable $V_t(s)$.

No nonnegativity of the weights and no compatibility of the order with the operations is
needed. -/
theorem exists_pathProb_eq_viterbi :
    ∀ (t : ℕ) (s : S),
      ∃ z : Fin (t + 1) → S, z (Fin.last t) = s ∧ pathProb h x t z = viterbi h x t s
  | 0, s => ⟨fun _ => s, rfl, by simp [pathProb, viterbi]⟩
  | t + 1, s => by
      obtain ⟨s', -, hs'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun s' => viterbi h x t s' * h.trans s' s)
      obtain ⟨z, hz, hzv⟩ := exists_pathProb_eq_viterbi t s'
      refine ⟨Fin.snoc z s, by simp, ?_⟩
      rw [pathProb_snoc, hz, hzv, viterbi, hs']

/-- **Viterbi computes the MAP value.** Let $h$ be a hidden Markov model with a finite nonempty set
of states $S$ and initial weights $\pi$, transition weights $a$ and emission weights $b$ that are
nonnegative elements of a linearly ordered commutative semiring, and let $x_0, x_1, \dots$ be
observations. Let $\delta$ be the Viterbi variables, $\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s' \in S} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$, $\max_{s \in S} \delta_t(s)$ equals the maximum, over all state paths
$z \in S^{t+1}$, of the joint weight of $z$ and $x_0, \dots, x_t$. -/
theorem sup'_viterbi_eq (hn : h.Nonneg) (t : ℕ) :
    (Finset.univ : Finset S).sup' Finset.univ_nonempty (viterbi h x t) =
      (Finset.univ : Finset (Fin (t + 1) → S)).sup' Finset.univ_nonempty (pathProb h x t) := by
  refine le_antisymm (Finset.sup'_le _ _ fun s _ => ?_) (Finset.sup'_le _ _ fun z _ => ?_)
  · obtain ⟨z, -, hz⟩ := exists_pathProb_eq_viterbi (h := h) x t s
    rw [← hz]
    exact Finset.le_sup' _ (Finset.mem_univ z)
  · exact le_trans (pathProb_le_viterbi x hn t z) (Finset.le_sup' _ (Finset.mem_univ _))

end Viterbi

/-! ## Tabulated algorithms on `Fin n` -/

section Tabulated

variable {n : ℕ} (x : ℕ → O)

/-- **Sum of the entries of a vector.** For a vector $v = (v_0, \dots, v_{n-1})$ of length $n$ with
entries in an additive commutative monoid, its entry sum is $\sum_{s < n} v_s$.

The vector is passed as an argument, so a table computed once is summed without recomputing it. -/
def sumVec [AddCommMonoid R] (v : Vector R n) : R := ∑ s : Fin n, v[s]

section ForwardTab

variable [Semiring R] (h : HMM (Fin n) O R)

/-- **One step of the tabulated forward algorithm.** Let $h$ be a hidden Markov model with states
$\{0, \dots, n-1\}$ and weights in a semiring $R$, with transition weight $a(s', s)$ from $s'$ to
$s$ and emission weight $e(s, o)$ of the observation $o$ from the state $s$, and let $x$ be an
observation sequence. For a table $v \in R^n$ and a step $t$, the forward step returns the table
whose entry at a state $s$ is

$$\Bigl(\sum_{s'=0}^{n-1} v_{s'} \, a(s', s)\Bigr) \, e(s, x_{t+1}).$$
-/
def forwardStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => (∑ s', v[s'] * h.trans s' s) * h.emit s (x (t + 1))

/-- **Tabulated forward algorithm.** Let $h$ be a hidden Markov model with states
$\{0, \dots, n-1\}$ and weights in a semiring $R$, with initial weight $\pi(s)$ and emission
weight $e(s, o)$ of the observation $o$ from the state $s$, and let $x$ be an observation
sequence. The forward table is the sequence of vectors in $R^n$ defined by recursion on time: at
time $0$ its entry at $s$ is $\pi(s) \, e(s, x_0)$, and the table at time $t + 1$ is the forward
step at step $t$ applied to the table at time $t$.

Each step takes $O(n^2)$ operations, and the entry at $s$ of the table at time $t$ is the forward
variable $\alpha_t(s)$. -/
def forwardTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => h.init s * h.emit s (x 0)
  | t + 1 => forwardStep x h (forwardTab t) t

theorem forwardTab_get : ∀ (t : ℕ) (s : Fin n), (forwardTab x h t)[s] = forward h x t s
  | 0, s => by simp [forwardTab, forward]
  | t + 1, s => by simp [forwardTab, forwardStep, forward, forwardTab_get t]

/-- **Tabulated likelihood of a hidden Markov model.** For a hidden Markov model $h$ with states
$0, \dots, n - 1$ and weights in a semiring, observations $x_0, x_1, \dots$ and $t \in \mathbb{N}$,
the tabulated likelihood at time $t$ is the sum $\sum_{s < n} v_s$ of the entries of the forward
table $v = (v_0, \dots, v_{n-1})$ at time $t$.

The forward table is computed step by step with $O(n^2)$ semiring operations per step, so the
tabulated likelihood costs $O(t n^2)$ operations; it equals the likelihood of $x_0, \dots, x_t$. -/
def likelihoodTab (t : ℕ) : R := sumVec (forwardTab x h t)

theorem likelihoodTab_eq (t : ℕ) : likelihoodTab x h t = likelihood h x t := by
  rw [likelihood_eq_sum_forward, likelihoodTab, sumVec]
  exact Finset.sum_congr rfl fun s _ => forwardTab_get x h t s

end ForwardTab

section ViterbiTab

variable [NeZero n] [CommSemiring R] [LinearOrder R] [IsOrderedRing R] (h : HMM (Fin n) O R)

omit [IsOrderedRing R] in
/-- **First maximizer of a function on a finite range.** Let $n \ge 1$ and let $R$ be a linearly
ordered set. For a function $f$ from $\{0, \dots, n-1\}$ to $R$, the maximizer of $f$ is the first
$i$, in the order $0, \dots, n-1$, at which $f$ attains its maximum, that is, $f(j) \le f(i)$ for
every $j$. -/
def argmaxFin (f : Fin n → R) : Fin n := ((List.finRange n).argmax f).getD 0

omit [CommSemiring R] [IsOrderedRing R] in
theorem le_argmaxFin (f : Fin n → R) (i : Fin n) : f i ≤ f (argmaxFin f) := by
  unfold argmaxFin
  cases hm : (List.finRange n).argmax f with
  | none =>
      rw [List.argmax_eq_none] at hm
      exact absurd hm (List.ne_nil_of_mem (List.mem_finRange (0 : Fin n)))
  | some m => exact List.le_of_mem_argmax (List.mem_finRange i) hm

omit [CommSemiring R] [IsOrderedRing R] in
theorem sup'_eq_argmaxFin (f : Fin n → R) :
    Finset.univ.sup' Finset.univ_nonempty f = f (argmaxFin f) :=
  le_antisymm (Finset.sup'_le _ _ fun i _ => le_argmaxFin f i)
    (Finset.le_sup' f (Finset.mem_univ _))

/-- **One step of the tabulated Viterbi recursion for a hidden Markov model.** Let $h$ be a hidden
Markov model with states $\{0, \dots, n - 1\}$, where $n \ge 1$, transition weights $a(s', s)$
and emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. Given a vector $v \in R^n$ and
$t \in \mathbb{N}$, the Viterbi step returns the vector in $R^n$ whose entry at state $s$ is

$$\Big(\max_{s'} v_{s'} \, a(s', s)\Big) \, b(s, x_{t+1}).$$
-/
def viterbiStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => Finset.univ.sup' Finset.univ_nonempty (fun s' => v[s'] * h.trans s' s) *
    h.emit s (x (t + 1))

/-- **The tabulated Viterbi variables of a hidden Markov model.** Let $h$ be a hidden Markov model
with states $\{0, \dots, n - 1\}$, where $n \ge 1$, initial weights $\pi(s)$, transition weights
$a(s', s)$ and emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. The Viterbi table assigns to each
$t \in \mathbb{N}$ a vector $T_t \in R^n$: the vector $T_0$ has entry $\pi(s) \, b(s, x_0)$ at
each state $s$, and $T_{t+1}$ is the Viterbi step at time $t$ applied to $T_t$, the vector whose
entry at state $s$ is $\big(\max_{s'} (T_t)_{s'} \, a(s', s)\big) \, b(s, x_{t+1})$.

The entry of $T_t$ at state $s$ is the Viterbi variable of $s$ at time $t$. -/
def viterbiTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => h.init s * h.emit s (x 0)
  | t + 1 => viterbiStep x h (viterbiTab t) t

omit [IsOrderedRing R] in
theorem viterbiTab_get : ∀ (t : ℕ) (s : Fin n), (viterbiTab x h t)[s] = viterbi h x t s
  | 0, s => by simp [viterbiTab, viterbi]
  | t + 1, s => by simp [viterbiTab, viterbiStep, viterbi, viterbiTab_get t]

/-- **Backpointer of the tabulated Viterbi algorithm.** Let $h$ be a hidden Markov model with
states $\{0, \dots, n-1\}$, where $n \ge 1$, and weights in a commutative semiring $R$ with a
linear order, and let $a(s', s)$ be its transition weight from $s'$ to $s$. For a table
$v \in R^n$ and a state $s$, the backpointer of $s$ is the first state $s'$, in the order
$0, \dots, n-1$, that maximizes $v_{s'} \, a(s', s)$.

No compatibility of the order with the operations is needed. -/
def back (v : Vector R n) (s : Fin n) : Fin n := argmaxFin fun s' => v[s'] * h.trans s' s

/-- **Backtracked path of the tabulated Viterbi algorithm.** Let $h$ be a hidden Markov model
with states $\{0, \dots, n-1\}$, where $n \ge 1$, and weights in a commutative semiring with a
linear order, and fix an observation sequence $x$. For a state $s$, the backtracked path
$b_t(s) = (b_t(s)_0, \dots, b_t(s)_t)$ of length $t + 1$ is defined by recursion on $t$:
$b_0(s)$ is the one-state path $(s)$, and $b_{t+1}(s)$ is $b_t(s')$ followed by $s$, where
$s'$ is the backpointer of $s$ computed from the Viterbi table at time $t$.

No compatibility of the order with the operations is needed. -/
def bestPath : (t : ℕ) → Fin n → Fin (t + 1) → Fin n
  | 0, s => fun _ => s
  | t + 1, s => Fin.snoc (bestPath t (back h (viterbiTab x h t) s)) s

omit [IsOrderedRing R] in
theorem bestPath_last : ∀ (t : ℕ) (s : Fin n), bestPath x h t s (Fin.last t) = s
  | 0, _ => rfl
  | t + 1, s => by simp [bestPath]

omit [IsOrderedRing R] in
/-- **The backtracked path of a hidden Markov model attains the Viterbi variable.** Let $h$ be a
hidden Markov model with states $0, \dots, n - 1$, where $n \ge 1$, initial weights $\pi$,
transition weights $a$ and emission weights $b$ in a commutative semiring with a linear order, and
let $x_0, x_1, \dots$ be observations. Let $\delta$ be the Viterbi variables,
$\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s'} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$ and every state $s$, the joint weight of $x_0, \dots, x_t$ and the backtracked
path of length $t + 1$ ending in $s$, obtained by following the backpointers, equals
$\delta_t(s)$. -/
theorem pathProb_bestPath : ∀ (t : ℕ) (s : Fin n),
    pathProb h x t (bestPath x h t s) = viterbi h x t s
  | 0, s => by simp [bestPath, pathProb, viterbi]
  | t + 1, s => by
      have hf : (fun s' => (viterbiTab x h t)[s'] * h.trans s' s) =
          fun s' => viterbi h x t s' * h.trans s' s := funext fun s' => by rw [viterbiTab_get]
      rw [bestPath, pathProb_snoc, bestPath_last, pathProb_bestPath t, viterbi,
        sup'_eq_argmaxFin, back, hf]

omit [CommSemiring R] [IsOrderedRing R] in
/-- **Index of a largest entry of a table.** Let $n \ge 1$ and let $R$ be a linearly ordered set.
For a table $v = (v_0, \dots, v_{n-1}) \in R^n$, the maximizing index of $v$ is the first index
$s$, in the order $0, \dots, n-1$, such that $v_{s'} \le v_s$ for every $s'$. -/
def argmaxVec (v : Vector R n) : Fin n := argmaxFin fun s => v[s]

/-- **Viterbi's MAP path.** Let $h$ be a hidden Markov model with states $\{0, \dots, n - 1\}$,
where $n \ge 1$, whose weights lie in a linearly ordered commutative semiring $R$, with transition
weights $a(s', s)$, and let $x$ be a sequence of observations. For $t \in \mathbb{N}$, let
$T_0, \dots, T_t \in R^n$ be the tabulated Viterbi variables of $h$ on $x$. The Viterbi path of
length $t + 1$ is the state path $(z_0, \dots, z_t)$ in which $z_t$ is the first state $s$, in the
order $0, \dots, n - 1$, that maximizes $(T_t)_s$, and, for $k < t$, $z_k$ is the first state $s'$
that maximizes $(T_k)_{s'} \, a(s', z_{k+1})$. -/
def viterbiPath (t : ℕ) : Fin (t + 1) → Fin n :=
  bestPath x h t (argmaxVec (viterbiTab x h t))

/-- **The Viterbi path is a most probable path.** Let $h$ be a hidden Markov model with states
$0, \dots, n - 1$, where $n \ge 1$, and nonnegative weights in a linearly ordered commutative
semiring, and let $x_0, x_1, \dots$ be observations. For every $t \in \mathbb{N}$ and every state
path $z = (z_0, \dots, z_t)$, the joint weight of $z$ and $x_0, \dots, x_t$ is at most the joint
weight of the Viterbi path of length $t + 1$ and $x_0, \dots, x_t$. -/
theorem pathProb_le_viterbiPath (hn : h.Nonneg) (t : ℕ) (z : Fin (t + 1) → Fin n) :
    pathProb h x t z ≤ pathProb h x t (viterbiPath x h t) := by
  rw [viterbiPath, argmaxVec, pathProb_bestPath]
  refine le_trans (pathProb_le_viterbi x hn t z) ?_
  have := le_argmaxFin (fun s => (viterbiTab x h t)[s]) (z (Fin.last t))
  simpa only [viterbiTab_get] using this

end ViterbiTab

end Tabulated

end Cslib.MachineLearning.Sequence.HiddenMarkov
