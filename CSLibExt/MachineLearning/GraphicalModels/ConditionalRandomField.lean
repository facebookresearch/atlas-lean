/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Linear-chain conditional random fields: forward algorithm and Viterbi

A linear-chain conditional random field (Lafferty, McCallum, and Pereira, *Conditional random
fields: Probabilistic models for segmenting and labeling sequence data*, ICML 2001; Sutton and
McCallum, *An introduction to conditional random fields*, FNT-ML 2012) models the conditional
distribution `p(y | x)` of a label sequence `y` given an input sequence `x` directly, as a
normalized product of position-dependent potentials. Unlike a hidden Markov model
(`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`), whose potentials are
position-independent and normalize per transition, a CRF's potentials may depend on the whole
input at each position and need only normalize globally, over all label sequences.

A chain CRF has states `S`, inputs `O`, and weights in `R` (typically
`ℝ` or `ℚ`): unary potentials `unary x t s` and transition potentials `trans x t s s'`, each
taking the whole observation sequence `x`, so edge features may depend jointly on the two
states, the full input, and the position. The
`logScore` of a label path is the sum of the log-potentials; here we work with the potentials
themselves. The log-linear parametrization `unary = exp (∑ wₖ fₖ)`, `trans = exp (∑ wₖ gₖ)`
is the special case obtained by instantiating the potentials with exponentials.
`pathWeight t z` is the unnormalized weight of a label path `z : Fin (t + 1) → S` given the
whole observation stream `x` (as in the standard definition, `p(y | x)` conditions on the
entire observation sequence, not just its prefix), `partition t` is the total weight of
all paths, and
`condProb t z = pathWeight t z / partition t` is the conditional probability of the path.

Main results:

* `forward_eq`: the forward variables are the path weights ending in each state;
  `partition_eq_sum_forward`: **the forward algorithm computes the partition function**.
* `pathWeight_le_viterbi`, `exists_pathWeight_eq_viterbi`: the Viterbi variables are the largest
  path weights ending in each state; `sup'_viterbi_eq`: **Viterbi computes the MAP value**.
* `sum_condProb_eq_one`: under `0 < partition t`, the conditional probabilities sum to `1`.
* `hmmToCRF_pathWeight`: every hidden Markov model embeds as a chain CRF with the same path
  weights, so a CRF generalizes an HMM.
* On `Fin n`, tabulated: `forwardTab`, `partitionTab_eq`; `viterbiTab`, backpointers `back`,
  `bestPath` (`pathWeight_bestPath`), and `crfPath` with `pathWeight_le_crfPath`: **the
  backtracked Viterbi path is a most probable label sequence**.

## Cost model

As in the HMM file: `forwardTab` and `viterbiTab` do `O(n²)` operations per step, `O(t n²)`
in total. The untabulated `forward`, `viterbi`, and `partition` are specifications.
Backtracking (`bestPath` / `crfPath`) recomputes `viterbiTab` from time zero at each level,
so reconstructing a path of length `t + 1` costs `O(t² n²)`, not one `O(t n²)` tabulated
pass; the tables themselves are computed once per `viterbiTab` call.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GraphicalModels.ConditionalRandomField

/-- **Linear-chain conditional random field.** Let $S$ be a type of states, $O$ a type of inputs
and $R$ a type of weights with a zero and a relation $\le$. A linear-chain conditional random
field consists of a unary potential $\phi(x, t, s) \in R$ and a transition potential
$\psi(x, t, s, s') \in R$ from $s$ to $s'$, given for every observation sequence
$x \colon \mathbb{N} \to O$, every position $t \in \mathbb{N}$ and all states $s, s' \in S$, such
that $0 \le \phi(x, t, s)$ and $0 \le \psi(x, t, s, s')$ always hold.

Both potentials see the whole, possibly infinite, observation sequence $x$, so path weights
condition on all of $x$, as the conditional probability $p(y \mid x)$ of a label sequence $y$
does in the standard definition. Nonnegativity makes the potentials unnormalized
probabilities. -/
structure ChainCRF (S O R : Type*) [Zero R] [LE R] where
  /-- The unary potential of a state at a position, as a function of the whole
  observation sequence. -/
  unary : (ℕ → O) → ℕ → S → R
  /-- The transition potential from the first state to the second at a step, as a function
  of the whole observation sequence (so edge features may depend jointly on the two
  states, the full input, and the position). -/
  trans : (ℕ → O) → ℕ → S → S → R
  /-- Unary potentials are nonnegative. -/
  unary_nonneg : ∀ (x : ℕ → O) (t : ℕ) (s : S), 0 ≤ unary x t s
  /-- Transition potentials are nonnegative. -/
  trans_nonneg : ∀ (x : ℕ → O) (t : ℕ) (s s' : S), 0 ≤ trans x t s s'

section Forward

variable {S O R : Type*} [Semiring R] [LE R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- **Weight of a label path in a chain CRF.** For a chain conditional random field with weights
in a semiring, unary potentials $u_t(s)$ and transition potentials $\tau_t(s, s')$ given the
observation stream $x$, the unnormalized weight of a label path $z = (z_0, \dots, z_t)$ is

$$w_t(z) = u_0(z_0) \prod_{i=1}^{t} \tau_{i-1}(z_{i-1}, z_i)\, u_i(z_i),$$

with the factors multiplied from left to right in increasing order of $i$. -/
def pathWeight : (t : ℕ) → (Fin (t + 1) → S) → R
  | 0, z => c.unary x 0 (z 0)
  | t + 1, z => pathWeight t (Fin.init z) * c.trans x t (z (Fin.last t).castSucc)
      (z (Fin.last (t + 1))) * c.unary x (t + 1) (z (Fin.last (t + 1)))

/-- **Partition function of a chain CRF.** For a chain conditional random field with a finite set
of states and weights in a semiring, and an observation stream $x$, the partition function at
time $t$ is $Z_t = \sum_z w_t(z)$, the total weight of all label paths $z$ of length $t + 1$,
where $w_t(z)$ is the unnormalized weight of $z$ given $x$. -/
def partition (t : ℕ) : R := ∑ z : Fin (t + 1) → S, pathWeight c x t z

/-- **Forward variables of a chain CRF.** For a chain conditional random field with a finite set
of states, weights in a semiring, unary potentials $u_t(s)$ and transition potentials
$\tau_t(s', s)$ given the observation stream $x$, the forward variables are defined by
$\alpha_0(s) = u_0(s)$ and
$\alpha_{t+1}(s) = \left(\sum_{s'} \alpha_t(s')\, \tau_t(s', s)\right) u_{t+1}(s)$, the sum running
over all states $s'$.

The forward variable $\alpha_t(s)$ is the total weight of the label paths of length $t + 1$ ending
in $s$. -/
def forward : ℕ → S → R
  | 0, s => c.unary x 0 s
  | t + 1, s => (∑ s', forward t s' * c.trans x t s' s) * c.unary x (t + 1) s

omit [Fintype S] in
theorem pathWeight_snoc (t : ℕ) (z : Fin (t + 1) → S) (s : S) :
    pathWeight c x (t + 1) (Fin.snoc z s) = pathWeight c x t z * c.trans x t (z (Fin.last t)) s *
      c.unary x (t + 1) s := by
  simp [pathWeight, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]

/-- **The forward variables are path weights.** Let $c$ be a chain CRF with a finite set of
states $S$ and weights in a semiring $R$ carrying a relation $\le$, and let $x$ be an
observation sequence. For every $t \in \mathbb{N}$ and every state $s \in S$, the forward
variable $\alpha_t(s)$ equals the total path weight of the label paths
$z = (z_0, \dots, z_t) \in S^{t+1}$ that end in $z_t = s$:

$$\alpha_t(s) = \sum_{z \in S^{t+1},\ z_t = s} w_t(z),$$

where $w_t(z)$ is the path weight of $z$. -/
theorem forward_eq [DecidableEq S] : ∀ (t : ℕ) (s : S),
    forward c x t s = ∑ z : Fin (t + 1) → S,
      if z (Fin.last t) = s then pathWeight c x t z else 0
  | 0, s => by
      rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
      simp [forward, pathWeight, Fin.last]
  | t + 1, s => by
      rw [Cslib.MachineLearning.Sequence.HiddenMarkov.sum_snoc]
      simp only [Fin.snoc_last, pathWeight_snoc, forward, forward_eq t]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
      simp

/-- **The forward algorithm computes the partition function.** For a chain conditional random
field with a finite set of states and weights in a semiring, and an observation stream $x$, for
every $t$ the partition function at time $t$ equals $\sum_s \alpha_t(s)$, the sum over all
states $s$ of the forward variables $\alpha_t(s)$. -/
theorem partition_eq_sum_forward (t : ℕ) :
    partition c x t = ∑ s, forward c x t s := by
  classical
  simp only [forward_eq, partition]
  rw [Finset.sum_comm]
  simp

end Forward

/-! ## Viterbi -/

section Viterbi

variable {S O R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable [Fintype S] [Nonempty S] (c : ChainCRF S O R) (x : ℕ → O)

/-- **The Viterbi variables of a chain CRF.** Let $c$ be a chain conditional random field with
a finite nonempty set of states $S$ and weights in a linearly ordered commutative semiring $R$,
and let $x$ be an observation sequence. Write $\phi_t(s)$ for the unary potential of $c$ at $x$
of state $s$ at position $t$, and $\psi_t(s', s)$ for its transition potential from $s'$ to $s$
at step $t$. The Viterbi variables $V_t(s)$, for $t \in \mathbb{N}$ and $s \in S$, are defined
by $V_0(s) = \phi_0(s)$ and
$$V_{t+1}(s) = \Big(\max_{s' \in S} V_t(s') \, \psi_t(s', s)\Big) \, \phi_{t+1}(s).$$

Thus $V_t(s)$ is the largest weight of a label path of length $t + 1$ ending in $s$. -/
def viterbi : ℕ → S → R
  | 0, s => c.unary x 0 s
  | t + 1, s => Finset.univ.sup' Finset.univ_nonempty
      (fun s' => viterbi t s' * c.trans x t s' s) * c.unary x (t + 1) s

variable {c}

omit [Fintype S] [Nonempty S] in
theorem pathWeight_nonneg :
    ∀ (t : ℕ) (z : Fin (t + 1) → S), 0 ≤ pathWeight c x t z
  | 0, _ => c.unary_nonneg _ _ _
  | t + 1, _ => mul_nonneg
      (mul_nonneg (pathWeight_nonneg t _) (c.trans_nonneg _ _ _ _)) (c.unary_nonneg _ _ _)

omit [Nonempty S] in
theorem partition_nonneg (t : ℕ) : 0 ≤ partition c x t := by
  refine Finset.sum_nonneg fun z _ => pathWeight_nonneg x t z

/-- **Path weights of a chain CRF are bounded by the Viterbi variables.** For a chain conditional
random field with a nonempty finite set of states, weights in a linearly ordered commutative
semiring, and an observation stream $x$, for every $t$ and every label path
$z = (z_0, \dots, z_t)$, the weight of $z$ is at most the Viterbi variable at time $t$ of its last
state $z_t$. -/
theorem pathWeight_le_viterbi :
    ∀ (t : ℕ) (z : Fin (t + 1) → S),
      pathWeight c x t z ≤ viterbi c x t (z (Fin.last t))
  | 0, z => le_of_eq (by simp [pathWeight, viterbi, Fin.last])
  | t + 1, z => by
      simp only [pathWeight, viterbi]
      refine mul_le_mul_of_nonneg_right ?_ (c.unary_nonneg _ _ _)
      refine le_trans
        (mul_le_mul_of_nonneg_right (pathWeight_le_viterbi t _) (c.trans_nonneg _ _ _ _)) ?_
      exact Finset.le_sup' (fun s' => viterbi c x t s' * c.trans x t s' (z (Fin.last (t + 1))))
        (Finset.mem_univ _)

/-- **The Viterbi variables of a chain CRF are attained.** Let $c$ be a chain CRF with a finite
nonempty set of states $S$ and weights in a linearly ordered commutative semiring, and let $x$
be an observation sequence. For every $t \in \mathbb{N}$ and every state $s \in S$ there is a
label path $z = (z_0, \dots, z_t) \in S^{t+1}$ with $z_t = s$ whose path weight equals the
Viterbi variable of $s$ at time $t$. -/
theorem exists_pathWeight_eq_viterbi :
    ∀ (t : ℕ) (s : S),
      ∃ z : Fin (t + 1) → S, z (Fin.last t) = s ∧ pathWeight c x t z = viterbi c x t s
  | 0, s => ⟨fun _ => s, rfl, by simp [pathWeight, viterbi]⟩
  | t + 1, s => by
      obtain ⟨s', -, hs'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun s' => viterbi c x t s' * c.trans x t s' s)
      obtain ⟨z, hz, hzv⟩ := exists_pathWeight_eq_viterbi t s'
      refine ⟨Fin.snoc z s, by simp, ?_⟩
      rw [pathWeight_snoc, hz, hzv, viterbi, hs']

/-- **Viterbi computes the MAP value of a chain CRF.** Let $c$ be a chain conditional random
field with a finite nonempty set of states $S$ and weights in a linearly ordered commutative
semiring $R$, and let $x$ be an observation sequence. For every $t \in \mathbb{N}$, the maximum
over $s \in S$ of the Viterbi variable $V_t(s)$ of $c$ at $x$ equals the maximum, over all label
paths $z : \{0, \dots, t\} \to S$, of the weight of $z$. -/
theorem sup'_viterbi_eq (t : ℕ) :
    (Finset.univ : Finset S).sup' Finset.univ_nonempty (viterbi c x t) =
      (Finset.univ : Finset (Fin (t + 1) → S)).sup' Finset.univ_nonempty (pathWeight c x t) := by
  refine le_antisymm (Finset.sup'_le _ _ fun s _ => ?_) (Finset.sup'_le _ _ fun z _ => ?_)
  · obtain ⟨z, -, hz⟩ := exists_pathWeight_eq_viterbi (c := c) x t s
    rw [← hz]
    exact Finset.le_sup' _ (Finset.mem_univ z)
  · exact le_trans (pathWeight_le_viterbi x t z) (Finset.le_sup' _ (Finset.mem_univ _))

end Viterbi

/-! ## Conditional probabilities -/

section Probabilities

variable {S O R : Type*} [Semifield R] [PartialOrder R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- **Conditional probability of a label path in a chain CRF.** Let $c$ be a chain CRF with a
finite set of states $S$ and weights in a semifield $R$ carrying a partial order $\le$, and let
$x$ be an observation sequence. For $t \in \mathbb{N}$, the conditional probability of a label
path $z \in S^{t+1}$ given $x$ is $w_t(z) / Z_t$, where $w_t(z)$ is the path weight of $z$ and
$Z_t$ is the partition function, the total path weight of all label paths in $S^{t+1}$; the
quotient is $0$ when $Z_t = 0$. -/
def condProb (t : ℕ) (z : Fin (t + 1) → S) : R := pathWeight c x t z / partition c x t

/-- **The conditional probabilities sum to $1$.** Let $c$ be a chain conditional random field
with finitely many states $S$ and weights in a semifield $R$ equipped with a partial order (not
assumed compatible with the operations), let $x$ be an observation sequence, and let
$t \in \mathbb{N}$. If the partition function of $c$ at $x$ and time $t$ is positive, then the
conditional probabilities $p(z \mid x)$ of all label paths $z : \{0, \dots, t\} \to S$ of length
$t + 1$ sum to $1$. -/
theorem sum_condProb_eq_one (t : ℕ) (hpos : 0 < partition c x t) :
    ∑ z : Fin (t + 1) → S, condProb c x t z = 1 := by
  simp only [condProb, ← Finset.sum_div]
  rw [show (∑ z : Fin (t + 1) → S, pathWeight c x t z) = partition c x t from rfl]
  exact div_self (ne_of_gt hpos)

end Probabilities

section ProbabilitiesNonneg

variable {S O R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- **Conditional probabilities of a chain CRF are nonnegative.** Let $c$ be a chain CRF with a
finite set of states $S$ and weights in a linearly ordered field $R$, and let $x$ be an
observation sequence. For every $t \in \mathbb{N}$ and every label path
$z = (z_0, \dots, z_t) \in S^{t+1}$, the conditional probability of $z$ given $x$ is nonnegative.

No positivity of the partition function is assumed; nonnegativity comes from the nonnegativity
of the potentials. -/
theorem condProb_nonneg (t : ℕ) (z : Fin (t + 1) → S) :
    0 ≤ condProb c x t z :=
  div_nonneg (pathWeight_nonneg x t z) (partition_nonneg x t)

end ProbabilitiesNonneg

/-! ## Every HMM embeds as a CRF -/

section Embedding

variable {S O R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable (h : Cslib.MachineLearning.Sequence.HiddenMarkov.HMM S O R) (x : ℕ → O)

/-- **The chain CRF of a hidden Markov model.** Let $h$ be a hidden Markov model with initial
weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$ in a linearly
ordered commutative semiring, all nonnegative. Its chain CRF has, for every observation stream
$x$, unary potentials $u_0(s) = \pi(s)\, b(s, x_0)$ and $u_t(s) = b(s, x_t)$ for $t \ge 1$, and
transition potentials $\tau_t(s, s') = a(s, s')$ at every step $t$. -/
def hmmToCRF (hn : h.Nonneg) : ChainCRF S O R where
  unary x t s := if t = 0 then h.init s * h.emit s (x t) else h.emit s (x t)
  trans _x _t s s' := h.trans s s'
  unary_nonneg x t s := by
    by_cases ht : t = 0
    · subst ht
      simp only [ite_true]
      exact mul_nonneg (hn.init _) (hn.emit _ _)
    · simp only [ht, ite_false]
      exact hn.emit _ _
  trans_nonneg _x _t s s' := hn.trans _ _

/-- **The chain CRF of a hidden Markov model has the same path weights.** Let $h$ be a hidden
Markov model with nonnegative weights in a linearly ordered commutative semiring, and let $x$ be
an observation stream. For every $t$ and every state path $z = (z_0, \dots, z_t)$, the weight of
$z$ in the chain CRF of $h$ given $x$ equals the joint weight in $h$ of the state path $z$ and the
observations $x_0, \dots, x_t$. -/
theorem hmmToCRF_pathWeight (hn : h.Nonneg) :
    ∀ (t : ℕ) (z : Fin (t + 1) → S),
      pathWeight (hmmToCRF h hn) x t z =
        Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb h x t z
  | 0, z => by simp [pathWeight, Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb, hmmToCRF]
  | t + 1, z => by
      have hz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) :=
        (Fin.snoc_init_self z).symm
      rw [hz, pathWeight_snoc, hmmToCRF_pathWeight hn t]
      simp [Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb, hmmToCRF, Fin.snoc_last,
        Fin.snoc_castSucc]

end Embedding

/-! ## Tabulated algorithms on `Fin n` -/

section Tabulated

variable {O R : Type*} {n : ℕ} (x : ℕ → O)

section ForwardTab

variable [Semiring R] [LE R] (c : ChainCRF (Fin n) O R)

/-- **One step of the tabulated CRF forward algorithm.** Let $c$ be a chain CRF with states
$\{0, \dots, n-1\}$ and weights in a semiring $R$ carrying a relation $\le$, with unary
potential $\phi_t(s)$ at position $t$ and transition potential $\psi_t(s', s)$ from $s'$ to $s$
at step $t$, given the observation sequence $x$. For a table $v \in R^n$ and a step $t$, the
forward step returns the table whose entry at a state $s$ is

$$\Bigl(\sum_{s'=0}^{n-1} v_{s'} \, \psi_t(s', s)\Bigr) \, \phi_{t+1}(s).$$
-/
def forwardStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => (∑ s', v[s'] * c.trans x t s' s) * c.unary x (t + 1) s

/-- **Tabulated CRF forward algorithm.** Let $c$ be a chain CRF with states $\{0, \dots, n-1\}$
and weights in a semiring $R$ carrying a relation $\le$, with unary potential $\phi_t(s)$ at
position $t$ given the observation sequence $x$. The forward table is the sequence of vectors in
$R^n$ defined by recursion on time: at time $0$ its entry at $s$ is $\phi_0(s)$, and the table at
time $t + 1$ is the forward step at step $t$ applied to the table at time $t$.

Each step takes $O(n^2)$ operations. -/
def forwardTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => c.unary x 0 s
  | t + 1 => forwardStep x c (forwardTab t) t

theorem forwardTab_get : ∀ (t : ℕ) (s : Fin n), (forwardTab x c t)[s] = forward c x t s
  | 0, s => by simp [forwardTab, forward]
  | t + 1, s => by simp [forwardTab, forwardStep, forward, forwardTab_get t]

/-- **The tabulated forward algorithm for chain CRFs.** For a chain conditional random field with
states $0, \dots, n - 1$ and weights in a semiring, and an observation stream $x$, the tabulated
partition function at time $t$ is the sum of the entries of the forward table at time $t$, the
vector $(\alpha_t(0), \dots, \alpha_t(n - 1))$ of forward variables computed step by step from
time $0$.

It equals the partition function at time $t$ and takes $O(t n^2)$ operations. -/
def partitionTab (t : ℕ) : R :=
  Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec (forwardTab x c t)

theorem partitionTab_eq (t : ℕ) : partitionTab x c t = partition c x t := by
  rw [partition_eq_sum_forward, partitionTab,
    Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec]
  exact Finset.sum_congr rfl fun s _ => forwardTab_get x c t s

end ForwardTab

section ViterbiTab

variable [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable [NeZero n] (c : ChainCRF (Fin n) O R)

/-- **One step of the tabulated Viterbi recursion for a chain CRF.** Let $c$ be a chain
conditional random field with states $\{0, \dots, n - 1\}$, where $n \ge 1$, and weights in a
linearly ordered commutative semiring $R$, and let $x$ be an observation sequence. Write
$\phi_t(s)$ for the unary potential of $c$ at $x$ of state $s$ at position $t$, and
$\psi_t(s', s)$ for its transition potential from $s'$ to $s$ at step $t$. Given a vector
$v \in R^n$ and $t \in \mathbb{N}$, the Viterbi step returns the vector in $R^n$ whose entry at
state $s$ is
$$\Big(\max_{s'} v_{s'} \, \psi_t(s', s)\Big) \, \phi_{t+1}(s).$$
-/
def viterbiStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun s' => v[s'] * c.trans x t s' s) * c.unary x (t + 1) s

/-- **The tabulated Viterbi variables of a chain CRF.** Let $c$ be a chain conditional random
field with states $\{0, \dots, n - 1\}$, where $n \ge 1$, and weights in a linearly ordered
commutative semiring $R$, and let $x$ be an observation sequence. Write $\phi_0(s)$ for the
unary potential of $c$ at $x$ of state $s$ at position $0$. The Viterbi table assigns to each
$t \in \mathbb{N}$ a vector $T_t \in R^n$: the vector $T_0$ has entry $\phi_0(s)$ at each state
$s$, and $T_{t+1}$ is the Viterbi step at time $t$ applied to $T_t$.

The entry of $T_t$ at state $s$ is the Viterbi variable $V_t(s)$. -/
def viterbiTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => c.unary x 0 s
  | t + 1 => viterbiStep x c (viterbiTab t) t

theorem viterbiTab_get : ∀ (t : ℕ) (s : Fin n), (viterbiTab x c t)[s] = viterbi c x t s
  | 0, s => by simp [viterbiTab, viterbi]
  | t + 1, s => by simp [viterbiTab, viterbiStep, viterbi, viterbiTab_get t]

/-- **Backpointer of the tabulated CRF Viterbi algorithm.** Let $c$ be a chain CRF with states
$\{0, \dots, n-1\}$, where $n \ge 1$, and weights in a linearly ordered commutative semiring
$R$, and let $\psi_t(s', s)$ be its transition potential from $s'$ to $s$ at step $t$ given the
observation sequence $x$. For a step $t$, a table $v \in R^n$ and a state $s$, the backpointer
of $s$ is the first state $s'$, in the order $0, \dots, n-1$, that maximizes
$v_{s'} \, \psi_t(s', s)$. -/
def back (t : ℕ) (v : Vector R n) (s : Fin n) : Fin n :=
  Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxFin fun s' => v[s'] * c.trans x t s' s

/-- **Backtracked path of the tabulated CRF Viterbi algorithm.** Let $c$ be a chain CRF with
states $\{0, \dots, n-1\}$, where $n \ge 1$, and weights in a linearly ordered commutative
semiring, and fix an observation sequence $x$. For a state $s$, the backtracked path
$b_t(s) = (b_t(s)_0, \dots, b_t(s)_t)$ of length $t + 1$ is defined by recursion on $t$:
$b_0(s)$ is the one-state path $(s)$, and $b_{t+1}(s)$ is $b_t(s')$ followed by $s$, where
$s'$ is the backpointer of $s$ at step $t$ computed from the Viterbi table at time $t$. -/
def bestPath : (t : ℕ) → Fin n → Fin (t + 1) → Fin n
  | 0, s => fun _ => s
  | t + 1, s => Fin.snoc (bestPath t (back x c t (viterbiTab x c t) s)) s

omit [IsOrderedRing R] in
theorem bestPath_last : ∀ (t : ℕ) (s : Fin n), bestPath x c t s (Fin.last t) = s
  | 0, _ => rfl
  | t + 1, s => by simp [bestPath]

/-- **The backtracked path of a chain CRF attains the Viterbi variable.** For a chain conditional
random field with states $0, \dots, n - 1$ where $n \ge 1$, weights in a linearly ordered
commutative semiring, and an observation stream $x$, for every $t$ and every state $s$ the weight
of the backtracked path of length $t + 1$ ending in $s$, obtained by following the backpointers,
equals the Viterbi variable at time $t$ of $s$. -/
theorem pathWeight_bestPath : ∀ (t : ℕ) (s : Fin n),
    pathWeight c x t (bestPath x c t s) = viterbi c x t s
  | 0, s => by simp [bestPath, pathWeight, viterbi]
  | t + 1, s => by
      have hf : (fun s' => (viterbiTab x c t)[s'] * c.trans x t s' s) =
          fun s' => viterbi c x t s' * c.trans x t s' s :=
        funext fun s' => by rw [viterbiTab_get]
      rw [bestPath, pathWeight_snoc, bestPath_last, pathWeight_bestPath t, viterbi,
        Cslib.MachineLearning.Sequence.HiddenMarkov.sup'_eq_argmaxFin, back, hf]

/-- **The Viterbi path of a chain CRF.** Let $c$ be a chain CRF with states $\{0, \dots, n-1\}$,
where $n \ge 1$, and weights in a linearly ordered commutative semiring, and let $x$ be an
observation sequence. For $t \in \mathbb{N}$, the Viterbi path of length $t + 1$ is the
backtracked path ending in the first state, in the order $0, \dots, n-1$, that maximizes the
Viterbi table at time $t$. -/
def crfPath (t : ℕ) : Fin (t + 1) → Fin n :=
  bestPath x c t
    (Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec (viterbiTab x c t))

/-- **The Viterbi path of a chain CRF has maximal weight.** For a chain conditional random field
with states $0, \dots, n - 1$ where $n \ge 1$, weights in a linearly ordered commutative
semiring, and an observation stream $x$, for every $t$ and every label path $z$ of length
$t + 1$, the weight of $z$ is at most the weight of Viterbi's MAP path of length $t + 1$. -/
theorem pathWeight_le_crfPath (t : ℕ) (z : Fin (t + 1) → Fin n) :
    pathWeight c x t z ≤ pathWeight c x t (crfPath x c t) := by
  rw [crfPath, Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec, pathWeight_bestPath]
  refine le_trans (pathWeight_le_viterbi x t z) ?_
  have := Cslib.MachineLearning.Sequence.HiddenMarkov.le_argmaxFin
    (fun s => (viterbiTab x c t)[s]) (z (Fin.last t))
  simpa only [viterbiTab_get] using this

end ViterbiTab

end Tabulated

end Cslib.MachineLearning.GraphicalModels.ConditionalRandomField
