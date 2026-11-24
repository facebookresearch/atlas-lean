/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Relation

namespace MetaMathlibExt

@[expose] public section

/-- **Zero-sum subsequences of cross number at most one (Geroldinger; Elledge–Hurlbert).** Let
$\Gamma$ be a finite abelian group of order $|\Gamma|$. Every sequence $g_1, \dots, g_{|\Gamma|}$
of $|\Gamma|$ elements of $\Gamma$ has a nonempty zero-sum subsequence with cross number at most
one: there is a nonempty set $S \subseteq \{1, \dots, |\Gamma|\}$ of indices with
$\sum_{i \in S} g_i = 0$ and $\sum_{i \in S} 1/\operatorname{ord}(g_i) \le 1$, where
$\operatorname{ord}(g_i)$ is the order of $g_i$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small
Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 3
(`integers-2024-A93-thm-3`). -/
public theorem_wanted exists_zero_sum_cross_number_le_one {Γ : Type*} [AddCommGroup Γ]
    [Fintype Γ] (g : Fin (Fintype.card Γ) → Γ) :
    ∃ s : Finset (Fin (Fintype.card Γ)), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
      ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- **Lemke–Kleitman theorem.** For every positive integer $n$, every sequence
$g_1, \dots, g_n$ of $n$ elements of $\mathbb{Z}/n\mathbb{Z}$ has a nonempty zero-sum
subsequence with cross number at most one: there is a nonempty set $S \subseteq \{1, \dots, n\}$
of indices with $\sum_{i \in S} g_i = 0$ and $\sum_{i \in S} 1/\operatorname{ord}(g_i) \le 1$,
where $\operatorname{ord}(g_i)$ is the additive order of $g_i$. The theorem is due to Lemke and
Kleitman and to Chung.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small
Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 2
(`integers-2024-A93-thm-2`). -/
public theorem_wanted ZMod.exists_zero_sum_cross_number_le_one {n : ℕ} (hn : 0 < n)
    (g : Fin n → ZMod n) :
    ∃ s : Finset (Fin n), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
      ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- **Good sequences in a finite abelian group.** Let $\Gamma$ be a finite abelian group, written
additively, and let $g = (g_1, \dots, g_t)$ be a sequence of $t$ elements of $\Gamma$. The
sequence $g$ is *good* if there is a nonempty set $S \subseteq \{1, \dots, t\}$ of indices with
$\sum_{i \in S} g_i = 0$ whose cross number $\sum_{i \in S} 1/|g_i|$ is at most $1$, where
$|g_i|$ is the order of $g_i$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1 (definition of good sequences). -/
def IsGoodSequence {Γ : Type*} [AddCommGroup Γ] [Finite Γ] {t : ℕ} (g : Fin t → Γ) : Prop :=
  ∃ s : Finset (Fin t), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
    ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- **Probability that a random sequence is good.** Let $\Gamma$ be a finite abelian group and
$t \ge 0$ an integer. A sequence $g_1, \dots, g_t$ in $\Gamma$ is good if some nonempty set
$S \subseteq \{1, \dots, t\}$ of indices has $\sum_{i \in S} g_i = 0$ and
$\sum_{i \in S} 1/\operatorname{ord}(g_i) \le 1$, where $\operatorname{ord}(g_i)$ is the order
of $g_i$. The good-sequence probability of $\Gamma$ at length $t$ is the number of good sequences
of length $t$ in $\Gamma$ divided by $|\Gamma|^t$, that is, the probability that a uniformly
random sequence of length $t$ in $\Gamma$ is good.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (the event `E_Γ(t)`). -/
noncomputable def goodSequenceProb (Γ : Type*) [AddCommGroup Γ] [Finite Γ] (t : ℕ) : ℝ :=
  ({g : Fin t → Γ | IsGoodSequence g}.ncard : ℝ) / (Nat.card Γ : ℝ) ^ t

/-- **Good-sequence probability at length zero.** For every finite abelian group $\Gamma$, the
probability that a uniformly random sequence of length $0$ in $\Gamma$ is good equals $0$: the
empty sequence has no nonempty zero-sum subsequence, so it is not good.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition. -/
theorem goodSequenceProb_zero (Γ : Type*) [AddCommGroup Γ] [Finite Γ] :
    goodSequenceProb Γ 0 = 0 := by
  have h : {g : Fin 0 → Γ | IsGoodSequence g} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, ⟨i, -⟩, -⟩
    exact i.elim0
  simp [goodSequenceProb, h]

/-- **Half-good threshold.** For a finite abelian group $\Gamma$, $P_{1/2}(\Gamma)$ is the least
$t \ge 0$ such that a uniformly random sequence of $t$ elements of $\Gamma$ is good (has a
nonempty zero-sum subsequence with cross number at most one) with probability at least $1/2$,
that is, such that at least half of the $|\Gamma|^t$ sequences of length $t$ are good. If no
such $t$ exists, $P_{1/2}(\Gamma)$ is defined to be $0$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of `P_{1/2}(Γ)`). -/
noncomputable def halfGoodThreshold (Γ : Type*) [AddCommGroup Γ] [Finite Γ] : ℕ :=
  sInf {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t}

/-- **Half-good threshold of a group of order at most two.** If $\Gamma$ is a finite abelian
group with at most two elements, then its half-good threshold $P_{1/2}(\Gamma)$ equals $1$.

The empty sequence is not good, while the one-term sequence $(0)$ is good, so a uniformly random
sequence of length one is good with probability at least $1/|\Gamma| \ge 1/2$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition of `P_{1/2}(Γ)`. -/
theorem halfGoodThreshold_eq_one_of_card_le_two (Γ : Type*) [AddCommGroup Γ] [Finite Γ]
    (h : Nat.card Γ ≤ 2) : halfGoodThreshold Γ = 1 := by
  have h0 : (0 : ℕ) ∉ {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t} := by
    simp only [Set.mem_ofPred_eq, goodSequenceProb_zero]
    norm_num
  have h1 : (1 : ℕ) ∈ {t : ℕ | (1 : ℝ) / 2 ≤ goodSequenceProb Γ t} := by
    have hgood : (fun _ => (0 : Γ)) ∈ {g : Fin 1 → Γ | IsGoodSequence g} :=
      ⟨Finset.univ, Finset.univ_nonempty, by simp, by simp⟩
    have hpos : 0 < {g : Fin 1 → Γ | IsGoodSequence g}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hgood⟩
    have hcard : 0 < Nat.card Γ := Nat.card_pos
    have hpos' : (1 : ℝ) ≤ ({g : Fin 1 → Γ | IsGoodSequence g}.ncard : ℝ) := by
      exact_mod_cast hpos
    have hcard' : (0 : ℝ) < (Nat.card Γ : ℝ) := by exact_mod_cast hcard
    have h2 : (Nat.card Γ : ℝ) ≤ 2 := by exact_mod_cast h
    show (1 : ℝ) / 2 ≤ goodSequenceProb Γ 1
    rw [goodSequenceProb, pow_one, le_div_iff₀ hcard']
    linarith
  refine le_antisymm (Nat.sInf_le h1) (Nat.one_le_iff_ne_zero.2 fun hz => ?_)
  rcases Nat.sInf_eq_zero.1 hz with h | h
  · exact h0 h
  · rw [h] at h1
    exact h1

/-- **Threshold functions.** Let $P : \mathbb{N} \times \mathbb{N} \to \mathbb{R}$, where
$P(k, s)$ is read as the probability of an event in the $k$-th space when $s$ random elements
are chosen. A function $t : \mathbb{N} \to \mathbb{R}$ is a *threshold function* for $P$ if
$t(k) > 0$ for all sufficiently large $k$ and, for every function $f : \mathbb{N} \to \mathbb{N}$,
$P(k, f(k)) \to 1$ as $k \to \infty$ whenever $t = o(f)$, and $P(k, f(k)) \to 0$ as
$k \to \infty$ whenever $f = o(t)$.

The source's thresholds are positive functions; since little-o ignores sign, without the
positivity condition $-t$ would be a threshold function whenever $t$ is.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of a threshold and of
`τ(G)`). -/
def IsThresholdFunction (P : ℕ → ℕ → ℝ) (t : ℕ → ℝ) : Prop :=
  (∀ᶠ k in Filter.atTop, 0 < t k) ∧ ∀ f : ℕ → ℕ,
    (t =o[Filter.atTop] (fun k => (f k : ℝ)) →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 1)) ∧
      ((fun k => (f k : ℝ)) =o[Filter.atTop] t →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 0))

/-- **Positive multiples of threshold functions.** Let $P : \mathbb{N} \times \mathbb{N} \to
\mathbb{R}$ and $t : \mathbb{N} \to \mathbb{R}$. If $t$ is a threshold function for $P$ and
$c > 0$ is a real number, then $k \mapsto c \, t(k)$ is also a threshold function for $P$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 1.1
definition of a threshold. -/
theorem IsThresholdFunction.const_mul {P : ℕ → ℕ → ℝ} {t : ℕ → ℝ}
    (h : IsThresholdFunction P t) {c : ℝ} (hc : 0 < c) :
    IsThresholdFunction P (fun k => c * t k) :=
  ⟨h.1.mono fun _ hk => mul_pos hc hk, fun f =>
    ⟨fun hf => (h.2 f).1 ((Asymptotics.isLittleO_const_mul_left_iff hc.ne').1 hf),
      fun hf => (h.2 f).2 ((Asymptotics.isLittleO_const_mul_right_iff hc.ne').1 hf)⟩⟩

/-- **Lagarias–Saks pebbling step.** Let $G$ be a simple graph on a vertex set $V$, and let $w$
assign a natural-number cost $w(uv)$ to each unordered pair of vertices $\{u, v\}$. For
configurations $C, C' : V \to \mathbb{N}$, there is a pebbling step from $C$ to $C'$ if there
is an edge $uv$ of $G$ with $0 < w(uv) \le C(u)$ such that $C'$ is obtained from $C$ by
removing $w(uv)$ pebbles from $u$ and adding one pebble to $v$.

Each edge has one cost, used in both directions. The source's costs are positive, and the step
requires $w(uv) > 0$, so a zero cost never creates a pebble for free.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 2.2 (pebbling step). -/
def PebblingStep {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (C C' : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 0 < w s(u, v) ∧ w s(u, v) ≤ C u ∧
    C' = Function.update (Function.update C u (C u - w s(u, v))) v (C v + 1)

/-- **Solvable pebbling configurations.** Let $G$ be a simple graph on a vertex set $V$ with
natural-number edge costs $w$. A configuration $C : V \to \mathbb{N}$ of pebbles is *solvable*
if for every target vertex $r$ there is a finite, possibly empty, sequence of pebbling steps on
$G$ with costs $w$ leading from $C$ to a configuration with at least one pebble on $r$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Sections 2.2 and 3.1 (`r`-solvability, for
every target). -/
def PebblingSolvable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (C : V → ℕ) : Prop :=
  ∀ r : V, ∃ C', Relation.ReflTransGen (PebblingStep G w) C C' ∧ 1 ≤ C' r

/-- **Configurations covering every vertex are solvable.** Let $G$ be a simple graph with
natural-number edge costs $w$. Every pebbling configuration $C$ on $G$ with $C(r) \ge 1$ for
every vertex $r$ is solvable with respect to $G$ and $w$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 2.2
definition. -/
theorem pebblingSolvable_of_forall_pos {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℕ) {C : V → ℕ} (hC : ∀ r, 1 ≤ C r) : PebblingSolvable G w C :=
  fun r => ⟨C, Relation.ReflTransGen.refl, hC r⟩

/-- **Probability that a random pebbling configuration is solvable.** Let $G$ be a simple graph on
a finite vertex set $V$ with $n$ vertices, let $w$ assign a natural-number cost to each unordered
pair of vertices, and let $t \ge 0$ be an integer. A configuration of $t$ pebbles is a function
$C : V \to \mathbb{N}$ with $\sum_{v \in V} C(v) = t$. The value is the number of configurations
of $t$ pebbles that are solvable with respect to $G$ and $w$, divided by the number of all
configurations of $t$ pebbles; that is, the probability that a configuration of $t$ pebbles
chosen uniformly at random is solvable. If there are no configurations of $t$ pebbles ($V$ empty
and $t > 0$), the value is $0$.

For $n \ge 1$ there are $\binom{n + t - 1}{t}$ configurations of $t$ pebbles (the space
$D_{G,t}$ of the source).

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.1 (configuration model). -/
noncomputable def solvableConfigurationProb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (t : ℕ) : ℝ :=
  ({C : V → ℕ | ∑ v, C v = t ∧ PebblingSolvable G w C}.ncard : ℝ) /
    ({C : V → ℕ | ∑ v, C v = t}.ncard : ℝ)

/-- **The solvability probability is at most one.** For every simple graph $G$ on a finite
vertex set with natural-number edge costs $w$ and every $t \ge 0$, the probability that a
uniformly random configuration of $t$ pebbles on $G$ is solvable is at most $1$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 3.1
definition. -/
theorem solvableConfigurationProb_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℕ) (t : ℕ) : solvableConfigurationProb G w t ≤ 1 := by
  have hfin : {C : V → ℕ | ∑ v, C v = t}.Finite := by
    refine (Set.Finite.pi (t := fun _ : V => Set.Iic t) fun _ => Set.finite_Iic t).subset ?_
    intro C hC v _
    rw [Set.mem_ofPred_eq] at hC
    rw [Set.mem_Iic, ← hC]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hle := Set.ncard_le_ncard (fun C (hC : C ∈ {C : V → ℕ | ∑ v, C v = t ∧
    PebblingSolvable G w C}) => (show C ∈ {C : V → ℕ | ∑ v, C v = t} from hC.1)) hfin
  exact div_le_one_of_le₀ (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- **Grid graph.** For natural numbers $d$ and $k$, the $d$-dimensional grid
$P_k^d = \square_{i<d} P_k$ is the simple graph on $\{0, \dots, k-1\}^d$ in which $x$ and $y$
are adjacent when there is a coordinate $i$ with $x_j = y_j$ for all $j \ne i$ and
$|x_i - y_i| = 1$. For $k = 2$ this is the $d$-cube $Q_d$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 2.1 (grids and cubes). -/
def gridGraph (d k : ℕ) : SimpleGraph (Fin d → Fin k) where
  Adj x y := ∃ i, (∀ j, j ≠ i → x j = y j) ∧ ((x i : ℕ) + 1 = y i ∨ (y i : ℕ) + 1 = x i)
  symm := ⟨fun _ _ ⟨i, h1, h2⟩ => ⟨i, fun j hj => (h1 j hj).symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, h2⟩ => by omega⟩

/-- **Grid edge costs.** Let $d$ and $k$ be natural numbers and let $w_0, \dots, w_{d-1}$ be
natural numbers. The grid cost with cost $w_i$ in coordinate $i$ assigns to each unordered pair
$\{x, y\}$ of points of $\{0, \dots, k-1\}^d$ the sum of the $w_i$ over the coordinates $i$ with
$x_i \ne y_i$. On an edge of the grid exactly one coordinate differs, so an edge in coordinate
$i$ costs $w_i$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.2 (cost `wᵢ` in coordinate `i`). -/
def gridCost {d k : ℕ} (w : Fin d → ℕ) : Sym2 (Fin d → Fin k) → ℕ :=
  Sym2.lift ⟨fun x y => ∑ i, if x i = y i then 0 else w i, fun x y =>
    Finset.sum_congr rfl fun i _ => by simp only [eq_comm]⟩

/-- **Grid cost of a pair differing in one coordinate.** Let $d$ and $k$ be natural numbers, let
$w_0, \dots, w_{d-1}$ be natural numbers, let $x, y \in \{0, \dots, k-1\}^d$, and let
$i \in \{0, \dots, d-1\}$. If $x_i \ne y_i$ and $x_j = y_j$ for every $j \ne i$, then the grid
cost of the pair $\{x, y\}$ with cost $w_j$ in coordinate $j$ is $w_i$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, characteristic lemma of the Section 3.2
grid costs. -/
theorem gridCost_eq_of_eq_off {d k : ℕ} (w : Fin d → ℕ) {x y : Fin d → Fin k} {i : Fin d}
    (hj : ∀ j, j ≠ i → x j = y j) (hi : x i ≠ y i) : gridCost w s(x, y) = w i := by
  show (∑ j, if x j = y j then 0 else w j) = w i
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hj j hji]) (by simp)]
  simp [hi]

/-- **Threshold version of Geroldinger's theorem.** Let $d \ge 0$, let $p_1, \dots, p_d$ be
primes, not necessarily distinct, and for each $k$ let
$\Gamma_k = \prod_{i=1}^d \mathbb{Z}/p_i^k\mathbb{Z}$, and let $P_{1/2}(\Gamma_k)$ be its
half-good threshold. Write $\lg = \log_2$. Then there is a real constant $C$ such that for all
sufficiently large $k$,

$$
P_{1/2}(\Gamma_k) \le k^d \exp\left(\left(\frac{(d+1)! \prod_{i=1}^d \lg p_i}{2}
\lg k\right)^{1/(d+1)} - \frac{d}{d+1} \lg \lg k + C\right).
$$

This is an upper bound only, as in the journal record (the source's final comments say the bound
need not be an equality). The case $d = 0$, where $\Gamma_k$ is trivial, is included.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 4 (`integers-2024-A93-thm-4`). -/
public theorem_wanted halfGoodThreshold_pi_zmod_prime_pow_le (d : ℕ) (p : Fin d → ℕ)
    [∀ i, Fact (p i).Prime] :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      (halfGoodThreshold ((i : Fin d) → ZMod (p i ^ k)) : ℝ) ≤
        (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (p i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) + C)

/-- **Bushaw–Kettle pebbling threshold for grids.** Let $d \ge 1$ and let $w_0, \dots, w_{d-1}$
be natural numbers with $w_i \ge 2$ for every $i$. For each $k$ give the grid $P_k^d$ on
$\{0, \dots, k-1\}^d$ the cost $w_i$ on every edge in coordinate $i$, and let
$t : \mathbb{N} \to \mathbb{R}$ be a threshold function, as $k \to \infty$, for the probability
that a uniformly random configuration of $s$ pebbles on $P_k^d$ is solvable. Write $\lg = \log_2$
and

$$
A(k) = \left(\frac{(d+1)! \prod_{i<d} \lg w_i}{2} \lg k\right)^{1/(d+1)} -
\frac{d}{d+1} \lg \lg k.
$$

Then there is a real constant $C$ such that for all sufficiently large $k$,

$$
k^d e^{A(k) - C} \le t(k) \le k^d e^{A(k) + C},
$$

that is, with $n = k^d$, $t(k) = n \exp[A(k) + O(1)]$.

The hypothesis $w_i \ge 2$ is not part of the quoted statement: with all costs equal to $1$
every nonempty configuration is solvable, so the thresholds are bounded while the right side
tends to infinity. Likewise $d \ge 1$ excludes $d = 0$, where the grid is a single vertex.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 9 (quoting Bushaw and Kettle,
`integers-2024-A93-thm-9`). -/
public theorem_wanted gridGraph_pebbling_threshold_eq (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℕ)
    (hw : ∀ i, 2 ≤ w i) (t : ℕ → ℝ)
    (ht : IsThresholdFunction
      (fun k s => solvableConfigurationProb (gridGraph d k) (gridCost w) s) t) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (w i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) - C) ≤ t k ∧
        t k ≤ (k : ℝ) ^ d * Real.exp ((((d + 1).factorial : ℝ) * (∏ i, Real.logb 2 (w i)) / 2 *
            Real.logb 2 k) ^ ((1 : ℝ) / (d + 1)) -
          (d : ℝ) / (d + 1) * Real.logb 2 (Real.logb 2 k) + C)

/-- **Pebbling threshold bounds for the cubes (Czygrinow–Wagner, Alon).** For $d \ge 0$ let
$Q_d$ be the $d$-cube, the grid graph on $\{0, 1\}^d$, with cost $2$ on every edge, and let
$t : \mathbb{N} \to \mathbb{R}$ be a threshold function, as $d \to \infty$, for the probability
that a uniformly random configuration of $s$ pebbles on $Q_d$ is solvable. Write $n = 2^d$ and
$\lg = \log_2$. Then for every real $\varepsilon > 0$, as $d \to \infty$,
$n^{1-\varepsilon} = O(t(d))$ and $t(d) = O\big(n / (\lg \lg n)^{1-\varepsilon}\big)$, that is,
$t \in \Omega(n^{1-\varepsilon}) \cap O\big(n / (\lg \lg n)^{1-\varepsilon}\big)$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 10 (`integers-2024-A93-thm-10`). -/
public theorem_wanted cube_pebbling_threshold_bounds (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction
      (fun d s => solvableConfigurationProb (gridGraph d 2) (gridCost fun _ => 2) s) t) :
    (fun d : ℕ => ((2 : ℝ) ^ d) ^ (1 - ε)) =O[Filter.atTop] t ∧
      t =O[Filter.atTop]
        fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε)

/-- **Threshold for good sequences in $\mathbb{Z}_2^d$.** Write $\lg = \log_2$. Let $t$ be a
threshold function, in $d$, for the probability that a uniformly random sequence of $s$ elements
of $\mathbb{Z}_2^d$ is good, and write $n = 2^d$. Then for every $\varepsilon > 0$,
$t(d) = O\left(n / (\lg \lg n)^{1-\varepsilon}\right)$ as $d \to \infty$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 11 (`integers-2024-A93-thm-11`). -/
public theorem_wanted zmod_two_pi_good_threshold_isBigO (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε)

/-- **Threshold for good sequences in $\mathbb{Z}/35^k\mathbb{Z}$.** Write $\lg = \log_2$. Let $t$
be a threshold function, in $k$, for the probability that a uniformly random sequence of $s$
elements of $\mathbb{Z}/35^k\mathbb{Z}$ is good. Then there is a real constant $C$ such that for
all sufficiently large $k$,
$$t(k) \le k^2 \exp\left((3 \lg 5 \lg 7 \lg k)^{1/3} - \tfrac{2}{3} \lg \lg k + C\right).$$

The source writes the prefactor as $n$; here $n = k^2$, the factor $k^d$ of the source's
Theorem 4 at $d = 2$, since $\mathbb{Z}/35^k\mathbb{Z} \cong \mathbb{Z}/5^k\mathbb{Z} \times
\mathbb{Z}/7^k\mathbb{Z}$. The constant $C$ depends on $t$: thresholds are only determined up to
constant factors, so no single $C$ serves every threshold.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Corollary 2 (`integers-2024-A93-cor-2`). -/
public theorem_wanted zmod_thirtyFive_pow_good_threshold_le (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun k s => goodSequenceProb (ZMod (35 ^ k)) s) t) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      t k ≤ (k : ℝ) ^ 2 * Real.exp ((3 * Real.logb 2 5 * Real.logb 2 7 * Real.logb 2 k) ^
          ((1 : ℝ) / 3) - 2 / 3 * Real.logb 2 (Real.logb 2 k) + C)

end

end MetaMathlibExt
