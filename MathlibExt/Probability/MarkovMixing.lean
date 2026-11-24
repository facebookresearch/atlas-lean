/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Floor.Defs

/-!
# Markov-chain mixing vocabulary

Total variation distance on a finite set, mixing at a time (the `1/4` convention), cutoff for a
family of distance profiles, discrete tori with their coordinate steps, the `±1` sign of a Boolean
spin, and the number of monochromatic edges of a colouring (Potts energy). Shared by the AimPL
"Markov chain mixing times" conjecture entries.
-/

@[expose] public section


namespace MathlibExt.Probability.MarkovMixing

/-- **Discrete torus.** For natural numbers $d$ and $n$, the vertices of the discrete torus
$\mathbb{Z}_n^d$ are the functions from $\{0, \dots, d-1\}$ to $\{0, \dots, n-1\}$, that is, the
$d$-tuples of residues modulo $n$. -/
abbrev Torus (d n : ℕ) := Fin d → Fin n

/-- **Coordinate step on the discrete torus.** For a vertex $x$ of the discrete torus
$\mathbb{Z}_n^d$ and a coordinate $k \in \{0, \dots, d-1\}$, the neighbour $x + e_k$ is obtained
from $x$ by replacing its $k$-th coordinate $x_k$ by $(x_k + 1) \bmod n$ and leaving the other
coordinates unchanged. -/
def stepUp {d n : ℕ} (k : Fin d) (x : Torus d n) : Torus d n :=
  Function.update x k ⟨((x k).val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt (x k).2)⟩

/-- **Sign of a Boolean spin.** The sign of a Boolean spin is the real number $+1$ if the spin
is true and $-1$ if it is false. -/
noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- **Total variation distance of functions on a finite set.** For real-valued functions $\mu$
and $\nu$ on a finite set $S$, their total variation distance is
$\frac{1}{2} \sum_{y \in S} |\mu(y) - \nu(y)|$. -/
noncomputable def tvDist {S : Type*} [Fintype S] (μ ν : S → ℝ) : ℝ :=
  (1 / 2) * ∑ y, |μ y - ν y|

/-- **Total variation distance of a matrix row from a function.** For a real $S \times S$ matrix
$Q$ indexed by a finite set $S$, a function $\pi : S \to \mathbb{R}$ and $x \in S$, this is the
total variation distance $\frac{1}{2} \sum_{y \in S} |Q(x, y) - \pi(y)|$ of the row $x$ of $Q$
from $\pi$. -/
noncomputable def tvRow {S : Type*} [Fintype S] (Q : Matrix S S ℝ) (π : S → ℝ) (x : S) : ℝ :=
  (1 / 2) * ∑ y, |Q x y - π y|

/-- **Being $1/4$-mixed at a given time.** Let $S$ be a finite set, $P$ a real $S \times S$
matrix and $\pi : S \to \mathbb{R}$. Then $P$ is mixed at time $t \in \mathbb{N}$ with respect to
$\pi$ if for every $x \in S$ the total variation distance
$\frac{1}{2} \sum_{y \in S} |P^t(x, y) - \pi(y)|$ between the row $x$ of the matrix power $P^t$
and $\pi$ is at most $1/4$.

The mixing time is the least $t$ at which $P$ is mixed. -/
def IsMixedAt {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (π : S → ℝ)
    (t : ℕ) : Prop :=
  ∀ x, tvDist (fun y => (P ^ t) x y) π ≤ 1 / 4

open Classical in
/-- **Number of monochromatic edges.** For a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ and a colouring $\sigma$ of its vertices with colours in
$\{0, \dots, q-1\}$, this is the number of edges $uv$ of $G$ with $\sigma_u = \sigma_v$, as a real
number, each edge counted once. -/
noncomputable def monoEdges {n q : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin q) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if G.Adj u v ∧ σ u = σ v then 1 else 0

/-- **Cutoff for a family of distance profiles.** A family of real numbers $d_n(t)$, indexed by
$n \in \mathbb{N}$ and times $t \in \mathbb{N}$, exhibits cutoff if there are real numbers $t_n$
with $t_n \to \infty$ such that for every $\eta$ with $0 < \eta < 1$, as $n \to \infty$,
$d_n(\lceil (1+\eta) t_n \rceil) \to 0$ and $d_n(\lfloor (1-\eta) t_n \rfloor) \to 1$. Here the
ceiling and floor are taken in $\mathbb{N}$, so a negative argument gives $0$. -/
def HasCutoff (d : ℕ → ℕ → ℝ) : Prop :=
  ∃ t : ℕ → ℝ, Filter.Tendsto t Filter.atTop Filter.atTop ∧ ∀ η : ℝ, 0 < η → η < 1 →
    Filter.Tendsto (fun n => d n ⌈(1 + η) * t n⌉₊) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => d n ⌊(1 - η) * t n⌋₊) Filter.atTop (nhds 1)

@[simp] theorem sgn_true : sgn true = 1 := by simp [sgn]

@[simp] theorem sgn_false : sgn false = -1 := by simp [sgn]

@[simp] theorem tvDist_self {S : Type*} [Fintype S] (μ : S → ℝ) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_comm {S : Type*} [Fintype S] (μ ν : S → ℝ) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist, abs_sub_comm]

theorem tvRow_eq_tvDist {S : Type*} [Fintype S] (Q : Matrix S S ℝ) (π : S → ℝ) (x : S) :
    tvRow Q π x = tvDist (Q x) π :=
  rfl

end MathlibExt.Probability.MarkovMixing
