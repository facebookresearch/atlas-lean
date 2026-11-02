/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Analysis.Series.ScottishBook5BoundedWanted

/-- **Index sequences of density one.** A sequence $s \colon \mathbb{N} \to \mathbb{N}$ has
density one when it is strictly increasing and $s(n+1)/(n+1) \to 1$ as $n \to \infty$.

For a strictly increasing sequence of natural numbers this ratio condition is equivalent to the
usual counting definition of density $1$ for its set of values. -/
def HasDensityOne (s : ℕ → ℕ) : Prop :=
  StrictMono s ∧
  Filter.Tendsto (fun n => ((s (n + 1) : ℝ)) / ((n : ℝ) + 1)) Filter.atTop (nhds 1)

/-- **Asymptotically convergent sequences.** A real sequence $(x_n)_{n \in \mathbb{N}}$ is
asymptotically convergent to a real number $S$ when there is an index sequence $s$ of density
one such that $x_{s(n)} \to S$ as $n \to \infty$.

Source: this is the typescript's definition, verbatim in content. -/
def AsymptoticallyConvergent (x : ℕ → ℝ) (S : ℝ) : Prop :=
  ∃ s : ℕ → ℕ, HasDensityOne s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (nhds S)

/-- **Summation by a matrix method.** A real matrix $(a_{ik})_{i,k \in \mathbb{N}}$ sums a real
sequence $(x_k)_{k \in \mathbb{N}}$ to a real number $S$ when for every row $i$ the series
$\sum_k a_{ik} x_k$ converges unconditionally (equivalently, absolutely) and the row sums
$\sum_k a_{ik} x_k$ tend to $S$ as $i \to \infty$. -/
def MatrixSums (a : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (S : ℝ) : Prop :=
  (∀ i : ℕ, Summable (fun k => a i k * x k)) ∧
  Filter.Tendsto (fun i => ∑' k, a i k * x k) Filter.atTop (nhds S)

/-- **Permanent matrix methods.** A real matrix $(a_{ik})_{i,k \in \mathbb{N}}$ is a permanent
(regular, or Toeplitz) method when it sums every convergent real sequence to its limit: for every
real sequence $x$ and real number $S$ with $x_n \to S$, the matrix sums $x$ to $S$.

The Silverman–Toeplitz conditions characterise exactly these methods.

Source: "Toeplitz method" is pinned to this standard reading; the typescript does not define it. -/
def IsPermanent (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : ℕ → ℝ, ∀ S : ℝ, Filter.Tendsto x Filter.atTop (nhds S) → MatrixSums a x S

/-- **Bounded sequences.** A real sequence $(x_n)_{n \in \mathbb{N}}$ is bounded when there is a
real number $B$ with $|x_n| \le B$ for all $n$. -/
def IsBounded (x : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, |x n| ≤ B

/-- **The bounded case of Scottish Book Problem 5.** There is a real matrix
$(a_{ik})_{i,k \in \mathbb{N}}$ that is a permanent matrix method such that for every bounded real
sequence $x$ and every real number $S$, the matrix sums $x$ to $S$ if and only if $x$ is
asymptotically convergent to $S$. -/
def ScottishBookProblem5Claim : Prop :=
  ∃ a : ℕ → ℕ → ℝ, IsPermanent a ∧
    ∀ x : ℕ → ℝ, IsBounded x →
      ∀ S : ℝ, MatrixSums a x S ↔ AsymptoticallyConvergent x S


/-- **Negative answer to Scottish Book Problem 5 for bounded sequences.** There is no real matrix
$(a_{ik})_{i,k \in \mathbb{N}}$ that is a permanent matrix method such that for every bounded real
sequence $x$ and every real number $S$, the matrix sums $x$ to $S$ if and only if $x$ is
asymptotically convergent to $S$.

Source: the typescript itself, Ad 5 (Mazur),
PDF p.5 / printed p.2, verified against the typescript page.
Ad 5 (2) states verbatim: "If a method (a_{ik}) sums all the
convergent sequences and every bounded sequence summable by the
sequence [sic — the method] is asymptotically convergent, then there
exists a sequence
of increasing integers {kₙ} with density 1, such that for every
bounded sequence {ξₙ} summable by this method, the sequence
{ξ_{kₙ}} is convergent." The typescript then draws the corollary
verbatim: "from (2) it follows that a permanent method summing all
bounded asymptotically convergent sequences must also sum some
other bounded sequences" — i.e. no permanent method sums exactly
the bounded asymptotically convergent sequences, which refutes the
equivalence formalized in `ScottishBookProblem5Claim`.
Proof sketch of the corollary from (2): suppose a permanent method
`a` summed exactly the bounded asymptotically convergent sequences
(to the right limits). Then `a` satisfies both hypotheses of (2)
(permanent, and every bounded `a`-summable sequence is
asymptotically convergent, by the assumed equivalence), so (2)
gives a fixed density-1 sequence {kₙ} along which every bounded
`a`-summable sequence converges. Let J = ℕ ∖ {k_{m²} : m ∈ ℕ};
J has density 1 (since k_{m²} ≥ m², the excluded set has density
0), and let ξ be 0 on J and 1 elsewhere. Then ξ is bounded and
asymptotically convergent to 0 (via J), so `a` sums ξ to 0; but
ξ_{kₙ} equals 1 when n is a square and 0 otherwise, so it
diverges — contradicting (2). (Cesàro does not satisfy (2)'s
hypothesis — e.g. (-1)^n is Cesàro-summable but not asymptotically
convergent — so it is not a counterexample to (2).)
Note: the earlier Phase 3c entry recorded only that Ad 5 (1) does
not settle the bounded question; Ad 5 (2) and its corollary do.
-/
theorem_wanted mazur5BoundedRefuted : ¬ ScottishBookProblem5Claim

end MathlibExt.Analysis.Series.ScottishBook5BoundedWanted
