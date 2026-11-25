/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting line-compatible sequences (Erdős Problem 733)

Erdős Problem 733: call a sequence `1 < X₁ ≤ ⋯ ≤ X_m ≤ n` line-compatible if there is a set of `n`
points in `ℝ²` such that there are `m` lines `ℓ₁, …, ℓ_m` containing at least two points, and the
number of points on `ℓ_i` is exactly `X_i`. Prove that there are at most `exp(O(n^{1/2}))` many
line-compatible sequences.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #733, https://www.erdosproblems.com/733 (status
PROVED). UnsolvedMath record UM-30006999 (`EP-733`), dataset ulamai/UnsolvedMath v1.8.0.

The lines are all lines determined by the point set (each line through two distinct points, counted
once), as in Erdős Problem 607 (the same count without multiplicities); a sequence is the multiset
of their point counts. `f(n)` is the `Set.ncard` of a finite set. `exp(O(√n))` is `∃ C, ∀ n, f(n) ≤
exp(C √n)` (`f(0) = 1`). Erdős's follow-up on the limit of `log f(n) / √n` is not formalized.
-/

open Classical in
/-- **Line sizes of a planar point set.** For a finite set $P \subseteq \mathbb{R}^2$, this is
the multiset of the numbers $|\ell \cap P|$, where $\ell$ ranges over the lines determined by
$P$, that is, the distinct lines through two distinct points of $P$, each counted once. -/
noncomputable def lineSizes (P : Finset (ℝ × ℝ)) : Multiset ℕ :=
  ((P.offDiag.image fun pq => line[ℝ, pq.1, pq.2]).val.map fun ℓ =>
    (P.filter fun r => r ∈ ℓ).card)

/-- **Number of line-compatible sequences.** For a natural number $n$, $f(n)$ is the number of
distinct multisets that arise as the line sizes of some $n$-point set $P \subseteq \mathbb{R}^2$,
that is, as the multiset of the numbers $|\ell \cap P|$ over the distinct lines $\ell$ through
two distinct points of $P$, each line counted once. These multisets are the line-compatible
sequences for $n$; there are finitely many, since each has at most $n^2$ entries, all at most
$n$. -/
noncomputable def lineCompatibleCount (n : ℕ) : ℕ :=
  {X : Multiset ℕ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineSizes P = X}.ncard

/-- **Subexponential count of line-compatible sequences (statement).** The proposition that
there is a real constant $C$ such that for every natural number $n$, the number $f(n)$ of
line-compatible sequences for $n$ is at most $e^{C \sqrt{n}}$; that is, there are at most
$\exp(O(\sqrt{n}))$ line-compatible sequences. This is Erdős Problem 733. -/
def lineCompatibleCountSubexponential : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, (lineCompatibleCount n : ℝ) ≤ Real.exp (C * Real.sqrt n)

/--
**Szemerédi–Trotter bound on line-compatible sequences.** There is a real constant $C$ such that
for every natural number $n$, the number of line-compatible sequences for $n$, that is, of
distinct multisets of the numbers $|\ell \cap P|$ over the distinct lines $\ell$ through two
distinct points of an $n$-point set $P \subseteq \mathbb{R}^2$, each line counted once, is at
most $e^{C \sqrt{n}}$. This answers Erdős Problem 733.

Source: T. F. Bloom, Erdős Problems,
Problem #733, https://www.erdosproblems.com/733 (status PROVED); resolution: E. Szemerédi and W. T.
Trotter, Extremal problems in discrete geometry, Combinatorica 3 (1983), 381-392,
erdosproblems.com/733: 'This is true, and was proved by Szemerédi and Trotter',
https://doi.org/10.1007/BF02579194.
-/
public theorem_wanted lineCompatibleCountSubexponential_holds : lineCompatibleCountSubexponential

end MathlibExt.Combinatorics.LineCompatibleSequencesErdosProblem733Wanted
