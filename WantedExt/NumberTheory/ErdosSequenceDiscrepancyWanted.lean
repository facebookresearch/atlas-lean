/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 992: discrepancy of fractional parts of `α * xₙ`

Erdős Problem 992 asks: for integers `x₁ < x₂ < ⋯`, is it true that for
almost all `α ∈ [0, 1]` the discrepancy
`D(N) = max over intervals I of |count - |I| * N|` satisfies
`D(N) ≪ N ^ (1/2) * (log N) ^ o(1)`?

Gaps vs the source record:
- Only the first (weaker) bound is formalized; the stronger
  `(log log N)`-variant mentioned in the record is omitted.
- The record takes the maximum over all intervals; here the discrepancy is
  the supremum over closed intervals with rational endpoints in `[0, 1]`
  (so that counting is well-defined with decidable membership), which
  approximates the full-interval supremum.
- Indexing is 0-based (`x : ℕ → ℤ` with `StrictMono x`) rather than 1-based.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted

/-! Source record `EP-992`. -/
open MeasureTheory Filter

open Classical in
/-- **Counting fractional parts in a rational interval.** For a sequence of integers
$(x_n)_{n \ge 0}$, a real number $\alpha$, a natural number $N$ and rationals $p, q$, the number of
indices $n < N$ for which the fractional part $\{\alpha x_n\}$ lies in the closed interval
$[p, q]$. -/
noncomputable def CountQ (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (p q : ℚ) : ℕ :=
  ((Finset.range N).filter fun n =>
    Int.fract (α * (x n : ℝ)) ∈ Set.Icc (p : ℝ) (q : ℝ)).card

/-- **Discrepancy of fractional parts over rational intervals.** For a sequence of integers
$(x_n)_{n \ge 0}$, a real number $\alpha$ and a natural number $N$, the discrepancy $D(N)$ is the
supremum, over rationals $p, q$ with $0 \le p \le q \le 1$, of $\lvert A(p, q) - (q - p) N \rvert$,
where $A(p, q)$ is the number of indices $n < N$ for which the fractional part $\{\alpha x_n\}$
lies in the closed interval $[p, q]$. -/
noncomputable def discrep (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup { d : ℝ | ∃ p q : ℚ, 0 ≤ (p : ℝ) ∧ (q : ℝ) ≤ 1 ∧ (p : ℝ) ≤ (q : ℝ) ∧
    d = |(CountQ x α N p q : ℝ) - ((q : ℝ) - (p : ℝ)) * (N : ℝ)| }

/-- **Erdős Problem 992 on the discrepancy of fractional parts.** For a strictly increasing
sequence of integers $x_0 < x_1 < \cdots$, a real number $\alpha$ and a natural number $N$, let
$D(N)$ be the supremum, over rationals $p, q$ with $0 \le p \le q \le 1$, of
$\lvert A(p, q) - (q - p) N \rvert$, where $A(p, q)$ is the number of indices $n < N$ for which
the fractional part $\{\alpha x_n\}$ lies in $[p, q]$. The statement is that for every such
sequence, for almost every $\alpha \in [0, 1]$ (Lebesgue measure) and every $\varepsilon > 0$,
there is a real constant $C$ such that $D(N) \le C \sqrt{N} (\log N)^{\varepsilon}$ for all
sufficiently large $N$. -/
def conjecture : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ᶠ N : ℕ in atTop,
          discrep x α N ≤ C * Real.sqrt (N : ℝ) * Real.rpow (Real.log (N : ℝ)) ε

/--
**Erdős Problem 992 has a negative answer.** For a sequence of integers $(x_n)_{n \ge 0}$, a real
number $\alpha$ and a natural number $N$, let $D(N)$ be the supremum, over rationals $p, q$ with
$0 \le p \le q \le 1$, of $\lvert A(p, q) - (q - p) N \rvert$, where $A(p, q)$ is the number of
indices $n < N$ for which the fractional part $\{\alpha x_n\}$ lies in $[p, q]$. It is not true
that for every strictly increasing sequence of integers $x_0 < x_1 < \cdots$, for almost every
$\alpha \in [0, 1]$ and every $\varepsilon > 0$ there is a real constant $C$ with
$D(N) \le C \sqrt{N} (\log N)^{\varepsilon}$ for all sufficiently large $N$.

Berkes and Philipp construct an increasing integer sequence $(n_k)$ with
$\limsup_N \lvert \sum_{k \le N} \cos(2\pi n_k \alpha) \rvert / \sqrt{N \log N} = \infty$ for almost
every $\alpha$; by Koksma's inequality, $D(N)$ is then not $O(\sqrt{N} (\log N)^{\varepsilon})$ for
$\varepsilon < 1/2$.

Source: C. Aistleitner, I. Berkes, R. Tichy, Lacunary sequences in analysis, probability and
number theory, arXiv preprint (2023), arXiv:2301.05561 (reporting I. Berkes, W. Philipp, J.
London Math. Soc. (2) 50 (1994), 454-464), https://arxiv.org/abs/2301.05561. Moved from
`OpenConjectures/NumberTheory/ErdosSequenceDiscrepancy`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted
