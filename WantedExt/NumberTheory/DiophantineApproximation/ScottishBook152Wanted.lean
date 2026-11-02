/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Defs.Filter

@[expose] public section

namespace MathlibExt.NumberTheory.DiophantineApproximation.ScottishBook152Wanted

/-- **Lattice points in a translated unit disc.** For $w = (w_1, w_2) \in \mathbb{R}^2$ and a
natural number $n$, the disc lattice count is the number of integer points
$(p_1, p_2) \in \mathbb{Z}^2$ in the closed disc of radius $1$ centred at $n w$, that is, with
$(p_1 - n w_1)^2 + (p_2 - n w_2)^2 \le 1$. -/
noncomputable def DiscLatticeCount (w : ℝ × ℝ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | ((p.1 : ℝ) - (n : ℝ) * w.1) ^ 2 +
    ((p.2 : ℝ) - (n : ℝ) * w.2) ^ 2 ≤ 1}

/--
**Steinhaus's disc frequencies exist.** Let $w = (w_1, w_2) \in \mathbb{R}^2$ be such that
$w_1$, $w_2$ and $w_1 / w_2$ are all irrational, and for each natural number $n$ let $c(n)$ be the
disc lattice count of $w$ and $n$, the number of integer lattice points in the closed disc of
radius $1$ centred at $n w$. Then for each $m$ equal to $2$, $3$ or $4$, the proportion of the
integers $n$ with $0 \le n < N$ and $c(n) = m$ converges to a real number as $N \to \infty$.

A closed disc of radius $1$ always covers at least two and at most five lattice points. The
frequency values themselves are not pinned down here: they are the measures of the corresponding
regions for the limiting distribution of $n w$ modulo the lattice, and in particular depend on
$w$.

Source: H. Steinhaus, Problem 152 of the Scottish Book; J. Mycielski's
commentary in Mauldin (ed.), The Scottish Book, 2nd ed. (2015) explains the
solution using facts from Diophantine approximation, as reported in the 2026
survey "90+ years of the Scottish Book" (arXiv:2603.27867).
-/
theorem_wanted steinhausDiscFrequenciesExist :
    ∀ w : ℝ × ℝ, Irrational w.1 → Irrational w.2 → Irrational (w.1 / w.2) →
      ∀ m : ℕ, m = 2 ∨ m = 3 ∨ m = 4 →
        ∃ freq : ℝ, Filter.Tendsto
          (fun N : ℕ => ((Finset.filter (fun n => DiscLatticeCount w n = m)
            (Finset.range N)).card : ℝ) / (N : ℝ))
          Filter.atTop (nhds freq)

end MathlibExt.NumberTheory.DiophantineApproximation.ScottishBook152Wanted
