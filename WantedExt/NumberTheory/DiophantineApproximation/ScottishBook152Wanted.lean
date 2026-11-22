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

/-- The number of integer lattice points in the disc of radius `1` centred
at `n * w`, where `w = (w.1, w.2)`. -/
noncomputable def DiscLatticeCount (w : ℝ × ℝ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | ((p.1 : ℝ) - (n : ℝ) * w.1) ^ 2 +
    ((p.2 : ℝ) - (n : ℝ) * w.2) ^ 2 ≤ 1}

/--
A disc of radius `1` covers at least two and at most five lattice points.
Translating it through vectors `n * w` (`n = 1, 2, ...`), where `w` has both
coordinates irrational and their ratio irrational, the frequencies of the
counts `2`, `3`, `4` exist: for each `m ∈ {2, 3, 4}` the proportion of
`n < N` with exactly `m` lattice points in the translated disc converges as
`N → ∞`. The frequency values themselves are not pinned down here: they are
the measures of the corresponding regions for the limiting distribution of
`n * w` modulo the lattice, and in particular depend on `w`.
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
