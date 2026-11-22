/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Percolation.PcNontrivial

/-!
# Continuity of the percolation probability

The percolation probability `p ↦ θ_d(p)` of Bernoulli bond percolation on `ℤ^d` is continuous on
`[0, 1] \ {p_c}` and right-continuous at `p_c`. Right-continuity everywhere holds because `θ` is a
decreasing limit of the continuous nondecreasing polynomials `p ↦ ℙ_p(0 ↔ ∂Λ_n)`; continuity
from the left above `p_c` uses the uniqueness of the infinite cluster. Whether `θ` is continuous
at `p_c`, that is whether `θ(p_c) = 0`, is open in dimensions `3 ≤ d ≤ 10`.

## Main statements

* `theta_continuousOn_ne_pc`: continuity on `[0, 1] \ {p_c}`.
* `theta_continuousWithinAt_pc`: right-continuity at `p_c`.

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of
  7 October 2018), Proposition 3.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Percolation.ThetaContinuityWanted

open StatMech.Percolation
open scoped NNReal

/-- **Percolation probability on the parameter interval.** The percolation probability `θ_d` as
a function on `{p : ℝ≥0 // p ≤ 1} = [0, 1]`. -/
noncomputable abbrev thetaOnUnit (d : ℕ) : {p : ℝ≥0 // p ≤ 1} → ℝ := fun p => theta d p.1 p.2

/-- **Continuity of θ away from p_c.** For Bernoulli bond percolation on `ℤ^d`, the map
`p ↦ θ_d(p)` is continuous on `[0, 1] \ {p_c(d)}`. Source: H. Duminil-Copin, *Introduction to
Bernoulli percolation*, lecture notes (2018), Proposition 3.2; the proof there uses the
uniqueness of the infinite cluster (Theorem 3.1) for continuity from the left above `p_c`. -/
public theorem_wanted theta_continuousOn_ne_pc (d : ℕ) :
    ContinuousOn (thetaOnUnit d) {p | p.1 ≠ pc d}

/-- **Right-continuity of θ at p_c.** For Bernoulli bond percolation on `ℤ^d`, the map
`p ↦ θ_d(p)` is right-continuous at `p_c(d)`. Source: H. Duminil-Copin, *Introduction to
Bernoulli percolation*, lecture notes (2018), Proposition 3.2. -/
public theorem_wanted theta_continuousWithinAt_pc (d : ℕ) :
    ContinuousWithinAt (thetaOnUnit d) {p | pc d ≤ p.1} ⟨pc d, pc_le_one⟩

end MathlibExt.Probability.Percolation.ThetaContinuityWanted
