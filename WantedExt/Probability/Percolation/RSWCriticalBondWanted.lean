/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.Percolation.RSW.Defs

/-!
# Russo–Seymour–Welsh bounds for critical bond percolation on `ℤ²`

The Russo–Seymour–Welsh theorem for Bernoulli bond percolation on `ℤ²` at `p = 1/2`: for every
aspect ratio `α > 0` the probability of an open left–right crossing of the rectangle
`[0, ⌊αn⌋] × [0, n]` is bounded away from `0`, and (once the rectangle is not degenerate) away
from `1`, uniformly in `n`.

The ported library defines the crossing events and the box-crossing property
(`StatMech.RSW.Box.boxCrossingEvent`, `StatMech.RSW.Box.P5`) but proves no RSW inequality.

## Main statements

* `rsw_box_crossing_lower`: the box-crossing property `P5` for `ℙ_{1/2}`.
* `rsw_box_crossing_two_sided`: `c ≤ ℙ_{1/2}(crossing) ≤ 1 - c` whenever `αn ≥ 1`.

The hypothesis `1 ≤ α * n` in the two-sided bound is needed: if `⌊αn⌋ = 0` the rectangle is a
single column, its left and right sides coincide, and the crossing event is certain.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §11.7.
-/

@[expose] public section

namespace MathlibExt.Probability.Percolation.RSWCriticalBondWanted

open MeasureTheory StatMech StatMech.RSW.Box
open scoped NNReal

/-- The critical bond percolation measure `ℙ_{1/2}` on `{0, 1}^{Sym2 ℤ²}`: every coordinate is
open independently with probability `1/2`. -/
noncomputable abbrev criticalBondMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site 2))) :=
  bernoulliProductMeasure (1 / 2 : ℝ≥0) (by norm_num)

/-- **Russo–Seymour–Welsh theorem** (lower bound) for critical bond percolation on `ℤ²`: for
every `α > 0` there is `c > 0` with `ℙ_{1/2}(open left–right crossing of [0, ⌊αn⌋] × [0, n]) ≥ c`
for every `n`.

Source: L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978); P. D. Seymour and
D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete Math. 3 (1978);
G. Grimmett, *Percolation*, 2nd ed. (1999), §11.7. -/
public theorem_wanted rsw_box_crossing_lower :
    P5 (fun _ => criticalBondMeasure.real)

/-- **Russo–Seymour–Welsh theorem** (two-sided form) for critical bond percolation on `ℤ²`: for
every `α > 0` there is `c > 0` with
`c ≤ ℙ_{1/2}(open left–right crossing of [0, ⌊αn⌋] × [0, n]) ≤ 1 - c` for every `n` with
`αn ≥ 1`. The upper bound follows from the lower bound for the dual crossing.

Source: L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978); P. D. Seymour and
D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete Math. 3 (1978);
G. Grimmett, *Percolation*, 2nd ed. (1999), §11.7. -/
public theorem_wanted rsw_box_crossing_two_sided :
    ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ α * n →
      c ≤ criticalBondMeasure.real (boxCrossingEvent α n) ∧
        criticalBondMeasure.real (boxCrossingEvent α n) ≤ 1 - c

end MathlibExt.Probability.Percolation.RSWCriticalBondWanted
