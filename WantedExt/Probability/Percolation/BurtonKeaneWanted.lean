/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import MathlibExt.Probability.Percolation.Theta

/-!
# Uniqueness of the infinite cluster in Bernoulli bond percolation

The Burton–Keane theorem for Bernoulli bond percolation on `ℤ^d`: for every `p ∈ [0, 1]` there is
almost surely at most one infinite open cluster.

The ported library proves that the number of infinite clusters `N` is almost surely constant
under any translation-ergodic measure (`StatMech.Percolation.numInfiniteClusters_ae_const`),
the first step of the Burton–Keane argument, but not the uniqueness statement.

## Main statements

* `burton_keane_bernoulli`: `N ≤ 1` almost surely under `bernoulliProductMeasure p`.

## References

* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Percolation.BurtonKeaneWanted

open MeasureTheory StatMech StatMech.Percolation
open scoped NNReal

/-- **Burton–Keane theorem** for Bernoulli bond percolation. For every dimension `d` and every
`p ∈ [0, 1]`, almost surely under the Bernoulli(`p`) bond percolation measure on `ℤ^d` there is
at most one infinite open cluster.

Source: R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121
(1989), 501–505. -/
public theorem_wanted burton_keane_bernoulli :
    ∀ (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1),
      ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Lattice.Site d)) p hp),
        numInfiniteClusters d ω ≤ 1

end MathlibExt.Probability.Percolation.BurtonKeaneWanted
