/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Percolation.Theta

/-!
# Exponential decay of the cluster volume below `p_c`

For Bernoulli bond percolation on `ℤ^d`, `d ≥ 2`, and `p < p_c`, the number of sites of the cluster
of the origin has an exponential tail. The repository proves exponential decay of the radius
(`StatMech.Percolation.crossProb_exp_decay_of_lt_pc`) and finite expected volume
(`StatMech.Percolation.summable_connProb_of_lt_pc`), not this tail bound.

## Main statements

* `cluster_volume_exp_decay`: `ℙ_p(|C(0)| ≥ n) ≤ C e^{-cn}` for every `n`.

The lecture notes state the bound as `exp(-c'_p n)` for every `n`. Since the origin always belongs
to its cluster, `ℙ_p(|C(0)| ≥ 1) = 1`, so that form needs either a prefactor or a restriction to
large `n`; the statement below carries a prefactor `C`, as the other decay statements of the
repository do.

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of
  7 October 2018), Theorem 3.7.
-/

@[expose] public section

namespace MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted

open StatMech StatMech.Lattice StatMech.Percolation
open scoped NNReal

/-- **Exponential decay of the cluster volume.** For Bernoulli bond percolation on `ℤ^d`,
`d ≥ 2`, and every `p < p_c(d)`, there are `c, C > 0` such that for every `n`, the probability that
the cluster `C(0)` of the origin has at least `n` sites is at most `C e^{-cn}`; an infinite cluster
counts as having at least `n` sites. Source: H. Duminil-Copin, *Introduction to Bernoulli
percolation*, lecture notes (2018), Theorem 3.7, proved there by coarse graining from exponential
decay of the radius (Theorem 3.3). The notes write the bound as `exp(-c'_p n)` for every `n`; at
`n = 1` the left side is `1`, so this version carries a prefactor `C`. -/
public theorem_wanted cluster_volume_exp_decay (d : ℕ) (hd : 2 ≤ d) (p : ℝ≥0) (hp : p ≤ 1)
    (hlt : p < pc d) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | (n : ℕ∞) ≤ (cluster d ω (origin d)).encard} ≤ C * Real.exp (-c * n)

end MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted
