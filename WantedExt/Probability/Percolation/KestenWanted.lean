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
# Kesten's theorem: `p_c(ℤ²) = 1/2`

The critical probability of Bernoulli bond percolation on the square lattice `ℤ²` is `1/2`, and
there is no infinite cluster at `p = 1/2`.

The repository proves `0 < p_c(2)` (`StatMech.Percolation.pc_pos`), `p_c(2) < 1`
(`StatMech.Percolation.pc_two_lt_one_via_fk` in PhyslibExt) and the sharpness of the phase
transition (`StatMech.Percolation.sharp_phase_transition_pc`); the uniqueness of the infinite
cluster, used in the proof of `θ_2(1/2) = 0`, is itself recorded as wanted
(`MathlibExt.Probability.Percolation.BurtonKeaneWanted.burton_keane_bernoulli`).

## Main statements

* `theta_two_half_eq_zero`: `θ_2(1/2) = 0` (Harris 1960).
* `pc_two_eq_half`: `p_c(2) = 1/2` (Kesten 1980).

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of
  7 October 2018), Corollary 4.2 and Theorem 4.3.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960), 13–20.
* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
-/

@[expose] public section

namespace MathlibExt.Probability.Percolation.KestenWanted

open StatMech.Percolation
open scoped NNReal

/-- **No infinite cluster at `p = 1/2` on `ℤ²`** (Harris 1960): for Bernoulli bond percolation on
the square lattice, `θ_2(1/2) = ℙ_{1/2}(0 is in an infinite cluster) = 0`. In particular
`p_c(2) ≥ 1/2`. Source: H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes
(2018), Corollary 4.2, proved there from the self-duality identity `ℙ_{1/2}(H_n) = 1/2` (4.1) and
Proposition 4.1, which uses the uniqueness of the infinite cluster; T. E. Harris, Proc. Cambridge
Philos. Soc. 56 (1960). -/
public theorem_wanted theta_two_half_eq_zero :
    theta 2 (1 / 2 : ℝ≥0) (by norm_num) = 0

/-- **Kesten's theorem** (Kesten 1980): the critical probability of Bernoulli bond percolation on
the square lattice `ℤ²` equals `1/2`. Together with `theta_two_half_eq_zero` it gives the second
assertion of the source theorem, that there is no infinite cluster at `p_c`. Source:
H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes (2018), Theorem 4.3,
proved there from Corollary 4.2 and exponential decay below `p_c` (Theorem 3.3); H. Kesten,
Comm. Math. Phys. 74 (1980). -/
public theorem_wanted pc_two_eq_half :
    pc 2 = 1 / 2

end MathlibExt.Probability.Percolation.KestenWanted
