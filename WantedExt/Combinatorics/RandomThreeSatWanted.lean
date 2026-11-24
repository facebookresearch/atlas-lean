/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Combinatorics.RandomThreeSat

@[expose] public section

namespace MathlibExt.Combinatorics.RandomThreeSatWanted

open CSLibExt.Combinatorics.RandomThreeSat

/-!
# Catalogue bounds for the random 3-SAT threshold

The two best rigorously proved bounds from Optimization Problems record
52a, stated as proof requests against the finite model in
`CSLibExt.Combinatorics.RandomThreeSat`. The decimal catalogue
endpoints are exact rationals. No literature proof is imported, and the
constant-threshold conjecture (`HasConstantThreshold`) — convergence of
the threshold to a single constant — remains open; Friedgut's (proved)
sharp-threshold theorem is recorded as background in the Sources entry,
not as a formal declaration here.
-/

/-- **Díaz–Kirousis–Mitsche–Pérez-Giménez upper bound for random 3-SAT.** The number $4.49$ is an
upper threshold cutoff for random 3-SAT: for every real $r > 4.49$, the probability that a
uniformly random formula with $\lfloor r n \rfloor$ clauses on $n$ variables is satisfiable tends
to $0$ as $n \to \infty$.

Source: Díaz, Kirousis, Mitsche, and Pérez-Giménez, *On the
satisfiability threshold of formulas with three literals per clause*
(2009), catalogue upper bound `4.490`. Known literature result; its
proof is not supplied here. -/
theorem_wanted diazKirousisMitschePerezUpperBound_wanted :
    IsUpperCutoff (449 / 100 : ℝ)

/-- **Hajiaghayi–Sorkin lower bound for random 3-SAT.** The number $3.52$ is a lower threshold
cutoff for random 3-SAT: for every real $r < 3.52$, the probability that a uniformly random
formula with $\lfloor r n \rfloor$ clauses on $n$ variables (no clauses when $r < 0$) is
satisfiable tends to $1$ as $n \to \infty$.

Source: Hajiaghayi and Sorkin, *The satisfiability threshold of
random 3-SAT is at least 3.52* (2003), and Kaporis, Kirousis, and Lalas
(2003), catalogue lower bound `3.52`. Known literature result; its
proof is not supplied here. -/
theorem_wanted hajiaghayiSorkinLowerBound_wanted :
    IsLowerCutoff (352 / 100 : ℝ)

end MathlibExt.Combinatorics.RandomThreeSatWanted
