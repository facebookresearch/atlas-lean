/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING REPAIRMAN (MINIMUM LATENCY) is NP-complete

Source:
F. Afrati, S. Cosmadakis, C. H. Papadimitriou, G. Papageorgiou, and N. Papakostantinou,
"The complexity of the travelling repairman problem", RAIRO Theoretical Informatics and
Applications 20 (1986), 79-87, doi:10.1051/ita/1986200100791 (definition of the problem;
NP-completeness of the general version, credited there to S. Sahni and T. Gonzalez,
"P-complete approximation problems", Journal of the ACM 23 (1976), 555-565,
doi:10.1145/321958.321975);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM TRAVELING REPAIRMAN (metric instances);
A. Blum, P. Chalasani, D. Coppersmith, B. Pulleyblank, P. Raghavan, and M. Sudan, "The minimum
latency problem", Proc. 26th ACM Symposium on Theory of Computing (1994), 163-171,
doi:10.1145/195058.195125 (NP-hard for points in the plane);
R. Sitters, "The minimum latency problem is NP-hard for weighted trees", Integer Programming
and Combinatorial Optimization (IPCO 2002), LNCS 2337, 230-239,
doi:10.1007/3-540-47867-1_17.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TravelingRepairmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TravelingRepairman

/-!
# TRAVELING REPAIRMAN (MINIMUM LATENCY) is NP-complete

INSTANCE: `n` locations `0, …, n - 1` with a distance matrix `t[a, b] ∈ ℕ` that satisfies the
triangle inequality (symmetric, with zero diagonal), a distinguished starting location `s`, and
a bound `K`. QUESTION: is there a permutation `π(0) = s, π(1), …, π(n - 1)` of the locations
whose total latency `∑_{i=1}^{n-1} ∑_{j=1}^{i} t[π(j - 1), π(j)]` is at most `K`?

The cost is Afrati et al.'s (1986) formula: the latency of `π(i)` is the distance traveled from
`s` until `π(i)` is first visited, and the total latency is their sum (the latency of `s` itself
is `0`). The instance class is that of Crescenzi and Kann's MINIMUM TRAVELING REPAIRMAN and of Blum
et al. (1994): nonnegative integer lengths satisfying the triangle inequality. With the triangle
inequality, visiting the locations in the order `π` along direct legs is no worse than any walk that
first visits them in that order, so permutations capture the compendium entry's walks. Afrati et al.
state the general version NP-complete (crediting Sahni and Gonzalez 1976); Blum et al. observe that
a reduction from the traveling salesman problem makes the problem NP-hard already for points in
the plane, and Sitters (2002) proves it NP-hard for the shortest-path metrics of weighted
trees. The route is listed as a permutation of
`List.range n` that starts at `s`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRAVELING REPAIRMAN (MINIMUM LATENCY) is NP-complete.** Source: Afrati et al. (1986);
Crescenzi and Kann, MINIMUM TRAVELING REPAIRMAN; Blum et al. (1994); Sitters (2002). -/
public theorem_wanted travelingRepairman_npComplete :
    travelingRepairmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L travelingRepairmanDec

end MetaMathlibExt.Complexity.NPComplete.TravelingRepairman
