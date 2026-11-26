/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Center-star multiple alignment is a (2 - 2/k)-approximation

For `k` strings and a pairwise scoring `s` on `Option α` (`none` is a gap)
with zero self-costs (`s x x = 0`, in particular `s none none = 0`), the triangle inequality,
and symmetry, let the center `X c` be an input string minimizing the total optimal-pairwise
distance `∑ⱼ D(X c, Xⱼ)` over the inputs (Gusfield's selection rule) and let `Ac` be a multiple
alignment whose projection onto the rows `c` and `i` is an optimal pairwise alignment of `X c` and
`X i` for every `i`, as for the center-star alignment built by merging optimal pairwise alignments
to `X c` (Lemma 3.1). With `V` the sum-of-pairs value and `A*` an optimal multiple alignment,
`k * V(Ac) ≤ 2 * (k - 1) * V(A*)`, i.e. `V(Ac) / V(A*) ≤ 2 * (k - 1) / k < 2`; the ratio form
(`centerStar_ratio`) is proved in `Domains.Biology.ComputationalBiology.CenterStarCenterStarRatio`.
The projection property is the premise; the star bound
`V_{ij}(Ac) ≤ D(X c, X i) + D(X c, X j)` used in the proof is a consequence (triangle inequality
column by column) and is not assumed.
The symmetry of `s` and the zero self-costs (which give `D(X, X) = 0`) are used by the source
without being stated and are explicit hypotheses here.

Overlap: `CSLibExt/Algorithms/Lean/DynamicProgramming/MultipleSequenceAlignment.lean`
has the sum-of-pairs score as a sum of induced pairwise scores
(`msaScore_eq_sum_induced`) and the `msaScore_le_sum_nwScore` bound; the
center-star approximation bound is not stated there. The bound `centerStar_bound` is
proved in `Domains.Biology.ComputationalBiology.CenterStarCenterStarBound`, where
`PairAlignment`, `alignValue`, `erasesTo`, `IsPairAlignmentOf`, `pairDist`, `MSAlignment`,
`msErasesTo`, `inducedValue`, `msaValue` and `centerTotal` are defined. Sum-of-pairs NP-hardness
is in the WantedExt NP catalog.

Sources: D. Gusfield, "Efficient methods for multiple sequence alignment with
guaranteed error bounds", Bulletin of Mathematical Biology 55(1):141-154,
1993, doi:10.1007/BF02460299, Lemma 3.1 and Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Domains.Biology.ComputationalBiology.CenterStarCenterStarBound
public import Domains.Biology.ComputationalBiology.CenterStarCenterStarRatio

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.CenterStarWanted

end WantedExt.Biology.ComputationalBiology.CenterStarWanted
