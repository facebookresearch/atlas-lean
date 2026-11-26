/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# No-3-way-interaction MLE and 2 × 2 × 2 collapsings (AIM list, Conjecture 8)

AIM workshop Computational algebraic statistics, problem list, Conjecture 8: maximum likelihood
estimates for an `I × J × K` table under the no 3-way interaction model do not exist if and only if
they do not exist for all collapsings of the table to a `2 × 2 × 2` table. The list adds: later in
the week, Nicholas Eriksson showed that this conjecture is false already for `3 × 3 × 3` tables.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22

@[expose] public section

namespace MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted

/-!
Source: AIM workshop Computational algebraic statistics, problem list, Conjecture 8. UnsolvedMath
record UM-20001184 (`AIM-COMPUTATION-0022`), dataset ulamai/UnsolvedMath v1.8.0.

'Do not exist for all collapsings' is read as 'do not exist for every collapsing to exist', i.e. the
MLE fails to exist for some collapsing (the detection reading): this is the reading for which the
list's note says the conjecture first fails at `3 × 3 × 3` (for `2 × q × r` tables every facet of
the marginal cone comes from a binary collapsing, Eriksson–Fienberg–Rinaldo–Sullivant Prop. 12), and
the direction 'some collapsing has no MLE ⇒ the table has none' holds for all tables. The MLE (with
strictly positive cell probabilities, as the list requires) exists iff the observed two-way margins
lie in the relative interior of the marginal cone, iff some strictly positive real table has the
same two-way margins (Haberman's theorem as stated by Eriksson–Fienberg–Rinaldo–Sullivant, Cor. 3
and its proof); `MLEExists` is this criterion. A collapsing to `2 × 2 × 2` merges the levels of each
variable into two nonempty classes (surjections onto `Fin 2`) and sums the merged cells. The target
is the conjecture for `3 × 3 × 3` tables, the size the list names.
-/

open Function

end MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted
