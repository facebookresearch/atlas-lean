/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Splitting sets with dense or syndetic sumsets (Erdős Problem 741)

Erdős Problem 741 (Burr and Erdős): let `A ⊆ ℕ` be such that `A + A` has positive (upper) density.
Can one always decompose `A = A₁ ⊔ A₂` such that `A₁ + A₁` and `A₂ + A₂` both have positive (upper)
density? Is there a basis `A` of order `2` such that if `A = A₁ ⊔ A₂` then `A₁ + A₁` and `A₂ + A₂`
cannot both have bounded gaps?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import MathlibExt.Combinatorics.Additive.Basis
public import MathlibExt.Combinatorics.Additive.UpperDensitySumsetPartition
public import MathlibExt.Combinatorics.SumsetPartitionErdosProblem741

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #741, https://www.erdosproblems.com/741 (status SOLVED
(LEAN)). UnsolvedMath record UM-00002288 (`EP-741`), dataset ulamai/UnsolvedMath v1.8.0.

Upper density is MathlibExt's `Set.upperDensity`; the first question is stated for upper density,
the reading the problem page says captures its spirit (the version where the densities must exist
was answered negatively and is not formalized). A basis of order `2` is read asymptotically,
MathlibExt's `Set.IsAsymptoticAddBasisOfOrder A 2` (all but finitely many integers lie in `2 • A = A
+ A`), as in the resolving paper. Bounded gaps: some `g` with every interval `[n, n + g)` meeting
the set. Both answers are machine-generated (DeepMind; an internal OpenAI model); the problem page
states both answers and marks the problem solved. Compared with the formal-conjectures statement
`ErdosProblems/741.lean` (first question equivalent, marked solved there with a formal proof by the
DeepMind prover agent; the basis there is `A ∪ {0}` of exact order 2; no code imported).
-/

open scoped Pointwise

end MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
