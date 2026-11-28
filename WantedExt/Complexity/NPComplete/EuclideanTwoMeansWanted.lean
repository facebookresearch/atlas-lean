/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUCLIDEAN 2-MEANS is NP-complete

Source:
D. Aloise, A. Deshpande, P. Hansen and P. Popat, "NP-hardness of Euclidean sum-of-squares
clustering", Machine Learning 75 (2009), 245-248, doi:10.1007/s10994-009-5103-0
(sum-of-squares clustering into two clusters is NP-hard when the dimension is part of the input).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EuclideanTwoMeansDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanTwoMeans

open QuadraticProgramming (RatCode ratVal)

/-!
# EUCLIDEAN 2-MEANS is NP-complete

INSTANCE: a dimension `d` (part of the input), `n` points `x₁, …, xₙ ∈ ℚ^d`, and a rational
bound `B`. QUESTION: is there a partition of the points into two clusters `C₁, C₂` such that the
within-cluster sum of squared Euclidean distances to the cluster centroids,
`∑_{j = 1, 2} ∑_{x ∈ C_j} ‖x - μ_j‖²` with `μ_j = (1 / |C_j|) ∑_{x ∈ C_j} x`, is at most `B`?

The points are the list positions `Fin n`, each a list of `d` coordinates; a partition into two
clusters is a set `S` of points with `S` and its complement nonempty, so `WellFormed` asks for at
least two points. A rational number is encoded as `((p, q), r)` with value `(p - q) / r` and
`r > 0` (`QuadraticProgramming.RatCode`, `QuadraticProgramming.ratVal`, reused from
`QuadraticProgrammingWanted`). All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EUCLIDEAN 2-MEANS is NP-complete.** Source: Aloise, Deshpande, Hansen and Popat (2009). -/
public theorem_wanted euclideanTwoMeans_npComplete :
    euclideanTwoMeansDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L euclideanTwoMeansDec

end MetaMathlibExt.Complexity.NPComplete.EuclideanTwoMeans
