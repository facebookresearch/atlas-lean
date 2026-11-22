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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.QuadraticProgrammingWanted

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

/-- An instance: the dimension `d`, the points (each a list of `d` coordinates), and the bound
`B`. -/
abbrev EuclideanTwoMeansInstance := ℕ × List (List RatCode) × RatCode

/-- The points of the instance, `Fin n` for `n` listed points. -/
abbrev Point (i : EuclideanTwoMeansInstance) : Type := Fin i.2.1.length

/-- Coordinate `c` of point `x`. -/
def coord (i : EuclideanTwoMeansInstance) (x : Point i) (c : Fin i.1) : ℚ :=
  ratVal ((i.2.1.get x).getD c ((0, 0), 1))

/-- Coordinate `c` of the centroid `(1 / |C|) ∑_{x ∈ C} x` of the cluster `C`. -/
def centroid (i : EuclideanTwoMeansInstance) (C : Finset (Point i)) (c : Fin i.1) : ℚ :=
  (∑ x ∈ C, coord i x c) / C.card

/-- The sum of squared Euclidean distances `∑_{x ∈ C} ‖x - μ_C‖²` of the points of `C` to its
centroid. -/
def clusterCost (i : EuclideanTwoMeansInstance) (C : Finset (Point i)) : ℚ :=
  ∑ x ∈ C, ∑ c, (coord i x c - centroid i C c) ^ 2

/-- Well-formedness of an instance: at least two points, every point has `d` coordinates, and
every encoded rational has a positive denominator. -/
def WellFormed (i : EuclideanTwoMeansInstance) : Prop :=
  2 ≤ i.2.1.length ∧ (∀ x ∈ i.2.1, x.length = i.1 ∧ ∀ q ∈ x, 0 < q.2) ∧ 0 < i.2.2.2

/-- Some partition of the points into two nonempty clusters `S`, `Sᶜ` has total
within-cluster sum of squares at most `B`. -/
def EuclideanTwoMeansFeasible (i : EuclideanTwoMeansInstance) : Prop :=
  ∃ S : Finset (Point i), S.Nonempty ∧ Sᶜ.Nonempty ∧
    clusterCost i S + clusterCost i Sᶜ ≤ ratVal i.2.2

open Classical in
/-- EUCLIDEAN 2-MEANS as a decision problem over bitstrings. -/
noncomputable def euclideanTwoMeansDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EuclideanTwoMeansInstance) x with
  | some i => decide (WellFormed i ∧ EuclideanTwoMeansFeasible i)
  | none => false

/-- **EUCLIDEAN 2-MEANS is NP-complete.** Source: Aloise, Deshpande, Hansen and Popat (2009). -/
public theorem_wanted euclideanTwoMeans_npComplete :
    euclideanTwoMeansDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L euclideanTwoMeansDec

end MetaMathlibExt.Complexity.NPComplete.EuclideanTwoMeans
