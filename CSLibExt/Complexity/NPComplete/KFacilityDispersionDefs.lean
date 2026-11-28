/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MetricKCenterDefs

/-!
# K-FACILITY DISPERSION: definitions

INSTANCE: a complete graph `G = (V, E)` with distances `d(vᵢ, vⱼ) ∈ ℕ` satisfying the triangle
inequality, an integer `k` with `2 ≤ k ≤ |V|`, and a positive integer `K`.
QUESTION: is there a set of `k` facilities, i.e. a subset `F ⊆ V` with `|F| = k`, such that the
minimum distance between two facilities, `min_{f₁, f₂ ∈ F, f₁ ≠ f₂} d(f₁, f₂)`, is at least `K`?

This is the decision version of MAXIMUM K-FACILITY DISPERSION from the Crescenzi-Kann
compendium, the MAX-MIN facility dispersion problem (MMFD) of Ravi, Rosenkrantz and
Tayi. Their instance has `p` facilities with `2 ≤ p ≤ n`, so the minimum over pairs of distinct
facilities is defined. They record that MMFD is NP-hard when the distances satisfy the triangle
inequality, and prove (Theorem 3) that no polynomial-time algorithm has a performance guarantee
below 2 for that case unless P = NP.

The instance class is the one of METRIC K-CENTER
(`WantedExt.Complexity.NPComplete.MetricKCenterWanted`, the same compendium wording), and the
module reuses its instance `(d, k, K)`, its distance accessor and its `WellFormed` unchanged: a
square matrix, one row per vertex, that is a metric (zero exactly on the diagonal, symmetric,
triangle inequality), `0 < k ≤ |V|` and `0 < K`. It adds `2 ≤ k`. RRT allow a zero distance
between distinct nodes, which these metric conditions exclude; their hardness constructions use
positive distances only.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-FACILITY DISPERSION;
S. S. Ravi, D. J. Rosenkrantz, and G. K. Tayi, "Heuristic and special case algorithms for
dispersion problems", Operations Research 42 (1994), 299-310, doi:10.1287/opre.42.2.299.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion

open KCenter (KCenterInstance)
open MetricKCenter (distance)

/-- Well-formedness of an instance: METRIC K-CENTER's (a metric distance matrix, `0 < k ≤ |V|`,
`0 < K`) and `2 ≤ k`. -/
def WellFormed (i : KCenterInstance) : Prop :=
  MetricKCenter.WellFormed i ∧ 2 ≤ i.2.1

/-- Some set `F` of exactly `k` vertices has `d(f₁, f₂) ≥ K` for all distinct `f₁, f₂ ∈ F`,
i.e. the minimum distance between two facilities is at least `K`. -/
def KFacilityDispersionFeasible (i : KCenterInstance) : Prop :=
  ∃ F : Finset (Fin i.1.length), F.card = i.2.1 ∧
    ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ≠ f₂ → i.2.2 ≤ distance i f₁ f₂

open Classical in
/-- K-FACILITY DISPERSION as a decision problem over bitstrings. -/
noncomputable def kFacilityDispersionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KCenterInstance) x with
  | some i => decide (WellFormed i ∧ KFacilityDispersionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion
