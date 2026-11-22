/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A pseudoconvex domain in ℂ² with the homotopy type of S² (SCV problem list, Problem 37)

Several Complex Variables Problem List, Problem 37 (F. Forstnerič): does there exist a pseudoconvex
domain in `ℂ²` with the same homotopy type as `S²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homotopy.Equiv
public import WantedExt.Analysis.SeveralComplexVariablesShared

@[expose] public section

namespace MathlibExt.Analysis.PseudoconvexDomainHomotopySphereAMR119Problem0036Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 37. UnsolvedMath record UM-00800240
(`AMR-119-0036`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂ²` is `Fin 2 → ℂ`; pseudoconvex domains are `IsPseudoconvexDomain 2` from the shared module
(copied from `FatouBieberbachIntermediatePseudoconvex`: nonempty connected open sets whose
holomorphic hulls of compact subsets are compact). For open subsets of `ℂⁿ`, holomorphic convexity,
pseudoconvexity and being Stein agree (solution of the Levi problem). `S²` is the unit sphere of
`ℝ³`; homotopy type is `ContinuousMap.HomotopyEquiv`.
-/

open MathlibExt.Analysis.SeveralComplexVariablesShared

/-- SCV Problem List, Problem 37 (F. Forstnerič): there is a pseudoconvex domain in `ℂ²` with the
homotopy type of the 2-sphere `S² ⊆ ℝ³`. -/
def pseudoconvexDomainHomotopySphereExists : Prop :=
  ∃ Ω : Set (Fin 2 → ℂ), IsPseudoconvexDomain 2 Ω ∧
    Nonempty (ContinuousMap.HomotopyEquiv Ω (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))

/--
Resolved true: Gompf's Stein open subsets of ℂ² homeomorphic to S² × ℝ² are pseudoconvex domains
homotopy equivalent to S², counterexamples to Forstnerič's conjecture that no Stein open subset of
ℂ² is homotopy equivalent to S². Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz
(eds.), The Several Complex Variables Problem List, arXiv:math/9509202 (1995), Problem 37;
resolution: R. E. Gompf, Stein surfaces as open subsets of ℂ², J. Symplectic Geom. 3 (2005),
565-587, arXiv:math/0501509, Examples 2.4(a): for every smooth 2-knot K ⊂ ℂ², a Stein open subset U
⊂ ℂ² homeomorphic to S² × ℝ², giving 'a plethora of counterexamples to the conjecture of [Fo1] that
no Stein open subset of ℂ² is homotopy equivalent to S²' ([Fo1] = Forstnerič, Duke Math. J. 67
(1992)), https://arxiv.org/abs/math/0501509.
-/
public theorem_wanted pseudoconvexDomainHomotopySphereExists_holds :
    pseudoconvexDomainHomotopySphereExists

end MathlibExt.Analysis.PseudoconvexDomainHomotopySphereAMR119Problem0036Wanted
