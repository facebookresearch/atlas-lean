/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A union of balls in ℂ² that is not the ball, Δ × ℂ or ℂ² (SCV problem list, Problem 13)

Several Complex Variables Problem List, Problem 13: suppose `M` is a complex manifold of dimension 2
such that for every compact `K ⊂ M` there is an open `U` with `K ⊂ U ⊂ M` and `U` biholomorphic to
the unit ball. Does this imply that `M` is equivalent to the unit ball, `Δ × ℂ` or `ℂ²`? (This is
false in `ℂ³`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Sheaf.Basic

@[expose] public section

namespace MathlibExt.Analysis.UnionOfBallsShortCTwoAMR119Problem0013Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 13. UnsolvedMath record UM-00800217
(`AMR-119-0013`), dataset ulamai/UnsolvedMath v1.8.0.

Two-dimensional complex manifolds are types with a `ChartedSpace` structure modelled on `ℂ² =
EuclideanSpace ℂ (Fin 2)` and `IsManifold 𝓘(ℂ, ℂ²) ∞` (holomorphic transition maps), Hausdorff and
second countable as usual; the hypothesis already forces Hausdorff and connected, since any two
points lie in one open subset biholomorphic to the ball. Biholomorphisms are `∞`-smooth complex
diffeomorphisms, as in the Problem 14 module `LongCTwoNotBiholomorphicAMR119Problem0014Wanted`. The
three models are open subsets of `ℂ²` with the induced structure: the Euclidean unit ball, `Δ × ℂ`
as `{z : ‖z 0‖ < 1}`, and `ℂ²` itself. The question is read as 'is every such `M` biholomorphic to
one of the three?'.
-/

open scoped Manifold ContDiff

/-- The unit ball `{z : ‖z‖ < 1}` of `ℂ² = EuclideanSpace ℂ (Fin 2)` (Euclidean norm), as an open
subset, with its induced complex manifold structure. -/
def unitBall : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin 2)) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The product `Δ × ℂ` of the unit disc and the plane, realized as the open subset
`{z : ‖z 0‖ < 1}` of `ℂ²`. -/
def discTimesPlane : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin 2)) :=
  ⟨{z | ‖z 0‖ < 1}, isOpen_lt (by fun_prop) continuous_const⟩

/-- The hypothesis of SCV Problem 13 on a two-dimensional complex manifold `M`: every compact subset
`K ⊆ M` lies in an open subset `U ⊆ M` biholomorphic to the unit ball of `ℂ²`. -/
def CompactsInBalls (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) M] :
    Prop :=
  ∀ K : Set M, IsCompact K → ∃ U : TopologicalSpace.Opens M, K ⊆ U ∧
    Nonempty (U ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯ unitBall)

/-- SCV Problem List, Problem 13: every two-dimensional complex manifold in which every compact set
lies in an open subset biholomorphic to the unit ball is biholomorphic to the ball, to `Δ × ℂ` or to
`ℂ²`. -/
def unionOfBallsTrichotomy : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 2)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 2)) ∞ M],
    CompactsInBalls M →
      Nonempty (M ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯ unitBall) ∨
      Nonempty (M ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯
        discTimesPlane) ∨
      Nonempty (M ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯
        EuclideanSpace ℂ (Fin 2))

/--
Resolved false: Fornæss's short ℂ² (Adv. Stud. Pure Math. 42, Theorem 1.4 with k = 2) is a domain of
ℂ² that is an increasing union of open subsets biholomorphic to the unit ball, so every compact
subset lies in one of them; its Kobayashi metric vanishes identically, unlike the Fornæss-Sibony
models ball and Δ × ℂ, and it carries a nonconstant bounded-above plurisubharmonic function, so it
is not ℂ². Fornæss presents it as the answer to the remaining question whether there was any other
possibility. Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several
Complex Variables Problem List, arXiv:math/9509202 (1995), Problem 13; resolution: J. E. Fornæss,
Short ℂ^k, in Complex Analysis in Several Variables, Memorial Conference of Kiyoshi Oka's Centennial
Birthday, Adv. Stud. Pure Math. 42 (2004), 95-108, §1: after Fornæss-Sibony's theorem (an increasing
union of balls in ℂ² whose Kobayashi metric does not vanish identically is biholomorphic to the ball
or to Δ × ℂ) and ℂ² as the obvious example with vanishing Kobayashi metric, 'the question remaining
was whether there was any other possibility (Diederich-Sibony). In this paper we show that indeed
there are other such Ω'; Theorem 1.4 (k = 2): Ω ⊂ ℂ² is open and connected, Ω = ⋃ Ω_j increasing
with each Ω_j biholomorphic to the unit ball, the Kobayashi metric of Ω vanishes identically, and Ω
= {ψ < 0} for a plurisubharmonic ψ nonconstant on Ω, the reason Ω is not biholomorphic to ℂ²; J. E.
Fornæss and R. Pal, J. Geom. Anal. 32 (2022), Paper No. 133, §1, list short ℂ^k as a model domain
besides the ball, Δ × ℂ and ℂ^k, https://doi.org/10.2969/aspm/04210095.
-/
public theorem_wanted unionOfBallsTrichotomy_refuted : ¬ unionOfBallsTrichotomy

end MathlibExt.Analysis.UnionOfBallsShortCTwoAMR119Problem0013Wanted
