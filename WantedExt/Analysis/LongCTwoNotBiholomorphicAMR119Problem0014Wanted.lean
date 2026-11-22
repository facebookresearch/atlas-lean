/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A long ℂ² which is not biholomorphic to ℂ² (SCV problem list, Problem 14)

Several Complex Variables Problem List, Problem 14: is "long" `ℂ²` biholomorphic to `ℂ²`? (A complex
manifold is a long `ℂ²` if it is the union of proper subsets that are biholomorphic to `ℂ²`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Sheaf.Basic

@[expose] public section

namespace MathlibExt.Analysis.LongCTwoNotBiholomorphicAMR119Problem0014Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 14. UnsolvedMath record UM-00800218
(`AMR-119-0014`), dataset ulamai/UnsolvedMath v1.8.0.

Complex manifolds of dimension two are types with a `ChartedSpace` structure modelled on `ℂ² =
EuclideanSpace ℂ (Fin 2)` and `IsManifold 𝓘(ℂ, ℂ²) ∞` (holomorphic transition maps); biholomorphisms
are `∞`-smooth complex diffeomorphisms. A long `ℂ²` is, as in Fornæss's and Wold's usage, the union
of an increasing sequence of proper open subsets each biholomorphic to `ℂ²` (with the induced
manifold structure). The question is read as "is every long `ℂ²` biholomorphic to `ℂ²`?".
-/

open scoped Manifold ContDiff

/-- A two-dimensional complex manifold `X` (charts in `ℂ²`) is a long `ℂ²`: it is the union of an
increasing sequence of proper open subsets, each biholomorphic to `ℂ²`. -/
def IsLongCTwo (X : Type) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) X] :
    Prop :=
  ∃ U : ℕ → TopologicalSpace.Opens X, Monotone U ∧ (⋃ i, (U i : Set X)) = Set.univ ∧
    ∀ i, U i ≠ ⊤ ∧ Nonempty ((U i) ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)),
      𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯ EuclideanSpace ℂ (Fin 2))

/-- SCV Problem List, Problem 14: every long `ℂ²` is biholomorphic to `ℂ²`. -/
def everyLongCTwoBiholomorphic : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) X]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 2)) ∞ X], IsLongCTwo X →
      Nonempty (X ≃ₘ^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℂ, EuclideanSpace ℂ (Fin 2))⟯
        EuclideanSpace ℂ (Fin 2))

/--
Resolved false: Wold constructs a long ℂ² (an increasing union of proper subdomains biholomorphic to
ℂ²) which is not Stein, hence not biholomorphic to ℂ². Source: G. Buzzard, J. E. Fornæss, E. A.
Gavosto, S. G. Krantz (eds.), The Several Complex Variables Problem List, arXiv:math/9509202 (1995),
Problem 14; resolution: E. F. Wold, A long ℂ² which is not Stein, Ark. Mat. 48 (2010), 207-210,
Theorem 1.1 (a complex manifold X = ⋃ Xᵢ with Xᵢ ⊂ Xᵢ₊₁ and Xᵢ biholomorphic to ℂ², and X not
Stein), answering negatively the question 'Is any long ℂ² biholomorphic to ℂ²?' posed in §1,
https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7969-11512_2008_Article_84.pdf.
-/
public theorem_wanted everyLongCTwoBiholomorphic_refuted : ¬ everyLongCTwoBiholomorphic

end MathlibExt.Analysis.LongCTwoNotBiholomorphicAMR119Problem0014Wanted
