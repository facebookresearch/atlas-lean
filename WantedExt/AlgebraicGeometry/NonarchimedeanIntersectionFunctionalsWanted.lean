/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionals
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import Batteries.Util.ProofWanted

/-!
# Common-model descent of normalized nonarchimedean functionals

All mixed intersections, energy, entropy and J use the native scheme
projections, actual Cartier polarizations and fixed divisorial valuation
normalizations. Every model carries that the base polarization is a line
bundle of positive volume. The requests prove descent through the actual proper
birational common-model pullback; their conclusions are not input fields.

Reference: Boucksom--Hisamoto--Jonsson, arXiv:1504.06568v3, Proposition 7.24.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionalsWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels
open MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison
open MathlibExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionals

theorem_wanted commonModelMixedIntersection
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ)
    (P : LogPair k n) (L : P.variety.X.left.Modules)
    (_projective : ∃ N : ℕ, ∃ i : P.variety.X ⟶
      MathlibExt.AlgebraicGeometry.ProjectiveSpace.projectiveSpace k N,
      IsClosedImmersion i.left)
    (M N : VerticalModel P L) (_refinement : ModelRefinement M N) :
    mixedTrivial M = mixedTrivial N

theorem_wanted commonModelEnergyAndJ
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ)
    (P : LogPair k n) (L : P.variety.X.left.Modules)
    (_projective : ∃ N : ℕ, ∃ i : P.variety.X ⟶
      MathlibExt.AlgebraicGeometry.ProjectiveSpace.projectiveSpace k N,
      IsClosedImmersion i.left)
    (M N : VerticalModel P L) (_refinement : ModelRefinement M N) :
    energy M = energy N ∧ jFunctional M = jFunctional N

theorem_wanted commonModelEntropy
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (n : ℕ)
    (P : LogPair k n) (L : P.variety.X.left.Modules)
    (_projective : ∃ N : ℕ, ∃ i : P.variety.X ⟶
      MathlibExt.AlgebraicGeometry.ProjectiveSpace.projectiveSpace k N,
      IsClosedImmersion i.left)
    (M N : VerticalModel P L) (_refinement : ModelRefinement M N)
    (V : ∀ p (hp : p ∈ M.central), ComponentValuation M p hp)
    (W : ∀ p (hp : p ∈ N.central), ComponentValuation N p hp) :
    entropy M V = entropy N W

end WantedExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionalsWanted
