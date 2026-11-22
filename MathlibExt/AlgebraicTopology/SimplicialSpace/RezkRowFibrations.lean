/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RelativeSegalRows
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalEndpoint
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations

/-!
# Categorical row pullback-Homs of Rezk fibrations

For an actual Rezk fibration between complete Segal spaces, every original
right row pullback-Hom along a scalar monomorphism is a genuine categorical
fibration. Relative Segal calculus gives innerness and the quasicategory
structure on its chosen target. Complete-Segal endpoint triviality and the
exact box adjunction give lifting of the entire coherent walking-isomorphism
nerve with the original prescribed base. Apply the actual categorical
fibration criterion to that same original row arrow.

The resulting scalar family is the native `hasCategoricalRowPullbackHom`
predicate used by the Joyal–Tierney comparison.

Source: Joyal–Tierney, arXiv math/0607820v2, Lemma 4.3, p. 22,
and Proposition 1.13.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace

/-- JT4.3's concrete prerequisites: the actual Rezk row pullback-Hom is inner
between quasi-categories and lifts the chosen source endpoint of the full E. -/
private theorem rowPullbackHom_rezk_endpoint_packet
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hX : SimplicialSpace.completeSegalSpaces X)
    (hY : SimplicialSpace.completeSegalSpaces Y)
    (hp : SimplicialSpace.RezkModel.modelCategory.{u}.categoryWithFibrations.fibrations p)
    {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.InnerFibration (SimplicialSpace.rowPullbackHom v p) ∧
    SSet.Quasicategory ((SimplicialSpace.rowPowerFunctor T).obj X) ∧
    SSet.Quasicategory (SimplicialSpace.rowPullbackHomSquare v p).pt ∧
    HasLiftingProperty (SSet.yonedaEquiv.symm SSet.coherentIso.x₀)
      (SimplicialSpace.rowPullbackHom v p) ∧
    SimplicialSpace.rowPullbackHom v p ≫
        (SimplicialSpace.rowPullbackHomSquare v p).fst =
      SimplicialSpace.rowRestriction v X ∧
    SimplicialSpace.rowPullbackHom v p ≫
        (SimplicialSpace.rowPullbackHomSquare v p).snd =
      (SimplicialSpace.rowPowerFunctor T).map p := by
  have hSpineX : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((SimplicialSpace.boxLeftDivisionFunctor.map
        (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app X) := by
    intro n hn
    exact hX.2 (.inl ⟨n, hn⟩)
  have hSpineY : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((SimplicialSpace.boxLeftDivisionFunctor.map
        (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app Y) := by
    intro n hn
    exact hY.2 (.inl ⟨n, hn⟩)
  have hr := rowPullbackHom_packet p hX.1 hY.1
    (SimplicialSpace.RezkModel.reedyFibration_of_fibration p hp) hSpineX hSpineY v
  have hEndpoint :=
    SimplicialSpace.rowPullbackHom_hasLiftingProperty_coherentIsoEndpoint_of_boundaryRLP
      v p (SimplicialSpace.RezkModel.boxLeftPullbackHom_coherentIsoEndpoint_mem_boundaryRLP
        p hX hY hp)
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hEndpoint, hr.2.2.2.1, hr.2.2.2.2⟩



/-- The original relative row map of an actual Rezk fibration between complete
Segal spaces is a genuine categorical fibration, by the actual native criterion. -/
theorem rowPullbackHom_categoricalFibration
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hX : SimplicialSpace.completeSegalSpaces X)
    (hY : SimplicialSpace.completeSegalSpaces Y)
    (hp : SimplicialSpace.RezkModel.modelCategory.{u}.categoryWithFibrations.fibrations p)
    {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.categoricalFibrations (SimplicialSpace.rowPullbackHom v p) := by
  have h := SimplicialSpace.rowPullbackHom_rezk_endpoint_packet p hX hY hp v
  let _ : SSet.Quasicategory (SimplicialSpace.rowPullbackHomSquare v p).pt := h.2.2.1
  apply (SSet.categoricalFibrations_iff_innerFibration_and_coherentIsoEndpointLifting
    (SimplicialSpace.rowPullbackHom v p)).2
  refine ⟨h.1, ?_⟩
  change HasLiftingProperty (SSet.yonedaEquiv.symm SSet.coherentIso.x₀)
    (SimplicialSpace.rowPullbackHom v p)
  exact h.2.2.2.1

/-- The complete native hrow input used by the Rezk/Joyal comparison assembly. -/
theorem hasCategoricalRowPullbackHom_of_rezkFibration
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hX : SimplicialSpace.completeSegalSpaces X)
    (hY : SimplicialSpace.completeSegalSpaces Y)
    (hp : SimplicialSpace.RezkModel.modelCategory.{u}.categoryWithFibrations.fibrations p) :
    SimplicialSpace.hasCategoricalRowPullbackHom p := by
  intro S T v hv
  let _ : Mono v := hv
  exact rowPullbackHom_categoricalFibration p hX hY hp v


end SimplicialSpace
