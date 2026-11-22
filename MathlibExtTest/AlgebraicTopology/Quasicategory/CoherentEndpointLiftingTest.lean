/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoherentEndpointLifting

/-!
# Clients for coherent endpoint lifting

The public clients use only the source hypotheses, preserve the whole
supplied coherent-isomorphism base map, and retain both original strict
edge equations. No separate source quasicategory is supplied.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.CoherentEndpointLiftingTest

variable {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.InnerFibration p] [SSet.Quasicategory Y]


/-- Strict lifting solves the original full E base square with both equations. -/
example [SSet.HasStrictEquivalenceLifting p] (a : (Δ[0] : SSet.{u}) ⟶ X)
    (b : SSet.coherentIso.{u} ⟶ Y)
    (sq : CommSq a SSet.coherentIso.endpointInclusion p b) :
    ∃ l : SSet.coherentIso.{u} ⟶ X,
      SSet.coherentIso.endpointInclusion ≫ l = a ∧ l ≫ p = b := by
  have hLP := (SSet.hasStrictEquivalenceLifting_iff_hasLiftingProperty_coherentIso_endpointInclusion p).mp
    (inferInstance : SSet.HasStrictEquivalenceLifting p)
  let : sq.HasLift := hLP.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Endpoint lifting preserves the target vertex and entire original image edge. -/
example (hcoherent : HasLiftingProperty SSet.coherentIso.endpointInclusion p)
    {x₀ : X _⦋0⦌} {y₁ : Y _⦋0⦌}
    (g : SSet.Edge (p.app (op ⦋0⦌) x₀) y₁) (hg : g.IsEquivalence) :
    ∃ (x₁ : X _⦋0⦌) (_ : p.app (op ⦋0⦌) x₁ = y₁)
      (f : SSet.Edge x₀ x₁), f.IsEquivalence ∧ (f.map p).edge = g.edge := by
  let : SSet.HasStrictEquivalenceLifting p :=
    (SSet.hasStrictEquivalenceLifting_iff_hasLiftingProperty_coherentIso_endpointInclusion p).mpr hcoherent
  exact SSet.HasStrictEquivalenceLifting.exists_lift g hg


end MathlibExtTest.AlgebraicTopology.Quasicategory.CoherentEndpointLiftingTest
