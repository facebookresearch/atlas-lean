/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaTransport

/-! Actual norm-eight representatives suffice for phase-correct Ω conjugacy. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An actual norm-eight lattice representative yields an actual Conway binary transport to Ω. -/
theorem localOmega_binary_transport_of_normEight (r : Q) (u : leechIntegral)
    (hu : leechSquareSum u.val = 64)
    (hr : toAdd (qQuotHom r) = leechHyperbolicCoordinates (leechReduction u)) :
    ∃ c : Co1, co1BinaryAction c (toAdd (qQuotHom r)) =
      toAdd (qQuotHom sourceOmegaQ) := by
  obtain ⟨e, _, he⟩ := leechNormEight_concrete_transitive u hu
  have hv : leechIntegralAction e u = leechCoordinateFrameLattice 0 := Subtype.ext he
  refine ⟨QuotientGroup.mk e, ?_⟩
  change leechBinaryAction e (toAdd (qQuotHom r)) = toAdd (qQuotHom sourceOmegaQ)
  rw [hr, sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates]
  change leechHyperbolicCoordinates (leechReduction (leechIntegralAction e u)) = _
  rw [hv]

/-- Actual norm-eight Q elements are conjugate to actual Ω, with both central signs handled. -/
theorem localOmega_conjugate_of_normEight (r : Q) (u : leechIntegral)
    (hu : leechSquareSum u.val = 64)
    (hr : toAdd (qQuotHom r) = leechHyperbolicCoordinates (leechReduction u)) :
    ∃ h : H, h * inclQ r * h⁻¹ = inclQ sourceOmegaQ := by
  obtain ⟨c, hc⟩ := localOmega_binary_transport_of_normEight r u hu hr
  exact localOmega_conjugate_of_binary_transport r c hc

/-- Commuting with a Q element having an actual norm-eight representative gives
an actual local-group conjugate, without an Atlas conjugacy-class assumption. -/
theorem generated_commuting_q_conjugate_local_of_normEight (r : Q) (u : leechIntegral)
    (hu : leechSquareSum u.val = 64)
    (hr : toAdd (qQuotHom r) = leechHyperbolicCoordinates (leechReduction u))
    (g : G) (hg : Commute g (qIntoGenerated r)) :
    ∃ h : H, extraIntoGenerated *
      (localIntoGenerated h * g * (localIntoGenerated h)⁻¹) * extraIntoGenerated⁻¹ ∈
        localIntoGenerated.range := by
  obtain ⟨c, hc⟩ := localOmega_binary_transport_of_normEight r u hu hr
  exact generated_commuting_q_conjugate_local_of_binary_transport r c hc g hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
