/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFirstBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootClassRelation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact

/-! The complete actual triality-transition reduction for the octad-image local family, from the
checked binary octad forest. Five root transitions with both triality signs suffice; the four
roots other than Ω admit a genuine full-axis-fixing phase merge, and every transition is related
to one root by the actual binary root relation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual local transition representatives at the five roots; the Ω root is the identity. -/
def generatedAxisGlobalTwelveOctadRootLocal (j : Fin 5) : H :=
  if j = 0 then 1 else
    Classical.choose (generatedAxisGlobalBinaryRoot_surjective
      (generatedAxisGlobalTwelveOctadRootPoint j))

/-- The representatives have exactly the five root points as binary roots. -/
theorem generatedAxisGlobalTwelveOctadRootLocal_root (j : Fin 5) :
    generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveOctadRootLocal j) =
      generatedAxisGlobalTwelveOctadRootPoint j := by
  by_cases h : j = 0
  · subst h
    simp only [generatedAxisGlobalTwelveOctadRootLocal, ↓reduceIte]
    apply generatedAxisGlobalTwelveOctadMask_injective
    rw [generatedAxisGlobalTwelveOctadRootPoint_mask]
    apply generatedAxisGlobalTwelveOctadMask_of_decode _ _ (by decide)
    change co1BinaryAction (projH 1⁻¹) (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [inv_one, map_one, map_one, generatedAxisGlobalTwelveOctadRootMask,
      Matrix.cons_val_zero, generatedAxisGlobalTwelveOctadOmega_decode]
    rfl
  · simp only [generatedAxisGlobalTwelveOctadRootLocal, h, ↓reduceIte]
    exact Classical.choose_spec (generatedAxisGlobalBinaryRoot_surjective _)

/-- All actual binary Ω roots are covered from the five root transitions. -/
theorem generatedAxisGlobalTwelveOctad_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 5, ∃ c : H,
      c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveOctadRootLocal i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveOctad_binary_cover x
  exact ⟨i, c, hc, by rw [generatedAxisGlobalTwelveOctadRootLocal_root]; exact he⟩

/-- Every actual local element admits a phase-correct transition decomposition at the roots. -/
theorem generatedAxisGlobalTwelveOctad_actual_decompose (h : H) :
    ∃ i : Fin 5, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        (h = n * generatedAxisGlobalTwelveOctadRootLocal i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveOctadRootLocal i) * c) :=
  generatedAxisGlobal_decompose_two_signs (generatedOctadLocalAxisStabilizer 0 0)
    generatedAxisGlobalTwelveOctadRootLocal
    (generatedAxisGlobal_decompose_of_binary_cover (generatedOctadLocalAxisStabilizer 0 0)
      generatedAxisGlobalTwelveOctadRootLocal generatedAxisGlobalTwelveOctad_actual_binary_cover) h

/-- Ten real root transports suffice for all actual octad-family transitions. -/
theorem generatedAxisGlobalTwelveOctad_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 5,
      sExtra (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i) (generatedOctadLocalAxis 0 0)) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 5,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i)
        (generatedOctadLocalAxis 0 0)) ∈ generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h (generatedOctadLocalAxis 0 0)) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveOctad_actual_decompose h
  have hfix : rhoLocal c (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i) (generatedOctadLocalAxis 0 0))
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveOctadRootLocal i)
        (generatedOctadLocalAxis 0 0))
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

/-- An explicit extraspecial element whose binary image is orthogonal to the octad section. -/
def generatedAxisGlobalTwelveOctadPhaseQ : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode 16391), 1⟩

/-- The extraspecial element fixes the entire actual octad-image axis. -/
theorem generatedAxisGlobalTwelveOctadPhaseQ_fixed :
    rhoLocal (inclQ generatedAxisGlobalTwelveOctadPhaseQ) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0 := by
  have hk : generatedAxisGlobalTwelveOctadPhaseQ ∈ generatedOctadBasisQPhases.ker := by
    rw [MonoidHom.mem_ker]
    apply toAdd.injective
    rw [generatedOctadBasis_Q_phases_apply]
    decide +kernel
  exact generatedOctad_phase_kernel_le_axis_stabilizer 0 0 hk

set_option maxHeartbeats 4000000 in
-- Check the four odd pairings with the root masks.
/-- The element has odd pairing with each of the four non-Ω roots. -/
theorem generatedAxisGlobalTwelveOctadPhaseQ_pairing : ∀ j : Fin 4,
    qBeta (toAdd generatedAxisGlobalTwelveOctadPhaseQ.base)
        (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveOctadRootMask j.succ)) +
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveOctadRootMask j.succ))
        (toAdd generatedAxisGlobalTwelveOctadPhaseQ.base) = 1 := by
  decide +kernel

/-- Both triality signs at each non-Ω root have the same actual local orbit. -/
theorem generatedAxisGlobalTwelveOctad_merged_orbit (j : Fin 4) :
    ∃ k : H,
      sExtra (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal j.succ)
        (generatedOctadLocalAxis 0 0)) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal j.succ)
        (generatedOctadLocalAxis 0 0))) := by
  apply generatedAxisGlobal_triality_phase_merge _ _ generatedAxisGlobalTwelveOctadPhaseQ
    generatedAxisGlobalTwelveOctadPhaseQ_fixed
  rw [generatedAxisGlobalTwelveOctadRootLocal_root]
  exact generatedAxisGlobalTwelveOctadPhaseQ_pairing j

/-- Every actual octad-family transition is related to one root transition, with a sign. -/
theorem generatedAxisGlobalTwelveOctad_transition_root (t : H) :
    ∃ i : Fin 5,
      (∃ k : H, sExtra (rhoLocal t (generatedOctadLocalAxis 0 0)) =
        rhoLocal k (sExtra (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i)
          (generatedOctadLocalAxis 0 0)))) ∨
      (∃ k : H, sExtra (rhoLocal t (generatedOctadLocalAxis 0 0)) =
        rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i)
          (generatedOctadLocalAxis 0 0)))) := by
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveOctad_actual_binary_cover
    (generatedAxisGlobalBinaryRoot t)
  exact ⟨i, generatedAxisGlobal_triality_root_relation _ t _ c hc he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
