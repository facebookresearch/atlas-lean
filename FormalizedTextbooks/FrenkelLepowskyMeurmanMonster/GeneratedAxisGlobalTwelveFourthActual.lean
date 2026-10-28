/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord

/-! Complete actual Fourth-family transition reduction from the checked finite singular forest:
every triality transition of the actual Fourth local orbit is a local image of one of the
thirty-two vectors `τ^(±1) (r_j v₄)` at the sixteen explicit root words `r_j`. Root eleven is the
empty word; its inverse-triality vector has the actual octad-image class by the literal
definition of the Fourth representative. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All actual binary Ω roots are covered by the sixteen explicit local root words. -/
theorem generatedAxisGlobalTwelveFourth_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 16, ∃ c : H,
      c ∈ generatedFourthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFourthRootLocal i)) = x :=
  generatedAxisGlobalTwelveFourthBinary_cover

/-- Every actual local element admits a phase-correct transition decomposition at the roots. -/
theorem generatedAxisGlobalTwelveFourth_actual_decompose (h : H) :
    ∃ i : Fin 16, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedFourthLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalTwelveFourthRootLocal i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveFourthRootLocal i) * c) := by
  exact generatedAxisGlobal_decompose_two_signs generatedFourthLocalAxisStabilizer
    generatedAxisGlobalTwelveFourthRootLocal
    (generatedAxisGlobal_decompose_of_binary_cover generatedFourthLocalAxisStabilizer
      generatedAxisGlobalTwelveFourthRootLocal
      generatedAxisGlobalTwelveFourth_actual_binary_cover) h

/-- Thirty-two full real vector transports suffice for all actual Fourth-family transitions. -/
theorem generatedAxisGlobalTwelveFourth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 16,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 16,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedFourthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveFourth_actual_decompose h
  have hfix : rhoLocal c generatedFourthAxis = generatedFourthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveFourthRootLocal i)
        generatedFourthAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

/-- The listed Fourth representative is the literal Fourth axis. -/
theorem generatedAxisGlobalTwelveFourth_representative :
    generatedAxisGlobalTwelveRepresentative 3 = generatedFourthAxis :=
  rfl

/-- Inverse triality of the Fourth representative has the actual octad-image class. -/
theorem generatedAxisGlobalTwelveFourth_root11_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 11) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [generatedAxisGlobalTwelveFourthRootLocal_eleven, map_one, LinearEquiv.coe_one, id_eq,
    generatedFourthAxis_local_expression, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  apply generatedAxisGlobalTwelve_mem_of_octad_class
  rw [← (generatedAxis_triality_octad_class_iff
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0).mpr ⟨_, _, rfl⟩]
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  exact ⟨(localFiberIntoH generatedFourthLocalFiber)⁻¹, by
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]⟩

/-- Fourth-family coverage from the thirty-one remaining root transports. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of
    (hpos : ∀ i : Fin 16,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i : Fin 16, i ≠ 11 →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 := by
  intro h
  rw [generatedAxisGlobalTwelveFourth_representative]
  refine generatedAxisGlobalTwelveFourth_triality_of_actual_destinations _ hpos ?_ h
  intro i
  by_cases hi : i = 11
  · subst hi
    exact generatedAxisGlobalTwelveFourth_root11_negative
  · exact hneg i hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
