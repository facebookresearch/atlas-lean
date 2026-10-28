/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageOddPhaseReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitions

/-! Eleven genuine odd-family transition roots. These are actual real vectors;
this file proves their quotient meanings without assuming any local classification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two roots whose inverse transition is not covered by the seven phase merges. -/
def generatedAxisGlobalOddUnmergedRootIndex : Fin 2 → Fin 9 := ![5, 6]

/-- Nine forward and two inverse real transition vectors. -/
def generatedAxisGlobalOddDestinationRoots : Fin 9 ⊕ Fin 2 → GriessSpace :=
  Sum.elim
    (fun i => sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis))
    (fun j => sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddUnmergedRootIndex j)) generatedOddAxis))

/-- Exactly the two listed roots remain after the genuine phase merges. -/
theorem generatedAxisGlobalOddUnmergedRootIndex_iff (i : Fin 9) :
    (¬∃ j : Fin 7, generatedAxisGlobalOddPhaseRootIndex j = i) ↔
      ∃ j : Fin 2, generatedAxisGlobalOddUnmergedRootIndex j = i := by
  fin_cases i <;> decide

/-- Every forward transition is one of the eleven real root vectors. -/
theorem generatedAxisGlobalOddDestinationRoots_positive (i : Fin 9) :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalOddDestinationRoots := by
  exact ⟨Sum.inl i, 1, by rw [map_one]; rfl⟩

/-- Every inverse transition is in the local orbit of one of these eleven actual vectors. -/
theorem generatedAxisGlobalOddDestinationRoots_negative (i : Fin 9) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalOddDestinationRoots := by
  refine generatedAxisGlobalOdd_all_negative_of_phase_reduction
    generatedAxisGlobalOddDestinationRoots generatedAxisGlobalOddDestinationRoots_positive ?_ i
  intro k hk
  obtain ⟨j, rfl⟩ := (generatedAxisGlobalOddUnmergedRootIndex_iff k).mp hk
  exact ⟨Sum.inr j, 1, by rw [map_one]; rfl⟩

/-- Actual quotient classes of the eleven real transition roots. -/
def generatedAxisGlobalOddDestinationRootClass
    (i : Fin 9 ⊕ Fin 2) : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedAxisGlobalOddDestinationRoots i)

/-- Every listed root class is attained by the genuine transition map. -/
theorem generatedAxisGlobalOddDestinationRootClass_mem_range (i : Fin 9 ⊕ Fin 2) :
    generatedAxisGlobalOddDestinationRootClass i ∈
      Set.range (generatedAxisGlobalDestination generatedOddAxis) := by
  cases i with
  | inl i =>
    exact ⟨Quotient.mk _ (generatedAxisGlobalOddSourceRootLocalWord i), rfl⟩
  | inr j =>
    refine ⟨Quotient.mk _ (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddUnmergedRootIndex j)), ?_⟩
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddUnmergedRootIndex j)) generatedOddAxis)) =
      Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
          (generatedAxisGlobalOddUnmergedRootIndex j)) generatedOddAxis))
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    apply (generatedAxis_local_class_eq_iff _ _).mpr
    refine ⟨(inclQ singletonCocodeQ)⁻¹, ?_⟩
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
