/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualDestinationClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionActualFibers

/-! Exact original sector-axis fibers for the three nonpair secondary A destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Actual A class equality is exactly membership in the corresponding actual vector orbit. -/
theorem generatedFeasibleSecondaryAClass_eq_iff_mem_orbit (x y : GriessSpace) :
    generatedFeasibleSecondaryAClass x = generatedFeasibleSecondaryAClass y ↔
      x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) y := by
  constructor
  · intro he
    exact MulAction.mem_orbit_symm.mp
      ((generatedFeasibleSecondaryAClass_eq_iff x y).mp he)
  · intro hx
    exact (generatedFeasibleSecondaryAClass_eq_iff x y).mpr
      (MulAction.mem_orbit_symm.mp hx)

/-- The original nonpair N sector corresponding to a nonpair destination index. -/
def generatedFeasibleSecondaryNonPairNIndex (j : Fin 3) : Fin 6 :=
  ⟨j.val + 3, by omega⟩

/-- The actual A destination index corresponding to the same original nonpair sector. -/
def generatedFeasibleSecondaryNonPairAIndex (j : Fin 3) : Fin 5 :=
  ⟨j.val + 2, by omega⟩

private theorem nonpair_destination_index (j : Fin 3) (k : Fin 6) :
    generatedFeasibleSecondaryNActualDestinationIndex k =
      generatedFeasibleSecondaryNonPairAIndex j ↔
        k = generatedFeasibleSecondaryNonPairNIndex j := by
  have h : ∀ j : Fin 3, ∀ k : Fin 6,
      generatedFeasibleSecondaryNActualDestinationIndex k =
        generatedFeasibleSecondaryNonPairAIndex j ↔
          k = generatedFeasibleSecondaryNonPairNIndex j := by decide +kernel
  exact h j k

/-- A nonpair destination class has exactly its original full N sector as vector inputs. -/
theorem generatedFeasibleSecondary_nonpair_class_fiber (j : Fin 3) :
    {x : GriessSpace |
      x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
        generatedFeasibleSecondaryAClass (sExtra x) =
          generatedFeasibleSecondaryActualDestinations
            (generatedFeasibleSecondaryNonPairAIndex j)} =
      generatedFeasibleSecondaryNOrbit (generatedFeasibleSecondaryNonPairNIndex j) := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical] at hx
    obtain ⟨k, hk⟩ := (generatedFeasibleSecondaryNOrbit_coverage x).mp hx
    have hc := generatedFeasibleSecondaryNOrbit_actual_destination k x hk
    have hi := generatedFeasibleSecondaryActualDestinations_injective (hc.symm.trans he)
    have hk' := (nonpair_destination_index j k).mp hi
    rwa [hk'] at hk
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [generatedFeasibleSecondaryLocalOrbit_eq_physical]
      exact (generatedFeasibleSecondaryNOrbit_coverage x).mpr ⟨_, hx⟩
    · have hc := generatedFeasibleSecondaryNOrbit_actual_destination _ x hx
      have hi := (nonpair_destination_index j _).mpr rfl
      rwa [hi] at hc

/-- The actual containing-octad transition fiber is its complete original signed sector. -/
theorem generatedFeasibleSecondary_containing_transition_vectors :
    generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination = generatedFeasibleContainingOctadAxes := by
  have h := generatedFeasibleSecondary_nonpair_class_fiber 0
  change {x : GriessSpace |
    x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
      generatedFeasibleSecondaryAClass (sExtra x) =
        generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination} =
    generatedFeasibleContainingOctadOrbit at h
  simp_rw [generatedFeasibleSecondaryAClass_eq_iff_mem_orbit] at h
  exact h.trans generatedFeasibleContainingOctadOrbit_eq_axes

/-- The actual outside-octad transition fiber is its complete original signed sector. -/
theorem generatedFeasibleSecondary_outside_transition_vectors :
    generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleOutsideOctadDestination = generatedFeasibleOutsideOctadAxes := by
  have h := generatedFeasibleSecondary_nonpair_class_fiber 1
  change {x : GriessSpace |
    x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
      generatedFeasibleSecondaryAClass (sExtra x) =
        generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination} =
    generatedFeasibleOutsideOctadOrbit at h
  simp_rw [generatedFeasibleSecondaryAClass_eq_iff_mem_orbit] at h
  exact h.trans generatedFeasibleOutsideOctadOrbit_eq_axes

/-- The actual odd transition fiber is its complete original signed sector. -/
theorem generatedFeasibleSecondary_odd_transition_vectors :
    generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleSecondaryOddDestination = generatedFeasibleSecondaryOddAxes := by
  have h := generatedFeasibleSecondary_nonpair_class_fiber 2
  change {x : GriessSpace |
    x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
      generatedFeasibleSecondaryAClass (sExtra x) =
        generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination} =
    generatedFeasibleSecondaryOddOrbit at h
  simp_rw [generatedFeasibleSecondaryAClass_eq_iff_mem_orbit] at h
  exact h.trans generatedFeasibleSecondaryOddOrbit_eq_axes

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
