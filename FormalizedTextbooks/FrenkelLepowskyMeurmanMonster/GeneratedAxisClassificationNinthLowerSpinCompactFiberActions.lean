/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectSourceProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSpatialSourceActions

/-! Direct whole binary certificates place compact spin factors
in their actual original source fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The compact normalizer has the complete genuine source lattice binary action. -/
theorem generatedNinth_lower_spin_compact_compatibility (i : Fin 11) :
    spinBinaryAction (generatedNinthLowerSpinCompact i) =
      leechBinaryAction (generatedNinthLowerSpinSourceFiber i).val.2 := by
  rw [generatedNinth_lower_spin_direct_compatibility,
    generatedNinth_lower_spin_direct_source_binary]
  change leechBinaryAction
      (generatedNinthAffineTransport⁻¹ * generatedNinthAffineLowerSourceIsometry i *
        generatedNinthAffineTransport) = _
  rw [← generatedNinth_lower_spin_spatial_source_genuine]

/-- Each compact model is an actual compatible element of the defining local fiber product. -/
def generatedNinthLowerSpinCompactFiber (i : Fin 11) : localFiberSubgroup :=
  ⟨(generatedNinthLowerSpinCompact i, (generatedNinthLowerSpinSourceFiber i).val.2),
    generatedNinth_lower_spin_compact_compatibility i⟩

/-- The compact model gives a concrete genuine local group element. -/
def generatedNinthLowerSpinCompactLocal (i : Fin 11) : H :=
  localFiberIntoH (generatedNinthLowerSpinCompactFiber i)

/-- The compact genuine local element has the entire original source Conway projection. -/
theorem generatedNinth_lower_spin_compact_projection (i : Fin 11) :
    projH (generatedNinthLowerSpinCompactLocal i) =
      (QuotientGroup.mk (generatedNinthLowerSpinSourceFiber i).val.2 : Co1) := rfl

/-- Its Conway projection is the actual corrected original source projection. -/
theorem generatedNinth_lower_spin_compact_projection_eq_source (i : Fin 11) :
    projH (generatedNinthLowerSpinCompactLocal i) =
      projH (generatedNinthLowerSpinCorrectedLocal i) := by
  rw [generatedNinth_lower_spin_compact_projection,
    generatedNinth_lower_spin_corrected_projection]

/-- The complete compact generator is an element of the actual generated local image. -/
theorem generatedNinth_lower_spin_compact_generated_membership (i : Fin 11) :
    localIntoGenerated (generatedNinthLowerSpinCompactLocal i) ∈ localIntoGenerated.range :=
  ⟨generatedNinthLowerSpinCompactLocal i, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
