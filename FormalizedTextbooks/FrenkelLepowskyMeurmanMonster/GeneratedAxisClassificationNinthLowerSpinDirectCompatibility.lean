/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData

/-! Complete actual binary compatibility supplies genuine whole oriented local lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24, e (Pi.single j 1) = f (Pi.single j 1)) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply] using h j

/-- Every actual binary coordinate agrees for the genuine spin and oriented spatial factors. -/
theorem generatedNinth_lower_spin_direct_compatibility (i : Fin 11) :
    spinBinaryAction (generatedNinthLowerSpinCompact i) =
      leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) := by
  exact binary_equiv_eq_of_columns _ _ (fun j =>
    (generatedNinth_lower_spin_direct_compact_binary_generator i j).trans
      (generatedNinth_lower_spin_direct_isometry_binary i (Pi.single j 1)).symm)

/-- Both factors are genuine and compatible, retaining the full oriented spatial matrix. -/
def generatedNinthLowerSpinDirectFiber (i : Fin 11) : localFiberSubgroup :=
  ⟨(generatedNinthLowerSpinCompact i, generatedNinthLowerSpinDirectIsometry i),
    generatedNinth_lower_spin_direct_compatibility i⟩

/-- Each compatible factor pair gives a genuine local group element. -/
def generatedNinthLowerSpinDirectLocal (i : Fin 11) : H :=
  localFiberIntoH (generatedNinthLowerSpinDirectFiber i)

/-- Its Conway projection is the class of the complete oriented actual lattice isometry. -/
theorem generatedNinth_lower_spin_direct_projection (i : Fin 11) :
    projH (generatedNinthLowerSpinDirectLocal i) =
      (QuotientGroup.mk (generatedNinthLowerSpinDirectIsometry i) : Co1) := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
