/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactSourceBinaryCertificates

/-! Compact spin lifts retain compatibility with their complete original Co0 source words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The complete original spatial source word of each proposed whole-axis lift. -/
def generatedTwelfthSpinCompactSpatial (g : Fin 12) : leechIsomSubgroup :=
  (((generatedTwelfthSpinCompactSpatialWord g).map generatedTwelfthRootOrbitLetter).prod).val

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- All actual lattice binary coordinates agree with the genuine compact spin action. -/
theorem generatedTwelfth_spin_compact_compatibility (g : Fin 12) :
    spinBinaryAction (generatedTwelfthSpinCompact g) =
      leechBinaryAction (generatedTwelfthSpinCompactSpatial g) := by
  exact binary_equiv_eq_of_columns _ _ (fun j =>
    (generatedTwelfth_spin_compact_binary_generator_actual g j).trans
      (generatedTwelfth_spin_compact_source_binary_actual g j).symm)

/-- Every proposed compact lift is an actual compatible element of the defining fiber product. -/
def generatedTwelfthSpinCompactFiber (g : Fin 12) : localFiberSubgroup :=
  ⟨(generatedTwelfthSpinCompact g, generatedTwelfthSpinCompactSpatial g),
    generatedTwelfth_spin_compact_compatibility g⟩

/-- The compatible compact lift is a concrete genuine local group element. -/
def generatedTwelfthSpinCompactLocal (g : Fin 12) : H :=
  localFiberIntoH (generatedTwelfthSpinCompactFiber g)

/-- Its complete Conway projection is precisely the retained original whole spatial source word. -/
theorem generatedTwelfth_spin_compact_projection (g : Fin 12) :
    projH (generatedTwelfthSpinCompactLocal g) =
      (QuotientGroup.mk (generatedTwelfthSpinCompactSpatial g) : Co1) := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
