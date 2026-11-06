/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthBinaryActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthLocalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary

/-! Nineteen actual full-axis lifts for the fifth-family orbit certificate.
Each binary edge therefore acts by a genuine element fixing the actual axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All nineteen genuine spatial generators project from the actual full fifth-axis stabilizer. -/
theorem generatedAxisGlobalFifthSpatial_stabilizer (k : Fin 19) :
    QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) ∈
      generatedFifthProjectedAxisStabilizer := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalFifthSpatial, h, ↓reduceDIte]
    exact generatedFifthProjectedAxisStabilizer_sign_mem _
  · by_cases h' : k.val < 18
    · simp only [generatedAxisGlobalFifthSpatial, h, h', ↓reduceDIte]
      exact generatedFifthProjectedAxisStabilizer_permutation_mem _
    · simp only [generatedAxisGlobalFifthSpatial, h, h', ↓reduceDIte]
      exact generatedFifthProjectedAxisStabilizer_xi_mem

/-- Each original spatial generator has a genuine full-axis-fixing local lift. -/
theorem generatedAxisGlobalFifth_generator_lift_exists (k : Fin 19) :
    ∃ h : generatedFifthLocalAxisStabilizer,
      projH h.val = QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) :=
  generatedAxisGlobalFifthSpatial_stabilizer k

/-- Actual full-axis-fixing lifts, with all extraspecial corrections retained. -/
def generatedAxisGlobalFifthGenerator (k : Fin 19) : generatedFifthLocalAxisStabilizer :=
  Classical.choose (generatedAxisGlobalFifth_generator_lift_exists k)

/-- The chosen local lifts have exactly the original spatial projection. -/
theorem generatedAxisGlobalFifthGenerator_projection (k : Fin 19) :
    projH (generatedAxisGlobalFifthGenerator k).val =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) :=
  Classical.choose_spec (generatedAxisGlobalFifth_generator_lift_exists k)

/-- Every chosen generator fixes the complete genuine fifth axis. -/
theorem generatedAxisGlobalFifthGenerator_fixed (k : Fin 19) :
    rhoLocal (generatedAxisGlobalFifthGenerator k).val generatedFifthAxis = generatedFifthAxis :=
  (generatedAxisGlobalFifthGenerator k).property

/-- Every generator acts on the genuine binary Ω orbit by its checked actual matrix. -/
theorem generatedAxisGlobalFifthGenerator_binary (k : Fin 19)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalFifthGenerator k).val x).val =
      generatedAxisGlobalFifthBinaryMatrix k *ᵥ x.val := by
  change co1BinaryAction (projH (generatedAxisGlobalFifthGenerator k).val) x.val = _
  rw [generatedAxisGlobalFifthGenerator_projection, generatedAxisGlobalFifthSpatial_binary]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
