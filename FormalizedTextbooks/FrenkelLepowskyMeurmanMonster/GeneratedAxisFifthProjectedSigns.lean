/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthProjectedSystem
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignAssembly

/-! All genuine Golay signs belong to the actual fifth-axis stabilizer projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The twelve literal sign labels are exactly the original encoder coordinate basis. -/
theorem generatedFifthSignCode_basis (k : Fin 12) :
    sourceGeneratedSignCode (generatedFifthSignCode k) = monsterCo1GeometrySignCode k := by
  have hc : ∀ k : Fin 12, ∀ j : Fin 12,
      golayLabelCoefficients (generatedFifthSignCode k) j = (Pi.single k 1 : SpinIndex) j := by
    decide +kernel
  apply Subtype.ext
  change golayEncoder (golayLabelCoefficients (generatedFifthSignCode k)) =
    golayEncoder (Pi.single k 1)
  rw [funext (hc k)]

/-- Whole corrected sign lifts give all twelve genuine sign generators in the actual axis image. -/
theorem generatedFifthProjectedAxisStabilizer_sign_mem (k : Fin 12) :
    QuotientGroup.mk' signsSubgroup (monsterCo1GeometrySignIsometry k) ∈
      generatedFifthProjectedAxisStabilizer := by
  refine ⟨⟨localFiberIntoH (generatedFifthSignCorrectedFiber k),
    generatedFifth_sign_corrected_full k⟩, ?_⟩
  change projH (localFiberIntoH (generatedFifthSignCorrectedFiber k)) = _
  rw [generatedFifth_sign_corrected_projection, generatedFifthSignCode_basis]
  rfl

/-- Every element of the full actual Golay sign group projects from a genuine axis lift. -/
theorem generatedFifthProjectedAxisStabilizer_all_sign_mem (c : golayCode) :
    QuotientGroup.mk' signsSubgroup (golaySignIsometry c) ∈
      generatedFifthProjectedAxisStabilizer := by
  have h : monsterCo1GeometryBasisSignIsometrySubgroup ≤
      generatedFifthProjectedAxisStabilizer.comap (QuotientGroup.mk' signsSubgroup) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨k, rfl⟩
    exact generatedFifthProjectedAxisStabilizer_sign_mem k
  exact h (monsterCo1Geometry_all_sign_mem c)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
