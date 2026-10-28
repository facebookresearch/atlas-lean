/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortFixed0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortFixed1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortFixed2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortFixed3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialMatrixFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthStabilizerProjection

/-! Genuine full fourth-axis stabilizing lifts of all four original monomial flag generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
-- Reduce only the four bounded original word expressions when assembling the finite family.
/-- Every original corrected monomial word fixes the entire genuine fourth axis. -/
theorem generatedFourth_monomial_axis_fixed (k : Fin 4) :
    rhoLocal (localFiberIntoH (generatedFourthMonomialCorrectedFiber k)) generatedFourthAxis =
      generatedFourthAxis := by
  fin_cases k
  · exact generatedFourth_monomial_axis_fixed_0
  · exact generatedFourth_monomial_axis_fixed_1
  · exact generatedFourth_monomial_axis_fixed_2
  · exact generatedFourth_monomial_axis_fixed_3

/-- The four actual corrected words, now elements of the genuine full-axis H stabilizer. -/
def generatedFourthMonomialAxisLift (k : Fin 4) : generatedFourthLocalAxisStabilizer :=
  ⟨localFiberIntoH (generatedFourthMonomialCorrectedFiber k), generatedFourth_monomial_axis_fixed k⟩

/-- The exact original Co1 classes of the four genuine monomial flag words. -/
def generatedFourthMonomialFlagProjection (k : Fin 4) :
    generatedAxisE8Co1ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort :=
  ⟨(QuotientGroup.mk' signsSubgroup) (generatedFourthMonomialFiber k).val.2,
    ⟨(generatedFourthMonomialFiber k).val.2, generatedFourth_monomial_flag_mem k, rfl⟩⟩

/-- Full-axis lifts project to precisely their original physical monomial flag generators. -/
theorem generatedFourth_monomial_axis_lift_projection (k : Fin 4) :
    generatedFourthLocalAxisProjection (generatedFourthMonomialAxisLift k) =
      generatedFourthMonomialFlagProjection k := by
  apply Subtype.ext
  change (QuotientGroup.mk' signsSubgroup) (generatedFourthMonomialCorrectedFiber k).val.2 = _
  rw [generatedFourth_monomial_corrected_spatial]
  rfl

/-- All four genuine monomial flag generators lie in the actual projected axis stabilizer. -/
theorem generatedFourth_monomial_projection_mem_range (k : Fin 4) :
    generatedFourthMonomialFlagProjection k ∈ generatedFourthLocalAxisProjection.range :=
  ⟨generatedFourthMonomialAxisLift k, generatedFourth_monomial_axis_lift_projection k⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
