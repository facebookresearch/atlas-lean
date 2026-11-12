/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPPClassification

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPPClassification

/-- Negative speed far below the threshold (`c² = 100 > 4 = 4 r D`): `not_isFront_of_sq_lt`
does not apply, but the energy argument does. -/
example (U U' : ℝ → ℝ) : ¬ IsFront 1 1 (-10) U U' :=
  not_isFront_of_nonpos one_pos one_pos (by norm_num)

/-- Speed exactly `0` (a standing front) is excluded. -/
example (U U' : ℝ → ℝ) : ¬ IsFront 2 3 0 U U' :=
  not_isFront_of_nonpos (by norm_num) (by norm_num) le_rfl

/-- The negative-speed exclusion holds with no sign condition on the profile. -/
example (U U' : ℝ → ℝ) (hU : IsWaveProfile 1 1 (-3) U U') (hbot : Tendsto U atBot (𝓝 1))
    (htop : Tendsto U atTop (𝓝 0)) : False :=
  not_tendsto_of_nonpos one_pos one_pos (by norm_num) hU hbot htop

/-- Sharp unconditional bound for every real speed: no front of speed `1.9 < 2 = 2 √(1 · 1)`. -/
example (U U' : ℝ → ℝ) : ¬ IsFront 1 1 (19 / 10) U U' :=
  not_isFront_of_lt one_pos one_pos (by norm_num)

/-- The Ablowitz–Zeppetella front at `D = r = C = 1` is strictly decreasing. -/
example : StrictAnti (azWave 1 1 1) := strictAnti_azWave one_pos one_pos one_pos

/-- Non-vacuity of the speed set, unconditionally: `5/√6` is a strictly-decreasing-front speed. -/
example : azSpeed 1 1 ∈ {c | ∃ U U' : ℝ → ℝ, IsFront 1 1 c U U' ∧ StrictAnti U} :=
  azSpeed_mem_frontSpeeds one_pos one_pos

/-- The minimal-speed bound recovered from the explicit front: `2 √(r D) ≤ 5 √(r D / 6)`. -/
example (D r : ℝ) (hD : 0 < D) (hr : 0 < r) : 2 * √(r * D) ≤ azSpeed D r :=
  two_mul_sqrt_le_of_isFront hD hr (isFront_azWave hD hr one_pos)

/-- Unconditional half of the classification. -/
example : {c | ∃ U U' : ℝ → ℝ, IsFront 1 1 c U U'} ⊆ Set.Ici (2 * √(1 * 1)) :=
  frontSpeeds_subset_Ici one_pos one_pos

/-- Classification, with the KPP existence theorem as hypothesis: at `D = r = 1` the
minimal-speed boundary `c = 2` is a front speed. -/
example
    (hKPP : ∀ c, 2 * √(1 * 1) ≤ c → ∃ U U' : ℝ → ℝ, IsFront 1 1 c U U' ∧ StrictAnti U) :
    ∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' :=
  (exists_isFront_iff one_pos one_pos hKPP 2).2 (by norm_num)

/-- Classification, below the boundary: no front at `c = 3/2` even with `hKPP`. -/
example
    (hKPP : ∀ c, 2 * √(1 * 1) ≤ c → ∃ U U' : ℝ → ℝ, IsFront 1 1 c U U' ∧ StrictAnti U) :
    ¬ ∃ U U' : ℝ → ℝ, IsFront 1 1 (3 / 2) U U' := by
  rw [exists_isFront_iff one_pos one_pos hKPP]
  norm_num

/-- Strictly monotone version of the classification. -/
example
    (hKPP : ∀ c, 2 * √(1 * 1) ≤ c → ∃ U U' : ℝ → ℝ, IsFront 1 1 c U U' ∧ StrictAnti U) :
    (∃ U U' : ℝ → ℝ, IsFront 1 1 5 U U' ∧ StrictAnti U) :=
  (exists_isFront_strictAnti_iff one_pos one_pos hKPP 5).2 (by norm_num)

/-- The speed set and its least element, given `hKPP`. -/
example (D r : ℝ) (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) :
    {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U'} = Set.Ici (2 * √(r * D)) ∧
      IsLeast {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U'} (2 * √(r * D)) :=
  ⟨frontSpeeds_eq_Ici hD hr hKPP, isLeast_frontSpeeds hD hr hKPP⟩

#print axioms not_tendsto_of_nonpos
#print axioms not_isFront_of_lt
#print axioms strictAnti_azWave
#print axioms exists_isFront_iff
#print axioms exists_isFront_strictAnti_iff
#print axioms frontSpeeds_eq_Ici
#print axioms isLeast_frontSpeeds

end MathlibExtTest.Biology.Dynamics.FisherKPPClassification
