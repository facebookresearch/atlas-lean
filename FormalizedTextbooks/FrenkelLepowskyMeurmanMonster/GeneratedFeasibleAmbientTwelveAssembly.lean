/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientFirstZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientOctadZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientOddZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientFourthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientFifthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientSixthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientSeventhZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientNinthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue

/-! Conditional assembly of the actual feasible count over the twelve-family catalogue.

The orthogonal signed-short axis counts of nine catalogue representatives are discharged here
from their proved counts. Those of the Eighth, Root8 and Tenth representatives are explicit
hypotheses of this module; the Eighth and Root8 bounds are proved separately in
`GeneratedFeasibleAmbientEighthZero` and `GeneratedFeasibleAmbientRootEightZero`. With the
exact twelve local orbit lengths and the twelve coverage predicates of the global catalogue,
double counting bounds the orthogonal partners of the first axis by 11707448673375. Any finite
family of actual feasible vectors with pairwise distinct actual local stabilizer orbit sizes
summing to that number then fixes the actual feasible count. Every input of this module is an
explicit hypothesis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Upper bounds for the orthogonal axis counts of the twelve catalogue representatives. -/
def generatedFeasibleAmbientTwelveZeroBound : Fin 12 → ℕ :=
  ![93151, 4440, 506, 63, 16, 1, 3, 0, 0, 1, 0, 0]

/-- The orthogonal axis counts of the twelve representatives, with the Eighth, Root8 and Tenth
counts as explicit hypotheses. -/
theorem generatedFeasibleAmbient_twelve_zero_le
    (heighth : generatedFeasibleAmbientAxisZeroCount generatedEighthAxis ≤ 0)
    (hroot : generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1)
    (htenth : generatedFeasibleAmbientAxisZeroCount generatedTenthAxis ≤ 0) (i : Fin 12) :
    generatedFeasibleAmbientAxisZeroCount (generatedAxisGlobalTwelveRepresentative i) ≤
      generatedFeasibleAmbientTwelveZeroBound i := by
  fin_cases i
  · exact (generatedFeasibleAmbientAxisZeroCount_signedShort _ _).le
  · exact generatedFeasibleAmbientAxisZeroCount_octad.le
  · exact generatedFeasibleAmbientAxisZeroCount_odd.le
  · exact generatedFeasibleAmbientAxisZeroCount_fourth_le
  · exact generatedFeasibleAmbientAxisZeroCount_fifth.le
  · exact generatedFeasibleAmbientAxisZeroCount_sixth.le
  · exact generatedFeasibleAmbientAxisZeroCount_seventh.le
  · exact heighth
  · exact generatedFeasibleAmbientAxisZeroCount_ninth.le
  · exact hroot
  · exact generatedFeasibleAmbientAxisZeroCount_twelfth.le
  · exact htenth

/-- The double-counting sum of the twelve source lengths and orthogonal axis bounds. -/
theorem generatedFeasibleAmbient_twelve_arithmetic :
    ∑ i, generatedAxisGlobalTwelveCount i * generatedFeasibleAmbientTwelveZeroBound i =
      196560 * 11707448673375 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, generatedAxisGlobalTwelveCount,
    generatedFeasibleAmbientTwelveZeroBound]
  norm_num

/-- The actual orthogonal partners of the first axis are at most 11707448673375, from exact
local lengths, twelve-family coverage and the Eighth, Root8 and Tenth orthogonal axis bounds. -/
theorem generatedFeasibleAmbient_twelve_orthogonal_card_le
    (hc : GeneratedAxisGlobalTwelveCounted)
    (hcov : ∀ i, GeneratedAxisGlobalTwelveFamilyCovered i)
    (heighth : generatedFeasibleAmbientAxisZeroCount generatedEighthAxis ≤ 0)
    (hroot : generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1)
    (htenth : generatedFeasibleAmbientAxisZeroCount generatedTenthAxis ≤ 0) (p : Fin 276) :
    Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis (Sum.inl (0, p)) 0)) ≤
      11707448673375 := by
  have hcover : generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0) ⊆
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    (generatedAxisGlobalTwelve_orbit_eq_union hcov p).le
  have h := (generatedFeasibleAmbient_orthogonal_card_mul_le (Sum.inl (0, p)) 0
    generatedAxisGlobalTwelveRepresentative hcover).trans
    (generatedFeasibleAmbient_upper_of_bounds generatedAxisGlobalTwelveRepresentative
      generatedAxisGlobalTwelveCount generatedFeasibleAmbientTwelveZeroBound 11707448673375
      hc (generatedFeasibleAmbient_twelve_zero_le heighth hroot htenth)
      generatedFeasibleAmbient_twelve_arithmetic.le)
  omega

/-- The actual feasible count from the twelve-family catalogue inputs and a finite family of
actual feasible vectors whose actual local stabilizer orbits have pairwise distinct sizes
adding up to at least 11707448673375. -/
theorem generatedFeasibleAmbient_twelve_feasible_card
    (hc : GeneratedAxisGlobalTwelveCounted)
    (hcov : ∀ i, GeneratedAxisGlobalTwelveFamilyCovered i)
    (heighth : generatedFeasibleAmbientAxisZeroCount generatedEighthAxis ≤ 0)
    (hroot : generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1)
    (htenth : generatedFeasibleAmbientAxisZeroCount generatedTenthAxis ≤ 0)
    (p : Fin 276) {κ : Type*} [Fintype κ] (w : κ → GriessSpace) (f : κ → ℕ)
    (hw : ∀ j, w j ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1))
    (hf : ∀ j, Nat.card (MulAction.orbit (localAxisStabilizer p) (w j)) = f j)
    (hinj : Function.Injective f) (hsum : 11707448673375 ≤ ∑ j, f j) :
    Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 11707448673375 := by
  have hcover : generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0) ⊆
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    (generatedAxisGlobalTwelve_orbit_eq_union hcov p).le
  obtain ⟨hU, hUcard⟩ := generatedFeasibleAmbient_class_union_card p w f hw hf hinj
  exact generatedFeasibleAmbient_feasible_card_of_cover (Sum.inl (0, p))
    generatedAxisGlobalTwelveRepresentative 11707448673375 hcover
    (generatedFeasibleAmbient_upper_of_bounds generatedAxisGlobalTwelveRepresentative
      generatedAxisGlobalTwelveCount generatedFeasibleAmbientTwelveZeroBound 11707448673375
      hc (generatedFeasibleAmbient_twelve_zero_le heighth hroot htenth)
      generatedFeasibleAmbient_twelve_arithmetic.le)
    _ hU (hUcard ▸ hsum)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
