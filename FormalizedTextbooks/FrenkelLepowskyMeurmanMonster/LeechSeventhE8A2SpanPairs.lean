/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Planes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SpanTriple

/-! Every intrinsic nonorthogonal two-root plane belongs to the finite original catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The oriented finite relation holds for the original physical real roots. -/
theorem leechSeventhE8A2Plane_third_relation (p : Fin 1120) :
    leechSeventhE8A2PlaneRoots p 2 =
      (leechSeventhE8A2ThirdCoefficients p 0 : ℝ) • leechSeventhE8A2PlaneRoots p 0 +
      (leechSeventhE8A2ThirdCoefficients p 1 : ℝ) • leechSeventhE8A2PlaneRoots p 1 := by
  have hz : leechSeventhE8RootLocal (leechSeventhE8A2Indices p 2) =
      leechSeventhE8A2ThirdCoefficients p 0 •
        leechSeventhE8RootLocal (leechSeventhE8A2Indices p 0) +
      leechSeventhE8A2ThirdCoefficients p 1 •
        leechSeventhE8RootLocal (leechSeventhE8A2Indices p 1) := by
    ext i
    exact leechSeventhE8A2_third_relation p i
  let E : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 24 → ℝ) :=
    leechCoordinateEmbedding.comp generatedFifthFrameInsert
  have hm := congrArg E hz
  have he (j : Fin 3) : E (leechSeventhE8RootLocal (leechSeventhE8A2Indices p j)) =
      leechSeventhE8A2PlaneRoots p j := by
    simp only [E, LinearMap.comp_apply, leechSeventhE8A2PlaneRoots,
      leechSeventhE8RealRoot, leechSeventhE8Root_physical]
  simp only [map_add, map_smul, he] at hm
  simpa only [Int.cast_smul_eq_zsmul] using hm

/-- Any two distinct original roots of a candidate span its entire actual plane. -/
theorem leechSeventhE8A2Plane_span_pair (p : Fin 1120) (j k : Fin 3) (hjk : j ≠ k) :
    leechSeventhE8A2Plane p = Submodule.span ℝ
      {leechSeventhE8A2PlaneRoots p j, leechSeventhE8A2PlaneRoots p k} := by
  have ha : (leechSeventhE8A2ThirdCoefficients p 0 : ℝ) ≠ 0 := by
    rcases leechSeventhE8A2_third_coefficient_sign p 0 with h | h <;> rw [h] <;> norm_num
  have hb : (leechSeventhE8A2ThirdCoefficients p 1 : ℝ) ≠ 0 := by
    rcases leechSeventhE8A2_third_coefficient_sign p 1 with h | h <;> rw [h] <;> norm_num
  exact leechSeventh_span_triple_pair _ _ _ ha hb
    (leechSeventhE8A2Plane_third_relation p) j k hjk

/-- The intrinsic A2 planes spanned by nonorthogonal genuine roots of the selected E8 section. -/
def leechSeventhE8A2Planes : Set (Submodule ℝ (Fin 24 → ℝ)) := {W | ∃ r s : Fin 120,
  |∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i| = 16 ∧
    W = Submodule.span ℝ {leechSeventhE8RealRoot r, leechSeventhE8RealRoot s}}

/-- Every finite candidate is an intrinsic A2 plane of the actual original section. -/
theorem leechSeventhE8A2Plane_intrinsic (p : Fin 1120) :
    leechSeventhE8A2Plane p ∈ leechSeventhE8A2Planes := by
  refine ⟨leechSeventhE8A2Indices p 0, leechSeventhE8A2Indices p 1,
    leechSeventhE8A2_first_pair p, ?_⟩
  exact leechSeventhE8A2Plane_span_pair p 0 1 (by decide)

/-- The finite original candidate list covers every intrinsic actual two-root A2 plane. -/
theorem leechSeventhE8A2Planes_eq_range :
    leechSeventhE8A2Planes = Set.range leechSeventhE8A2Plane := by
  ext W
  constructor
  · rintro ⟨r, s, hrs, hW⟩
    obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := leechSeventhE8A2_pair_lookup r s hrs
    have hne : r ≠ s := by
      intro h
      subst s
      have hn := leechSeventhE8Root_norm_certificate r
      simp only [pow_two] at hn
      rw [hn] at hrs
      norm_num at hrs
    have hjk : j ≠ k := by
      intro h
      apply hne
      exact hj.symm.trans (h ▸ hk)
    refine ⟨leechSeventhE8A2PairIndex r s, ?_⟩
    rw [hW, leechSeventhE8A2Plane_span_pair _ j k hjk]
    simp only [leechSeventhE8A2PlaneRoots, hj, hk]
  · rintro ⟨p, rfl⟩
    exact leechSeventhE8A2Plane_intrinsic p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
