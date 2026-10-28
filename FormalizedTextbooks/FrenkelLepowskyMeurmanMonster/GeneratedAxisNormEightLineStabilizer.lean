/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Actual Co0 and Co1 stabilizers of the genuine norm-eight physical lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

instance : MulAction leechIsomSubgroup GeneratedNormEightLines where
  smul g P := ⟨conwayMatrixAction g P.val, by
    obtain ⟨u, hu⟩ := P.property
    refine ⟨g • u, ?_⟩
    rw [generatedNormEightLineMatrix_action, hu]⟩
  one_smul P := by
    apply Subtype.ext
    change conwayMatrixAction 1 P.val = P.val
    rw [map_one]
    rfl
  mul_smul g h P := by
    apply Subtype.ext
    change conwayMatrixAction (g * h) P.val =
      conwayMatrixAction g (conwayMatrixAction h P.val)
    rw [map_mul]
    rfl

theorem generatedNormEightLine_equivariant (g : leechIsomSubgroup) (u : LeechNormEight) :
    g • generatedNormEightLine u = generatedNormEightLine (g • u) :=
  Subtype.ext (generatedNormEightLineMatrix_action g u).symm

/-- Actual Co0 acts transitively on these physical lines. -/
theorem generatedNormEightLine_orbit_eq_univ :
    MulAction.orbit leechIsomSubgroup (generatedNormEightLine leechNormEightAxis) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro P
  obtain ⟨u, rfl⟩ := generatedNormEightLine_surjective P
  have hu : u ∈ MulAction.orbit leechIsomSubgroup leechNormEightAxis := by
    rw [leechNormEight_orbit_eq_univ]
    trivial
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, (generatedNormEightLine_equivariant g _).trans
    (congrArg generatedNormEightLine hg)⟩

/-- The full actual physical-line stabilizer inside Co0. -/
def generatedNormEightLineStabilizer : Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup (generatedNormEightLine leechNormEightAxis)

theorem generatedNormEightLineStabilizer_mem (g : leechIsomSubgroup) :
    g ∈ generatedNormEightLineStabilizer ↔
      conwayMatrixAction g (generatedNormEightLineMatrix leechNormEightAxis) =
        generatedNormEightLineMatrix leechNormEightAxis := by
  change g • generatedNormEightLine leechNormEightAxis =
    generatedNormEightLine leechNormEightAxis ↔ _
  exact Subtype.ext_iff

/-- The actual line stabilizer allows both orientations, and has order 41783132160. -/
theorem generatedNormEightLineStabilizer_card :
    Nat.card generatedNormEightLineStabilizer = 41783132160 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite GeneratedNormEightLines
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup
    (generatedNormEightLine leechNormEightAxis))
  let _ := Fintype.ofFinite generatedNormEightLineStabilizer
  have horbit : Nat.card (MulAction.orbit leechIsomSubgroup
      (generatedNormEightLine leechNormEightAxis)) = 199017000 := by
    rw [generatedNormEightLine_orbit_eq_univ,
      Nat.card_congr (Equiv.Set.univ GeneratedNormEightLines), generatedNormEightLines_card]
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group leechIsomSubgroup
    (generatedNormEightLine leechNormEightAxis)
  simp only [← Nat.card_eq_fintype_card, horbit, co0_card_exact] at h
  change 199017000 * Nat.card generatedNormEightLineStabilizer =
    8315553613086720000 at h
  omega

/-- Both genuine central signs preserve the actual unoriented line. -/
theorem generatedNormEight_signs_le_lineStabilizer :
    signsSubgroup ≤ generatedNormEightLineStabilizer := by
  intro g hg
  rw [generatedNormEightLineStabilizer_mem]
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    rw [he, map_one]
    rfl
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      simp [leechIsomMatrix, hg, Matrix.one_apply, Pi.single_apply]
    rw [conwayMatrixAction_eq_conjugate, hm]
    simp

/-- The genuine physical line stabilizer in the central-sign quotient Co1. -/
def generatedNormEightCo1LineStabilizer : Subgroup Co1 :=
  generatedNormEightLineStabilizer.map (QuotientGroup.mk' signsSubgroup)

theorem generatedNormEightLineStabilizer_index :
    generatedNormEightLineStabilizer.index = 199017000 := by
  have h := generatedNormEightLineStabilizer.card_mul_index
  rw [generatedNormEightLineStabilizer_card, co0_card_exact] at h
  omega

theorem generatedNormEightCo1LineStabilizer_index :
    generatedNormEightCo1LineStabilizer.index = 199017000 := by
  change (generatedNormEightLineStabilizer.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedNormEightLineStabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedNormEight_signs_le_lineStabilizer

/-- The actual Co1 norm-eight line stabilizer has order 20891566080. -/
theorem generatedNormEightCo1LineStabilizer_card :
    Nat.card generatedNormEightCo1LineStabilizer = 20891566080 := by
  have h := generatedNormEightCo1LineStabilizer.card_mul_index
  rw [generatedNormEightCo1LineStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 199017000)
    (h.trans (by decide : 4157776806543360000 = 20891566080 * 199017000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
