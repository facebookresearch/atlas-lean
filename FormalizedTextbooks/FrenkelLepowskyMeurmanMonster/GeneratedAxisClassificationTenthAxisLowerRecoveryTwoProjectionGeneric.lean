/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionData

/-! Exact whole signed binary words bind the original three projected source values.
All genuine original spatial binary bindings remain explicit hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The two actual source classes use the literal joint spatial product and original10. -/
def generatedTenthAxisLowerRecoveryTwoProjectionActual : Fin 2 → Co1 :=
  ![QuotientGroup.mk' signsSubgroup (generatedTenthAxisLowerRecoveryJointCompactSpatial 0),
    generatedTenthAxisLowerRecoveryThreeProjectionActual 10]

/-- A genuine projected generator or its inverse, retaining the literal original orientation. -/
def generatedTenthAxisLowerRecoveryTwoProjectionLetter (g : Fin 4) : Co1 :=
  let i : Fin 2 := ⟨g.val % 2, Nat.mod_lt _ (by decide)⟩
  if g.val < 2 then generatedTenthAxisLowerRecoveryTwoProjectionActual i else
    (generatedTenthAxisLowerRecoveryTwoProjectionActual i)⁻¹

/-- Evaluate the whole signed two-generator word in the actual Conway quotient. -/
def generatedTenthAxisLowerRecoveryTwoProjectionWord (w : List (Fin 4)) : Co1 :=
  (w.map generatedTenthAxisLowerRecoveryTwoProjectionLetter).prod

/-- The actual projected joint is literally the product of original9 and original1. -/
theorem generatedTenth_axis_lower_recovery_two_projection_joint :
    generatedTenthAxisLowerRecoveryTwoProjectionActual 0 =
      generatedTenthAxisLowerRecoveryThreeProjectionActual 9 *
      generatedTenthAxisLowerRecoveryThreeProjectionActual 1 := by
  change QuotientGroup.mk' signsSubgroup
    (generatedTenthAxisLowerRecoveryCompactSpatial 9 *
      generatedTenthAxisLowerRecoveryCompactSpatial 1) = _
  exact (QuotientGroup.mk' signsSubgroup).map_mul _ _

/-- Every joint product column, original10 column and genuine inverse column is exact. -/
theorem generatedTenth_axis_lower_recovery_two_projection_columns :
    (∀ j : Fin 24, generatedAxisGlobalQMaskVector
      (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9)
      (generatedTenthAxisLowerRecoveryCompactBinaryColumns 1 j) =
        generatedTenthAxisLowerRecoveryTwoProjectionColumns 0 j) ∧
    (∀ j : Fin 24, generatedTenthAxisLowerRecoveryCompactBinaryColumns 10 j =
      generatedTenthAxisLowerRecoveryTwoProjectionColumns 1 j) ∧
    (∀ g : Fin 2, ∀ j : Fin 24,
      generatedAxisGlobalQMaskVector (generatedTenthAxisLowerRecoveryTwoProjectionColumns ⟨g.val, by
        omega⟩)
        (generatedTenthAxisLowerRecoveryTwoProjectionColumns ⟨g.val + 2, by omega⟩ j) = 2 ^ j.val)
          := by
  decide +kernel

private theorem packed_basis : ∀ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j 1 := by
  decide +kernel

private theorem source_basis
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (i : Fin 11) (j : Fin 24) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual i) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryCompactBinaryColumns i j)
        := by
  change leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial i) _ = _
  simpa only [packed_basis] using hsource i j

private theorem positive_basis
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (g : Fin 2) (j : Fin 24) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual g) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryTwoProjectionColumns
        ⟨g.val, by omega⟩ j) := by
  fin_cases g
  · change co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual 0)
      (Pi.single j 1) =
        monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryTwoProjectionColumns 0 j)
    rw [generatedTenth_axis_lower_recovery_two_projection_joint, map_mul]
    change co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual 9)
      (co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual 1) (Pi.single j 1)) = _
    rw [source_basis hsource 1 j]
    have hm := (generatedAxisGlobalQMaskVector_actual
      (co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual 9))
      (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9) (source_basis hsource 9)
      (generatedTenthAxisLowerRecoveryCompactBinaryColumns 1 j)).symm
    rw [hm, generatedTenth_axis_lower_recovery_two_projection_columns.1 j]
  · change co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual 10)
      (Pi.single j 1) =
        monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryTwoProjectionColumns 1 j)
    rw [source_basis hsource 10 j,
      generatedTenth_axis_lower_recovery_two_projection_columns.2.1 j]

private theorem positive_mask_action
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (g : Fin 2) (v : ℕ) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual g)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalQMaskVector (generatedTenthAxisLowerRecoveryTwoProjectionColumns ⟨g.val,
          by omega⟩) v) :=
  (generatedAxisGlobalQMaskVector_actual _ _ (positive_basis hsource g) v).symm

private theorem signed_basis
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (g : Fin 4) (j : Fin 24) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionLetter g) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryTwoProjectionColumns g j)
        := by
  by_cases h : g.val < 2
  · let a : Fin 2 := ⟨g.val, h⟩
    have he : (⟨a.val, by omega⟩ : Fin 4) = g := Fin.ext rfl
    change co1BinaryAction (if g.val < 2 then _ else _) _ = _
    rw [ite_eq_left h]
    have hm : (⟨g.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = a :=
      Fin.ext (Nat.mod_eq_of_lt h)
    rw [hm, ← he]
    exact positive_basis hsource a j
  · let a : Fin 2 := ⟨g.val % 2, Nat.mod_lt _ (by decide)⟩
    have ha : a.val + 2 = g.val := by dsimp [a]; omega
    have he : (⟨a.val + 2, by omega⟩ : Fin 4) = g := Fin.ext ha
    change co1BinaryAction (if g.val < 2 then _ else _) _ = _
    rw [ite_eq_right h, map_inv]
    apply (co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual a)).injective
    change co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual a)
      ((co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionActual a)).symm (Pi.single j
        1)) = _
    rw [LinearEquiv.apply_symm_apply, positive_mask_action hsource a]
    rw [← he, generatedTenth_axis_lower_recovery_two_projection_columns.2.2 a j]
    exact (packed_basis j).symm

/-- All full original columns replay through the genuine signed two-generator word. -/
theorem generatedTenth_axis_lower_recovery_two_projection_word_action
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (w : List (Fin 4)) (v : ℕ) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryTwoProjectionMaskWord w v)
        := by
  induction w generalizing v with
  | nil =>
    rw [generatedTenthAxisLowerRecoveryTwoProjectionWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons g w ih =>
    rw [generatedTenthAxisLowerRecoveryTwoProjectionWord, List.map_cons, List.prod_cons, map_mul]
    change co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionLetter g)
      (co1BinaryAction (generatedTenthAxisLowerRecoveryTwoProjectionWord w)
        (monsterCo1GeometryBinaryMaskDecode v)) = _
    rw [ih]
    exact (generatedAxisGlobalQMaskVector_actual _ _ (signed_basis hsource g)
      (generatedTenthAxisLowerRecoveryTwoProjectionMaskWord w v)).symm

/-- Exact full word certificates give genuine original source class equality. -/
theorem generatedTenth_axis_lower_recovery_two_projection_candidate_word_of_certificate
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hword : ∀ i : Fin 3, ∀ j : Fin 24,
      generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
        (generatedTenthAxisLowerRecoveryTwoProjectionWords i) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex i) j)
    (i : Fin 3) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex i) =
      generatedTenthAxisLowerRecoveryTwoProjectionWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords i) := by
  apply co1BinaryAction_injective
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  have h := generatedTenth_axis_lower_recovery_two_projection_word_action hsource
    (generatedTenthAxisLowerRecoveryTwoProjectionWords i) (2 ^ j.val)
  rw [hword i j] at h
  simpa only [Pi.basisFun_apply, packed_basis] using
    (source_basis hsource _ j).trans h.symm

/-- Membership of the actual joint and original10 implies all three original source memberships. -/
theorem generatedTenth_axis_lower_recovery_two_projection_mem_of_certificate
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hword : ∀ i : Fin 3, ∀ j : Fin 24,
      generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
        (generatedTenthAxisLowerRecoveryTwoProjectionWords i) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex i) j)
    (P : Subgroup Co1) (h : ∀ g : Fin 2, generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈ P)
      (i : Fin 3) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex i) ∈ P := by
  rw [generatedTenth_axis_lower_recovery_two_projection_candidate_word_of_certificate hsource hword]
  have hl (g : Fin 4) : generatedTenthAxisLowerRecoveryTwoProjectionLetter g ∈ P := by
    dsimp only [generatedTenthAxisLowerRecoveryTwoProjectionLetter]
    split_ifs
    · exact h _
    · exact P.inv_mem (h _)
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
  exact hl g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
