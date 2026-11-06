/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionData

/-! Full original binary bindings turn signed source words into genuine Conway words.
All actual spatial binary obligations remain explicit hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The actual source spatial Conway value, without a chosen spin representative. -/
def generatedTenthAxisLowerRecoveryThreeProjectionActual (i : Fin 11) : Co1 :=
  QuotientGroup.mk' signsSubgroup (generatedTenthAxisLowerRecoveryCompactSpatial i)

/-- Positive source letters and their genuine inverses. -/
def generatedTenthAxisLowerRecoveryThreeProjectionLetter (g : Fin 6) : Co1 :=
  let i := generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex ⟨g.val % 3, Nat.mod_lt _ (by
    decide)⟩
  if g.val < 3 then generatedTenthAxisLowerRecoveryThreeProjectionActual i else
    (generatedTenthAxisLowerRecoveryThreeProjectionActual i)⁻¹

/-- Evaluate the entire auxiliary signed source word in the actual Conway quotient. -/
def generatedTenthAxisLowerRecoveryThreeProjectionWord (w : List (Fin 6)) : Co1 :=
  (w.map generatedTenthAxisLowerRecoveryThreeProjectionLetter).prod

/-- All forward columns equal the original compact data; every inverse column is exact. -/
theorem generatedTenth_axis_lower_recovery_three_projection_columns :
    (∀ g : Fin 3, ∀ j : Fin 24,
      generatedTenthAxisLowerRecoveryThreeProjectionColumns ⟨g.val, by omega⟩ j =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g) j) ∧
    (∀ g : Fin 3, ∀ j : Fin 24,
      generatedAxisGlobalQMaskVector (generatedTenthAxisLowerRecoveryThreeProjectionColumns ⟨g.val,
        by omega⟩)
        (generatedTenthAxisLowerRecoveryThreeProjectionColumns ⟨g.val + 3, by omega⟩ j) = 2 ^ j.val)
          := by
  decide +kernel

private theorem packed_basis : ∀ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j 1 := by
  decide +kernel

private theorem source_binary_basis
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (i : Fin 11) (j : Fin 24) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual i) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryCompactBinaryColumns i j)
        := by
  change leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial i) _ = _
  simpa only [packed_basis] using hsource i j

private theorem positive_mask_action
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (g : Fin 3) (v : ℕ) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g))
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
        monsterCo1GeometryBinaryMaskDecode
          (generatedAxisGlobalQMaskVector (generatedTenthAxisLowerRecoveryThreeProjectionColumns
            ⟨g.val, by omega⟩) v) := by
  exact (generatedAxisGlobalQMaskVector_actual _ _ (fun j => by
    rw [generatedTenth_axis_lower_recovery_three_projection_columns.1 g j]
    exact source_binary_basis hsource _ j) v).symm

private theorem signed_basis
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (g : Fin 6) (j : Fin 24) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionLetter g) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryThreeProjectionColumns g j)
        := by
  by_cases h : g.val < 3
  · let a : Fin 3 := ⟨g.val, h⟩
    have he : (⟨a.val, by omega⟩ : Fin 6) = g := Fin.ext rfl
    change co1BinaryAction (if g.val < 3 then _ else _) _ = _
    rw [ite_eq_left h]
    have hm : (⟨g.val % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = a :=
      Fin.ext (Nat.mod_eq_of_lt h)
    rw [hm, ← he, generatedTenth_axis_lower_recovery_three_projection_columns.1 a j]
    exact source_binary_basis hsource _ j
  · let a : Fin 3 := ⟨g.val % 3, Nat.mod_lt _ (by decide)⟩
    have ha : a.val + 3 = g.val := by dsimp [a]; omega
    have he : (⟨a.val + 3, by omega⟩ : Fin 6) = g := Fin.ext ha
    change co1BinaryAction (if g.val < 3 then _ else _) _ = _
    rw [ite_eq_right h, map_inv]
    apply (co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex a))).injective
    change co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex a))
      ((co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionActual
        (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex a))).symm (Pi.single j 1)) = _
    rw [LinearEquiv.apply_symm_apply, positive_mask_action hsource a]
    rw [← he, generatedTenth_axis_lower_recovery_three_projection_columns.2 a j]
    exact (packed_basis j).symm

/-- Each signed original word acts through all actual binary columns. -/
theorem generatedTenth_axis_lower_recovery_three_projection_word_action
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (w : List (Fin 6)) (v : ℕ) :
    co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryThreeProjectionMaskWord w
        v) := by
  induction w generalizing v with
  | nil =>
    rw [generatedTenthAxisLowerRecoveryThreeProjectionWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons g w ih =>
    rw [generatedTenthAxisLowerRecoveryThreeProjectionWord, List.map_cons, List.prod_cons, map_mul]
    change co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionLetter g)
      (co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionWord w)
        (monsterCo1GeometryBinaryMaskDecode v)) = _
    rw [ih]
    exact (generatedAxisGlobalQMaskVector_actual _ _ (signed_basis hsource g)
      (generatedTenthAxisLowerRecoveryThreeProjectionMaskWord w v)).symm

/-- Complete word certificates and full actual binary binding imply exact source class equality. -/
theorem generatedTenth_axis_lower_recovery_three_projection_candidate_word_of_certificate
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hword : ∀ i : Fin 11, ∀ j : Fin 24,
      generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
        (generatedTenthAxisLowerRecoveryThreeProjectionWords i) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns i j) (i : Fin 11) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual i =
      generatedTenthAxisLowerRecoveryThreeProjectionWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords i) := by
  apply co1BinaryAction_injective
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  have h := generatedTenth_axis_lower_recovery_three_projection_word_action hsource
    (generatedTenthAxisLowerRecoveryThreeProjectionWords i) (2 ^ j.val)
  rw [hword i j] at h
  simpa only [Pi.basisFun_apply, packed_basis] using
    (source_binary_basis hsource i j).trans h.symm

/-- Membership of three actual source classes implies membership of all eleven. -/
theorem generatedTenth_axis_lower_recovery_three_projection_mem_of_certificate
    (hsource : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition i)
    (hword : ∀ i : Fin 11, ∀ j : Fin 24,
      generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
        (generatedTenthAxisLowerRecoveryThreeProjectionWords i) (2 ^ j.val) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns i j)
    (P : Subgroup Co1)
    (h : ∀ g : Fin 3, generatedTenthAxisLowerRecoveryThreeProjectionActual
      (generatedTenthAxisLowerRecoveryThreeProjectionCandidateIndex g) ∈ P) (i : Fin 11) :
    generatedTenthAxisLowerRecoveryThreeProjectionActual i ∈ P := by
  rw [generatedTenth_axis_lower_recovery_three_projection_candidate_word_of_certificate hsource
    hword]
  have hl (g : Fin 6) : generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈ P := by
    dsimp only [generatedTenthAxisLowerRecoveryThreeProjectionLetter]
    split_ifs
    · exact h _
    · exact P.inv_mem (h _)
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
  exact hl g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
