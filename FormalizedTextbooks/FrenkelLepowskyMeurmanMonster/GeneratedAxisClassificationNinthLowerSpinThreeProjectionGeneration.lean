/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectSourceProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinActualLowerCard
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Whole twenty-four-bit word certificates identify all eleven actual original Conway
source classes using candidates zero, nine and ten and their inverses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The three selected genuine original source candidates. -/
def generatedNinthLowerSpinThreeCandidateIndex : Fin 3 → Fin 11 := ![0, 9, 10]

/-- Complete positive and inverse binary columns of the three original candidates. -/
def generatedNinthLowerSpinThreeProjectionColumns : Fin 6 → Fin 24 → ℕ :=
  ![
    ![780855, 6543924, 4829188, 4813444, 7010241, 2699299, 64, 6543336, 256, 731108, 650091, 2048,
      4397056, 4331520, 2158592, 4718592, 12288, 6959104, 7143424, 2719744, 7929856, 6926336,
      2686976, 12595203],
    ![8864216, 1426514, 3748977, 5546403, 6095172, 8723085, 4311695, 2636831, 5049287, 8982890,
      10672541, 10177181, 13454550, 1971787, 7453440, 16774077, 10739794, 11106214, 6523664,
      6592148, 9926290, 13951737, 13195039, 1359380],
    ![13865918, 14917595, 16361469, 5824116, 549489, 10189828, 7005743, 3867335, 12938000,
      12141665, 7275135, 10660826, 4998022, 846163, 15477023, 4466701, 1305489, 12708297, 11446991,
      788996, 775794, 15494029, 7471959, 10030481],
    ![780855, 6543924, 4829188, 4813444, 7010241, 2699299, 64, 6543336, 256, 731108, 650091, 2048,
      4397056, 4331520, 2158592, 4718592, 12288, 6959104, 7143424, 2719744, 7929856, 6926336,
      2686976, 12595203],
    ![6966702, 576316, 12859193, 4500188, 12023165, 12587354, 1293195, 12141611, 8514318, 4735228,
      1410765, 14817081, 14599690, 3974451, 14617769, 15603210, 13139929, 2146856, 3240467,
      14062505, 7443564, 9834478, 552355, 14551109],
    ![176384, 9912958, 3638067, 8712562, 8026416, 13514064, 5243599, 7326663, 2808848, 15492676,
      5568045, 11696740, 7171710, 13382983, 5166797, 12874348, 13761814, 6672640, 15328610,
      8944241, 9469495, 14546897, 2550016, 9612030]
  ]

/-- Literal signed words in the three original actual source candidates. -/
def generatedNinthLowerSpinThreeProjectionWords : Fin 11 → List (Fin 6) :=
  ![
    [0],
    [1, 0, 4, 0, 1, 0, 4, 0],
    [1, 2, 0, 5, 4, 5, 1, 0, 4, 0, 2, 1, 0, 4],
    [1, 2, 0, 5, 4, 2, 1, 0, 4, 5, 5, 0, 2, 4, 0, 1],
    [1, 2, 0, 5, 4, 5, 1, 0, 4, 2, 4, 0, 1],
    [5, 0, 1, 0, 4, 2, 4, 0, 1, 2, 0, 5],
    [5, 0, 2, 2, 1, 0, 4, 5, 4, 0, 1, 2, 0, 5, 0],
    [1, 2, 0, 5, 4, 2, 1, 0, 4, 5, 5, 0, 2, 4, 0, 1, 1, 0, 4, 0],
    [1, 2, 0, 5, 0, 4, 0],
    [1],
    [2]
  ]

/-- Positive letters and their genuine inverses in the original Conway quotient. -/
def generatedNinthLowerSpinThreeProjectionLetter (g : Fin 6) : Co1 :=
  let i := generatedNinthLowerSpinThreeCandidateIndex ⟨g.val % 3, Nat.mod_lt _ (by decide)⟩
  if g.val < 3 then generatedNinthLowerSpinActualGenerator i
  else (generatedNinthLowerSpinActualGenerator i)⁻¹

/-- A complete genuine original source word in the Conway quotient. -/
def generatedNinthLowerSpinThreeProjectionWord (w : List (Fin 6)) : Co1 :=
  (w.map generatedNinthLowerSpinThreeProjectionLetter).prod

/-- Replay every original binary coordinate through the complete signed word. -/
def generatedNinthLowerSpinThreeProjectionMaskWord (w : List (Fin 6)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => generatedAxisGlobalQMaskVector
    (generatedNinthLowerSpinThreeProjectionColumns g) m) v

set_option maxHeartbeats 8000000 in
-- Check all full inverse columns and all original candidate columns through complete words.
private theorem complete_columns :
    (∀ g : Fin 3, ∀ j : Fin 24,
      generatedNinthLowerSpinThreeProjectionColumns ⟨g.val, by omega⟩ j =
        generatedNinthLowerSpinShortPackedColumns
          (generatedNinthLowerSpinThreeCandidateIndex g) j) ∧
    (∀ g : Fin 3, ∀ j : Fin 24,
      generatedAxisGlobalQMaskVector
        (generatedNinthLowerSpinThreeProjectionColumns ⟨g.val, by omega⟩)
        (generatedNinthLowerSpinThreeProjectionColumns ⟨g.val + 3, by omega⟩ j) = 2 ^ j.val) ∧
    (∀ i : Fin 11, ∀ j : Fin 24,
      generatedNinthLowerSpinThreeProjectionMaskWord
        (generatedNinthLowerSpinThreeProjectionWords i) (2 ^ j.val) =
          generatedNinthLowerSpinShortPackedColumns i j) := by
  decide +kernel

private theorem packed_basis : ∀ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j 1 := by
  decide +kernel

private theorem source_binary_basis (i : Fin 11) (j : Fin 24) :
    co1BinaryAction (generatedNinthLowerSpinActualGenerator i) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinShortPackedColumns i j) := by
  change co1BinaryAction (QuotientGroup.mk (generatedNinthAffineLowerTransportedIsometry i)) _ = _
  rw [← generatedNinth_lower_spin_direct_source_class i]
  change leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) _ = _
  rw [generatedNinth_lower_spin_direct_isometry_binary]
  have hm := (generatedNinth_lower_spin_short_packed_metadata i).1 j
  change toAdd (qQuotHom (generatedNinthLowerSpinShortPackedImages i j)) = _ at hm
  exact (generatedNinth_lower_spin_direct_compact_binary_certificate i j).symm.trans hm

private theorem positive_mask_action (g : Fin 3) (v : ℕ) :
    co1BinaryAction (generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex g))
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalQMaskVector
        (generatedNinthLowerSpinThreeProjectionColumns ⟨g.val, by omega⟩) v) := by
  exact (generatedAxisGlobalQMaskVector_actual _ _ (fun j => by
    rw [complete_columns.1 g j]
    exact source_binary_basis _ j) v).symm

private theorem signed_basis (g : Fin 6) (j : Fin 24) :
    co1BinaryAction (generatedNinthLowerSpinThreeProjectionLetter g) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthLowerSpinThreeProjectionColumns g j) := by
  by_cases h : g.val < 3
  · let a : Fin 3 := ⟨g.val, h⟩
    have he : (⟨a.val, by omega⟩ : Fin 6) = g := Fin.ext rfl
    change co1BinaryAction (if g.val < 3 then _ else _) _ = _
    rw [ite_eq_left h]
    have hm : (⟨g.val % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = a :=
      Fin.ext (Nat.mod_eq_of_lt h)
    rw [hm, ← he, complete_columns.1 a j]
    exact source_binary_basis _ j
  · let a : Fin 3 := ⟨g.val % 3, Nat.mod_lt _ (by decide)⟩
    have ha : a.val + 3 = g.val := by dsimp [a]; omega
    have he : (⟨a.val + 3, by omega⟩ : Fin 6) = g := Fin.ext ha
    change co1BinaryAction (if g.val < 3 then _ else _) _ = _
    rw [ite_eq_right h, map_inv]
    apply (co1BinaryAction (generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex a))).injective
    change (co1BinaryAction (generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex a)))
        ((co1BinaryAction (generatedNinthLowerSpinActualGenerator
          (generatedNinthLowerSpinThreeCandidateIndex a))).symm (Pi.single j 1)) = _
    rw [LinearEquiv.apply_symm_apply, positive_mask_action a]
    rw [← he, complete_columns.2.1 a j]
    exact (packed_basis j).symm

/-- Whole mask replay equals the actual full binary action of each genuine source word. -/
theorem generatedNinth_lower_spin_three_projection_word_action (w : List (Fin 6)) (v : ℕ) :
    co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord w)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
        monsterCo1GeometryBinaryMaskDecode
          (generatedNinthLowerSpinThreeProjectionMaskWord w v) := by
  induction w generalizing v with
  | nil =>
    rw [generatedNinthLowerSpinThreeProjectionWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons g w ih =>
    rw [generatedNinthLowerSpinThreeProjectionWord, List.map_cons, List.prod_cons, map_mul]
    change co1BinaryAction (generatedNinthLowerSpinThreeProjectionLetter g)
      (co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord w)
        (monsterCo1GeometryBinaryMaskDecode v)) = _
    rw [ih]
    exact (generatedAxisGlobalQMaskVector_actual _ _ (signed_basis g)
      (generatedNinthLowerSpinThreeProjectionMaskWord w v)).symm

/-- Binary faithfulness identifies every complete original Conway source class with its word. -/
theorem generatedNinth_lower_spin_three_projection_candidate_word (i : Fin 11) :
    generatedNinthLowerSpinActualGenerator i =
      generatedNinthLowerSpinThreeProjectionWord
        (generatedNinthLowerSpinThreeProjectionWords i) := by
  apply co1BinaryAction_injective
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  have h := generatedNinth_lower_spin_three_projection_word_action
    (generatedNinthLowerSpinThreeProjectionWords i) (2 ^ j.val)
  rw [complete_columns.2.2 i j] at h
  simpa only [Pi.basisFun_apply, packed_basis] using
    (source_binary_basis i j).trans h.symm

/-- Membership of three genuine original source values implies membership of all eleven. -/
theorem generatedNinth_lower_spin_three_projection_candidates_mem (P : Subgroup Co1)
    (h : ∀ g : Fin 3, generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex g) ∈ P) (i : Fin 11) :
    generatedNinthLowerSpinActualGenerator i ∈ P := by
  rw [generatedNinth_lower_spin_three_projection_candidate_word]
  have hl (g : Fin 6) : generatedNinthLowerSpinThreeProjectionLetter g ∈ P := by
    dsimp only [generatedNinthLowerSpinThreeProjectionLetter]
    split_ifs
    · exact h _
    · exact P.inv_mem (h _)
  have hw (w : List (Fin 6)) : generatedNinthLowerSpinThreeProjectionWord w ∈ P := by
    induction w with
    | nil => simpa only [generatedNinthLowerSpinThreeProjectionWord, List.map_nil,
        List.prod_nil] using P.one_mem
    | cons a w ih => exact P.mul_mem (hl a) ih
  exact hw _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
