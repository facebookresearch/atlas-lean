/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthLetterData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQProjectedEquality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! The sixteen letters of the Eighth-family forest are genuine elements of the actual
projected Eighth-axis stabilizer.

They are the twelve Golay basis sign isometries and four explicit permutation words fixing
the original dodecad and coordinate 20 (two generators of the flag stabilizer and their
inverses). Each is a genuine matrix fixer of the Eighth axis, hence lies in the projection of
the whole-axis stabilizer. Their binary actions are the literal letter columns of the forest. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Evaluate the four permutation words on coordinate 20 and the original dodecad.
private theorem perm_flag : ∀ k : Fin 4,
    (generatedAxisGlobalTwelveEighthPerm k).val 20 = 20 ∧
      golayPermute (generatedAxisGlobalTwelveEighthPerm k).val generatedEighthDodecadWord.val =
        generatedEighthDodecadWord.val := by
  decide +kernel

/-- Each permutation word fixes the original dodecad and coordinate 20. -/
theorem generatedAxisGlobalTwelveEighthPerm_mem (k : Fin 4) :
    generatedAxisGlobalTwelveEighthPerm k ∈ generatedEighthPermutationFlagStabilizer :=
  (generatedEighthPermutationFlagStabilizer_mem _).mpr (perm_flag k)

/-- The physical matrices are the actual permutation actions on integral coordinates. -/
theorem generatedAxisGlobalTwelveEighthPerm_embedding (k : Fin 4) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveEighthPerm k)).val
      (leechCoordinateEmbedding u) =
    leechCoordinateEmbedding (generatedAxisGlobalTwelveEighthPermPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24,
      generatedAxisGlobalTwelveEighthPermPhysical k i j =
        if (generatedAxisGlobalTwelveEighthPerm k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold generatedAxisGlobalTwelveEighthPermPhysical
    rw [← generatedAxisGlobalTwelveEighthPerm_forward]
    have he : (generatedAxisGlobalTwelveEighthPerm k).val j = i ↔
        (generatedAxisGlobalTwelveEighthPerm k).val.symm i = j := by
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- Each integral matrix is the actual permutation action on the lattice basis. -/
theorem generatedAxisGlobalTwelveEighthPerm_basis (k : Fin 4) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveEighthPerm k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ
      (generatedAxisGlobalTwelveEighthPermIntegral k *ᵥ u)) := by
  rw [generatedAxisGlobalTwelveEighthPerm_embedding, Matrix.mulVec_mulVec,
    generatedAxisGlobalTwelveEighthPerm_integral_certificate, ← Matrix.mulVec_mulVec]

/-- The binary matrices are the actual Conway quotient actions of the permutations. -/
theorem generatedAxisGlobalTwelveEighthPerm_binary (k : Fin 4) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk (golayPermutationIsometry
      (generatedAxisGlobalTwelveEighthPerm k))) v =
        generatedAxisGlobalTwelveEighthPermBinary k *ᵥ v := by
  change leechBinaryAction _ v = _
  rw [generatedAxisGlobalTwelveEighthPermBinary_certificate]
  exact leechBinaryAction_of_basis_certificate _ _ (generatedAxisGlobalTwelveEighthPerm_basis k) v

/-- The sixteen Eighth letters: twelve Golay basis signs, then the four permutations. -/
def generatedAxisGlobalTwelveEighthLetter (g : Fin 16) : Co1 :=
  if h : g.val < 12 then QuotientGroup.mk (monsterCo1GeometrySignIsometry ⟨g.val, h⟩)
  else QuotientGroup.mk (golayPermutationIsometry
    (generatedAxisGlobalTwelveEighthPerm ⟨g.val - 12, by omega⟩))

/-- The binary matrix of each letter. -/
def generatedAxisGlobalTwelveEighthLetterMatrix (g : Fin 16) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if h : g.val < 12 then monsterCo1GeometrySignBinary ⟨g.val, h⟩
  else generatedAxisGlobalTwelveEighthPermBinary ⟨g.val - 12, by omega⟩

/-- Each letter acts on binary vectors by its matrix. -/
theorem generatedAxisGlobalTwelveEighthLetter_binary (g : Fin 16) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (generatedAxisGlobalTwelveEighthLetter g) v =
      generatedAxisGlobalTwelveEighthLetterMatrix g *ᵥ v := by
  unfold generatedAxisGlobalTwelveEighthLetter generatedAxisGlobalTwelveEighthLetterMatrix
  split_ifs
  · exact monsterCo1GeometrySign_binary _ v
  · exact generatedAxisGlobalTwelveEighthPerm_binary _ v

/-- Every letter lies in the actual projected Eighth-axis stabilizer. -/
theorem generatedAxisGlobalTwelveEighthLetter_mem (g : Fin 16) :
    generatedAxisGlobalTwelveEighthLetter g ∈ generatedEighthProjectedAxisStabilizer := by
  unfold generatedAxisGlobalTwelveEighthLetter
  split_ifs with h
  · apply generatedEighth_spatial_quotient_mem
    have hm := (generatedEighthSpatialEnumeration
      (monsterCo1GeometrySignCode ⟨g.val, h⟩,
        ⟨1, generatedEighthPermutationFlagStabilizer.one_mem⟩)).property
    have he : golayMonomialPair (monsterCo1GeometrySignCode ⟨g.val, h⟩, 1) =
        monsterCo1GeometrySignIsometry ⟨g.val, h⟩ := by
      change golaySignIsometry _ * golayPermutationIsometry 1 = golaySignIsometry _
      rw [show golayPermutationIsometry 1 = 1 from golayPermutationHom.map_one, mul_one]
    rw [← he]
    exact hm
  · apply generatedEighth_spatial_quotient_mem
    have hm := (generatedEighthSpatialEnumeration
      (0, ⟨generatedAxisGlobalTwelveEighthPerm ⟨g.val - 12, by omega⟩,
        generatedAxisGlobalTwelveEighthPerm_mem _⟩)).property
    have he : golayMonomialPair (0, generatedAxisGlobalTwelveEighthPerm ⟨g.val - 12, by omega⟩) =
        golayPermutationIsometry (generatedAxisGlobalTwelveEighthPerm ⟨g.val - 12, by omega⟩) := by
      change golaySignIsometry 0 * _ = _
      rw [show golaySignIsometry 0 = 1 from golaySignHom.map_one, one_mul]
    rw [← he]
    exact hm

/-- The literal binary columns of each letter. -/
def generatedAxisGlobalTwelveEighthLetterColumn (g : Fin 16) (j : Fin 24) : ℕ :=
  (eighthForestLetterCols g).getD j.val 0

set_option maxHeartbeats 10000000 in
-- Compare all 384 literal columns with the letter matrices.
private theorem letter_columns : ∀ g : Fin 16, ∀ j : Fin 24,
    generatedAxisGlobalTwelveEighthLetterMatrix g *ᵥ Pi.single j 1 =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveEighthLetterColumn g j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- The literal column lists have the indexed columns.
private theorem letterCols_eq : ∀ g : Fin 16,
    eighthForestLetterCols g = List.ofFn (generatedAxisGlobalTwelveEighthLetterColumn g) := by
  decide +kernel

/-- Each letter acts on masks by XOR of its literal columns. -/
theorem generatedAxisGlobalTwelveEighthLetter_mask (g : Fin 16) (v : ℕ) :
    co1BinaryAction (generatedAxisGlobalTwelveEighthLetter g)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalQMaskVector (generatedAxisGlobalTwelveEighthLetterColumn g) v) := by
  refine (generatedAxisGlobalQMaskVector_actual _ _ (fun i => ?_) v).symm
  rw [generatedAxisGlobalTwelveEighthLetter_binary]
  exact letter_columns g i

private theorem maskSum_ofFn_eq_applyCols (n : ℕ) (f : Fin n → ℕ) (v : ℕ) :
    monsterCo1GeometryBinaryMaskSum
        (List.ofFn (fun i : Fin n => if v.testBit i.val then f i else 0)) =
      eighthForestApplyCols (List.ofFn f) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, monsterCo1GeometryBinaryMaskSum, eighthForestApplyCols]
    have h0 : v.testBit 0 = decide (v % 2 = 1) := Nat.testBit_zero v
    have hs : ∀ i : Fin n, v.testBit (i.succ).val = (v / 2).testBit i.val := by
      intro i
      rw [Fin.val_succ, Nat.testBit_add_one]
    simp only [Fin.val_zero, h0, decide_eq_true_eq, hs]
    rw [← ih (fun i => f i.succ) (v / 2)]
    rfl

/-- A word in the Eighth letters, as an element of `Co1` (the last letter acts first). -/
def generatedAxisGlobalTwelveEighthWord (w : List (Fin 16)) : Co1 :=
  (w.map generatedAxisGlobalTwelveEighthLetter).prod

/-- The fast evaluator computes exactly the actual binary action of every letter word. -/
theorem generatedAxisGlobalTwelveEighthWord_action (w : List (Fin 16)) (v : ℕ) :
    co1BinaryAction (generatedAxisGlobalTwelveEighthWord w)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (eighthForestWordApply w v) := by
  induction w generalizing v with
  | nil =>
    simp only [generatedAxisGlobalTwelveEighthWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons g w ih =>
    simp only [generatedAxisGlobalTwelveEighthWord, List.map_cons, List.prod_cons, map_mul,
      LinearEquiv.mul_apply] at ih ⊢
    rw [ih, generatedAxisGlobalTwelveEighthLetter_mask]
    congr 1
    simp only [eighthForestWordApply, List.foldr_cons]
    rw [generatedAxisGlobalQMaskVector, maskSum_ofFn_eq_applyCols, letterCols_eq]

/-- Every letter word lies in the actual projected Eighth-axis stabilizer. -/
theorem generatedAxisGlobalTwelveEighthWord_mem (w : List (Fin 16)) :
    generatedAxisGlobalTwelveEighthWord w ∈ generatedEighthProjectedAxisStabilizer := by
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
  exact generatedAxisGlobalTwelveEighthLetter_mem g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
