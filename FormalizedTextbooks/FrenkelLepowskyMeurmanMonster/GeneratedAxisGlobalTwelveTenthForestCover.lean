/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestStage1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestStage2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestStage3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestStage4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestStage5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestLinear
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialBinaryAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic

/-! Every singular binary mask lies in the orbit of one of the 87 forest roots under every
subgroup of `Co1` containing the six gated Tenth letters.

Each doubling step adds the masks whose image under a word in the letters is already present;
the row operations of the step compute exactly the actual binary action of that word, which is
checked on the 24 basis masks. The five stage theorems then reach every singular mask. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem maskSum_ofFn_eq_applyCols (n : ℕ) (f : Fin n → ℕ) (v : ℕ) :
    monsterCo1GeometryBinaryMaskSum
        (List.ofFn (fun i : Fin n => if v.testBit i.val then f i else 0)) =
      tenthForestApplyCols (List.ofFn f) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, monsterCo1GeometryBinaryMaskSum, tenthForestApplyCols]
    have h0 : v.testBit 0 = decide (v % 2 = 1) := Nat.testBit_zero v
    have hs : ∀ i : Fin n, v.testBit (i.succ).val = (v / 2).testBit i.val := by
      intro i
      rw [Fin.val_succ, Nat.testBit_add_one]
    simp only [Fin.val_zero, h0, decide_eq_true_eq, hs]
    rw [← ih (fun i => f i.succ) (v / 2)]
    rfl

set_option maxRecDepth 100000 in
-- The literal letter columns are the gated Tenth projection columns.
private theorem letterCols_eq : ∀ g : Fin 6,
    tenthForestLetterCols g =
      List.ofFn (generatedTenthAxisLowerRecoveryThreeProjectionColumns g) := by
  decide +kernel

/-- The fast evaluator computes exactly the gated mask action of every letter word. -/
theorem tenthForestWordApply_eq (w : List (Fin 6)) (v : ℕ) :
    tenthForestWordApply w v = generatedTenthAxisLowerRecoveryThreeProjectionMaskWord w v := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    simp only [tenthForestWordApply, generatedTenthAxisLowerRecoveryThreeProjectionMaskWord,
      List.foldr_cons] at ih ⊢
    rw [ih, generatedAxisGlobalQMaskVector, maskSum_ofFn_eq_applyCols, letterCols_eq]

/-- The row operations of every step compute its word's gated mask action on the basis. -/
theorem tenthForestStage_basis (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (tenthForestStageOps s).zip (tenthForestStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) =
        generatedTenthAxisLowerRecoveryThreeProjectionMaskWord p.2 (2 ^ j) := by
  intro p hp j hj
  rw [← tenthForestWordApply_eq]
  exact tenthForestStage_basis_words s hs p hp j hj

/-- The row operations of every step compute the actual binary action of its word. -/
theorem tenthForestStage_action (s : ℕ) (hs : s < 5)
    (p : List (ℕ × ℕ) × List (Fin 6))
    (hp : p ∈ (tenthForestStageOps s).zip (tenthForestStageWords s)) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap p.1 b) =
      co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionWord p.2)
        (monsterCo1GeometryBinaryMaskDecode b) := by
  apply tenthForestOpsMap_decode_of_basis p.1
    (co1BinaryAction (generatedTenthAxisLowerRecoveryThreeProjectionWord p.2)).toLinearMap
  intro j
  rw [tenthForestStage_basis s hs p hp j.val j.isLt, LinearEquiv.coe_coe,
    generatedTenth_axis_lower_recovery_three_projection_word_action
      generatedTenth_compact_spatial_binary_all]

/-- The masks lying in the orbit of a forest root under a subgroup of `Co1`. -/
def TenthForestReached (G : Subgroup Co1) (b : ℕ) : Prop :=
  ∃ m ∈ tenthForestRoots, ∃ c ∈ G, co1BinaryAction c (monsterCo1GeometryBinaryMaskDecode m) =
    monsterCo1GeometryBinaryMaskDecode (n := 24) b

/-- One stage of doubling keeps every reached position inside the root orbits. -/
theorem tenthForestStage_reached (G : Subgroup Co1)
    (hG : ∀ g : Fin 6, generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈ G)
    (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
    (hP : ∀ b, S.testBit b = true → TenthForestReached G b) :
    ∀ b, (tenthForestDoubles (tenthForestStageOps s) S).testBit b = true →
      TenthForestReached G b := by
  have hfst : ((tenthForestStageOps s).zip (tenthForestStageWords s)).map Prod.fst =
      tenthForestStageOps s :=
    List.map_fst_zip (le_of_eq (tenthForestStage_length s hs))
  have hword (w : List (Fin 6)) : generatedTenthAxisLowerRecoveryThreeProjectionWord w ∈ G := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact hG g
  rw [← hfst]
  apply tenthForestDoubles_induction (TenthForestReached G)
  · rw [hfst]
    exact tenthForestStageOps_valid s
  · intro ops hops b _ hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hops
    obtain ⟨m, hm, c, hc, he⟩ := hb
    refine ⟨m, hm, (generatedTenthAxisLowerRecoveryThreeProjectionWord p.2)⁻¹ * c,
      G.mul_mem (G.inv_mem (hword p.2)) hc, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, he, tenthForestStage_action s hs p hp, map_inv,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  · exact hS
  · exact hP

private theorem foldl_xor_ofFn (g : ℕ → Bool) (n : ℕ) :
    (List.ofFn (fun i : Fin n => g i.val)).foldl xor false =
      (Nat.rec false (fun k acc => xor (g k) acc) n : Bool) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil]
    rw [ih, Bool.xor_comm]

private theorem quadParity_eq (b n : ℕ) :
    tenthForestQuadParityUpTo b n =
      (Nat.rec false (fun k acc => xor (b.testBit k && b.testBit (k + 12)) acc) n : Bool) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tenthForestQuadParityUpTo, ih]

/-- A singular mask is not a nonsingular position. -/
theorem tenthForestNonsingular_of_singular (b : ℕ) (hs : generatedAxisGlobalMaskSingular b = true) :
    tenthForestNonsingular.testBit b = false := by
  rw [tenthForestNonsingular_testBit, quadParity_eq]
  have h := foldl_xor_ofFn (fun k => b.testBit k && b.testBit (k + 12)) 12
  simp only [generatedAxisGlobalMaskSingular, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  rw [← h, hs, Bool.and_false]

/-- Every singular binary mask lies in the orbit of a forest root, under every subgroup of
`Co1` containing the six gated Tenth letters. -/
theorem tenthForest_reached (G : Subgroup Co1)
    (hG : ∀ g : Fin 6, generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈ G)
    (b : ℕ) (hb : b < 16777216) (hs : generatedAxisGlobalMaskSingular b = true) :
    TenthForestReached G b := by
  have h0 : ∀ b, tenthForestStart.testBit b = true → TenthForestReached G b := by
    intro b hb
    rw [tenthForestStart_testBit, decide_eq_true_eq] at hb
    exact ⟨b, hb, 1, G.one_mem, by rw [map_one, LinearEquiv.coe_one, id]⟩
  have hb0 := tenthForestStart_bounded
  have hval (s : ℕ) := tenthForestStageOps_valid s
  have hstage (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
      (hP : ∀ b, S.testBit b = true → TenthForestReached G b) :
      TenthForestBounded (tenthForestDoubles (tenthForestStageOps s) S) ∧
        ∀ b, (tenthForestDoubles (tenthForestStageOps s) S).testBit b = true →
          TenthForestReached G b :=
    ⟨tenthForestDoubles_bounded _ (hval s) S hS, tenthForestStage_reached G hG s hs S hS hP⟩
  obtain ⟨hb1, h1⟩ := hstage 0 (by decide) _ hb0 h0
  rw [tenthForest_stage1] at hb1 h1
  obtain ⟨hb2, h2⟩ := hstage 1 (by decide) _ hb1 h1
  rw [tenthForest_stage2] at hb2 h2
  obtain ⟨hb3, h3⟩ := hstage 2 (by decide) _ hb2 h2
  rw [tenthForest_stage3] at hb3 h3
  obtain ⟨hb4, h4⟩ := hstage 3 (by decide) _ hb3 h3
  rw [tenthForest_stage4] at hb4 h4
  obtain ⟨_, h5⟩ := hstage 4 (by decide) _ hb4 h4
  apply h5
  have hall := congrArg (fun S => S.testBit b) tenthForest_stage5
  simp only [Nat.testBit_or, tenthForestAll_testBit, tenthForestNonsingular_of_singular b hs,
    Bool.false_or, decide_eq_true hb] at hall
  exact hall

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
