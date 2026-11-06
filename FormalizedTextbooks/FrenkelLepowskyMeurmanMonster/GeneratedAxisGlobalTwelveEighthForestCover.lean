/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestStage1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestStage2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestStage3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestStage4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestStage5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestLinear
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic

/-! Every singular binary mask lies in the orbit of one of the Eighth forest roots under the
actual projected Eighth-axis stabilizer.

Each doubling step adds the masks whose image under a word in the sixteen letters is already
present; the row operations of the step compute exactly the actual binary action of that word,
which is checked on the 24 basis masks. The five stage theorems then reach every singular mask.
The argument follows the gated Tenth bitset forest with the Eighth letters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The row operations of every step compute the actual binary action of its word. -/
theorem eighthForestStage_action (s : ℕ) (hs : s < 5)
    (p : List (ℕ × ℕ) × List (Fin 16))
    (hp : p ∈ (eighthForestStageOps s).zip (eighthForestStageWords s)) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap p.1 b) =
      co1BinaryAction (generatedAxisGlobalTwelveEighthWord p.2)
        (monsterCo1GeometryBinaryMaskDecode b) := by
  apply tenthForestOpsMap_decode_of_basis p.1
    (co1BinaryAction (generatedAxisGlobalTwelveEighthWord p.2)).toLinearMap
  intro j
  rw [eighthForestStage_basis_words s hs p hp j.val j.isLt, LinearEquiv.coe_coe,
    generatedAxisGlobalTwelveEighthWord_action]

/-- The masks lying in the orbit of an Eighth forest root under a subgroup of `Co1`. -/
def EighthForestReached (G : Subgroup Co1) (b : ℕ) : Prop :=
  ∃ m ∈ eighthForestRoots, ∃ c ∈ G, co1BinaryAction c (monsterCo1GeometryBinaryMaskDecode m) =
    monsterCo1GeometryBinaryMaskDecode (n := 24) b

/-- One stage of doubling keeps every reached position inside the root orbits. -/
theorem eighthForestStage_reached (G : Subgroup Co1)
    (hG : ∀ w : List (Fin 16), generatedAxisGlobalTwelveEighthWord w ∈ G)
    (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
    (hP : ∀ b, S.testBit b = true → EighthForestReached G b) :
    ∀ b, (tenthForestDoubles (eighthForestStageOps s) S).testBit b = true →
      EighthForestReached G b := by
  have hfst : ((eighthForestStageOps s).zip (eighthForestStageWords s)).map Prod.fst =
      eighthForestStageOps s :=
    List.map_fst_zip (le_of_eq (eighthForestStage_length s hs))
  rw [← hfst]
  apply tenthForestDoubles_induction (EighthForestReached G)
  · rw [hfst]
    exact eighthForestStageOps_valid s
  · intro ops hops b _ hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hops
    obtain ⟨m, hm, c, hc, he⟩ := hb
    refine ⟨m, hm, (generatedAxisGlobalTwelveEighthWord p.2)⁻¹ * c,
      G.mul_mem (G.inv_mem (hG p.2)) hc, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, he, eighthForestStage_action s hs p hp, map_inv,
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
theorem eighthForestNonsingular_of_singular (b : ℕ)
    (hs : generatedAxisGlobalMaskSingular b = true) :
    tenthForestNonsingular.testBit b = false := by
  rw [tenthForestNonsingular_testBit, quadParity_eq]
  have h := foldl_xor_ofFn (fun k => b.testBit k && b.testBit (k + 12)) 12
  simp only [generatedAxisGlobalMaskSingular, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  rw [← h, hs, Bool.and_false]

/-- Every singular binary mask lies in the orbit of an Eighth forest root, under every subgroup
of `Co1` containing all words in the sixteen letters. -/
theorem eighthForest_reached (G : Subgroup Co1)
    (hG : ∀ w : List (Fin 16), generatedAxisGlobalTwelveEighthWord w ∈ G)
    (b : ℕ) (hb : b < 16777216) (hs : generatedAxisGlobalMaskSingular b = true) :
    EighthForestReached G b := by
  have h0 : ∀ b, eighthForestStart.testBit b = true → EighthForestReached G b := by
    intro b hb
    rw [eighthForestStart_testBit, decide_eq_true_eq] at hb
    exact ⟨b, hb, 1, G.one_mem, by rw [map_one, LinearEquiv.coe_one, id]⟩
  have hb0 := eighthForestStart_bounded
  have hval (s : ℕ) := eighthForestStageOps_valid s
  have hstage (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
      (hP : ∀ b, S.testBit b = true → EighthForestReached G b) :
      TenthForestBounded (tenthForestDoubles (eighthForestStageOps s) S) ∧
        ∀ b, (tenthForestDoubles (eighthForestStageOps s) S).testBit b = true →
          EighthForestReached G b :=
    ⟨tenthForestDoubles_bounded _ (hval s) S hS, eighthForestStage_reached G hG s hs S hS hP⟩
  obtain ⟨hb1, h1⟩ := hstage 0 (by decide) _ hb0 h0
  rw [eighthForest_stage1] at hb1 h1
  obtain ⟨hb2, h2⟩ := hstage 1 (by decide) _ hb1 h1
  rw [eighthForest_stage2] at hb2 h2
  obtain ⟨hb3, h3⟩ := hstage 2 (by decide) _ hb2 h2
  rw [eighthForest_stage3] at hb3 h3
  obtain ⟨hb4, h4⟩ := hstage 3 (by decide) _ hb3 h3
  rw [eighthForest_stage4] at hb4 h4
  obtain ⟨_, h5⟩ := hstage 4 (by decide) _ hb4 h4
  apply h5
  have hall := congrArg (fun S => S.testBit b) eighthForest_stage5
  simp only [Nat.testBit_or, tenthForestAll_testBit, eighthForestNonsingular_of_singular b hs,
    Bool.false_or, decide_eq_true hb] at hall
  exact hall

/-- Every singular binary mask lies in the orbit of an Eighth forest root under the actual
projected Eighth-axis stabilizer. -/
theorem eighthForest_reached_projected (b : ℕ) (hb : b < 16777216)
    (hs : generatedAxisGlobalMaskSingular b = true) :
    EighthForestReached generatedEighthProjectedAxisStabilizer b :=
  eighthForest_reached _ generatedAxisGlobalTwelveEighthWord_mem b hb hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
