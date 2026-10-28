/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightStage1
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightStage2
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightStage3
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightStage4
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightStage5
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestLinear
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskColumns
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Every singular binary mask lies in the orbit of one of the root-eight forest roots under
every subgroup of `Co1` containing lifts of the four root-eight letters.

The statements are generic in the lifts: any four elements of `Co1` acting on Λ/2Λ by the
displayed letter columns. Each doubling step adds the masks whose image under a letter word is
already present; the row operations of the step compute exactly the binary action of that word,
which is checked on the 24 basis masks. The stage theorems then reach every singular mask. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Elements of `Co1` acting on Λ/2Λ exactly by the four root-eight letter columns. -/
def RootEightForestLifts (L : Fin 4 → Co1) : Prop :=
  ∀ g : Fin 4, ∀ v : Fin 24 → ZMod 2,
    co1BinaryAction (L g) v = generatedAxisGlobalMaskColumnMatrix (rootEightForestColumns g) *ᵥ v

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

/-- The list evaluator of a column table is the genuine binary matrix action. -/
theorem rootEightForestApplyCols_decode (a : Fin 24 → ℕ) (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestApplyCols (List.ofFn a) v) =
      generatedAxisGlobalMaskColumnMatrix a *ᵥ monsterCo1GeometryBinaryMaskDecode v := by
  rw [← maskSum_ofFn_eq_applyCols, ← generatedAxisGlobalMaskColumnAction_decode]
  rfl

/-- The fast evaluator computes exactly the binary action of every letter word. -/
theorem rootEightForestWordApply_decode {L : Fin 4 → Co1} (hL : RootEightForestLifts L)
    (w : List (Fin 4)) (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (rootEightForestWordApply w v) =
      co1BinaryAction (w.map L).prod (monsterCo1GeometryBinaryMaskDecode v) := by
  induction w with
  | nil => simp [rootEightForestWordApply]
  | cons g w ih =>
    have hw : rootEightForestWordApply (g :: w) v =
        tenthForestApplyCols (rootEightForestLetterCols g) (rootEightForestWordApply w v) := rfl
    rw [hw, rootEightForestLetterCols_eq, rootEightForestApplyCols_decode, ih, ← hL g,
      List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]

/-- The row operations of every step compute the actual binary action of its word. -/
theorem rootEightForestStage_action {L : Fin 4 → Co1} (hL : RootEightForestLifts L)
    (s : ℕ) (hs : s < 5) (p : List (ℕ × ℕ) × List (Fin 4))
    (hp : p ∈ (rootEightForestStageOps s).zip (rootEightForestStageWords s)) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap p.1 b) =
      co1BinaryAction (p.2.map L).prod (monsterCo1GeometryBinaryMaskDecode b) := by
  apply tenthForestOpsMap_decode_of_basis p.1 (co1BinaryAction (p.2.map L).prod).toLinearMap
  intro j
  rw [rootEightForestStage_basis_words s hs p hp j.val j.isLt, LinearEquiv.coe_coe,
    rootEightForestWordApply_decode hL]

/-- The masks lying in the orbit of a forest root under a subgroup of `Co1`. -/
def RootEightForestReached (G : Subgroup Co1) (b : ℕ) : Prop :=
  ∃ m ∈ rootEightForestRoots, ∃ c ∈ G, co1BinaryAction c (monsterCo1GeometryBinaryMaskDecode m) =
    monsterCo1GeometryBinaryMaskDecode (n := 24) b

/-- One stage of doubling keeps every reached position inside the root orbits. -/
theorem rootEightForestStage_reached {L : Fin 4 → Co1} (hL : RootEightForestLifts L)
    (G : Subgroup Co1) (hG : ∀ g : Fin 4, L g ∈ G)
    (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
    (hP : ∀ b, S.testBit b = true → RootEightForestReached G b) :
    ∀ b, (tenthForestDoubles (rootEightForestStageOps s) S).testBit b = true →
      RootEightForestReached G b := by
  have hfst : ((rootEightForestStageOps s).zip (rootEightForestStageWords s)).map Prod.fst =
      rootEightForestStageOps s :=
    List.map_fst_zip (le_of_eq (rootEightForestStage_length s hs))
  have hword (w : List (Fin 4)) : (w.map L).prod ∈ G := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact hG g
  rw [← hfst]
  apply tenthForestDoubles_induction (RootEightForestReached G)
  · rw [hfst]
    exact rootEightForestStageOps_valid s
  · intro ops hops b _ hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hops
    obtain ⟨m, hm, c, hc, he⟩ := hb
    refine ⟨m, hm, (p.2.map L).prod⁻¹ * c, G.mul_mem (G.inv_mem (hword p.2)) hc, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, he, rootEightForestStage_action hL s hs p hp, map_inv,
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
theorem rootEightForestNonsingular_of_singular (b : ℕ)
    (hs : generatedAxisGlobalMaskSingular b = true) :
    tenthForestNonsingular.testBit b = false := by
  rw [tenthForestNonsingular_testBit, quadParity_eq]
  have h := foldl_xor_ofFn (fun k => b.testBit k && b.testBit (k + 12)) 12
  simp only [generatedAxisGlobalMaskSingular, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  rw [← h, hs, Bool.and_false]

/-- Every singular binary mask lies in the orbit of a forest root, under every subgroup of
`Co1` containing lifts of the four root-eight letters. -/
theorem rootEightForest_reached {L : Fin 4 → Co1} (hL : RootEightForestLifts L)
    (G : Subgroup Co1) (hG : ∀ g : Fin 4, L g ∈ G)
    (b : ℕ) (hb : b < 16777216) (hs : generatedAxisGlobalMaskSingular b = true) :
    RootEightForestReached G b := by
  have h0 : ∀ b, rootEightForestStart.testBit b = true → RootEightForestReached G b := by
    intro b hb
    rw [rootEightForestStart_testBit, decide_eq_true_eq] at hb
    exact ⟨b, hb, 1, G.one_mem, by rw [map_one, LinearEquiv.coe_one, id]⟩
  have hb0 := rootEightForestStart_bounded
  have hval (s : ℕ) := rootEightForestStageOps_valid s
  have hstage (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
      (hP : ∀ b, S.testBit b = true → RootEightForestReached G b) :
      TenthForestBounded (tenthForestDoubles (rootEightForestStageOps s) S) ∧
        ∀ b, (tenthForestDoubles (rootEightForestStageOps s) S).testBit b = true →
          RootEightForestReached G b :=
    ⟨tenthForestDoubles_bounded _ (hval s) S hS, rootEightForestStage_reached hL G hG s hs S hS hP⟩
  obtain ⟨hb1, h1⟩ := hstage 0 (by decide) _ hb0 h0
  rw [rootEightForest_stage1] at hb1 h1
  obtain ⟨hb2, h2⟩ := hstage 1 (by decide) _ hb1 h1
  rw [rootEightForest_stage2] at hb2 h2
  obtain ⟨hb3, h3⟩ := hstage 2 (by decide) _ hb2 h2
  rw [rootEightForest_stage3] at hb3 h3
  obtain ⟨hb4, h4⟩ := hstage 3 (by decide) _ hb3 h3
  rw [rootEightForest_stage4] at hb4 h4
  obtain ⟨_, h5⟩ := hstage 4 (by decide) _ hb4 h4
  apply h5
  have hall := congrArg (fun S => S.testBit b) rootEightForest_stage5
  simp only [Nat.testBit_or, tenthForestAll_testBit, rootEightForestNonsingular_of_singular b hs,
    Bool.false_or, decide_eq_true hb] at hall
  exact hall

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
