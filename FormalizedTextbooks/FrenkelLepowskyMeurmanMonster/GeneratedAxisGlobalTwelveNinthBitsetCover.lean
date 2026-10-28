/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetStage1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetStage2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetStage3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetStage4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetStage5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestLinear
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthShortRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeWholeActualLower

/-! Complete Ninth-family binary forest: every genuine binary Ω point is reached from one of the
eight type-four forest roots by an actual element fixing the whole Ninth axis.

Each doubling step adds the masks whose image under a word in the six Ninth letters (the three
proved whole-axis candidate projections and their inverses) is already present; the row
operations of the step compute exactly the actual binary action of that word, checked on the
24 basis masks. The five stage theorems reach every singular mask. A reached Ω point is the
image of a root mask under the actual projected Ninth-axis stabilizer, which lifts to the
whole-axis stabilizer; the zero and short roots are excluded by lattice norms. The argument
follows the gated Tenth bitset forest. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem maskSum_ofFn_eq_applyCols (n : ℕ) (f : Fin n → ℕ) (v : ℕ) :
    monsterCo1GeometryBinaryMaskSum
        (List.ofFn (fun i : Fin n => if v.testBit i.val then f i else 0)) =
      ninthForestApplyCols (List.ofFn f) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, monsterCo1GeometryBinaryMaskSum, ninthForestApplyCols]
    have h0 : v.testBit 0 = decide (v % 2 = 1) := Nat.testBit_zero v
    have hs : ∀ i : Fin n, v.testBit (i.succ).val = (v / 2).testBit i.val := by
      intro i
      rw [Fin.val_succ, Nat.testBit_add_one]
    simp only [Fin.val_zero, h0, decide_eq_true_eq, hs]
    rw [← ih (fun i => f i.succ) (v / 2)]
    rfl

set_option maxRecDepth 100000 in
-- The literal letter columns are the proved Ninth projection columns.
private theorem letterCols_eq : ∀ g : Fin 6,
    ninthForestLetterCols g = List.ofFn (generatedNinthLowerSpinThreeProjectionColumns g) := by
  decide +kernel

/-- The fast evaluator computes exactly the proved mask action of every letter word. -/
theorem ninthForestWordApply_eq (w : List (Fin 6)) (v : ℕ) :
    ninthForestWordApply w v = generatedNinthLowerSpinThreeProjectionMaskWord w v := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    simp only [ninthForestWordApply, generatedNinthLowerSpinThreeProjectionMaskWord,
      List.foldr_cons] at ih ⊢
    rw [ih, generatedAxisGlobalQMaskVector, maskSum_ofFn_eq_applyCols, letterCols_eq]

/-- The row operations of every step compute the actual binary action of its word. -/
theorem ninthForestStage_action (s : ℕ) (hs : s < 5)
    (p : List (ℕ × ℕ) × List (Fin 6))
    (hp : p ∈ (ninthForestStageOps s).zip (ninthForestStageWords s)) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (tenthForestOpsMap p.1 b) =
      co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord p.2)
        (monsterCo1GeometryBinaryMaskDecode b) := by
  apply tenthForestOpsMap_decode_of_basis p.1
    (co1BinaryAction (generatedNinthLowerSpinThreeProjectionWord p.2)).toLinearMap
  intro j
  rw [ninthForestStage_basis_words s hs p hp j.val j.isLt, ninthForestWordApply_eq,
    LinearEquiv.coe_coe, generatedNinth_lower_spin_three_projection_word_action]

/-- The masks lying in the orbit of a Ninth forest root under a subgroup of `Co1`. -/
def NinthForestReached (G : Subgroup Co1) (b : ℕ) : Prop :=
  ∃ m ∈ ninthForestRoots, ∃ c ∈ G, co1BinaryAction c (monsterCo1GeometryBinaryMaskDecode m) =
    monsterCo1GeometryBinaryMaskDecode (n := 24) b

/-- One stage of doubling keeps every reached position inside the root orbits. -/
theorem ninthForestStage_reached (G : Subgroup Co1)
    (hG : ∀ g : Fin 6, generatedNinthLowerSpinThreeProjectionLetter g ∈ G)
    (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
    (hP : ∀ b, S.testBit b = true → NinthForestReached G b) :
    ∀ b, (tenthForestDoubles (ninthForestStageOps s) S).testBit b = true →
      NinthForestReached G b := by
  have hfst : ((ninthForestStageOps s).zip (ninthForestStageWords s)).map Prod.fst =
      ninthForestStageOps s :=
    List.map_fst_zip (le_of_eq (ninthForestStage_length s hs))
  have hword (w : List (Fin 6)) : generatedNinthLowerSpinThreeProjectionWord w ∈ G := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact hG g
  rw [← hfst]
  apply tenthForestDoubles_induction (NinthForestReached G)
  · rw [hfst]
    exact ninthForestStageOps_valid s
  · intro ops hops b _ hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hops
    obtain ⟨m, hm, c, hc, he⟩ := hb
    refine ⟨m, hm, (generatedNinthLowerSpinThreeProjectionWord p.2)⁻¹ * c,
      G.mul_mem (G.inv_mem (hword p.2)) hc, ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, he, ninthForestStage_action s hs p hp, map_inv,
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
theorem ninthForestNonsingular_of_singular (b : ℕ)
    (hs : generatedAxisGlobalMaskSingular b = true) :
    tenthForestNonsingular.testBit b = false := by
  rw [tenthForestNonsingular_testBit, quadParity_eq]
  have h := foldl_xor_ofFn (fun k => b.testBit k && b.testBit (k + 12)) 12
  simp only [generatedAxisGlobalMaskSingular, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  rw [← h, hs, Bool.and_false]

/-- Every singular binary mask lies in the orbit of a Ninth forest root, under every subgroup of
`Co1` containing the six Ninth letters. -/
theorem ninthForest_reached (G : Subgroup Co1)
    (hG : ∀ g : Fin 6, generatedNinthLowerSpinThreeProjectionLetter g ∈ G)
    (b : ℕ) (hb : b < 16777216) (hs : generatedAxisGlobalMaskSingular b = true) :
    NinthForestReached G b := by
  have h0 : ∀ b, ninthForestStart.testBit b = true → NinthForestReached G b := by
    intro b hb
    rw [ninthForestStart_testBit, decide_eq_true_eq] at hb
    exact ⟨b, hb, 1, G.one_mem, by rw [map_one, LinearEquiv.coe_one, id]⟩
  have hb0 := ninthForestStart_bounded
  have hval (s : ℕ) := ninthForestStageOps_valid s
  have hstage (s : ℕ) (hs : s < 5) (S : ℕ) (hS : TenthForestBounded S)
      (hP : ∀ b, S.testBit b = true → NinthForestReached G b) :
      TenthForestBounded (tenthForestDoubles (ninthForestStageOps s) S) ∧
        ∀ b, (tenthForestDoubles (ninthForestStageOps s) S).testBit b = true →
          NinthForestReached G b :=
    ⟨tenthForestDoubles_bounded _ (hval s) S hS, ninthForestStage_reached G hG s hs S hS hP⟩
  obtain ⟨hb1, h1⟩ := hstage 0 (by decide) _ hb0 h0
  rw [ninthForest_stage1] at hb1 h1
  obtain ⟨hb2, h2⟩ := hstage 1 (by decide) _ hb1 h1
  rw [ninthForest_stage2] at hb2 h2
  obtain ⟨hb3, h3⟩ := hstage 2 (by decide) _ hb2 h2
  rw [ninthForest_stage3] at hb3 h3
  obtain ⟨hb4, h4⟩ := hstage 3 (by decide) _ hb3 h3
  rw [ninthForest_stage4] at hb4 h4
  obtain ⟨_, h5⟩ := hstage 4 (by decide) _ hb4 h4
  apply h5
  have hall := congrArg (fun S => S.testBit b) ninthForest_stage5
  simp only [Nat.testBit_or, tenthForestAll_testBit, ninthForestNonsingular_of_singular b hs,
    Bool.false_or, decide_eq_true hb] at hall
  exact hall

/-- Every letter lies in the actual projected Ninth-axis stabilizer. -/
theorem generatedAxisGlobalTwelveNinthLetter_mem (g : Fin 6) :
    generatedNinthLowerSpinThreeProjectionLetter g ∈ generatedNinthProjectedAxisStabilizer := by
  have hc : ∀ i : Fin 3, generatedNinthLowerSpinActualGenerator
      (generatedNinthLowerSpinThreeCandidateIndex i) ∈ generatedNinthProjectedAxisStabilizer := by
    intro i
    exact ⟨⟨_, generatedNinth_lower_spin_three_whole_actual_membership i⟩,
      generatedNinth_lower_spin_direct_projection_eq_original _⟩
  unfold generatedNinthLowerSpinThreeProjectionLetter
  split_ifs
  · exact hc _
  · exact generatedNinthProjectedAxisStabilizer.inv_mem (hc _)

/-- The eight type-four forest root masks, Ω first. -/
def generatedAxisGlobalTwelveNinthRootMask : Fin 8 → ℕ :=
  ![2048, 1, 4, 177, 272, 50, 250, 77024]

/-- A forest root is a type-four root mask or lies outside the binary Ω orbit. -/
theorem generatedAxisGlobalTwelveNinthForestRoot_cases (m : ℕ) (hm : m ∈ ninthForestRoots) :
    (∃ j, generatedAxisGlobalTwelveNinthRootMask j = m) ∨
      monsterCo1GeometryBinaryMaskDecode (n := 24) m ∉ generatedAxisGlobalBinaryOrbit := by
  unfold ninthForestRoots ninthForestTypeFourRoots ninthForestOtherRoots at hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inl ⟨6, rfl⟩
    · exact Or.inl ⟨7, rfl⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr generatedAxisGlobalTwelveNinthZeroRoot_not_mem_orbit
    · exact Or.inr (generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit 0)
    · exact Or.inr (generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit 1)
    · exact Or.inr (generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit 2)
    · exact Or.inr (generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit 3)
    · exact Or.inr (generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit 4)

/-- Every genuine binary Ω point is reached from one of the eight type-four root masks by an
actual element fixing the whole Ninth axis. -/
theorem generatedAxisGlobalTwelveNinth_binary_cover_masks (x : generatedAxisGlobalBinaryOrbit) :
    ∃ j : Fin 8, ∃ c : H, c ∈ generatedNinthLocalAxisStabilizer ∧
      co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveNinthRootMask j)) = x.val := by
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := ninthForest_reached _ generatedAxisGlobalTwelveNinthLetter_mem
    b.val b.isLt hs
  obtain ⟨⟨h, hh⟩, rfl⟩ := hc
  have he' : co1BinaryAction (projH h) (monsterCo1GeometryBinaryMaskDecode m) = x.val := by
    rw [← hb]
    exact he
  rcases generatedAxisGlobalTwelveNinthForestRoot_cases m hm with ⟨j, hj⟩ | hn
  · exact ⟨j, h, hh, by rw [hj]; exact he'⟩
  · exfalso
    apply hn
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24) m =
        (generatedAxisGlobalBinaryAct h⁻¹ x).val := by
      change _ = co1BinaryAction (projH h⁻¹) x.val
      rw [← he', map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct h⁻¹ x).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
