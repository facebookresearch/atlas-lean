/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestTables
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestRankData

/-! Local finite descent obligations for the actual Fourth-family binary forest, a Boolean
evaluation of one obligation with explicit natural-number operations, and a binary-split
Boolean loop over a block of masks, with soundness. The inverse operators are bound to genuine
local stabilizer data; the root masks are bound to genuine roots separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact twenty-seven roots of the singular forest in genuine coordinate masks. -/
def generatedAxisGlobalTwelveFourthForestRootMasks : List ℕ :=
  [0, 3, 6, 7, 14, 16, 48, 92, 4110, 14399, 4390912, 5229564, 4245504, 5227504, 5224440, 5983236,
    7980904, 4255804, 6344796, 2285660, 5239792, 788531, 2048, 528384, 8324080, 8187955, 2652160]

/-- One local arithmetic obligation: a singular mask is a listed root (edge code seven) or has
an actual inverse-generator parent of strictly smaller proposed natural rank. -/
def generatedAxisGlobalTwelveFourthForestStep (edge b : ℕ) : Prop :=
  generatedAxisGlobalMaskSingular b = true →
    (edge = 7 ∧ b ∈ generatedAxisGlobalTwelveFourthForestRootMasks) ∨
    (edge < 5 ∧ generatedAxisGlobalTwelveFourthForestRank
      (generatedAxisGlobalMaskRowsAction
        (generatedAxisGlobalTwelveFourthInverseRows ⟨edge % 5, Nat.mod_lt _ (by decide)⟩) b) <
          generatedAxisGlobalTwelveFourthForestRank b)

/-- Boolean evaluation of one obligation with explicit operations. -/
def generatedAxisGlobalTwelveFourthStepBool (edge b : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.or (Bool.and (Nat.beq edge 7) (generatedAxisGlobalTwelveFourthForestRootMasks.contains b))
      (Bool.and (Nat.blt edge 5)
        (Nat.blt
          (generatedAxisGlobalTwelveFourthForestRank
            (generatedAxisGlobalTwelveFourthFastInverse edge b))
          (generatedAxisGlobalTwelveFourthForestRank b))))
    (generatedAxisGlobalTwelveFourthSingular b)

/-- A true Boolean evaluation proves the actual descending-edge obligation. -/
theorem generatedAxisGlobalTwelveFourthStepBool_sound (edge b : ℕ) (hb : b < 2 ^ 24)
    (h : generatedAxisGlobalTwelveFourthStepBool edge b = true) :
    generatedAxisGlobalTwelveFourthForestStep edge b := by
  intro hs
  have hf : generatedAxisGlobalTwelveFourthSingular b = true := by
    rw [generatedAxisGlobalTwelveFourthSingular_eq]
    exact hs
  rw [generatedAxisGlobalTwelveFourthStepBool, hf] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, List.contains_iff_mem,
    Nat.blt_eq] at h
  rcases h with ⟨h7, hr⟩ | ⟨h5, hlt⟩
  · exact Or.inl ⟨h7, hr⟩
  · refine Or.inr ⟨h5, ?_⟩
    have he : (⟨edge % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨edge, h5⟩ :=
      Fin.ext (Nat.mod_eq_of_lt h5)
    rw [he, ← generatedAxisGlobalTwelveFourthFastInverse_eq ⟨edge, h5⟩ b hb]
    exact hlt

/-- The three-bit edge code of offset `i` in a block. -/
def generatedAxisGlobalTwelveFourthEdgeAt (edges i : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight edges (Nat.mul 3 i)) 8

/-- Binary-split Boolean loop over the offsets `lo, ..., lo + 2 ^ d - 1` of a block. -/
def generatedAxisGlobalTwelveFourthBlockCheck (edges start d : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool)
    (fun lo => generatedAxisGlobalTwelveFourthStepBool
      (generatedAxisGlobalTwelveFourthEdgeAt edges lo) (Nat.add start lo))
    (fun d rec lo => Bool.and (rec lo) (rec (Nat.add lo (Nat.shiftLeft 1 d)))) d

/-- A true loop proves every obligation of its offsets. -/
theorem generatedAxisGlobalTwelveFourthBlockCheck_sound (edges start : ℕ) :
    ∀ d lo : ℕ, start + lo + 2 ^ d ≤ 2 ^ 24 →
      generatedAxisGlobalTwelveFourthBlockCheck edges start d lo = true →
      ∀ i < 2 ^ d, generatedAxisGlobalTwelveFourthForestStep
        (generatedAxisGlobalTwelveFourthEdgeAt edges (lo + i)) (start + (lo + i)) := by
  intro d
  induction d with
  | zero =>
    intro lo hb h i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact generatedAxisGlobalTwelveFourthStepBool_sound _ _ (by omega) h
  | succ d ih =>
    intro lo hb h i hi
    have h' : Bool.and (generatedAxisGlobalTwelveFourthBlockCheck edges start d lo)
        (generatedAxisGlobalTwelveFourthBlockCheck edges start d (lo + 2 ^ d)) = true := by
      have hs : Nat.shiftLeft 1 d = 2 ^ d := Nat.one_shiftLeft d
      change Bool.and (generatedAxisGlobalTwelveFourthBlockCheck edges start d lo)
        (generatedAxisGlobalTwelveFourthBlockCheck edges start d
          (Nat.add lo (Nat.shiftLeft 1 d))) = true at h
      rw [hs] at h
      exact h
    rw [Bool.and_eq_true] at h'
    have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    by_cases hlt : i < 2 ^ d
    · exact ih lo (by omega) h'.1 i hlt
    · have hk := ih (lo + 2 ^ d) (by omega) h'.2 (i - 2 ^ d) (by omega)
      have he : lo + 2 ^ d + (i - 2 ^ d) = lo + i := by omega
      rw [he] at hk
      exact hk

/-- A checked block proves an obligation for every offset of the block. -/
theorem generatedAxisGlobalTwelveFourthBlockSteps_of_check (edges start : ℕ)
    (hs : start + 4096 ≤ 2 ^ 24)
    (h : generatedAxisGlobalTwelveFourthBlockCheck edges start 12 0 = true) (i : Fin 4096) :
    ∃ e : ℕ, generatedAxisGlobalTwelveFourthForestStep e (start + i.val) := by
  have hk := generatedAxisGlobalTwelveFourthBlockCheck_sound edges start 12 0 (by simpa using hs) h
    i.val (by simp)
  simp only [Nat.zero_add] at hk
  exact ⟨_, hk⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
