/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthFastParent
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFastParity

/-! Finite descent obligations for the Twelfth binary singular forest and their sound
Boolean evaluation.

The obligation at a singular mask is that it is a listed root or has a strictly smaller proposed
rank after one actual parent operator. The Boolean evaluator reads the proposed edge and rank of
a mask from the code leaf of its 4096-mask block and evaluates the parent operator by its checked
byte tables; soundness lemmas transport `true` results back to the obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The descent obligation at one coordinate mask. -/
def generatedAxisGlobalTwelveTwelfthForestStep (b : ℕ) : Prop :=
  generatedAxisGlobalMaskSingular b = true →
    b ∈ generatedAxisGlobalTwelveTwelfthForestRootMasks ∨
      ∃ e : Fin 6, generatedAxisGlobalTwelveTwelfthRank
        (generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthParentColumns e) b) <
          generatedAxisGlobalTwelveTwelfthRank b

/-- Even parity of a twelve-bit mask, by folding its halves and one 64-bit table read. -/
def generatedAxisGlobalTwelveTwelfthParity (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight 7608434000728254870
    (Nat.land (Nat.xor x (Nat.shiftRight x 6)) 63)) 1) 0

set_option maxHeartbeats 4000000 in
-- Check all 4096 twelve-bit inputs.
/-- The folded parity agrees with the direct twelve-bit parity. -/
theorem generatedAxisGlobalTwelveTwelfthParity_certificate : ∀ x : Fin 4096,
    generatedAxisGlobalTwelveTwelfthParity x.val = generatedAxisGlobalParityTwelve x.val := by
  have h : ∀ a : Fin 16, ∀ c : Fin 256,
      generatedAxisGlobalTwelveTwelfthParity (256 * a.val + c.val) =
        generatedAxisGlobalParityTwelve (256 * a.val + c.val) := by
    decide +kernel
  intro x
  have hx : x.val / 256 < 16 := by have := x.isLt; omega
  have hh := h ⟨x.val / 256, hx⟩ ⟨x.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : 256 * (x.val / 256) + x.val % 256 = x.val := by omega
  simpa only [he] using hh

/-- Singularity of a coordinate mask by raw arithmetic. -/
def generatedAxisGlobalTwelveTwelfthSingular (b : ℕ) : Bool :=
  generatedAxisGlobalTwelveTwelfthParity (Nat.land (Nat.land b (Nat.shiftRight b 12)) 4095)

/-- The raw singularity test is the genuine quadratic-form test. -/
theorem generatedAxisGlobalTwelveTwelfthSingular_eq (b : ℕ) :
    generatedAxisGlobalTwelveTwelfthSingular b = generatedAxisGlobalMaskSingular b := by
  rw [generatedAxisGlobalMaskSingular_parity, generatedAxisGlobalParityTwelve_mod]
  have h : Nat.land (Nat.land b (Nat.shiftRight b 12)) 4095 = (b &&& (b >>> 12)) % 4096 := by
    change (b &&& (b >>> 12)) &&& (2 ^ 12 - 1) = (b &&& (b >>> 12)) % 2 ^ 12
    exact Nat.and_two_pow_sub_one_eq_mod _ 12
  unfold generatedAxisGlobalTwelveTwelfthSingular
  rw [h]
  exact generatedAxisGlobalTwelveTwelfthParity_certificate
    ⟨(b &&& (b >>> 12)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- The code byte of entry `i` of a block leaf. -/
def generatedAxisGlobalTwelveTwelfthCodeAt (leaf i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight leaf (Nat.mul 8 i)) 255

/-- Boolean evaluation of the obligation at entry `i` of the block starting at `base`. -/
def generatedAxisGlobalTwelveTwelfthStepB (leaf base i : ℕ) : Bool :=
  Bool.rec true
    (Bool.rec
      (List.elem (Nat.add base i) generatedAxisGlobalTwelveTwelfthForestRootMasks)
      (Nat.blt
        (generatedAxisGlobalTwelveTwelfthRank
          (generatedAxisGlobalTwelveTwelfthFastParent
            (Nat.shiftRight (generatedAxisGlobalTwelveTwelfthCodeAt leaf i) 4)
            (Nat.add base i)))
        (Nat.land (generatedAxisGlobalTwelveTwelfthCodeAt leaf i) 15))
      (Nat.blt (Nat.shiftRight (generatedAxisGlobalTwelveTwelfthCodeAt leaf i) 4) 6))
    (generatedAxisGlobalTwelveTwelfthSingular (Nat.add base i))

/-- Boolean evaluation of all entries `i0 + i`, `i < 2 ^ d`, of one block. -/
def generatedAxisGlobalTwelveTwelfthLoopB (leaf base : ℕ) : ℕ → ℕ → Bool :=
  fun d => Nat.rec (motive := fun _ => ℕ → Bool)
    (fun i => generatedAxisGlobalTwelveTwelfthStepB leaf base i)
    (fun d ih i => Bool.and (ih i) (ih (Nat.add i (Nat.pow 2 d)))) d

/-- The proposed code of a mask is the corresponding entry of its block leaf. -/
theorem generatedAxisGlobalTwelveTwelfthCode_block (j i : ℕ) (hi : i < 4096) :
    generatedAxisGlobalTwelveTwelfthCode (4096 * j + i) =
      generatedAxisGlobalTwelveTwelfthCodeAt
        (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree j) i := by
  have h1 : Nat.shiftRight (4096 * j + i) 12 = j := by
    change (4096 * j + i) >>> 12 = j
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : Nat.land (4096 * j + i) 4095 = i := by
    change (4096 * j + i) &&& (2 ^ 12 - 1) = i
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  unfold generatedAxisGlobalTwelveTwelfthCode generatedAxisGlobalTwelveTwelfthCodeAt
  rw [h1, h2]

/-- A `true` Boolean entry proves the descent obligation at its mask. -/
theorem generatedAxisGlobalTwelveTwelfthStepB_sound (j i : ℕ) (hj : j < 4096) (hi : i < 4096)
    (h : generatedAxisGlobalTwelveTwelfthStepB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree j)
      (4096 * j) i = true) :
    generatedAxisGlobalTwelveTwelfthForestStep (4096 * j + i) := by
  intro hs
  have hb : 4096 * j + i < 2 ^ 24 := by omega
  have hrank : generatedAxisGlobalTwelveTwelfthRank (4096 * j + i) =
      Nat.land (generatedAxisGlobalTwelveTwelfthCodeAt
        (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree j) i)
        15 := by
    unfold generatedAxisGlobalTwelveTwelfthRank
    rw [generatedAxisGlobalTwelveTwelfthCode_block j i hi]
  unfold generatedAxisGlobalTwelveTwelfthStepB at h
  have hf : generatedAxisGlobalTwelveTwelfthSingular (Nat.add (4096 * j) i) = true := by
    change generatedAxisGlobalTwelveTwelfthSingular (4096 * j + i) = true
    rw [generatedAxisGlobalTwelveTwelfthSingular_eq]
    exact hs
  rw [hf] at h
  cases he : Nat.blt (Nat.shiftRight (generatedAxisGlobalTwelveTwelfthCodeAt
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree j) i) 4) 6
  · rw [he] at h
    left
    have hm : List.elem (4096 * j + i) generatedAxisGlobalTwelveTwelfthForestRootMasks = true := h
    exact List.elem_iff.mp hm
  · rw [he] at h
    right
    have he6 := Nat.le_of_ble_eq_true he
    refine ⟨⟨_, he6⟩, ?_⟩
    have hlt := Nat.le_of_ble_eq_true h
    rw [hrank, ← generatedAxisGlobalTwelveTwelfthFastParent_eq _ _ hb]
    exact hlt

/-- A `true` block loop proves every Boolean entry it covers. -/
theorem generatedAxisGlobalTwelveTwelfthLoopB_sound (leaf base : ℕ) :
    ∀ d i0, generatedAxisGlobalTwelveTwelfthLoopB leaf base d i0 = true →
      ∀ i < 2 ^ d, generatedAxisGlobalTwelveTwelfthStepB leaf base (i0 + i) = true := by
  intro d
  induction d with
  | zero =>
    intro i0 h i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact h
  | succ d ih =>
    intro i0 h i hi
    have h' : (generatedAxisGlobalTwelveTwelfthLoopB leaf base d i0 &&
        generatedAxisGlobalTwelveTwelfthLoopB leaf base d (i0 + 2 ^ d)) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hl : i < 2 ^ d
    · exact ih i0 h'.1 i hl
    · have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      have := ih (i0 + 2 ^ d) h'.2 (i - 2 ^ d) (by omega)
      rw [show i0 + 2 ^ d + (i - 2 ^ d) = i0 + i by omega] at this
      exact this

/-- A `true` block loop proves the descent obligations at all 4096 masks of its block. -/
theorem generatedAxisGlobalTwelveTwelfthBlock_sound (j : ℕ) (hj : j < 4096)
    (h : generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree j)
      (4096 * j) 12 0 = true) (i : ℕ) (hi : i < 4096) :
    generatedAxisGlobalTwelveTwelfthForestStep (4096 * j + i) := by
  have hs := generatedAxisGlobalTwelveTwelfthLoopB_sound _ _ 12 0 h i (by omega)
  rw [Nat.zero_add] at hs
  exact generatedAxisGlobalTwelveTwelfthStepB_sound j i hj hi hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
