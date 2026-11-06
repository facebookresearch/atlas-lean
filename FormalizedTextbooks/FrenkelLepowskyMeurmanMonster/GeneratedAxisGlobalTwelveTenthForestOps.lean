/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Bitset operations on the `2 ^ 24` binary mask positions.

A natural number `S` is read as the set of masks `b` with `S.testBit b`. The coordinate sets
`tenthForestBit i` (masks with bit `i`) are built by doubling a single period. A row operation
flips coordinate `j` of every mask on which the parity of `b &&& r` is odd; on sets it is computed
by masked shifts. Every step is an ordinary natural-number operation, and its exact set meaning is
proved here for every position. These operations certify binary forests by set doubling. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Replicate the pattern `u` of width `w`, `2 ^ k` times. -/
def tenthForestRep (u w : ℕ) : ℕ → ℕ
  | 0 => u
  | k + 1 => tenthForestRep u w k ||| (tenthForestRep u w k <<< (w * 2 ^ k))

theorem tenthForestRep_testBit (u w : ℕ) (hu : u < 2 ^ w) (k b : ℕ) :
    (tenthForestRep u w k).testBit b = (decide (b < w * 2 ^ k) && u.testBit (b % w)) := by
  induction k generalizing b with
  | zero =>
    simp only [tenthForestRep, pow_zero, mul_one]
    by_cases hb : b < w
    · simp [hb, Nat.mod_eq_of_lt hb]
    · have hle : 2 ^ w ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hb, Nat.testBit_lt_two_pow (lt_of_lt_of_le hu hle)]
  | succ k ih =>
    simp only [tenthForestRep, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    have hd : w * 2 ^ (k + 1) = w * 2 ^ k + w * 2 ^ k := by rw [pow_succ]; ring
    rw [hd]
    by_cases h1 : b < w * 2 ^ k
    · have h2 : ¬ b ≥ w * 2 ^ k := by omega
      simp [h1, h2, show b < w * 2 ^ k + w * 2 ^ k by omega]
    · have h2 : b ≥ w * 2 ^ k := by omega
      have hm : (b - w * 2 ^ k) % w = b % w := by
        conv_rhs => rw [show b = (b - w * 2 ^ k) + w * 2 ^ k by omega]
        rw [Nat.add_mul_mod_self_left]
      simp only [h1, decide_false, Bool.false_and, Bool.false_or, h2, decide_true,
        Bool.true_and, hm]
      by_cases h3 : b - w * 2 ^ k < w * 2 ^ k
      · simp [h3, show b < w * 2 ^ k + w * 2 ^ k by omega]
      · simp [h3, show ¬ b < w * 2 ^ k + w * 2 ^ k by omega]

/-- The positions whose mask has coordinate `i`, for the `2 ^ 24` masks. -/
def tenthForestBit (i : ℕ) : ℕ :=
  tenthForestRep ((2 ^ 2 ^ i - 1) <<< 2 ^ i) (2 ^ (i + 1)) (23 - i)

private theorem testBit_lt_two_pow_succ (c i : ℕ) (hc : c < 2 ^ (i + 1)) :
    c.testBit i = decide (2 ^ i ≤ c) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ i := by positivity
  have hc' : c < 2 ^ i * 2 := by rw [← pow_succ]; exact hc
  have hq : c / 2 ^ i < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    omega
  by_cases h : 2 ^ i ≤ c
  · have h1 : 1 ≤ c / 2 ^ i := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    have : c / 2 ^ i = 1 := by omega
    simp [this, h]
  · have : c / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem tenthForestBit_testBit (i : ℕ) (hi : i < 24) (b : ℕ) :
    (tenthForestBit i).testBit b = (decide (b < 16777216) && b.testBit i) := by
  have h0 : 0 < 2 ^ 2 ^ i := by positivity
  have hu : (2 ^ 2 ^ i - 1) <<< 2 ^ i < 2 ^ 2 ^ (i + 1) := by
    rw [Nat.shiftLeft_eq, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) h0
  have hw : 2 ^ (i + 1) * 2 ^ (23 - i) = 16777216 := by
    rw [← pow_add, show i + 1 + (23 - i) = 24 by omega]; norm_num
  rw [tenthForestBit, tenthForestRep_testBit _ _ hu, hw]
  by_cases hb : b < 16777216
  · simp only [hb, decide_true, Bool.true_and]
    have hc : b % 2 ^ (i + 1) < 2 ^ (i + 1) := Nat.mod_lt _ (by positivity)
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    have hbi : b.testBit i = (b % 2 ^ (i + 1)).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    rw [hbi, testBit_lt_two_pow_succ _ _ hc]
    have hc' : b % 2 ^ (i + 1) < 2 ^ i + 2 ^ i := by rw [pow_succ] at hc; omega
    by_cases h : 2 ^ i ≤ b % 2 ^ (i + 1)
    · have h' : b % 2 ^ (i + 1) - 2 ^ i < 2 ^ i := by omega
      simp [h, h']
    · simp [h]
  · simp only [decide_eq_false hb, Bool.false_and]

/-- The parity of the common coordinates of `r` and `b` below `n`. -/
def tenthForestParityUpTo (r b : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (r.testBit n && b.testBit n) (tenthForestParityUpTo r b n)

/-- The parity of the common coordinates of `r` and `b` among the 24 coordinates. -/
def tenthForestParity (r b : ℕ) : Bool := tenthForestParityUpTo r b 24

/-- The positions of odd parity against `r` among the first `n` coordinates. -/
def tenthForestParityMaskUpTo (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if r.testBit n then tenthForestBit n ^^^ tenthForestParityMaskUpTo r n
      else tenthForestParityMaskUpTo r n

/-- The positions of odd parity against `r`. -/
def tenthForestParityMask (r : ℕ) : ℕ := tenthForestParityMaskUpTo r 24

theorem tenthForestParityMaskUpTo_testBit (r n : ℕ) (hn : n ≤ 24) (b : ℕ) :
    (tenthForestParityMaskUpTo r n).testBit b =
      (decide (b < 16777216) && tenthForestParityUpTo r b n) := by
  induction n with
  | zero => simp [tenthForestParityMaskUpTo, tenthForestParityUpTo]
  | succ n ih =>
    have ih' := ih (by omega)
    by_cases hr : r.testBit n
    · simp only [tenthForestParityMaskUpTo, hr, ↓reduceIte, Nat.testBit_xor,
        tenthForestBit_testBit n (by omega), ih', tenthForestParityUpTo, Bool.true_and]
      cases decide (b < 16777216) <;> simp
    · simp only [tenthForestParityMaskUpTo, hr, Bool.false_eq_true, ↓reduceIte, ih',
        tenthForestParityUpTo, Bool.false_and, Bool.false_xor]

theorem tenthForestParityMask_testBit (r b : ℕ) :
    (tenthForestParityMask r).testBit b = (decide (b < 16777216) && tenthForestParity r b) :=
  tenthForestParityMaskUpTo_testBit r 24 le_rfl b

/-- Flip coordinate `j` of a mask exactly when its parity against `r` is odd. -/
def tenthForestRowMap (j r b : ℕ) : ℕ := if tenthForestParity r b then b ^^^ 2 ^ j else b

/-- The set image of a row operation, by masked shifts. -/
def tenthForestRowSet (j r S : ℕ) : ℕ :=
  let SP := S &&& tenthForestParityMask r
  let SQ := SP &&& tenthForestBit j
  let SR := SP ^^^ SQ
  ((S ^^^ SP) ||| (SR <<< 2 ^ j)) ||| (SQ >>> 2 ^ j)

private theorem add_two_pow_of_testBit_false (p j : ℕ) (h : p.testBit j = false) :
    p + 2 ^ j = p ^^^ 2 ^ j := by
  induction j generalizing p with
  | zero =>
    apply Nat.eq_of_testBit_eq
    intro i
    have hp : p % 2 = 0 := by
      have := Nat.testBit_zero p; rw [h] at this; simp at this; omega
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_two_pow]
      have : (p + 2 ^ 0) / 2 = p / 2 := by rw [pow_zero]; omega
      rw [this]
      simp
  | succ j ih =>
    apply Nat.eq_of_testBit_eq
    intro i
    have hq : (p / 2).testBit j = false := by rw [Nat.testBit_div_two]; exact h
    have hd : (p + 2 ^ (j + 1)) / 2 = p / 2 + 2 ^ j := by rw [pow_succ]; omega
    cases i with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_zero, Nat.testBit_zero]
      have : (p + 2 ^ (j + 1)) % 2 = p % 2 := by rw [pow_succ]; omega
      simp [this]
    | succ i =>
      rw [Nat.testBit_succ, hd, ih _ hq, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ,
        Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp


private theorem parityUpTo_xor_two_pow (r b j n : ℕ) (hr : r.testBit j = false) :
    tenthForestParityUpTo r (b ^^^ 2 ^ j) n = tenthForestParityUpTo r b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tenthForestParityUpTo, ih, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hn : j = n
    · subst hn; simp [hr]
    · simp [hn]

theorem tenthForestParity_xor_two_pow (r b j : ℕ) (hr : r.testBit j = false) :
    tenthForestParity r (b ^^^ 2 ^ j) = tenthForestParity r b :=
  parityUpTo_xor_two_pow r b j 24 hr

private theorem sub_two_pow_of_testBit_true (b j : ℕ) (h : b.testBit j = true) :
    b - 2 ^ j = b ^^^ 2 ^ j := by
  have hx : (b ^^^ 2 ^ j).testBit j = false := by simp [Nat.testBit_xor, h]
  have he := add_two_pow_of_testBit_false _ _ hx
  have hb : (b ^^^ 2 ^ j) ^^^ 2 ^ j = b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hb] at he
  omega

private theorem testBit_sub_two_pow_of_false (b j : ℕ) (h : b.testBit j = false)
    (hge : 2 ^ j ≤ b) : (b - 2 ^ j).testBit j = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  have he := add_two_pow_of_testBit_false _ _ hc
  rw [Nat.sub_add_cancel hge] at he
  have := congrArg (fun x => x.testBit j) he
  simp [Nat.testBit_xor, hc, h] at this

private theorem testBit_two_pow_add_of_true (b j : ℕ) (h : b.testBit j = true) :
    (2 ^ j + b).testBit j = false := by
  have hx : (b ^^^ 2 ^ j).testBit j = false := by simp [Nat.testBit_xor, h]
  have he := add_two_pow_of_testBit_false _ _ hx
  have hb : (b ^^^ 2 ^ j) ^^^ 2 ^ j = b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hb] at he
  have hs : 2 ^ j + b = 2 ^ (j + 1) + (b ^^^ 2 ^ j) := by rw [pow_succ]; omega
  rw [hs, Nat.testBit_two_pow_add_gt (by omega), hx]

private theorem xor_two_pow_lt (b j : ℕ) (hb : b < 16777216) (hj : j < 24) :
    b ^^^ 2 ^ j < 16777216 :=
  Nat.xor_lt_two_pow (n := 24) hb (Nat.pow_lt_pow_right (by omega) hj)

/-- A natural number whose set has only positions below `2 ^ 24`. -/
def TenthForestBounded (S : ℕ) : Prop := ∀ b, 16777216 ≤ b → S.testBit b = false

/-- Exact set meaning of one row operation, at every position. -/
theorem tenthForestRowSet_testBit (j r S : ℕ) (hj : j < 24) (hr : r.testBit j = false)
    (hS : TenthForestBounded S) (b : ℕ) :
    (tenthForestRowSet j r S).testBit b =
      (decide (b < 16777216) && S.testBit (tenthForestRowMap j r b)) := by
  have hSP (x : ℕ) : (S &&& tenthForestParityMask r).testBit x =
      (S.testBit x && (decide (x < 16777216) && tenthForestParity r x)) := by
    rw [Nat.testBit_and, tenthForestParityMask_testBit]
  have hX (x : ℕ) := tenthForestBit_testBit j hj x
  simp only [tenthForestRowSet, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and, hSP, hX, tenthForestRowMap]
  by_cases hb : b < 16777216
  · -- the shifted terms only meet the partner position
    by_cases hp : tenthForestParity r b
    · by_cases hbj : b.testBit j
      · have hge : 2 ^ j ≤ b := Nat.ge_two_pow_of_testBit hbj
        have hsub := sub_two_pow_of_testBit_true b j hbj
        have hpar := tenthForestParity_xor_two_pow r b j hr
        have hlt := xor_two_pow_lt b j hb hj
        have hxj : (b ^^^ 2 ^ j).testBit j = false := by
          simp [Nat.testBit_xor, hbj]
        have hadd := testBit_two_pow_add_of_true b j hbj
        simp [hb, hp, hge, hsub, hpar, hlt, hxj, hadd]
      · have hbj' : b.testBit j = false := by simpa using hbj
        have hadd : 2 ^ j + b = b ^^^ 2 ^ j := by
          rw [Nat.add_comm]; exact add_two_pow_of_testBit_false b j hbj'
        have hpar := tenthForestParity_xor_two_pow r b j hr
        have hlt := xor_two_pow_lt b j hb hj
        have hxj : (b ^^^ 2 ^ j).testBit j = true := by
          simp [Nat.testBit_xor, hbj']
        have hsub (hge : 2 ^ j ≤ b) := testBit_sub_two_pow_of_false b j hbj' hge
        by_cases hge : 2 ^ j ≤ b
        · have hnot : ¬ 16777216 ≤ b - 2 ^ j := by
            have := Nat.sub_le b (2 ^ j); omega
          simp [hb, hp, hadd, hpar, hlt, hxj, hsub hge, hge, hnot]
        · simp [hb, hp, hadd, hpar, hlt, hxj, hge]
    · have hp' : tenthForestParity r b = false := by simpa using hp
      -- neither shifted term contributes
      have h1 : (decide (b ≥ 2 ^ j) && ((S.testBit (b - 2 ^ j) &&
          (decide (b - 2 ^ j < 16777216) && tenthForestParity r (b - 2 ^ j))) ^^
          (S.testBit (b - 2 ^ j) && (decide (b - 2 ^ j < 16777216) &&
            tenthForestParity r (b - 2 ^ j)) &&
          (decide (b - 2 ^ j < 16777216) && (b - 2 ^ j).testBit j)))) = false := by
        by_cases hge : b ≥ 2 ^ j
        · by_cases hq : (b - 2 ^ j).testBit j
          · simp only [hq, Bool.and_true]
            cases S.testBit (b - 2 ^ j) <;> cases decide (b - 2 ^ j < 16777216) <;>
              cases tenthForestParity r (b - 2 ^ j) <;> simp
          · have hq' : (b - 2 ^ j).testBit j = false := by simpa using hq
            have he := add_two_pow_of_testBit_false _ _ hq'
            rw [Nat.sub_add_cancel hge] at he
            have hpar := tenthForestParity_xor_two_pow r (b - 2 ^ j) j hr
            rw [← he] at hpar
            have hq2 : tenthForestParity r (b - 2 ^ j) = false := hpar.symm.trans hp'
            simp [hq', hq2]
        · simp [hge]
      have h2 : (S.testBit (2 ^ j + b) && (decide (2 ^ j + b < 16777216) &&
          tenthForestParity r (2 ^ j + b)) &&
          (decide (2 ^ j + b < 16777216) && (2 ^ j + b).testBit j)) = false := by
        by_cases hbj : b.testBit j
        · simp [testBit_two_pow_add_of_true b j hbj]
        · have hbj' : b.testBit j = false := by simpa using hbj
          have hadd : 2 ^ j + b = b ^^^ 2 ^ j := by
            rw [Nat.add_comm]; exact add_two_pow_of_testBit_false b j hbj'
          rw [hadd, tenthForestParity_xor_two_pow r b j hr, hp']
          simp
      rw [h1, h2]
      simp [hb, hp']
  · have hSb : S.testBit b = false := hS b (by omega)
    have h1 : (decide (b ≥ 2 ^ j) && ((S.testBit (b - 2 ^ j) &&
        (decide (b - 2 ^ j < 16777216) && tenthForestParity r (b - 2 ^ j))) ^^
        (S.testBit (b - 2 ^ j) && (decide (b - 2 ^ j < 16777216) &&
          tenthForestParity r (b - 2 ^ j)) &&
        (decide (b - 2 ^ j < 16777216) && (b - 2 ^ j).testBit j)))) = false := by
      by_cases hge : b ≥ 2 ^ j
      · by_cases hlt : b - 2 ^ j < 16777216
        · by_cases hq : (b - 2 ^ j).testBit j
          · simp only [hq, Bool.and_true]
            cases S.testBit (b - 2 ^ j) <;> cases decide (b - 2 ^ j < 16777216) <;>
              cases tenthForestParity r (b - 2 ^ j) <;> simp
          · have hq' : (b - 2 ^ j).testBit j = false := by simpa using hq
            have he := add_two_pow_of_testBit_false _ _ hq'
            rw [Nat.sub_add_cancel hge] at he
            have := xor_two_pow_lt (b - 2 ^ j) j hlt hj
            rw [← he] at this
            exact absurd this hb
        · simp [hlt]
      · simp [hge]
    have h2 : decide (2 ^ j + b < 16777216) = false := by
      simp only [decide_eq_false_iff_not, not_lt]
      exact Nat.le_trans (by omega) (Nat.le_add_left b (2 ^ j))
    rw [h1]
    simp [hb, hSb, h2]

theorem tenthForestRowSet_bounded (j r S : ℕ) (hj : j < 24) (hr : r.testBit j = false)
    (hS : TenthForestBounded S) : TenthForestBounded (tenthForestRowSet j r S) := by
  intro b hb
  rw [tenthForestRowSet_testBit j r S hj hr hS]
  simp [show ¬ b < 16777216 by omega]

/-- A row operation is valid when its target coordinate is a coordinate absent from `r`. -/
def TenthForestRowValid (o : ℕ × ℕ) : Prop := o.1 < 24 ∧ o.2.testBit o.1 = false

/-- The composite position map of a list of row operations (the last one acts first). -/
def tenthForestOpsMap (ops : List (ℕ × ℕ)) (b : ℕ) : ℕ :=
  ops.foldr (fun o x => tenthForestRowMap o.1 o.2 x) b

/-- The set image of a list of row operations (the first one is computed first). -/
def tenthForestOpsSet (ops : List (ℕ × ℕ)) (S : ℕ) : ℕ :=
  ops.foldl (fun T o => tenthForestRowSet o.1 o.2 T) S

theorem tenthForestOpsMap_lt (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, TenthForestRowValid o)
    (b : ℕ) (hb : b < 16777216) : tenthForestOpsMap ops b < 16777216 := by
  induction ops with
  | nil => simpa [tenthForestOpsMap] using hb
  | cons o ops ih =>
    have ho := hops o (by simp)
    have h' := ih (fun o' h => hops o' (by simp [h]))
    simp only [tenthForestOpsMap, List.foldr_cons, tenthForestRowMap] at h' ⊢
    split_ifs
    · exact xor_two_pow_lt _ _ h' ho.1
    · exact h'

theorem tenthForestOpsSet_testBit (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, TenthForestRowValid o)
    (S : ℕ) (hS : TenthForestBounded S) (b : ℕ) :
    (tenthForestOpsSet ops S).testBit b =
      (decide (b < 16777216) && S.testBit (tenthForestOpsMap ops b)) ∧
    TenthForestBounded (tenthForestOpsSet ops S) := by
  induction ops generalizing S b with
  | nil =>
    refine ⟨?_, hS⟩
    simp only [tenthForestOpsSet, List.foldl_nil, tenthForestOpsMap, List.foldr_nil]
    by_cases hb : b < 16777216
    · simp [hb]
    · simp [hb, hS b (by omega)]
  | cons o ops ih =>
    have ho := hops o (by simp)
    have hrest : ∀ o' ∈ ops, TenthForestRowValid o' := fun o' h => hops o' (by simp [h])
    have hS' := tenthForestRowSet_bounded o.1 o.2 S ho.1 ho.2 hS
    have hih := ih hrest (tenthForestRowSet o.1 o.2 S) hS'
    refine ⟨?_, (hih 0).2⟩
    simp only [tenthForestOpsSet, List.foldl_cons] at hih ⊢
    rw [(hih b).1, tenthForestRowSet_testBit o.1 o.2 S ho.1 ho.2 hS]
    simp only [tenthForestOpsMap, List.foldr_cons]
    by_cases hb : b < 16777216
    · have hlt : ops.foldr (fun o x => tenthForestRowMap o.1 o.2 x) b < 16777216 :=
        tenthForestOpsMap_lt ops hrest b hb
      simp [hb, hlt]
    · simp [hb]

/-- One doubling step: add every position whose image under the row operations is present. -/
def tenthForestDouble (ops : List (ℕ × ℕ)) (S : ℕ) : ℕ := S ||| tenthForestOpsSet ops S

theorem tenthForestDouble_testBit (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, TenthForestRowValid o)
    (S : ℕ) (hS : TenthForestBounded S) (b : ℕ) :
    (tenthForestDouble ops S).testBit b = true →
      S.testBit b = true ∨ (b < 16777216 ∧ S.testBit (tenthForestOpsMap ops b) = true) := by
  intro h
  rw [tenthForestDouble, Nat.testBit_or, (tenthForestOpsSet_testBit ops hops S hS b).1] at h
  by_cases hb : S.testBit b
  · exact Or.inl hb
  · right
    simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

theorem tenthForestDouble_bounded (ops : List (ℕ × ℕ)) (hops : ∀ o ∈ ops, TenthForestRowValid o)
    (S : ℕ) (hS : TenthForestBounded S) : TenthForestBounded (tenthForestDouble ops S) := by
  intro b hb
  rw [tenthForestDouble, Nat.testBit_or, hS b hb,
    (tenthForestOpsSet_testBit ops hops S hS 0).2 b hb]
  rfl

/-- The parity of the hyperbolic quadratic form on the first `n` coordinate pairs. -/
def tenthForestQuadParityUpTo (b : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (b.testBit n && b.testBit (n + 12)) (tenthForestQuadParityUpTo b n)

/-- The positions of odd quadratic parity on the first `n` coordinate pairs. -/
def tenthForestQuadMaskUpTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (tenthForestBit n &&& tenthForestBit (n + 12)) ^^^ tenthForestQuadMaskUpTo n

/-- The nonsingular positions: odd value of the hyperbolic quadratic form. -/
def tenthForestNonsingular : ℕ := tenthForestQuadMaskUpTo 12

/-- All `2 ^ 24` positions. -/
def tenthForestAll : ℕ := 2 ^ 16777216 - 1

theorem tenthForestQuadMaskUpTo_testBit (n : ℕ) (hn : n ≤ 12) (b : ℕ) :
    (tenthForestQuadMaskUpTo n).testBit b =
      (decide (b < 16777216) && tenthForestQuadParityUpTo b n) := by
  induction n with
  | zero => simp [tenthForestQuadMaskUpTo, tenthForestQuadParityUpTo]
  | succ n ih =>
    simp only [tenthForestQuadMaskUpTo, tenthForestQuadParityUpTo, Nat.testBit_xor,
      Nat.testBit_and, tenthForestBit_testBit n (by omega),
      tenthForestBit_testBit (n + 12) (by omega), ih (by omega)]
    cases decide (b < 16777216) <;> simp

theorem tenthForestNonsingular_testBit (b : ℕ) :
    tenthForestNonsingular.testBit b = (decide (b < 16777216) && tenthForestQuadParityUpTo b 12) :=
  tenthForestQuadMaskUpTo_testBit 12 le_rfl b

theorem tenthForestAll_testBit (b : ℕ) : tenthForestAll.testBit b = decide (b < 16777216) := by
  rw [tenthForestAll, Nat.testBit_two_pow_sub_one]

/-- Successive doubling steps, one row-operation list per step. -/
def tenthForestDoubles (opss : List (List (ℕ × ℕ))) (S : ℕ) : ℕ :=
  opss.foldl (fun T ops => tenthForestDouble ops T) S

/-- Join two blocks: the second block starts at position `16384 * 2 ^ k`. -/
def tenthForestJoin (k a b : ℕ) : ℕ := a ||| (b <<< (16384 * 2 ^ k))

/-- The positions of a finite list of masks. -/
def tenthForestOfList (l : List ℕ) : ℕ := l.foldl (fun S m => S ||| (1 <<< m)) 0

private theorem ofList_aux (l : List ℕ) (S b : ℕ) :
    (l.foldl (fun S m => S ||| (1 <<< m)) S).testBit b = (S.testBit b || decide (b ∈ l)) := by
  induction l generalizing S with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases h : b = m
    · subst h; simp
    · have : ¬ (b ≥ m ∧ b - m = 0) := by omega
      simp only [List.mem_cons, h, false_or]
      cases hb : (1 : ℕ).testBit (b - m) with
      | false => simp
      | true =>
        have : b - m = 0 := by
          by_contra hne
          have := Nat.testBit_lt_two_pow (x := 1) (i := b - m)
            (by calc 1 < 2 := by norm_num
                _ = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (b - m) := Nat.pow_le_pow_right (by norm_num) (by omega))
          rw [hb] at this; exact absurd this (by simp)
        by_cases hge : b ≥ m
        · omega
        · simp [hge]

theorem tenthForestOfList_testBit (l : List ℕ) (b : ℕ) :
    (tenthForestOfList l).testBit b = decide (b ∈ l) := by
  rw [tenthForestOfList, ofList_aux]; simp

theorem tenthForestDoubles_bounded (opss : List (List (ℕ × ℕ)))
    (hops : ∀ ops ∈ opss, ∀ o ∈ ops, TenthForestRowValid o) (S : ℕ)
    (hS : TenthForestBounded S) : TenthForestBounded (tenthForestDoubles opss S) := by
  induction opss generalizing S with
  | nil => simpa [tenthForestDoubles] using hS
  | cons ops opss ih =>
    simp only [tenthForestDoubles, List.foldl_cons]
    exact ih (fun o h => hops o (by simp [h])) _
      (tenthForestDouble_bounded ops (hops ops (by simp)) S hS)

/-- Every position of `S` reachable through `opss` traces back to a position of the start. -/
theorem tenthForestDoubles_induction (P : ℕ → Prop) (opss : List (List (ℕ × ℕ)))
    (hops : ∀ ops ∈ opss, ∀ o ∈ ops, TenthForestRowValid o)
    (hstep : ∀ ops ∈ opss, ∀ b, b < 16777216 → P (tenthForestOpsMap ops b) → P b)
    (S : ℕ) (hS : TenthForestBounded S) (hP : ∀ b, S.testBit b = true → P b) :
    ∀ b, (tenthForestDoubles opss S).testBit b = true → P b := by
  induction opss generalizing S with
  | nil => simpa [tenthForestDoubles] using hP
  | cons ops opss ih =>
    simp only [tenthForestDoubles, List.foldl_cons]
    have hv := hops ops (by simp)
    apply ih (fun o h => hops o (by simp [h])) (fun o h => hstep o (by simp [h])) _
      (tenthForestDouble_bounded ops hv S hS)
    intro b hb
    rcases tenthForestDouble_testBit ops hv S hS b hb with h | ⟨hlt, h⟩
    · exact hP b h
    · exact hstep ops (by simp) b hlt (hP _ h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
