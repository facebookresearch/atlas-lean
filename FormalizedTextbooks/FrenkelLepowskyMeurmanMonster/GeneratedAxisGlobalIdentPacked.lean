/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

/-! # Packed signed vectors for fast kernel evaluation

Generic infrastructure for the cheap whole-vector identification method (worker `gident`).
A natural number is read as a sequence of fields of fixed width `w`; field `i` of `P` is
`P / 2^(w*i) % 2^w`.  A *signed packed vector* is a pair `(p, m)` whose field-wise difference
gives integer coordinates.  The operations below (addition, scaling, masking, translations and
transvections of field indices, sign flips) are evaluated by a handful of big-number operations
in the kernel, and each comes with an exact field-wise specification under explicit bounds.
No numerical certificate enters this module. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent



/-- Field `i` of width `w` in a packed natural number. -/
def fld (w P i : ℕ) : ℕ := P / 2 ^ (w * i) % 2 ^ w

/-- Bits of a field are the corresponding bits of the packed number. -/
theorem testBit_fld (w P i b : ℕ) :
    (fld w P i).testBit b = (decide (b < w) && P.testBit (w * i + b)) := by
  unfold fld
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  congr 1
  rw [Nat.add_comm]

/-- Every field is below `2^w`. -/
theorem fld_lt (w P i : ℕ) : fld w P i < 2 ^ w := Nat.mod_lt _ (by positivity)

/-- Fields of a bitwise conjunction. -/
theorem fld_land (w P M i : ℕ) : fld w (P &&& M) i = fld w P i &&& fld w M i := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [testBit_fld, Nat.testBit_and]
  cases decide (b < w) <;> simp

/-- Fields of a bitwise disjunction. -/
theorem fld_lor (w P M i : ℕ) : fld w (P ||| M) i = fld w P i ||| fld w M i := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [testBit_fld, Nat.testBit_or]
  cases decide (b < w) <;> simp

/-- Fields of a bitwise exclusive or. -/
theorem fld_xor (w P M i : ℕ) : fld w (P ^^^ M) i = fld w P i ^^^ fld w M i := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [testBit_fld, Nat.testBit_xor]
  cases decide (b < w) <;> simp

/-- A right shift by whole fields moves field indices down. -/
theorem fld_shiftRight (w P k i : ℕ) : fld w (P >>> (w * k)) i = fld w P (i + k) := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [testBit_fld, Nat.testBit_shiftRight]
  congr 2
  ring

/-- A left shift by whole fields moves field indices up and clears the low fields. -/
theorem fld_shiftLeft (w P k i : ℕ) :
    fld w (P <<< (w * k)) i = if k ≤ i then fld w P (i - k) else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < w
  · split_ifs with hk
    · simp only [testBit_fld, Nat.testBit_shiftLeft, hb, decide_true, Bool.true_and]
      have h1 : w * k ≤ w * i + b := le_trans (Nat.mul_le_mul_left w hk) (Nat.le_add_right _ _)
      simp only [h1, decide_true, Bool.true_and]
      congr 1
      rw [Nat.mul_sub]
      have : w * k ≤ w * i := Nat.mul_le_mul_left w hk
      omega
    · simp only [testBit_fld, Nat.testBit_shiftLeft, hb, decide_true, Bool.true_and,
        Nat.zero_testBit]
      have h1 : ¬ (w * k ≤ w * i + b) := by
        intro h
        have : w * i + b < w * (i + 1) := by rw [Nat.mul_succ]; omega
        have : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left w (by omega)
        omega
      simp [h1]
  · split_ifs <;> simp [testBit_fld, hb]

/-- Fields of a single full field at position zero. -/
theorem fld_two_pow_sub_one (w i : ℕ) : fld w (2 ^ w - 1) i = if i = 0 then 2 ^ w - 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, Nat.testBit_two_pow_sub_one]
  split_ifs with h
  · subst h; rw [Nat.testBit_two_pow_sub_one]; simp
  · simp only [Nat.zero_testBit]
    by_cases hb : b < w
    · have : ¬ (w * i + b < w) := by
        have : w ≤ w * i := Nat.le_mul_of_pos_right w (by omega)
        omega
      simp [this]
    · simp [hb]

/-- The all-ones mask of `n` fields. -/
def allMask (w n : ℕ) : ℕ := 2 ^ (w * n) - 1

/-- Fields of the all-ones mask. -/
theorem fld_allMask (w n i : ℕ) : fld w (allMask w n) i = if i < n then 2 ^ w - 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, allMask, Nat.testBit_two_pow_sub_one]
  split_ifs with h
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases hb : b < w
    · have : w * i + b < w * n := by
        have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w h
        rw [Nat.mul_succ] at this; omega
      simp [hb, this]
    · simp [hb]
  · simp only [Nat.zero_testBit]
    by_cases hb : b < w
    · have : ¬ (w * i + b < w * n) := by
        have : w * n ≤ w * i := Nat.mul_le_mul_left w (by omega)
        omega
      simp [hb, this]
    · simp [hb]

/-- Fields below a bound determine the number. -/
theorem lt_of_fld (w n P : ℕ) (hw : 0 < w) (h : ∀ i, n ≤ i → fld w P i = 0) : P < 2 ^ (w * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  have hi := h (b / w) (by
    by_contra hc
    push Not at hc
    have : w * (b / w + 1) ≤ w * n := Nat.mul_le_mul_left w hc
    have : b < w * (b / w + 1) := by
      rw [Nat.mul_succ]
      have := Nat.lt_div_mul_add (a := b) hw
      rw [Nat.mul_comm] at this
      omega
    omega)
  have := congrArg (fun x => x.testBit (b % w)) hi
  simp only [testBit_fld, Nat.zero_testBit, Nat.mod_lt _ hw, decide_true, Bool.true_and] at this
  rwa [Nat.div_add_mod] at this


/-- Field zero is the residue modulo `2^w`. -/
theorem fld_zero_right (w P : ℕ) : fld w P 0 = P % 2 ^ w := by
  simp [fld]

/-- Field `i+1` is field `i` after dividing by `2^w`. -/
theorem fld_succ (w P i : ℕ) : fld w P (i + 1) = fld w (P / 2 ^ w) i := by
  unfold fld
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

/-- Addition without carries between fields. -/
theorem fld_add (w : ℕ) : ∀ (n P Q : ℕ), P < 2 ^ (w * n) → Q < 2 ^ (w * n) →
    (∀ i < n, fld w P i + fld w Q i < 2 ^ w) →
    P + Q < 2 ^ (w * n) ∧ ∀ i < n, fld w (P + Q) i = fld w P i + fld w Q i := by
  intro n
  induction n with
  | zero =>
    intro P Q hP hQ _
    have hP0 : P = 0 := by simpa using hP
    have hQ0 : Q = 0 := by simpa using hQ
    subst hP0 hQ0
    simp
  | succ n ih =>
    intro P Q hP hQ h
    have hw : 0 < 2 ^ w := by positivity
    have hP' : P / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hw, ← pow_add]
      calc P < 2 ^ (w * (n + 1)) := hP
        _ = 2 ^ (w * n + w) := by ring_nf
    have hQ' : Q / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hw, ← pow_add]
      calc Q < 2 ^ (w * (n + 1)) := hQ
        _ = 2 ^ (w * n + w) := by ring_nf
    have h0 := h 0 (Nat.succ_pos n)
    rw [fld_zero_right, fld_zero_right] at h0
    have hrest : ∀ i < n, fld w (P / 2 ^ w) i + fld w (Q / 2 ^ w) i < 2 ^ w := by
      intro i hi
      have := h (i + 1) (by omega)
      rwa [fld_succ, fld_succ] at this
    obtain ⟨hbound, hfld⟩ := ih (P / 2 ^ w) (Q / 2 ^ w) hP' hQ' hrest
    have hsplit : P + Q = (P % 2 ^ w + Q % 2 ^ w) + 2 ^ w * (P / 2 ^ w + Q / 2 ^ w) := by
      have h1 := Nat.mod_add_div P (2 ^ w)
      have h2 := Nat.mod_add_div Q (2 ^ w)
      nlinarith
    have hmod : (P + Q) % 2 ^ w = P % 2 ^ w + Q % 2 ^ w := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    have hdiv : (P + Q) / 2 ^ w = P / 2 ^ w + Q / 2 ^ w := by
      rw [hsplit, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt h0, zero_add]
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      have : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by rw [← pow_add]; ring_nf
      rw [this]
      have : P / 2 ^ w + Q / 2 ^ w ≤ 2 ^ (w * n) - 1 := by omega
      calc P % 2 ^ w + Q % 2 ^ w + 2 ^ w * (P / 2 ^ w + Q / 2 ^ w)
          < 2 ^ w + 2 ^ w * (P / 2 ^ w + Q / 2 ^ w) := by omega
        _ ≤ 2 ^ w + 2 ^ w * (2 ^ (w * n) - 1) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
        _ = 2 ^ w * 2 ^ (w * n) := by
          have : 1 ≤ 2 ^ (w * n) := Nat.one_le_two_pow
          rw [Nat.mul_sub, mul_one]
          have : 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := Nat.le_mul_of_pos_right _ (by positivity)
          omega
    · intro i hi
      cases i with
      | zero => rw [fld_zero_right, fld_zero_right, fld_zero_right, hmod]
      | succ i =>
        rw [fld_succ, fld_succ, fld_succ, hdiv]
        exact hfld i (by omega)


/-- Repeat a block `B` of `s` bits `c` times. -/
def rep (B s : ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => rep B s c ||| (B <<< (s * c))

/-- Bits of a repeated block. -/
theorem testBit_rep (B s : ℕ) (hB : B < 2 ^ s) : ∀ (c b : ℕ),
    (rep B s c).testBit b = (decide (b < s * c) && B.testBit (b % s)) := by
  intro c
  induction c with
  | zero => intro b; simp [rep]
  | succ c ih =>
    intro b
    simp only [rep, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases h1 : b < s * c
    · have h2 : b < s * (c + 1) := by nlinarith
      have h3 : ¬ s * c ≤ b := by omega
      simp [h1, h2, h3]
    · have h3 : s * c ≤ b := by omega
      by_cases h2 : b < s * (c + 1)
      · have hm : b % s = b - s * c := by
          have hlt : b - s * c < s := by rw [Nat.mul_succ] at h2; omega
          have hb : b = (b - s * c) + s * c := by omega
          conv_lhs => rw [hb]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        simp [h1, h2, h3, hm]
      · simp only [h1, h2, h3, decide_false, Bool.false_and, decide_true, Bool.true_and,
          Bool.false_or]
        apply Nat.testBit_lt_two_pow
        calc B < 2 ^ s := hB
          _ ≤ 2 ^ (b - s * c) := Nat.pow_le_pow_right (by norm_num) (by
              rw [Nat.mul_succ] at h2; omega)

/-- The field mask of the fields whose index has bit `k` set, among `2^K` fields. -/
def bmask (w K k : ℕ) : ℕ :=
  rep ((2 ^ (w * 2 ^ k) - 1) <<< (w * 2 ^ k)) (w * 2 ^ (k + 1)) (2 ^ (K - (k + 1)))

/-- Bits of a shifted block of ones. -/
theorem testBit_two_pow_sub_one_shift (a s b : ℕ) :
    ((2 ^ a - 1) <<< s).testBit b = (decide (s ≤ b) && decide (b < s + a)) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : s ≤ b
  · simp only [h, decide_true, Bool.true_and]
    congr 1
    apply propext
    omega
  · simp [h]

/-- The repeated block of `bmask` fits in its period. -/
theorem bmask_block_lt (w k : ℕ) :
    (2 ^ (w * 2 ^ k) - 1) <<< (w * 2 ^ k) < 2 ^ (w * 2 ^ (k + 1)) := by
  rw [Nat.shiftLeft_eq]
  have h : w * 2 ^ (k + 1) = w * 2 ^ k + w * 2 ^ k := by ring
  rw [h, pow_add]
  have : 2 ^ (w * 2 ^ k) - 1 < 2 ^ (w * 2 ^ k) := Nat.sub_lt (by positivity) one_pos
  calc (2 ^ (w * 2 ^ k) - 1) * 2 ^ (w * 2 ^ k) < 2 ^ (w * 2 ^ k) * 2 ^ (w * 2 ^ k) :=
        Nat.mul_lt_mul_of_pos_right this (by positivity)
    _ = _ := rfl

/-- Bit `k` of `i` is set iff `2^k ≤ i % 2^(k+1)`. -/
theorem testBit_iff_mod (i k : ℕ) : i.testBit k = decide (2 ^ k ≤ i % 2 ^ (k + 1)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : i % 2 ^ (k + 1) = i / 2 ^ k % 2 * 2 ^ k + i % 2 ^ k := by
    rw [pow_succ, Nat.mod_mul, Nat.mul_comm]
    ring
  have h2 : i % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have h3 : i / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [h1]
  have : i / 2 ^ k % 2 = 0 ∨ i / 2 ^ k % 2 = 1 := by omega
  rcases this with h | h
  · rw [h]; simpa using h2
  · rw [h]; simp

/-- Fields of the bit mask: full exactly where bit `k` of the index is set. -/
theorem fld_bmask (w K k i : ℕ) (hk : k < K) (hi : i < 2 ^ K) :
    fld w (bmask w K k) i = if i.testBit k then 2 ^ w - 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, bmask, testBit_rep _ _ (bmask_block_lt w k), testBit_two_pow_sub_one_shift]
  by_cases hb : b < w
  · have hK : 2 ^ (k + 1) * 2 ^ (K - (k + 1)) = 2 ^ K := by
      rw [← pow_add]; congr 1; omega
    have hlt : w * i + b < w * 2 ^ (k + 1) * 2 ^ (K - (k + 1)) := by
      rw [Nat.mul_assoc, hK]
      have : w * (i + 1) ≤ w * 2 ^ K := Nat.mul_le_mul_left w hi
      rw [Nat.mul_succ] at this
      omega
    have hmod : (w * i + b) % (w * 2 ^ (k + 1)) = w * (i % 2 ^ (k + 1)) + b := by
      have hi' : i = 2 ^ (k + 1) * (i / 2 ^ (k + 1)) + i % 2 ^ (k + 1) :=
        (Nat.div_add_mod i (2 ^ (k + 1))).symm
      have hr : i % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
      have hlt2 : w * (i % 2 ^ (k + 1)) + b < w * 2 ^ (k + 1) := by
        have : w * (i % 2 ^ (k + 1) + 1) ≤ w * 2 ^ (k + 1) := Nat.mul_le_mul_left w hr
        rw [Nat.mul_succ] at this
        omega
      have : w * i + b = (w * (i % 2 ^ (k + 1)) + b) + (w * 2 ^ (k + 1)) * (i / 2 ^ (k + 1)) := by
        conv_lhs => rw [hi']
        ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
    rw [hmod]
    have hr : i % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
    have e1 : (w * 2 ^ k ≤ w * (i % 2 ^ (k + 1)) + b) ↔ 2 ^ k ≤ i % 2 ^ (k + 1) := by
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have : w * (i % 2 ^ (k + 1) + 1) ≤ w * 2 ^ k := Nat.mul_le_mul_left w hc
        rw [Nat.mul_succ] at this
        omega
      · intro h
        have := Nat.mul_le_mul_left w h
        omega
    have e2 : w * (i % 2 ^ (k + 1)) + b < w * 2 ^ k + w * 2 ^ k := by
      have : w * (i % 2 ^ (k + 1) + 1) ≤ w * 2 ^ (k + 1) := Nat.mul_le_mul_left w hr
      rw [Nat.mul_succ] at this
      have h2 : w * 2 ^ (k + 1) = w * 2 ^ k + w * 2 ^ k := by ring
      omega
    rw [testBit_iff_mod i k]
    by_cases hc : 2 ^ k ≤ i % 2 ^ (k + 1)
    · simp [hb, hlt, e1.mpr hc, e2, hc, Nat.testBit_two_pow_sub_one]
    · have : ¬ (w * 2 ^ k ≤ w * (i % 2 ^ (k + 1)) + b) := fun h => hc (e1.mp h)
      simp [hb, hlt, this, hc]
  · simp only [hb, decide_false, Bool.false_and]
    split_ifs
    · rw [Nat.testBit_two_pow_sub_one]; simp [hb]
    · simp




/-- Adding `2^k` to a number with clear bit `k` does not change the higher bits. -/
theorem add_two_pow_div (i k : ℕ) (h : i.testBit k = false) :
    (2 ^ k + i) / 2 ^ (k + 1) = i / 2 ^ (k + 1) := by
  have hm : i % 2 ^ (k + 1) < 2 ^ k := by
    have h1 : i % 2 ^ (k + 1) = i / 2 ^ k % 2 * 2 ^ k + i % 2 ^ k := by
      rw [pow_succ, Nat.mod_mul, Nat.mul_comm]; ring
    have h2 : i / 2 ^ k % 2 = 0 := by
      have := Nat.testBit_eq_decide_div_mod_eq (x := i) (i := k)
      rw [h] at this
      have h3 : i / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      by_contra hc
      have : i / 2 ^ k % 2 = 1 := by omega
      simp [this] at *
    rw [h1, h2]
    simp only [zero_mul, zero_add]
    exact Nat.mod_lt _ (by positivity)
  have hi : i = 2 ^ (k + 1) * (i / 2 ^ (k + 1)) + i % 2 ^ (k + 1) := (Nat.div_add_mod _ _).symm
  have hlt : 2 ^ k + i % 2 ^ (k + 1) < 2 ^ (k + 1) := by
    have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega
  have e : 2 ^ k + i = (2 ^ k + i % 2 ^ (k + 1)) + 2 ^ (k + 1) * (i / 2 ^ (k + 1)) := by
    conv_lhs => rw [hi]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

/-- Exclusive or with `2^k` adds `2^k` when bit `k` is clear. -/
theorem xor_two_pow_of_testBit_false (i k : ℕ) (h : i.testBit k = false) :
    i ^^^ 2 ^ k = i + 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.add_comm]
  rcases lt_trichotomy j k with hj | hj | hj
  · rw [Nat.testBit_two_pow_add_gt hj]
    simp [Nat.ne_of_gt hj]
  · subst hj
    rw [Nat.testBit_two_pow_add_eq, h]
    simp
  · have hne : k ≠ j := Nat.ne_of_lt hj
    simp only [hne, decide_false, Bool.xor_false]
    obtain ⟨m, rfl⟩ : ∃ m, j = m + (k + 1) := ⟨j - (k + 1), by omega⟩
    rw [Nat.testBit_add, Nat.testBit_add, add_two_pow_div i k h]

/-- Exclusive or with `2^k` flips bit `k`. -/
theorem xor_two_pow_eq (i k : ℕ) :
    i ^^^ 2 ^ k = if i.testBit k then i - 2 ^ k else i + 2 ^ k := by
  split_ifs with h
  · have hge : 2 ^ k ≤ i := Nat.ge_two_pow_of_testBit h
    set i' := i - 2 ^ k with hi'
    have hi : i = 2 ^ k + i' := by omega
    have h' : i'.testBit k = false := by
      have := Nat.testBit_two_pow_add_eq i' k
      rw [← hi, h] at this
      simpa using this.symm
    rw [hi, Nat.add_comm, ← xor_two_pow_of_testBit_false i' k h', Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  · exact xor_two_pow_of_testBit_false i k (by simpa using h)


/-- Multiplication by a constant without carries between fields. -/
theorem fld_mul (w c : ℕ) : ∀ (n P : ℕ), P < 2 ^ (w * n) →
    (∀ i < n, c * fld w P i < 2 ^ w) →
    c * P < 2 ^ (w * n) ∧ ∀ i < n, fld w (c * P) i = c * fld w P i := by
  intro n
  induction n with
  | zero =>
    intro P hP _
    have hP0 : P = 0 := by simpa using hP
    subst hP0
    simp
  | succ n ih =>
    intro P hP h
    have hw : 0 < 2 ^ w := by positivity
    have hP' : P / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hw, ← pow_add]
      calc P < 2 ^ (w * (n + 1)) := hP
        _ = 2 ^ (w * n + w) := by ring_nf
    have h0 := h 0 (Nat.succ_pos n)
    rw [fld_zero_right] at h0
    have hrest : ∀ i < n, c * fld w (P / 2 ^ w) i < 2 ^ w := by
      intro i hi
      have := h (i + 1) (by omega)
      rwa [fld_succ] at this
    obtain ⟨hbound, hfld⟩ := ih (P / 2 ^ w) hP' hrest
    have hsplit : c * P = c * (P % 2 ^ w) + 2 ^ w * (c * (P / 2 ^ w)) := by
      have h1 := Nat.mod_add_div P (2 ^ w)
      calc c * P = c * (P % 2 ^ w + 2 ^ w * (P / 2 ^ w)) := by rw [h1]
        _ = _ := by ring
    have hmod : (c * P) % 2 ^ w = c * (P % 2 ^ w) := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    have hdiv : (c * P) / 2 ^ w = c * (P / 2 ^ w) := by
      rw [hsplit, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt h0, zero_add]
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      have e : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by rw [← pow_add]; ring_nf
      rw [e]
      have : c * (P / 2 ^ w) ≤ 2 ^ (w * n) - 1 := by omega
      calc c * (P % 2 ^ w) + 2 ^ w * (c * (P / 2 ^ w))
          < 2 ^ w + 2 ^ w * (c * (P / 2 ^ w)) := by omega
        _ ≤ 2 ^ w + 2 ^ w * (2 ^ (w * n) - 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
        _ = 2 ^ w * 2 ^ (w * n) := by
          have : 1 ≤ 2 ^ (w * n) := Nat.one_le_two_pow
          rw [Nat.mul_sub, mul_one]
          have : 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := Nat.le_mul_of_pos_right _ (by positivity)
          omega
    · intro i hi
      cases i with
      | zero => rw [fld_zero_right, fld_zero_right, hmod]
      | succ i =>
        rw [fld_succ, fld_succ, hdiv]
        exact hfld i (by omega)

/-- A field of a row of `S` fields. -/
theorem fld_split (w S P t i : ℕ) (hi : i < S) :
    fld w P (S * t + i) = fld w (fld (w * S) P t) i := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, testBit_fld, testBit_fld]
  by_cases hb : b < w
  · have h1 : w * i + b < w * S := by
      have : w * (i + 1) ≤ w * S := Nat.mul_le_mul_left w hi
      rw [Nat.mul_succ] at this; omega
    simp only [hb, h1, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [hb]

/-- Subtracting `2^k` from a number with clear bit `k` sets bit `k`. -/
theorem testBit_sub_two_pow_of_false (t k : ℕ) (h : t.testBit k = false) (hle : 2 ^ k ≤ t) :
    (t - 2 ^ k).testBit k = true := by
  have e : t = 2 ^ k + (t - 2 ^ k) := by omega
  have := Nat.testBit_two_pow_add_eq (t - 2 ^ k) k
  rw [← e, h] at this
  simpa using this.symm

/-- Subtracting `2^k` from a number with set bit `k` clears bit `k`. -/
theorem testBit_sub_two_pow_of_true (t k : ℕ) (h : t.testBit k = true) :
    (t - 2 ^ k).testBit k = false := by
  have hge : 2 ^ k ≤ t := Nat.ge_two_pow_of_testBit h
  have e : t = 2 ^ k + (t - 2 ^ k) := by omega
  have := Nat.testBit_two_pow_add_eq (t - 2 ^ k) k
  rw [← e, h] at this
  simpa using this.symm

/-- The field mask of fields whose index has bit `k` clear. -/
def lmask (W K k : ℕ) : ℕ := allMask W (2 ^ K) ^^^ bmask W K k

/-- Fields of the clear-bit mask. -/
theorem fld_lmask (W K k t : ℕ) (hk : k < K) (ht : t < 2 ^ K) :
    fld W (lmask W K k) t = if t.testBit k then 0 else 2 ^ W - 1 := by
  rw [lmask, fld_xor, fld_allMask, fld_bmask W K k t hk ht, ite_eq_left ht]
  split_ifs <;> simp

/-- Translation of field indices by `2^k` (XOR), at field width `W`, among `2^K` fields. -/
def tr (W K k P : ℕ) : ℕ :=
  (((P &&& lmask W K k) <<< (W * 2 ^ k)) ||| ((P >>> (W * 2 ^ k)) &&& lmask W K k)) &&&
    allMask W (2 ^ K)

/-- A translated packed number still fits in `2^K` fields. -/
theorem tr_lt (W K k P : ℕ) : tr W K k P < 2 ^ (W * 2 ^ K) := by
  unfold tr allMask
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (by positivity) one_pos)

/-- Translation moves the field at index `t ^^^ 2^k` to index `t`. -/
theorem fld_tr (W K k P t : ℕ) (hk : k < K) (ht : t < 2 ^ K) :
    fld W (tr W K k P) t = fld W P (t ^^^ 2 ^ k) := by
  have hlt : fld W P (t ^^^ 2 ^ k) < 2 ^ W := fld_lt _ _ _
  unfold tr
  rw [fld_land, fld_allMask, ite_eq_left ht, fld_lor, fld_shiftLeft, fld_land, fld_land,
    fld_shiftRight, fld_lmask W K k t hk ht, xor_two_pow_eq]
  by_cases hb : t.testBit k
  · have hge : 2 ^ k ≤ t := Nat.ge_two_pow_of_testBit hb
    have hb' := testBit_sub_two_pow_of_true t k hb
    have hpos : 0 < 2 ^ k := by positivity
    have hlt' : t - 2 ^ k < 2 ^ K := by omega
    rw [ite_eq_left hge, fld_lmask W K k (t - 2 ^ k) hk hlt', hb']
    simp only [hb, ite_true, ite_false, Bool.false_eq_true, Nat.and_zero, Nat.or_zero]
    rw [xor_two_pow_eq, ite_eq_left hb] at hlt
    rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]
  · have hb0 : t.testBit k = false := by simpa using hb
    rw [xor_two_pow_eq, ite_eq_right hb] at hlt
    simp only [hb, ite_false, Bool.false_eq_true]
    by_cases hge : 2 ^ k ≤ t
    · have hb' := testBit_sub_two_pow_of_false t k hb0 hge
      have hpos : 0 < 2 ^ k := by positivity
      have hlt' : t - 2 ^ k < 2 ^ K := by omega
      rw [ite_eq_left hge, fld_lmask W K k (t - 2 ^ k) hk hlt', hb']
      simp only [ite_true, Nat.and_zero, Nat.zero_or]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]
    · rw [ite_eq_right hge, Nat.zero_or]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]


/-! ## Signed packed vectors -/

/-- A signed packed vector is a pair of packed naturals: positive and negative parts. -/
abbrev SVec := ℕ × ℕ

/-- The signed value of field `i` of a signed packed vector. -/
def sval (w : ℕ) (x : SVec) (i : ℕ) : ℤ := (fld w x.1 i : ℤ) - (fld w x.2 i : ℤ)

/-- Both parts fit in `n` fields and every field of both parts is at most `B`. -/
def SBnd (w n B : ℕ) (x : SVec) : Prop :=
  x.1 < 2 ^ (w * n) ∧ x.2 < 2 ^ (w * n) ∧ ∀ i < n, fld w x.1 i ≤ B ∧ fld w x.2 i ≤ B

/-- Field-wise sum of signed packed vectors. -/
def sadd (x y : SVec) : SVec := (x.1 + y.1, x.2 + y.2)

/-- Field-wise negation of a signed packed vector. -/
def sneg (x : SVec) : SVec := (x.2, x.1)

/-- Restriction of a signed packed vector to the fields of a mask. -/
def ssel (M : ℕ) (x : SVec) : SVec := (x.1 &&& M, x.2 &&& M)

/-- Multiplication of every field of a signed packed vector by a natural constant. -/
def sscale (c : ℕ) (x : SVec) : SVec := (c * x.1, c * x.2)

/-- The zero signed packed vector. -/
def szero : SVec := (0, 0)

/-- Field bounds can be weakened. -/
theorem SBnd.mono {w n B B' : ℕ} {x : SVec} (h : SBnd w n B x) (hB : B ≤ B') :
    SBnd w n B' x :=
  ⟨h.1, h.2.1, fun i hi => ⟨le_trans (h.2.2 i hi).1 hB, le_trans (h.2.2 i hi).2 hB⟩⟩

/-- The zero vector satisfies every bound. -/
theorem SBnd_zero (w n B : ℕ) : SBnd w n B szero := by
  refine ⟨by simp [szero], by simp [szero], fun i _ => ?_⟩
  simp [szero, fld]

/-- The zero vector has zero values. -/
theorem sval_zero (w i : ℕ) : sval w szero i = 0 := by simp [sval, szero, fld]

/-- Bounds and values of a field-wise sum. -/
theorem sadd_spec {w n B C : ℕ} {x y : SVec} (hx : SBnd w n B x) (hy : SBnd w n C y)
    (hBC : B + C < 2 ^ w) :
    SBnd w n (B + C) (sadd x y) ∧ ∀ i < n, sval w (sadd x y) i = sval w x i + sval w y i := by
  have h1 := fld_add w n x.1 y.1 hx.1 hy.1 (fun i hi => by
    have := (hx.2.2 i hi).1; have := (hy.2.2 i hi).1; omega)
  have h2 := fld_add w n x.2 y.2 hx.2.1 hy.2.1 (fun i hi => by
    have := (hx.2.2 i hi).2; have := (hy.2.2 i hi).2; omega)
  refine ⟨⟨h1.1, h2.1, fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only [sadd]
    rw [h1.2 i hi, h2.2 i hi]
    have a1 := hx.2.2 i hi; have a2 := hy.2.2 i hi
    omega
  · simp only [sval, sadd]
    rw [h1.2 i hi, h2.2 i hi]
    push_cast; ring

/-- Bounds and values of a negation. -/
theorem sneg_spec {w n B : ℕ} {x : SVec} (hx : SBnd w n B x) :
    SBnd w n B (sneg x) ∧ ∀ i, sval w (sneg x) i = - sval w x i := by
  refine ⟨⟨hx.2.1, hx.1, fun i hi => ⟨(hx.2.2 i hi).2, (hx.2.2 i hi).1⟩⟩, fun i => ?_⟩
  simp [sval, sneg]

/-- A field mask: each field below `n` is full exactly where `p` holds and zero elsewhere. -/
def IsFieldMask (w n : ℕ) (M : ℕ) (p : ℕ → Prop) [DecidablePred p] : Prop :=
  ∀ i < n, fld w M i = if p i then 2 ^ w - 1 else 0

/-- Bounds and values of a restriction to a field mask. -/
theorem ssel_spec {w n B : ℕ} {x : SVec} (hx : SBnd w n B x) (M : ℕ) (p : ℕ → Prop)
    [DecidablePred p] (hM : IsFieldMask w n M p) :
    SBnd w n B (ssel M x) ∧ ∀ i < n, sval w (ssel M x) i = if p i then sval w x i else 0 := by
  have key : ∀ (P : ℕ) (i : ℕ), i < n → fld w (P &&& M) i = if p i then fld w P i else 0 := by
    intro P i hi
    rw [fld_land, hM i hi]
    split_ifs
    · exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt w P i)
    · simp
  refine ⟨⟨lt_of_le_of_lt Nat.and_le_left hx.1, lt_of_le_of_lt Nat.and_le_left hx.2.1,
    fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only [ssel]
    rw [key _ i hi, key _ i hi]
    split_ifs
    · exact hx.2.2 i hi
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp only [sval, ssel]
    rw [key _ i hi, key _ i hi]
    split_ifs <;> simp

/-- Bounds and values of a scaled vector. -/
theorem sscale_spec {w n B : ℕ} {x : SVec} (hx : SBnd w n B x) (c : ℕ) (hc : c * B < 2 ^ w) :
    SBnd w n (c * B) (sscale c x) ∧ ∀ i < n, sval w (sscale c x) i = c * sval w x i := by
  have h1 := fld_mul w c n x.1 hx.1 (fun i hi => lt_of_le_of_lt
    (Nat.mul_le_mul_left c (hx.2.2 i hi).1) hc)
  have h2 := fld_mul w c n x.2 hx.2.1 (fun i hi => lt_of_le_of_lt
    (Nat.mul_le_mul_left c (hx.2.2 i hi).2) hc)
  refine ⟨⟨h1.1, h2.1, fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only [sscale]
    rw [h1.2 i hi, h2.2 i hi]
    exact ⟨Nat.mul_le_mul_left c (hx.2.2 i hi).1, Nat.mul_le_mul_left c (hx.2.2 i hi).2⟩
  · simp only [sval, sscale]
    rw [h1.2 i hi, h2.2 i hi]
    push_cast; ring

/-! ## Translations of field indices -/

/-- Signed translation by `2^k` at field width `W` among `2^K` fields. -/
def str (W K k : ℕ) (x : SVec) : SVec := (tr W K k x.1, tr W K k x.2)

/-- Translation keeps indices below `2^K`. -/
theorem xor_two_pow_lt (t k K : ℕ) (hk : k < K) (ht : t < 2 ^ K) : t ^^^ 2 ^ k < 2 ^ K :=
  Nat.xor_lt_two_pow ht (Nat.pow_lt_pow_right (by norm_num) hk)

/-- Bounds and values of a signed translation. -/
theorem str_spec {W K B : ℕ} {x : SVec} (hx : SBnd W (2 ^ K) B x) (k : ℕ) (hk : k < K) :
    SBnd W (2 ^ K) B (str W K k x) ∧
      ∀ t < 2 ^ K, sval W (str W K k x) t = sval W x (t ^^^ 2 ^ k) := by
  refine ⟨⟨tr_lt _ _ _ _, tr_lt _ _ _ _, fun t ht => ?_⟩, fun t ht => ?_⟩
  · simp only [str]
    rw [fld_tr W K k _ t hk ht, fld_tr W K k _ t hk ht]
    exact hx.2.2 _ (xor_two_pow_lt t k K hk ht)
  · simp only [sval, str]
    rw [fld_tr W K k _ t hk ht, fld_tr W K k _ t hk ht]

/-- Translation by an arbitrary mask, given as the list of its bits. -/
def strs (W K : ℕ) : List ℕ → SVec → SVec
  | [], x => x
  | k :: ks, x => strs W K ks (str W K k x)

/-- The XOR of the powers of two in a list. -/
def xorBits : List ℕ → ℕ
  | [] => 0
  | k :: ks => 2 ^ k ^^^ xorBits ks

/-- A list of bits below `K` gives a mask below `2^K`. -/
theorem xorBits_lt (K : ℕ) : ∀ (ks : List ℕ), (∀ k ∈ ks, k < K) → xorBits ks < 2 ^ K
  | [], _ => by simp [xorBits]
  | k :: ks, h => by
    simp only [xorBits]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (h k (by simp)))
      (xorBits_lt K ks (fun j hj => h j (by simp [hj])))

/-- Bounds and values of a translation by a list of bits. -/
theorem strs_spec {W K B : ℕ} : ∀ (ks : List ℕ) {x : SVec}, SBnd W (2 ^ K) B x →
    (∀ k ∈ ks, k < K) →
    SBnd W (2 ^ K) B (strs W K ks x) ∧
      ∀ t < 2 ^ K, sval W (strs W K ks x) t = sval W x (t ^^^ xorBits ks)
  | [], x, hx, _ => ⟨hx, fun t _ => by simp [strs, xorBits]⟩
  | k :: ks, x, hx, hks => by
    have hk : k < K := hks k (by simp)
    obtain ⟨h1, h2⟩ := str_spec hx k hk
    obtain ⟨h3, h4⟩ := strs_spec ks h1 (fun j hj => hks j (by simp [hj]))
    refine ⟨h3, fun t ht => ?_⟩
    simp only [strs]
    rw [h4 t ht, h2 _ (Nat.xor_lt_two_pow ht (xorBits_lt K ks (fun j hj => hks j (by simp [hj])))),
      xorBits, Nat.xor_assoc, Nat.xor_comm (xorBits ks) (2 ^ k)]


/-- All fields of zero vanish. -/
theorem fld_zero_right_zero (w i : ℕ) : fld w 0 i = 0 := by simp [fld]

/-! ## Field masks from bitsets -/

/-- Spread the low `m` bits of `B` into full fields of width `w`. -/
def spread (w B : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => spread w B m ||| (if B.testBit m then (2 ^ w - 1) <<< (w * m) else 0)

/-- Fields of a spread bitset. -/
theorem fld_spread (w B : ℕ) : ∀ (m i : ℕ),
    fld w (spread w B m) i = if i < m ∧ B.testBit i then 2 ^ w - 1 else 0 := by
  intro m
  induction m with
  | zero => intro i; simp [spread, fld]
  | succ m ih =>
    intro i
    simp only [spread, fld_lor, ih]
    by_cases hB : B.testBit m
    · rw [ite_eq_left hB, fld_shiftLeft, fld_two_pow_sub_one]
      by_cases him : i = m
      · subst him; simp [hB]
      · have h1 : (if m ≤ i then (if i - m = 0 then 2 ^ w - 1 else 0) else 0) = 0 := by
          split_ifs <;> first | rfl | omega
        rw [h1, Nat.or_zero]
        congr 1
        apply propext
        constructor
        · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
    · rw [ite_eq_right hB, fld_zero_right_zero, Nat.or_zero]
      congr 1
      apply propext
      constructor
      · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
      · rintro ⟨h, h'⟩
        refine ⟨?_, h'⟩
        by_contra hc
        have : i = m := by omega
        subst this; exact hB h'

/-- A spread bitset is the field mask of its set bits. -/
theorem spread_isFieldMask (w n B : ℕ) :
    IsFieldMask w n (spread w B n) (fun i => B.testBit i = true) := by
  intro i hi
  rw [fld_spread]
  by_cases h : B.testBit i <;> simp [h, hi]

/-! ## Transvections of field indices -/

/-- Relabel fields by `t ↦ t ^^^ (bit c of t) * 2^j`. -/
def tv (W K c j P : ℕ) : ℕ := (P &&& lmask W K c) ||| tr W K j (P &&& bmask W K c)

/-- A transvected packed number still fits in `2^K` fields. -/
theorem tv_lt (W K c j P : ℕ) (hP : P < 2 ^ (W * 2 ^ K)) : tv W K c j P < 2 ^ (W * 2 ^ K) := by
  unfold tv
  apply Nat.or_lt_two_pow
  · exact lt_of_le_of_lt Nat.and_le_left hP
  · exact tr_lt _ _ _ _

/-- The index map of a transvection. -/
def tvIdx (c j t : ℕ) : ℕ := if t.testBit c then t ^^^ 2 ^ j else t

/-- A transvection moves the field at `tvIdx c j t` to `t`. -/
theorem fld_tv (W K c j P t : ℕ) (hc : c < K) (hj : j < K) (hcj : c ≠ j) (ht : t < 2 ^ K) :
    fld W (tv W K c j P) t = fld W P (tvIdx c j t) := by
  have hpart : ∀ u, u < 2 ^ K → fld W (P &&& bmask W K c) u =
      if u.testBit c then fld W P u else 0 := by
    intro u hu
    rw [fld_land, fld_bmask W K c u hc hu]
    split_ifs
    · exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt _ _ _)
    · simp
  unfold tv tvIdx
  rw [fld_lor, fld_land, fld_lmask W K c t hc ht, fld_tr W K j _ t hj ht,
    hpart _ (xor_two_pow_lt t j K hj ht)]
  have hbit : (t ^^^ 2 ^ j).testBit c = t.testBit c := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    simp [Ne.symm hcj]
  rw [hbit]
  by_cases h : t.testBit c
  · simp [h]
  · simp only [h, ite_false, Bool.false_eq_true, Nat.or_zero]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt _ _ _)

/-- The transvection index map keeps indices below `2^K`. -/
theorem tvIdx_lt (c j t K : ℕ) (hj : j < K) (ht : t < 2 ^ K) : tvIdx c j t < 2 ^ K := by
  unfold tvIdx
  split_ifs
  · exact xor_two_pow_lt t j K hj ht
  · exact ht

/-- Elementary index operations: translation by a bit, or a transvection. -/
inductive IdxOp
  | flip (k : ℕ)
  | trans (c j : ℕ)

/-- Validity of an index operation for `2^K` fields. -/
def IdxOp.Valid (K : ℕ) : IdxOp → Prop
  | .flip k => k < K
  | .trans c j => c < K ∧ j < K ∧ c ≠ j

/-- The index map of an elementary operation. -/
def IdxOp.idx : IdxOp → ℕ → ℕ
  | .flip k, t => t ^^^ 2 ^ k
  | .trans c j, t => tvIdx c j t

/-- The packed action of an elementary operation (one part). -/
def IdxOp.act (W K : ℕ) : IdxOp → ℕ → ℕ
  | .flip k, P => tr W K k P
  | .trans c j, P => tv W K c j P

/-- Elementary index operations keep packed numbers within `2^K` fields. -/
theorem IdxOp.act_lt (W K : ℕ) (o : IdxOp) (P : ℕ) (hP : P < 2 ^ (W * 2 ^ K)) :
    o.act W K P < 2 ^ (W * 2 ^ K) := by
  cases o with
  | flip k => exact tr_lt _ _ _ _
  | trans c j => exact tv_lt _ _ _ _ _ hP

/-- Valid elementary index maps keep indices below `2^K`. -/
theorem IdxOp.idx_lt (K : ℕ) (o : IdxOp) (ho : o.Valid K) (t : ℕ) (ht : t < 2 ^ K) :
    o.idx t < 2 ^ K := by
  cases o with
  | flip k => exact xor_two_pow_lt t k K ho ht
  | trans c j => exact tvIdx_lt c j t K ho.2.1 ht

/-- The field-wise effect of an elementary index operation. -/
theorem IdxOp.fld_act (W K : ℕ) (o : IdxOp) (ho : o.Valid K) (P t : ℕ) (ht : t < 2 ^ K) :
    fld W (o.act W K P) t = fld W P (o.idx t) := by
  cases o with
  | flip k => exact fld_tr W K k P t ho ht
  | trans c j => exact fld_tv W K c j P t ho.1 ho.2.1 ho.2.2 ht

/-- Apply a list of index operations in order (first operation first). -/
def actOps (W K : ℕ) : List IdxOp → ℕ → ℕ
  | [], P => P
  | o :: os, P => actOps W K os (o.act W K P)

/-- The composed index map: the value at `t` comes from `idxOps os t`. -/
def idxOps : List IdxOp → ℕ → ℕ
  | [], t => t
  | o :: os, t => o.idx (idxOps os t)

/-- Bounds and field-wise effect of a list of index operations. -/
theorem actOps_spec (W K : ℕ) : ∀ (os : List IdxOp), (∀ o ∈ os, o.Valid K) →
    ∀ (P : ℕ), P < 2 ^ (W * 2 ^ K) →
    actOps W K os P < 2 ^ (W * 2 ^ K) ∧
      ∀ t < 2 ^ K, idxOps os t < 2 ^ K ∧ fld W (actOps W K os P) t = fld W P (idxOps os t)
  | [], _, P, hP => ⟨hP, fun t ht => ⟨ht, rfl⟩⟩
  | o :: os, hos, P, hP => by
    have ho : o.Valid K := hos o (by simp)
    have hos' : ∀ o ∈ os, o.Valid K := fun o' h => hos o' (by simp [h])
    obtain ⟨h1, h2⟩ := actOps_spec W K os hos' (o.act W K P) (IdxOp.act_lt W K o P hP)
    refine ⟨h1, fun t ht => ?_⟩
    obtain ⟨h3, h4⟩ := h2 t ht
    refine ⟨IdxOp.idx_lt K o ho _ h3, ?_⟩
    simp only [actOps, idxOps]
    rw [h4, IdxOp.fld_act W K o ho P _ h3]

/-- Signed relabeling by a list of index operations. -/
def sops (W K : ℕ) (os : List IdxOp) (x : SVec) : SVec := (actOps W K os x.1, actOps W K os x.2)

/-- Bounds and values of a signed relabeling. -/
theorem sops_spec {W K B : ℕ} (os : List IdxOp) (hos : ∀ o ∈ os, o.Valid K) {x : SVec}
    (hx : SBnd W (2 ^ K) B x) :
    SBnd W (2 ^ K) B (sops W K os x) ∧
      ∀ t < 2 ^ K, idxOps os t < 2 ^ K ∧ sval W (sops W K os x) t = sval W x (idxOps os t) := by
  obtain ⟨a1, a2⟩ := actOps_spec W K os hos x.1 hx.1
  obtain ⟨b1, b2⟩ := actOps_spec W K os hos x.2 hx.2.1
  refine ⟨⟨a1, b1, fun t ht => ?_⟩, fun t ht => ?_⟩
  · simp only [sops]
    rw [(a2 t ht).2, (b2 t ht).2]
    exact hx.2.2 _ (a2 t ht).1
  · refine ⟨(a2 t ht).1, ?_⟩
    simp only [sval, sops]
    rw [(a2 t ht).2, (b2 t ht).2]

/-- Negate the fields selected by a mask. -/
def sflip (all M : ℕ) (x : SVec) : SVec := sadd (ssel (all ^^^ M) x) (sneg (ssel M x))

/-- Bounds and values of a selective negation; the bound is preserved. -/
theorem sflip_spec {w n B : ℕ} {x : SVec} (hx : SBnd w n B x) (M : ℕ) (p : ℕ → Prop)
    [DecidablePred p] (hM : IsFieldMask w n M p) (hB : B < 2 ^ w) :
    SBnd w n B (sflip (allMask w n) M x) ∧
      ∀ i < n, sval w (sflip (allMask w n) M x) i = if p i then - sval w x i else sval w x i := by
  have hC : IsFieldMask w n (allMask w n ^^^ M) (fun i => ¬ p i) := by
    intro i hi
    rw [fld_xor, fld_allMask, ite_eq_left hi, hM i hi]
    split_ifs <;> simp_all
  have key : ∀ (P Q : ℕ), P < 2 ^ (w * n) → Q < 2 ^ (w * n) →
      (∀ i < n, fld w P i ≤ B ∧ fld w Q i ≤ B) →
      (P &&& (allMask w n ^^^ M)) + (Q &&& M) < 2 ^ (w * n) ∧
      ∀ i < n, fld w ((P &&& (allMask w n ^^^ M)) + (Q &&& M)) i =
        if p i then fld w Q i else fld w P i := by
    intro P Q hP hQ hb
    have fP : ∀ i < n, fld w (P &&& (allMask w n ^^^ M)) i = if p i then 0 else fld w P i := by
      intro i hi
      rw [fld_land, hC i hi]
      by_cases hp : p i
      · simp [hp]
      · simp only [hp, not_false_eq_true, ↓reduceIte]
        exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt w P i)
    have fQ : ∀ i < n, fld w (Q &&& M) i = if p i then fld w Q i else 0 := by
      intro i hi
      rw [fld_land, hM i hi]
      by_cases hp : p i
      · simp only [hp, ↓reduceIte]
        exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt w Q i)
      · simp [hp]
    have hadd := fld_add w n _ _ (lt_of_le_of_lt Nat.and_le_left hP)
      (lt_of_le_of_lt Nat.and_le_left hQ) (fun i hi => by
        rw [fP i hi, fQ i hi]
        by_cases hp : p i
        · simpa [hp] using lt_of_le_of_lt (hb i hi).2 hB
        · simpa [hp] using lt_of_le_of_lt (hb i hi).1 hB)
    refine ⟨hadd.1, fun i hi => ?_⟩
    rw [hadd.2 i hi, fP i hi, fQ i hi]
    split_ifs <;> simp
  have k1 := key x.1 x.2 hx.1 hx.2.1 (fun i hi => ⟨(hx.2.2 i hi).1, (hx.2.2 i hi).2⟩)
  have k2 := key x.2 x.1 hx.2.1 hx.1 (fun i hi => ⟨(hx.2.2 i hi).2, (hx.2.2 i hi).1⟩)
  refine ⟨⟨k1.1, k2.1, fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only [sflip, sadd, ssel, sneg]
    rw [k1.2 i hi, k2.2 i hi]
    split_ifs
    · exact ⟨(hx.2.2 i hi).2, (hx.2.2 i hi).1⟩
    · exact hx.2.2 i hi
  · simp only [sval, sflip, sadd, ssel, sneg]
    rw [k1.2 i hi, k2.2 i hi]
    split_ifs <;> ring

/-! ## Field-mask algebra -/

/-- The bit mask is the field mask of its bit. -/
theorem bmask_isFieldMask (w K k : ℕ) (hk : k < K) :
    IsFieldMask w (2 ^ K) (bmask w K k) (fun t => t.testBit k = true) := by
  intro t ht
  rw [fld_bmask w K k t hk ht]

/-- The all-ones mask is the field mask of the true predicate. -/
theorem allMask_isFieldMask (w n : ℕ) : IsFieldMask w n (allMask w n) (fun _ => True) := by
  intro t ht
  rw [fld_allMask, ite_eq_left ht, ite_eq_left trivial]

/-- Zero is the field mask of the false predicate. -/
theorem zero_isFieldMask (w n : ℕ) : IsFieldMask w n 0 (fun _ => False) := by
  intro t _
  simp [fld_zero_right_zero]

/-- Conjunction of field masks. -/
theorem isFieldMask_and {w n M N : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hM : IsFieldMask w n M p) (hN : IsFieldMask w n N q) :
    IsFieldMask w n (M &&& N) (fun t => p t ∧ q t) := by
  intro t ht
  rw [fld_land, hM t ht, hN t ht]
  by_cases hp : p t <;> by_cases hq : q t <;> simp [hp, hq]

/-- Disjunction of field masks. -/
theorem isFieldMask_or {w n M N : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hM : IsFieldMask w n M p) (hN : IsFieldMask w n N q) :
    IsFieldMask w n (M ||| N) (fun t => p t ∨ q t) := by
  intro t ht
  rw [fld_lor, hM t ht, hN t ht]
  by_cases hp : p t <;> by_cases hq : q t <;> simp [hp, hq]

/-- Exclusive or of field masks. -/
theorem isFieldMask_xor {w n M N : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hM : IsFieldMask w n M p) (hN : IsFieldMask w n N q) :
    IsFieldMask w n (M ^^^ N) (fun t => ¬ (p t ↔ q t)) := by
  intro t ht
  rw [fld_xor, hM t ht, hN t ht]
  by_cases hp : p t <;> by_cases hq : q t <;> simp [hp, hq]

/-- Complement of a field mask. -/
theorem isFieldMask_not {w n M : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hM : IsFieldMask w n M p) : IsFieldMask w n (allMask w n ^^^ M) (fun t => ¬ p t) := by
  intro t ht
  rw [fld_xor, fld_allMask, ite_eq_left ht, hM t ht]
  by_cases hp : p t <;> simp [hp]

/-- A field mask may be restated with an equivalent predicate. -/
theorem IsFieldMask.congr {w n M : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hM : IsFieldMask w n M p) (h : ∀ t < n, (p t ↔ q t)) : IsFieldMask w n M q := by
  intro t ht
  rw [hM t ht]
  by_cases hp : p t
  · rw [ite_eq_left hp, ite_eq_left ((h t ht).mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp ((h t ht).mpr hq))]

/-- Relabeling a field mask by index operations relabels its predicate. -/
theorem isFieldMask_actOps {W K M : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (os : List IdxOp) (hos : ∀ o ∈ os, o.Valid K) (hM0 : M < 2 ^ (W * 2 ^ K))
    (hM : IsFieldMask W (2 ^ K) M p) :
    IsFieldMask W (2 ^ K) (actOps W K os M) (fun t => p (idxOps os t)) := by
  intro t ht
  obtain ⟨_, h2⟩ := actOps_spec W K os hos M hM0
  rw [(h2 t ht).2, hM _ (h2 t ht).1]

/-! ## Dot products -/

/-- Field extraction by shift and mask (fast in the kernel). -/
def fldS (w P i : ℕ) : ℕ := (P >>> (w * i)) &&& (2 ^ w - 1)

/-- The fast extraction agrees with the field. -/
theorem fldS_eq (w P i : ℕ) : fldS w P i = fld w P i := by
  rw [fldS, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, fld]

/-- The positive part of a signed dot product of the first `m` fields. -/
def ndotP (w : ℕ) (x y : SVec) : ℕ → ℕ
  | 0 => 0
  | m + 1 => ndotP w x y m + (fldS w x.1 m * fldS w y.1 m + fldS w x.2 m * fldS w y.2 m)

/-- The negative part of a signed dot product of the first `m` fields. -/
def ndotN (w : ℕ) (x y : SVec) : ℕ → ℕ
  | 0 => 0
  | m + 1 => ndotN w x y m + (fldS w x.1 m * fldS w y.2 m + fldS w x.2 m * fldS w y.1 m)

/-- The signed dot product of the first `m` fields, computed with natural arithmetic. -/
def sdot (w : ℕ) (x y : SVec) (m : ℕ) : ℤ := (ndotP w x y m : ℤ) - (ndotN w x y m : ℤ)

/-- The dot product loop computes the finite sum of products. -/
theorem sdot_eq (w : ℕ) (x y : SVec) : ∀ m : ℕ,
    sdot w x y m = ∑ i ∈ Finset.range m, sval w x i * sval w y i := by
  intro m
  induction m with
  | zero => simp [sdot, ndotP, ndotN]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [sdot, ndotP, ndotN, sval, fldS_eq]
    push_cast
    ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
