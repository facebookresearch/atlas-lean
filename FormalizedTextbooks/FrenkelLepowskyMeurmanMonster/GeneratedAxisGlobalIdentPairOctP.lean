/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairTri

/-! # The octad part of the exact pairings by a packed Walsh-Hadamard transform

The octad short terms of `L` are packed into `2^16` fields of width `w` (field index `64 o + e`,
range-halving packer `packR`), transformed by a six-stage packed Walsh-Hadamard network (`whtP`),
and read once per octad term of `W` at the twisted index `64 o + octTw e`, with the diagonal sign
`octD`.  This uses that the octad Fourier matrix is a diagonal sign times a twisted Hadamard matrix
(`octMT_tw`).  The result `triShortO` equals the fast short part `triShortF` unconditionally
(`triShortO_eq`; it falls back to `triShortF` when the packing check fails), and `pairTriO` equals
the packed pairing `pairTriP` (`pairTriO_eq`), so the identification criteria apply. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Replication of field patterns by doubling -/

/-- Repeat the low `s` fields of `B` `2^t` times. -/
def dblM (w B s : ℕ) : ℕ → ℕ
  | 0 => B
  | t + 1 => dblM w B s t ||| (dblM w B s t <<< (w * (s * 2 ^ t)))

theorem dblM_lt (w B s : ℕ) (hB : B < 2 ^ (w * s)) :
    ∀ t, dblM w B s t < 2 ^ (w * (s * 2 ^ t))
  | 0 => by simpa [dblM] using hB
  | t + 1 => by
    have ih := dblM_lt w B s hB t
    rw [dblM]
    have h2 : w * (s * 2 ^ (t + 1)) = w * (s * 2 ^ t) + w * (s * 2 ^ t) := by ring
    apply Nat.or_lt_two_pow
    · calc dblM w B s t < 2 ^ (w * (s * 2 ^ t)) := ih
        _ ≤ 2 ^ (w * (s * 2 ^ (t + 1))) := Nat.pow_le_pow_right (by norm_num) (by rw [h2]; omega)
    · rw [Nat.shiftLeft_eq, h2, pow_add]
      exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem fld_dblM (w B s : ℕ) (hs : 0 < s) (hB : B < 2 ^ (w * s)) :
    ∀ t i, i < s * 2 ^ t → fld w (dblM w B s t) i = fld w B (i % s)
  | 0, i, hi => by
    simp only [pow_zero, mul_one] at hi
    simp [dblM, Nat.mod_eq_of_lt hi]
  | t + 1, i, hi => by
    have hA := dblM_lt w B s hB t
    rw [dblM, fld_lor, show w * (s * 2 ^ t) = w * (s * 2 ^ t) from rfl, fld_shiftLeft]
    by_cases h : i < s * 2 ^ t
    · have : ¬ s * 2 ^ t ≤ i := by omega
      simp only [this, ↓reduceIte, Nat.or_zero]
      exact fld_dblM w B s hs hB t i h
    · have h1 : s * 2 ^ t ≤ i := by omega
      have h2 : i - s * 2 ^ t < s * 2 ^ t := by
        have : s * 2 ^ (t + 1) = s * 2 ^ t + s * 2 ^ t := by ring
        omega
      rw [fld_eq_zero_of_lt w _ (s * 2 ^ t) i hA h1, Nat.zero_or]
      simp only [h1, ↓reduceIte]
      rw [fld_dblM w B s hs hB t _ h2]
      congr 1
      have : i = (i - s * 2 ^ t) + s * 2 ^ t := by omega
      conv_rhs => rw [this]
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

/-- A 64-field pattern from a bitset, replicated over `2^16` fields. -/
def rep64 (w B : ℕ) : ℕ := dblM w (spread w B 64) 64 10

theorem spread_lt (w B : ℕ) : ∀ m, spread w B m < 2 ^ (w * m)
  | 0 => by simp [spread]
  | m + 1 => by
    rw [spread]
    apply Nat.or_lt_two_pow
    · calc spread w B m < 2 ^ (w * m) := spread_lt w B m
        _ ≤ 2 ^ (w * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by
          rw [Nat.mul_succ]; omega)
    · split_ifs
      · rw [Nat.shiftLeft_eq, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * m))]
        exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) one_pos) (by positivity)
      · positivity

/-- The replicated pattern is the field mask of the bitset read modulo `64`. -/
theorem rep64_isFieldMask (w B : ℕ) :
    IsFieldMask w (2 ^ 16) (rep64 w B) (fun t => B.testBit (t % 64) = true) := by
  intro t ht
  unfold rep64
  rw [fld_dblM w _ 64 (by norm_num) (spread_lt w B 64) 10 t (by norm_num at ht ⊢; omega),
    fld_spread]
  have : t % 64 < 64 := Nat.mod_lt _ (by norm_num)
  by_cases hb : B.testBit (t % 64) <;> simp [hb, this]

/-! ## Translations and butterflies with given masks -/

/-- Translation of field indices by `2^k` (XOR) among `2^K` fields, with the clear-bit mask `M0`. -/
def trM (W K k M0 P : ℕ) : ℕ :=
  (((P &&& M0) <<< (W * 2 ^ k)) ||| ((P >>> (W * 2 ^ k)) &&& M0)) &&& allMask W (2 ^ K)

theorem trM_lt (W K k M0 P : ℕ) : trM W K k M0 P < 2 ^ (W * 2 ^ K) := by
  unfold trM allMask
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (by positivity) one_pos)

/-- Translation moves the field at index `t ^^^ 2^k` to index `t`. -/
theorem fld_trM (W K k M0 P t : ℕ) (ht : t < 2 ^ K)
    (hM : IsFieldMask W (2 ^ K) M0 (fun u => u.testBit k = false)) :
    fld W (trM W K k M0 P) t = fld W P (t ^^^ 2 ^ k) := by
  have hlt : fld W P (t ^^^ 2 ^ k) < 2 ^ W := fld_lt _ _ _
  unfold trM
  rw [fld_land, fld_allMask, ite_eq_left ht, fld_lor, fld_shiftLeft, fld_land, fld_land,
    fld_shiftRight, hM t ht, xor_two_pow_eq]
  simp only []
  by_cases hb : t.testBit k
  · have hge : 2 ^ k ≤ t := Nat.ge_two_pow_of_testBit hb
    have hb' := testBit_sub_two_pow_of_true t k hb
    have hpos : 0 < 2 ^ k := by positivity
    have hlt' : t - 2 ^ k < 2 ^ K := by omega
    rw [ite_eq_left hge, hM (t - 2 ^ k) hlt']
    simp only [hb', hb, Bool.true_eq_false, ↓reduceIte, Nat.and_zero, Nat.or_zero]
    rw [xor_two_pow_eq, ite_eq_left hb] at hlt
    rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]
  · have hb0 : t.testBit k = false := by simpa using hb
    rw [xor_two_pow_eq, ite_eq_right hb] at hlt
    simp only [hb0, ↓reduceIte]
    by_cases hge : 2 ^ k ≤ t
    · have hb' := testBit_sub_two_pow_of_false t k hb0 hge
      have hpos : 0 < 2 ^ k := by positivity
      have hlt' : t - 2 ^ k < 2 ^ K := by omega
      rw [ite_eq_left hge, hM (t - 2 ^ k) hlt']
      simp only [hb', Bool.true_eq_false, ↓reduceIte, Nat.and_zero, Nat.zero_or,
        Bool.false_eq_true]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]
    · rw [ite_eq_right hge, Nat.zero_or]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow hlt, Nat.and_two_pow_sub_one_of_lt_two_pow hlt]

/-- Signed translation with a given clear-bit mask. -/
def strM (W K k M0 : ℕ) (x : SVec) : SVec := (trM W K k M0 x.1, trM W K k M0 x.2)

theorem strM_spec {W K B : ℕ} {x : SVec} (hx : SBnd W (2 ^ K) B x) (k M0 : ℕ) (hk : k < K)
    (hM : IsFieldMask W (2 ^ K) M0 (fun u => u.testBit k = false)) :
    SBnd W (2 ^ K) B (strM W K k M0 x) ∧
      ∀ t < 2 ^ K, sval W (strM W K k M0 x) t = sval W x (t ^^^ 2 ^ k) := by
  refine ⟨⟨trM_lt _ _ _ _ _, trM_lt _ _ _ _ _, fun t ht => ?_⟩, fun t ht => ?_⟩
  · simp only [strM]
    rw [fld_trM W K k M0 _ t ht hM, fld_trM W K k M0 _ t ht hM]
    exact hx.2.2 _ (xor_two_pow_lt t k K hk ht)
  · simp only [sval, strM]
    rw [fld_trM W K k M0 _ t ht hM, fld_trM W K k M0 _ t ht hM]

/-- One butterfly on index bit `k`: sums on clear fields, differences on set fields. -/
def bflyM (W K k M0 M1 : ℕ) (x : SVec) : SVec :=
  sadd (ssel M0 (sadd x (strM W K k M0 x))) (ssel M1 (sadd (strM W K k M0 x) (sneg x)))

theorem bflyM_spec {W K B : ℕ} {x : SVec} (hx : SBnd W (2 ^ K) B x) (k M0 M1 : ℕ) (hk : k < K)
    (hM0 : IsFieldMask W (2 ^ K) M0 (fun u => u.testBit k = false))
    (hM1 : IsFieldMask W (2 ^ K) M1 (fun u => u.testBit k = true))
    (hB : (B + B) + (B + B) < 2 ^ W) :
    SBnd W (2 ^ K) ((B + B) + (B + B)) (bflyM W K k M0 M1 x) ∧
      ∀ t < 2 ^ K, sval W (bflyM W K k M0 M1 x) t =
        if t.testBit k then sval W x (t ^^^ 2 ^ k) - sval W x t
        else sval W x t + sval W x (t ^^^ 2 ^ k) := by
  obtain ⟨s1, v1⟩ := strM_spec hx k M0 hk hM0
  obtain ⟨n1, nv1⟩ := sneg_spec hx
  have hBB : B + B < 2 ^ W := by omega
  obtain ⟨a1, av1⟩ := sadd_spec hx s1 hBB
  obtain ⟨a2, av2⟩ := sadd_spec s1 n1 hBB
  obtain ⟨c1, cv1⟩ := ssel_spec a1 M0 _ hM0
  obtain ⟨c2, cv2⟩ := ssel_spec a2 M1 _ hM1
  obtain ⟨d1, dv1⟩ := sadd_spec c1 c2 hB
  refine ⟨d1, fun t ht => ?_⟩
  unfold bflyM
  rw [dv1 t ht, cv1 t ht, cv2 t ht, av1 t ht, av2 t ht, v1 t ht, nv1 t]
  by_cases hb : t.testBit k
  · simp [hb]
    ring
  · simp [hb]

/-! ## The Walsh-Hadamard network -/

/-- Parity of the low bits depends only on those bits. -/
theorem bpar_congr (x y : ℕ) : ∀ n, (∀ i < n, x.testBit i = y.testBit i) → bpar x n = bpar y n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bpar]
    rw [bpar_congr x y n (fun i hi => h i (by omega)), h n (by omega)]

/-- The Walsh-Hadamard value on the low `n` index bits. -/
def whtVal (y : ℕ → ℤ) (n t : ℕ) : ℤ :=
  ∑ u ∈ Finset.range (2 ^ n), (if bpar (t &&& u) n then -1 else 1) * y (t / 2 ^ n * 2 ^ n + u)

/-- The base of the block of `t` gains bit `n` of `t`. -/
theorem div_pow_succ_mul (t n : ℕ) :
    t / 2 ^ n * 2 ^ n = t / 2 ^ (n + 1) * 2 ^ (n + 1) + (if t.testBit n then 2 ^ n else 0) := by
  have h1 := Nat.div_add_mod t (2 ^ n)
  have h2 := Nat.div_add_mod t (2 ^ (n + 1))
  have h3 : t % 2 ^ (n + 1) = (if t.testBit n then 2 ^ n else 0) + t % 2 ^ n := by
    rw [Nat.mod_pow_succ]
    have hb : t / 2 ^ n % 2 = if t.testBit n then 1 else 0 := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ n) with h | h <;> simp [h]
    rw [hb]
    split_ifs <;> ring
  have e1 : 2 ^ n * (t / 2 ^ n) = t / 2 ^ n * 2 ^ n := Nat.mul_comm _ _
  have e2 : 2 ^ (n + 1) * (t / 2 ^ (n + 1)) = t / 2 ^ (n + 1) * 2 ^ (n + 1) := Nat.mul_comm _ _
  omega

/-- One more index bit for the Walsh-Hadamard value. -/
theorem whtVal_succ (y : ℕ → ℤ) (n t : ℕ) :
    whtVal y (n + 1) t =
      if t.testBit n then whtVal y n (t ^^^ 2 ^ n) - whtVal y n t
      else whtVal y n t + whtVal y n (t ^^^ 2 ^ n) := by
  have hb : ∀ u < 2 ^ n, u.testBit n = false := fun u hu => Nat.testBit_lt_two_pow hu
  have hlow : ∀ u < 2 ^ n, bpar (t &&& u) (n + 1) = bpar (t &&& u) n := by
    intro u hu
    simp [bpar, Nat.testBit_and, hb u hu]
  have hhigh : ∀ u < 2 ^ n, bpar (t &&& (2 ^ n + u)) (n + 1) =
      (bpar (t &&& u) n ^^ t.testBit n) := by
    intro u hu
    simp only [bpar, Nat.testBit_and]
    have hc : bpar (t &&& (2 ^ n + u)) n = bpar (t &&& u) n := by
      apply bpar_congr
      intro i hi
      rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow_add_gt hi]
    rw [hc, Nat.testBit_two_pow_add_eq, hb u hu]
    simp
  have hxor : ∀ u < 2 ^ n, bpar ((t ^^^ 2 ^ n) &&& u) n = bpar (t &&& u) n := by
    intro u hu
    apply bpar_congr
    intro i hi
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
    have : n ≠ i := by omega
    simp [this]
  have hdx : (t ^^^ 2 ^ n) / 2 ^ (n + 1) = t / 2 ^ (n + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
    have : n ≠ i + (n + 1) := by omega
    simp [this]
  have hbx : (t ^^^ 2 ^ n).testBit n = !t.testBit n := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    simp
  have hbase := div_pow_succ_mul t n
  have hbase' := div_pow_succ_mul (t ^^^ 2 ^ n) n
  rw [hdx, hbx] at hbase'
  set base := t / 2 ^ (n + 1) * 2 ^ (n + 1) with hbase_def
  have e1 : whtVal y (n + 1) t =
      ∑ u ∈ Finset.range (2 ^ n), (if bpar (t &&& u) n then -1 else 1) * y (base + u) +
      ∑ u ∈ Finset.range (2 ^ n),
        (if (bpar (t &&& u) n ^^ t.testBit n) then -1 else 1) * y (base + 2 ^ n + u) := by
    unfold whtVal
    have hr : Finset.range (2 ^ (n + 1)) = Finset.range (2 ^ n + 2 ^ n) := by
      rw [pow_succ, Nat.mul_two]
    rw [hr, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro u hu
      rw [hlow u (Finset.mem_range.mp hu)]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [hhigh u (Finset.mem_range.mp hu), Nat.add_assoc]
  have e2 : whtVal y n t = ∑ u ∈ Finset.range (2 ^ n), (if bpar (t &&& u) n then -1 else 1) *
      y (base + (if t.testBit n then 2 ^ n else 0) + u) := by
    unfold whtVal
    rw [hbase]
  have e3 : whtVal y n (t ^^^ 2 ^ n) = ∑ u ∈ Finset.range (2 ^ n),
      (if bpar (t &&& u) n then -1 else 1) *
        y (base + (if (!t.testBit n) = true then 2 ^ n else 0) + u) := by
    unfold whtVal
    rw [hbase']
    apply Finset.sum_congr rfl
    intro u hu
    rw [hxor u (Finset.mem_range.mp hu)]
  rw [e1, e2, e3]
  cases h : t.testBit n
  · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.not_false]
  · have hneg : ∀ u, (if (!bpar (t &&& u) n) = true then (-1 : ℤ) else 1) * y (base + 2 ^ n + u) =
        -((if bpar (t &&& u) n then -1 else 1) * y (base + 2 ^ n + u)) := by
      intro u
      cases bpar (t &&& u) n <;> simp
    simp only [Bool.xor_true, ↓reduceIte, Nat.add_zero, Bool.not_true, Bool.false_eq_true]
    rw [Finset.sum_congr rfl (fun u _ => hneg u), Finset.sum_neg_distrib]
    ring

/-- Masks of clear and set index bits within blocks of `64`. -/
def octBit0 : ℕ → ℕ
  | 0 => 0x5555555555555555
  | 1 => 0x3333333333333333
  | 2 => 0x0f0f0f0f0f0f0f0f
  | 3 => 0x00ff00ff00ff00ff
  | 4 => 0x0000ffff0000ffff
  | _ => 0x00000000ffffffff

/-- Masks of set index bits within blocks of `64`. -/
def octBit1 : ℕ → ℕ
  | 0 => 0xaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000
  | _ => 0xffffffff00000000

set_option maxRecDepth 10000 in
theorem octBit_spec : ∀ k : Fin 6, ∀ u : Fin 64,
    (octBit0 k.val).testBit u.val = !u.val.testBit k.val ∧
      (octBit1 k.val).testBit u.val = u.val.testBit k.val := by
  decide +kernel

theorem octBit0_isFieldMask (w k : ℕ) (hk : k < 6) :
    IsFieldMask w (2 ^ 16) (rep64 w (octBit0 k)) (fun u => u.testBit k = false) := by
  apply (rep64_isFieldMask w (octBit0 k)).congr
  intro t _
  have h := (octBit_spec ⟨k, hk⟩ ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩).1
  simp only at h
  have hm : (t % 64).testBit k = t.testBit k := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow]
    simp [hk]
  rw [h, hm]
  simp

theorem octBit1_isFieldMask (w k : ℕ) (hk : k < 6) :
    IsFieldMask w (2 ^ 16) (rep64 w (octBit1 k)) (fun u => u.testBit k = true) := by
  apply (rep64_isFieldMask w (octBit1 k)).congr
  intro t _
  have h := (octBit_spec ⟨k, hk⟩ ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩).2
  simp only at h
  have hm : (t % 64).testBit k = t.testBit k := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow]
    simp [hk]
  rw [h, hm]

/-- The packed Walsh-Hadamard network on the low `k` index bits. -/
def whtP (w : ℕ) (x : SVec) : ℕ → SVec
  | 0 => x
  | k + 1 => bflyM w 16 k (rep64 w (octBit0 k)) (rep64 w (octBit1 k)) (whtP w x k)

theorem whtP_spec (w B : ℕ) (x : SVec) (hx : SBnd w (2 ^ 16) B x) (hB : 4 ^ 6 * B < 2 ^ w) :
    ∀ k ≤ 6, SBnd w (2 ^ 16) (4 ^ k * B) (whtP w x k) ∧
      ∀ t < 2 ^ 16, sval w (whtP w x k) t = whtVal (sval w x) k t
  | 0, _ => by
    refine ⟨by rw [pow_zero, one_mul]; exact hx, fun t _ => ?_⟩
    simp [whtP, whtVal, bpar]
  | k + 1, hk => by
    obtain ⟨ih1, ih2⟩ := whtP_spec w B x hx hB k (by omega)
    have h4 : 4 ^ (k + 1) * B ≤ 4 ^ 6 * B :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
    have hsum : (4 ^ k * B + 4 ^ k * B) + (4 ^ k * B + 4 ^ k * B) = 4 ^ (k + 1) * B := by ring
    obtain ⟨b1, b2⟩ := bflyM_spec ih1 k _ _ (by omega) (octBit0_isFieldMask w k (by omega))
      (octBit1_isFieldMask w k (by omega)) (by omega)
    refine ⟨by rw [← hsum]; exact b1, fun t ht => ?_⟩
    simp only [whtP]
    rw [b2 t ht, ih2 t ht, ih2 _ (xor_two_pow_lt t k 16 (by omega) ht), whtVal_succ]
/-! ## Packing integer terms by halving the index range -/

/-- Shift a signed packed vector up by `s` bits. -/
def sshl (s : ℕ) (x : SVec) : SVec := (x.1 <<< s, x.2 <<< s)

/-- Absolute sum of the values of a term list. -/
def absSum (l : List (ℕ × ℤ)) : ℕ := (l.map (fun p => p.2.natAbs)).sum

/-- Sum of the values at index `i` of a term list. -/
def idxSum (l : List (ℕ × ℤ)) (i : ℕ) : ℤ := (l.map (fun p => if p.1 = i then p.2 else 0)).sum

/-- Pack the terms of a list with indices below `2^k`, halving the index range. -/
def packR (w : ℕ) : ℕ → List (ℕ × ℤ) → SVec
  | _, [] => szero
  | 0, l => ((l.map (fun p => p.2.toNat)).sum, (l.map (fun p => (-p.2).toNat)).sum)
  | k + 1, l =>
    sadd (packR w k (l.filter (fun p => decide (p.1 < 2 ^ k))))
      (sshl (w * 2 ^ k) (packR w k ((l.filter (fun p => decide (2 ^ k ≤ p.1))).map
        (fun p => (p.1 - 2 ^ k, p.2)))))

/-- A sum over a list splits along complementary filters. -/
theorem sum_filter_split {M : Type} [AddCommMonoid M] (f : ℕ × ℤ → M) (q q' : ℕ × ℤ → Bool)
    (hq : ∀ p, q' p = !q p) : ∀ l : List (ℕ × ℤ),
    (l.map f).sum = ((l.filter q).map f).sum + ((l.filter q').map f).sum
  | [] => by simp
  | p :: l => by
    have ih := sum_filter_split f q q' hq l
    rw [List.filter_cons, List.filter_cons, hq p]
    cases h : q p
    · simp only [Bool.not_false, ↓reduceIte, List.map_cons, List.sum_cons, ih,
        Bool.false_eq_true]
      abel
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, List.map_cons, List.sum_cons, ih]
      abel

theorem absSum_split (k : ℕ) (l : List (ℕ × ℤ)) :
    absSum l = absSum (l.filter (fun p => decide (p.1 < 2 ^ k))) +
      absSum ((l.filter (fun p => decide (2 ^ k ≤ p.1))).map (fun p => (p.1 - 2 ^ k, p.2))) := by
  unfold absSum
  rw [List.map_map]
  exact sum_filter_split (fun p => p.2.natAbs) (fun p => decide (p.1 < 2 ^ k))
    (fun p => decide (2 ^ k ≤ p.1)) (fun p => by
      show decide (2 ^ k ≤ p.1) = !decide (p.1 < 2 ^ k)
      by_cases h : p.1 < 2 ^ k
      · simp [h]
      · simp [h]; omega) l

theorem idxSum_split (k : ℕ) (l : List (ℕ × ℤ)) (i : ℕ) :
    idxSum l i = idxSum (l.filter (fun p => decide (p.1 < 2 ^ k))) i +
      idxSum (l.filter (fun p => decide (2 ^ k ≤ p.1))) i := by
  unfold idxSum
  exact sum_filter_split (fun p => if p.1 = i then p.2 else 0) (fun p => decide (p.1 < 2 ^ k))
    (fun p => decide (2 ^ k ≤ p.1)) (fun p => by
      show decide (2 ^ k ≤ p.1) = !decide (p.1 < 2 ^ k)
      by_cases h : p.1 < 2 ^ k
      · simp [h]
      · simp [h]; omega) l

theorem idxSum_eq_zero (l : List (ℕ × ℤ)) (i : ℕ) (h : ∀ p ∈ l, p.1 ≠ i) : idxSum l i = 0 := by
  unfold idxSum
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ite_eq_right (h p (by simp)), ih (fun q hq => h q (by simp [hq]))]
    simp

theorem idxSum_map_sub (s : ℕ) (l : List (ℕ × ℤ)) (i : ℕ) (h : ∀ p ∈ l, s ≤ p.1) (hi : s ≤ i) :
    idxSum (l.map (fun p => (p.1 - s, p.2))) (i - s) = idxSum l i := by
  unfold idxSum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have := h p hp
  simp only [Function.comp_apply]
  congr 1
  apply propext
  omega

theorem list_sum_map_sub_int {α : Type} (l : List α) (f g : α → ℤ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun a => f a - g a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    ring

theorem natAbs_toNat_le (c : ℤ) : c.toNat ≤ c.natAbs ∧ (-c).toNat ≤ c.natAbs := by
  omega

theorem toNat_sub_toNat (c : ℤ) : (c.toNat : ℤ) - ((-c).toNat : ℤ) = c := by
  omega

/-- Shifted packed vectors. -/
theorem sshl_spec {w k B : ℕ} {x : SVec} (hx : SBnd w (2 ^ k) B x) :
    SBnd w (2 ^ (k + 1)) B (sshl (w * 2 ^ k) x) ∧
      ∀ i, sval w (sshl (w * 2 ^ k) x) i = if 2 ^ k ≤ i then sval w x (i - 2 ^ k) else 0 := by
  have hpow : 2 ^ (w * 2 ^ (k + 1)) = 2 ^ (w * 2 ^ k) * 2 ^ (w * 2 ^ k) := by
    rw [← pow_add]; congr 1; rw [pow_succ]; ring
  have hlt : ∀ P, P < 2 ^ (w * 2 ^ k) → P <<< (w * 2 ^ k) < 2 ^ (w * 2 ^ (k + 1)) := by
    intro P hP
    rw [Nat.shiftLeft_eq, hpow]
    exact Nat.mul_lt_mul_of_pos_right hP (by positivity)
  refine ⟨⟨hlt _ hx.1, hlt _ hx.2.1, fun i hi => ?_⟩, fun i => ?_⟩
  · simp only [sshl]
    rw [fld_shiftLeft, fld_shiftLeft]
    split_ifs with h
    · exact hx.2.2 _ (by rw [pow_succ] at hi; omega)
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp only [sval, sshl]
    rw [fld_shiftLeft, fld_shiftLeft]
    split_ifs <;> simp

/-- Bounded packed vectors may be viewed with more fields; the new fields are zero. -/
theorem sbnd_extend {w k B : ℕ} {x : SVec} (hx : SBnd w (2 ^ k) B x) :
    SBnd w (2 ^ (k + 1)) B x ∧ ∀ i, 2 ^ k ≤ i → sval w x i = 0 := by
  have hle : 2 ^ (w * 2 ^ k) ≤ 2 ^ (w * 2 ^ (k + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
      (by norm_num) (by omega)))
  have z : ∀ i, 2 ^ k ≤ i → fld w x.1 i = 0 ∧ fld w x.2 i = 0 := fun i hi =>
    ⟨fld_eq_zero_of_lt w _ _ i hx.1 hi, fld_eq_zero_of_lt w _ _ i hx.2.1 hi⟩
  refine ⟨⟨lt_of_lt_of_le hx.1 hle, lt_of_lt_of_le hx.2.1 hle, fun i hi => ?_⟩, fun i hi => ?_⟩
  · by_cases h : i < 2 ^ k
    · exact hx.2.2 i h
    · rw [(z i (by omega)).1, (z i (by omega)).2]
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp only [sval]
    rw [(z i hi).1, (z i hi).2]
    simp

/-- The halving packer is exact. -/
theorem packR_spec (w : ℕ) : ∀ (k : ℕ) (l : List (ℕ × ℤ)), (∀ p ∈ l, p.1 < 2 ^ k) →
    absSum l < 2 ^ w →
    SBnd w (2 ^ k) (absSum l) (packR w k l) ∧ ∀ i < 2 ^ k, sval w (packR w k l) i = idxSum l i
  | k, [], _, _ => by
    have hz : packR w k [] = szero := by cases k <;> rfl
    rw [hz]
    refine ⟨SBnd_zero _ _ _, fun i _ => ?_⟩
    simp only [sval_zero, idxSum, List.map_nil, List.sum_nil]
  | 0, p :: l, hl, hS => by
    have h0 : ∀ q ∈ p :: l, q.1 = 0 := fun q hq => by have := hl q hq; simp at this; omega
    have hA : ((p :: l).map (fun p => p.2.toNat)).sum ≤ absSum (p :: l) := by
      unfold absSum
      exact List.sum_le_sum (fun q _ => (natAbs_toNat_le q.2).1)
    have hB : ((p :: l).map (fun p => (-p.2).toNat)).sum ≤ absSum (p :: l) := by
      unfold absSum
      exact List.sum_le_sum (fun q _ => (natAbs_toNat_le q.2).2)
    have f1 : ∀ P, P ≤ absSum (p :: l) → fld w P 0 = P := by
      intro P hP
      rw [fld_zero_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [pow_zero]
    refine ⟨⟨by simp only [packR, mul_one]; omega, by simp only [packR, mul_one]; omega,
      fun i hi => ?_⟩, fun i hi => ?_⟩
    · have : i = 0 := by omega
      subst this
      simp only [packR]
      rw [f1 _ hA, f1 _ hB]
      exact ⟨hA, hB⟩
    · have : i = 0 := by omega
      subst this
      simp only [sval, packR]
      rw [f1 _ hA, f1 _ hB]
      unfold idxSum
      rw [Nat.cast_list_sum, Nat.cast_list_sum, List.map_map, List.map_map, list_sum_map_sub_int]
      apply congrArg
      apply List.map_congr_left
      intro q hq
      simp only [Function.comp_apply, h0 q hq, ↓reduceIte]
      exact toNat_sub_toNat q.2
  | k + 1, p :: l, hl, hS => by
    set L := p :: l with hL
    set lo := L.filter (fun p => decide (p.1 < 2 ^ k)) with hlo
    set hi := (L.filter (fun p => decide (2 ^ k ≤ p.1))).map (fun p => (p.1 - 2 ^ k, p.2))
      with hhi
    have hsplit := absSum_split k L
    rw [← hlo, ← hhi] at hsplit
    have hlo1 : ∀ q ∈ lo, q.1 < 2 ^ k := by
      intro q hq
      rw [hlo, List.mem_filter] at hq
      simpa using hq.2
    have hhi1 : ∀ q ∈ hi, q.1 < 2 ^ k := by
      intro q hq
      rw [hhi, List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      rw [List.mem_filter] at hr
      have h1 := hl r hr.1
      have h2 : 2 ^ k ≤ r.1 := by simpa using hr.2
      rw [pow_succ] at h1
      simp only
      omega
    obtain ⟨a1, a2⟩ := packR_spec w k lo hlo1 (by omega)
    obtain ⟨b1, b2⟩ := packR_spec w k hi hhi1 (by omega)
    obtain ⟨e1, e2⟩ := sbnd_extend a1
    obtain ⟨s1, s2⟩ := sshl_spec b1
    obtain ⟨d1, d2⟩ := sadd_spec e1 s1 (by omega)
    have hpk : packR w (k + 1) L = sadd (packR w k lo) (sshl (w * 2 ^ k) (packR w k hi)) := by
      rw [hL, hlo, hhi]
      rfl
    rw [hpk, hsplit]
    refine ⟨d1, fun i hi' => ?_⟩
    rw [d2 i hi', s2 i, idxSum_split k L i, ← hlo]
    by_cases hik : 2 ^ k ≤ i
    · rw [ite_eq_left hik, e2 i hik, b2 _ (by rw [pow_succ] at hi'; omega), hhi,
        idxSum_map_sub _ _ _ (fun q hq => by rw [List.mem_filter] at hq; simpa using hq.2) hik,
        idxSum_eq_zero lo i (fun q hq => by have := hlo1 q hq; omega), zero_add]
    · rw [ite_eq_right hik, a2 i (by omega),
        idxSum_eq_zero (L.filter (fun p => decide (2 ^ k ≤ p.1))) i (fun q hq => by
          rw [List.mem_filter] at hq; have : 2 ^ k ≤ q.1 := by simpa using hq.2
          omega), add_zero]
/-! ## The octad Fourier matrix as a twisted Hadamard matrix -/

/-- The diagonal sign of the octad Fourier matrix. -/
def octD (e : ℕ) : ℤ := if identOctDiagTable.testBit (e % 64) then -1 else 1

/-- The twisted row index: complemented on rows of odd weight. -/
def octTw (e : ℕ) : ℕ := if bpar (e % 64) 6 then e % 64 ^^^ 63 else e % 64

theorem octTw_lt (e : ℕ) : octTw e < 64 := by
  unfold octTw
  have h : e % 64 < 64 := Nat.mod_lt _ (by norm_num)
  split_ifs
  · have : e % 64 ^^^ 63 < 2 ^ 6 := Nat.xor_lt_two_pow (by norm_num; omega) (by norm_num)
    simpa using this
  · exact h

set_option maxRecDepth 100000 in
/-- The octad Fourier signs: a diagonal sign times a twisted Hadamard sign. -/
theorem octMT_tw_fin : ∀ e f : Fin 64,
    octMT true e.val f.val = octD e.val * (if bpar (octTw e.val &&& f.val) 6 then -1 else 1) ∧
    octMT false e.val f.val = octD f.val * (if bpar (octTw e.val &&& f.val) 6 then -1 else 1) := by
  decide +kernel

theorem octMT_tw (fwd : Bool) (e f : ℕ) :
    octMT fwd e f = (if fwd then octD e else octD f) *
      (if bpar (octTw e &&& (f % 64)) 6 then -1 else 1) := by
  have h := octMT_tw_fin ⟨e % 64, Nat.mod_lt _ (by norm_num)⟩ ⟨f % 64, Nat.mod_lt _ (by norm_num)⟩
  have hM : ∀ b, octMT b (e % 64) (f % 64) = octMT b e f := by
    intro b
    simp only [octMT, Nat.mod_mod]
  have hD : ∀ x, octD (x % 64) = octD x := by
    intro x
    simp only [octD, Nat.mod_mod]
  have hT : octTw (e % 64) = octTw e := by
    simp only [octTw, Nat.mod_mod]
  simp only [hM, hD, hT] at h
  cases fwd
  · simpa using h.2
  · simpa using h.1

/-! ## Walsh-Hadamard values on octad blocks -/

theorem whtVal_congr (y y' : ℕ → ℤ) (n t : ℕ)
    (h : ∀ u < 2 ^ n, y (t / 2 ^ n * 2 ^ n + u) = y' (t / 2 ^ n * 2 ^ n + u)) :
    whtVal y n t = whtVal y' n t := by
  unfold whtVal
  apply Finset.sum_congr rfl
  intro u hu
  rw [h u (Finset.mem_range.mp hu)]

theorem whtVal_block (y : ℕ → ℤ) (o e : ℕ) (he : e < 64) :
    whtVal y 6 (64 * o + e) =
      ∑ u ∈ Finset.range 64, (if bpar (e &&& u) 6 then -1 else 1) * y (64 * o + u) := by
  unfold whtVal
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [h64]
  apply Finset.sum_congr rfl
  intro u hu
  have hb : (64 * o + e) / 64 * 64 = 64 * o := by omega
  have hp : bpar ((64 * o + e) &&& u) 6 = bpar (e &&& u) 6 := by
    apply bpar_congr
    intro i hi
    rw [Nat.testBit_and, Nat.testBit_and]
    have he' : e < 2 ^ 6 := by norm_num; omega
    have : 64 * o + e = 2 ^ 6 * o + e := by norm_num
    rw [this, Nat.testBit_two_pow_mul_add o he', ite_eq_left hi]
  rw [hb, hp]

/-- A weighted block sum of index sums, as a sum over the terms. -/
theorem sum_block_idx (g : ℕ → ℤ) (o : ℕ) : ∀ l : List (ℕ × ℤ),
    ∑ u ∈ Finset.range 64, g u * idxSum l (64 * o + u) =
      (l.map (fun p => if p.1 / 64 = o then p.2 * g (p.1 % 64) else 0)).sum
  | [] => by simp [idxSum]
  | p :: l => by
    have hs : ∀ u, idxSum (p :: l) (64 * o + u) =
        (if p.1 = 64 * o + u then p.2 else 0) + idxSum l (64 * o + u) := by
      intro u
      simp [idxSum]
    simp only [hs, mul_add, Finset.sum_add_distrib, sum_block_idx g o l, List.map_cons,
      List.sum_cons]
    congr 1
    by_cases h : p.1 / 64 = o
    · rw [ite_eq_left h, Finset.sum_eq_single (p.1 % 64)]
      · have : p.1 = 64 * o + p.1 % 64 := by omega
        rw [ite_eq_left this]
        ring
      · intro u hu hne
        have hu' := Finset.mem_range.mp hu
        rw [ite_eq_right (by omega : ¬ p.1 = 64 * o + u), mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))) hnot
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro u hu
      have hu' := Finset.mem_range.mp hu
      rw [ite_eq_right (by omega : ¬ p.1 = 64 * o + u), mul_zero]

/-- Octad blocks as flat terms with index `64 o + e`. -/
theorem octFlat_blocks (o : ℕ) (F : ℕ → ℤ) (hF : ∀ x, F (x % 64) = F x) :
    ∀ bs : List (ℕ × List (ℕ × ℤ)),
    (bs.map (fun b => if b.1 = o then (b.2.map (fun q => q.2 * F q.1)).sum else 0)).sum =
      ((bs.flatMap (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2)))).map
        (fun p => if p.1 / 64 = o then p.2 * F (p.1 % 64) else 0)).sum
  | [] => by simp
  | b :: bs => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, ← octFlat_blocks o F hF bs,
      List.map_cons, List.sum_cons, List.map_map]
    congr 1
    have hq : ∀ q : ℕ × ℤ, (64 * b.1 + q.1 % 64) / 64 = b.1 ∧
        (64 * b.1 + q.1 % 64) % 64 = q.1 % 64 := by
      intro q
      omega
    split_ifs with h
    · congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      rw [(hq q).1, (hq q).2, ite_eq_left h, hF]
    · rw [List.map_congr_left (g := fun _ => (0 : ℤ)) (fun q _ => by
        simp only [Function.comp_apply, (hq q).1, h, ↓reduceIte])]
      simp

/-! ## The packed octad transform -/

/-- The octad terms of a vector, as flat terms with index `64 o + e`. -/
def octLFlat (L : IdentVec) : List (ℕ × ℤ) :=
  L.sh.oct.flatMap (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2)))

/-- The applicability check of the packed octad transform at field width `w`. -/
def octPackOk (w : ℕ) (L : IdentVec) : Bool :=
  (octLFlat L).all (fun p => decide (p.1 < 2 ^ 16)) && decide (4 ^ 6 * absSum (octLFlat L) < 2 ^ w)

/-- The packed octad terms (with diagonal signs for the inverse transform). -/
def octPackIn (w : ℕ) (fwd : Bool) (L : IdentVec) : SVec :=
  if fwd then packR w 16 (octLFlat L)
  else sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) (packR w 16 (octLFlat L))

/-- The packed Walsh-Hadamard transform of the octad terms. -/
def octPackX (w : ℕ) (fwd : Bool) (L : IdentVec) : SVec := whtP w (octPackIn w fwd L) 6

theorem octPackOk_spec (w : ℕ) (L : IdentVec) (hok : octPackOk w L = true) :
    (∀ p ∈ octLFlat L, p.1 < 2 ^ 16) ∧ 4 ^ 6 * absSum (octLFlat L) < 2 ^ w := by
  simp only [octPackOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  exact hok

theorem octPackIn_spec (w : ℕ) (fwd : Bool) (L : IdentVec) (hok : octPackOk w L = true) :
    SBnd w (2 ^ 16) (absSum (octLFlat L)) (octPackIn w fwd L) ∧
      ∀ t < 2 ^ 16, sval w (octPackIn w fwd L) t =
        (if fwd then 1 else octD t) * idxSum (octLFlat L) t := by
  obtain ⟨h1, h2⟩ := octPackOk_spec w L hok
  have hS : absSum (octLFlat L) < 2 ^ w := by omega
  obtain ⟨a1, a2⟩ := packR_spec w 16 (octLFlat L) h1 hS
  cases fwd
  · obtain ⟨f1, f2⟩ := sflip_spec a1 (rep64 w identOctDiagTable)
      (fun t => identOctDiagTable.testBit (t % 64) = true) (rep64_isFieldMask w _) hS
    refine ⟨f1, fun t ht => ?_⟩
    simp only [octPackIn, Bool.false_eq_true, ↓reduceIte]
    rw [f2 t ht, a2 t ht]
    unfold octD
    split_ifs <;> ring
  · refine ⟨a1, fun t ht => ?_⟩
    simp only [octPackIn, ↓reduceIte, one_mul]
    exact a2 t ht

theorem octPackX_spec (w : ℕ) (fwd : Bool) (L : IdentVec) (hok : octPackOk w L = true) :
    SBnd w (2 ^ 16) (4 ^ 6 * absSum (octLFlat L)) (octPackX w fwd L) ∧
      ∀ t < 2 ^ 16, sval w (octPackX w fwd L) t =
        whtVal (fun s => (if fwd then 1 else octD s) * idxSum (octLFlat L) s) 6 t := by
  obtain ⟨_, h2⟩ := octPackOk_spec w L hok
  obtain ⟨a1, a2⟩ := octPackIn_spec w fwd L hok
  obtain ⟨b1, b2⟩ := whtP_spec w _ _ a1 h2 6 le_rfl
  refine ⟨b1, fun t ht => ?_⟩
  unfold octPackX
  rw [b2 t ht]
  apply whtVal_congr
  intro u hu
  apply a2
  have : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [this] at hu ⊢
  have : (2 : ℕ) ^ 16 = 65536 := by norm_num
  rw [this] at ht ⊢
  omega

/-- Signed field extraction by shift and mask. -/
def svalS (w : ℕ) (x : SVec) (i : ℕ) : ℤ := (fldS w x.1 i : ℤ) - (fldS w x.2 i : ℤ)

/-- The integer octad coordinate of a triality image from the packed transform. -/
def octZ (w : ℕ) (fwd : Bool) (X : SVec) (o e : ℕ) : ℤ :=
  (if fwd then octD e else 1) * svalS w X (64 * o + octTw e)

/-- The packed octad coordinate is the integer octad coordinate. -/
theorem octZ_eq (w : ℕ) (fwd : Bool) (L : IdentVec) (hok : octPackOk w L = true) (o e : ℕ) :
    octZ w fwd (octPackX w fwd L) o e =
      (L.sh.oct.map (fun b => if b.1 = o then
        (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum := by
  have hF : ∀ x, octMT fwd e (x % 64) = octMT fwd e x := by
    intro x
    simp only [octMT, Nat.mod_mod]
  have hflat : (L.sh.oct.map (fun b => if b.1 = o then
      (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum =
      ((octLFlat L).map (fun p => if p.1 / 64 = o then p.2 * octMT fwd e (p.1 % 64) else 0)).sum :=
    octFlat_blocks o (octMT fwd e) hF L.sh.oct
  rw [hflat]
  obtain ⟨h1, _⟩ := octPackOk_spec w L hok
  obtain ⟨b1, b2⟩ := octPackX_spec w fwd L hok
  have hs : svalS w (octPackX w fwd L) (64 * o + octTw e) =
      sval w (octPackX w fwd L) (64 * o + octTw e) := by
    simp only [svalS, sval, fldS_eq]
  unfold octZ
  rw [hs]
  have htw := octTw_lt e
  by_cases ho : o < 1024
  · have ht : 64 * o + octTw e < 2 ^ 16 := by norm_num; omega
    rw [b2 _ ht, whtVal_block _ o _ htw, Finset.mul_sum]
    have key : ∀ u ∈ Finset.range 64,
        (if fwd then octD e else 1) * ((if bpar (octTw e &&& u) 6 then -1 else 1) *
          ((if fwd then 1 else octD (64 * o + u)) * idxSum (octLFlat L) (64 * o + u))) =
        octMT fwd e u * idxSum (octLFlat L) (64 * o + u) := by
      intro u hu
      have hu' : u < 64 := Finset.mem_range.mp hu
      rw [octMT_tw fwd e u, Nat.mod_eq_of_lt hu']
      have hD : octD (64 * o + u) = octD u := by
        unfold octD
        rw [show (64 * o + u) % 64 = u % 64 by omega]
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte, hD]
        ring
      · simp only [↓reduceIte]
        ring
    rw [Finset.sum_congr rfl key, sum_block_idx]
  · have ht : 2 ^ 16 ≤ 64 * o + octTw e := by norm_num; omega
    have z1 := fld_eq_zero_of_lt w _ _ _ b1.1 ht
    have z2 := fld_eq_zero_of_lt w _ _ _ b1.2.1 ht
    simp only [sval, z1, z2, Nat.cast_zero, sub_zero, mul_zero]
    symm
    rw [List.map_congr_left (g := fun _ => (0 : ℤ)) (fun p hp => by
      have := h1 p hp
      rw [ite_eq_right (by norm_num at this; omega)])]
    simp

/-! ## The short part and the pairing with the packed octad transform -/

/-- The short part with the octad terms from the packed transform (field width `w`); falls back
to `triShortF` when the packed transform does not apply. -/
def triShortO (w : ℕ) (fwd : Bool) (L W : IdentVec) : ℚ :=
  if octPackOk w L then
    W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
      L.sden * (((W.sh.oct.map (fun b => (b.2.map (fun q =>
        q.2 * octZ w fwd (octPackX w fwd L) b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8 +
      (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum)
  else triShortF fwd L W

theorem triShortG_eq_F (fwd : Bool) (L W : IdentVec) : triShortG fwd L W = triShortF fwd L W := by
  have h3 : ∀ o e, triOctT fwd L o e = triOctF fwd L o e := by
    intro o e
    rw [triOctT_eq]
    simp only [triOctF, triOctQ, octMF_eq]
  simp only [triShortG, triShortF, h3]

theorem octSum_cast (Z : ℕ → ℕ → ℤ) (c : ℚ) : ∀ bs : List (ℕ × List (ℕ × ℤ)),
    (bs.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * (c * (Z b.1 q.1 : ℚ) / 8))).sum)).sum =
      c * (((bs.map (fun b => (b.2.map (fun q => q.2 * Z b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8
  | [] => by simp
  | b :: bs => by
    have inner : ∀ qs : List (ℕ × ℤ),
        (qs.map (fun q => (q.2 : ℚ) * (c * (Z b.1 q.1 : ℚ) / 8))).sum =
          c * (((qs.map (fun q => q.2 * Z b.1 q.1)).sum : ℤ) : ℚ) / 8 := by
      intro qs
      induction qs with
      | nil => simp
      | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, ih]
        ring
    simp only [List.map_cons, List.sum_cons, Int.cast_add, inner, octSum_cast Z c bs]
    ring

/-- The packed-octad short part is the fast short part. -/
theorem triShortO_eq (w : ℕ) (fwd : Bool) (L W : IdentVec) :
    triShortO w fwd L W = triShortF fwd L W := by
  unfold triShortO
  split_ifs with h
  · rw [← triShortG_eq_F]
    unfold triShortG
    have ht : ∀ o e, triOctT fwd L o e =
        L.sden * ((octZ w fwd (octPackX w fwd L) o e : ℤ) : ℚ) / 8 := by
      intro o e
      unfold triOctT
      rw [octZ_eq w fwd L h o e]
    have hB : (W.sh.oct.map (fun b =>
        (b.2.map (fun q => (q.2 : ℚ) * triOctT fwd L b.1 q.1)).sum)).sum =
        L.sden * (((W.sh.oct.map (fun b => (b.2.map (fun q =>
          q.2 * octZ w fwd (octPackX w fwd L) b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8 := by
      simp only [ht]
      exact octSum_cast _ _ _
    rw [hB]
  · rfl

/-- The packed pairing with the packed octad transform (octad field width `wo`). -/
def pairTriO (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortO wo fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdot w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- The packed-octad pairing is the packed pairing. -/
theorem pairTriO_eq (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) :
    pairTriO wo w fwd L W X Y D E = pairTriP w fwd L W X Y D E := by
  unfold pairTriO pairTriP
  rw [triShortO_eq]

/-- Forward identification from the packed-octad pairing. -/
theorem ident_forward_packedO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriO wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward_packed i j h g L W hL hW hLt hWt hX hB hx hy (by rw [← pairTriO_eq wo, hp])

/-- Inverse identification from the packed-octad pairing. -/
theorem ident_inverse_packedO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriO wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse_packed i j h g L W hL hW hLt hWt hX hB hx hy (by rw [← pairTriO_eq wo, hp])

/-- A forward packed-octad identification places the image in the union of the local orbits. -/
theorem ident_forward_packedO_mem (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriO wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g
    (ident_forward_packedO i j h g L W hL hW hLt hWt hX hB hx hy hp)

/-- An inverse packed-octad identification places the image in the union of the local orbits. -/
theorem ident_inverse_packedO_mem (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriO wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g
    (ident_inverse_packedO i j h g L W hL hW hLt hWt hX hB hx hy hp)
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
