/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri

/-! # Compact packed tensors and their widening

Packed tensors whose numerators are small can be stored with narrow fields. `twWidenT wc w X`
re-spaces every column of `X` from fields of width `wc` to fields of width `w` (by halving), so
that a compact literal can enter packed computations of any width: the rational tensor and the
field bound `2 ^ wc - 1` are preserved (`twWidenT_rat`, `twWidenT_bnd`).

`twColCheck` compares the signed field values of all columns of two packed tensors up to a scale
factor by one equality of packed numbers per column (no carries under the field bounds; unpacked
lists and decidable list equality are avoided, being very costly in the kernel);
`twColCheck_rat` turns a successful check into an equality of rational tensors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-! ## Widening -/

/-- Re-space the first `2 ^ m` fields of width `wc` to fields of width `w` (by halving). -/
def twWiden (wc w : ℕ) : ℕ → ℕ → ℕ
  | 0, P => P &&& ((1 <<< wc) - 1)
  | m + 1, P => twWiden wc w m (P &&& ((1 <<< (wc * (1 <<< m))) - 1)) |||
      (twWiden wc w m (P >>> (wc * (1 <<< m))) <<< (w * (1 <<< m)))

/-- Fields above the bound of a number vanish. -/
theorem twFld_hi (w n A k : ℕ) (hA : A < 2 ^ (w * n)) (hk : n ≤ k) : fld w A k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, Nat.zero_testBit]
  by_cases hb : b < w
  · simp only [hb, decide_true, Bool.true_and]
    apply Nat.testBit_lt_two_pow
    calc A < 2 ^ (w * n) := hA
      _ ≤ 2 ^ (w * k + b) :=
        Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.mul_le_mul_left w hk) le_self_add)
  · simp [hb]

/-- Widened numbers have `2 ^ m` fields of width `w`. -/
theorem twWiden_lt (wc w : ℕ) (hw : wc ≤ w) : ∀ (m P : ℕ), twWiden wc w m P < 2 ^ (w * 2 ^ m)
  | 0, P => by
    simp only [twWiden, Nat.one_shiftLeft, pow_zero, mul_one]
    calc P &&& (2 ^ wc - 1) ≤ 2 ^ wc - 1 := Nat.and_le_right
      _ < 2 ^ wc := Nat.sub_lt (by positivity) one_pos
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  | m + 1, P => by
    rw [twWiden]
    simp only [Nat.one_shiftLeft]
    have h1 := twWiden_lt wc w hw m (P &&& (2 ^ (wc * 2 ^ m) - 1))
    have h2 := twWiden_lt wc w hw m (P >>> (wc * 2 ^ m))
    have e : w * 2 ^ (m + 1) = w * 2 ^ m + w * 2 ^ m := by rw [pow_succ]; ring
    rw [e]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) le_self_add)
    · rw [Nat.shiftLeft_eq, pow_add]
      exact Nat.mul_lt_mul_of_pos_right h2 (by positivity)

/-- The fields of a widened number are the narrow fields. -/
theorem twWiden_fld (wc w : ℕ) (hw : wc ≤ w) :
    ∀ (m P k : ℕ), k < 2 ^ m → fld w (twWiden wc w m P) k = fld wc P k
  | 0, P, k, hk => by
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [twWiden, Nat.one_shiftLeft]
    rw [fld_zero_right, fld_zero_right, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) hw))
  | m + 1, P, k, hk => by
    rw [twWiden]
    simp only [Nat.one_shiftLeft]
    have hA := twWiden_lt wc w hw m (P &&& (2 ^ (wc * 2 ^ m) - 1))
    rw [fld_lor, fld_shiftLeft]
    by_cases hkm : k < 2 ^ m
    · have hn : ¬ (2 ^ m ≤ k) := by omega
      rw [twWiden_fld wc w hw m _ k hkm, twFld_low wc (2 ^ m) P k hkm]
      simp [hn]
    · have hn : 2 ^ m ≤ k := by omega
      have hk' : k - 2 ^ m < 2 ^ m := by rw [pow_succ] at hk; omega
      rw [twFld_hi w (2 ^ m) _ k hA hn, twWiden_fld wc w hw m _ _ hk', fld_shiftRight]
      simp only [hn, ↓reduceIte, Nat.zero_or]
      congr 1
      omega

/-- A widened signed packed vector. -/
def twWidenS (wc w : ℕ) (x : SVec) : SVec := (twWiden wc w 12 x.1, twWiden wc w 12 x.2)

/-- A widened packed tensor. -/
def twWidenT (wc w : ℕ) (X : List SVec) : List SVec :=
  (List.range 24).map (fun j => twWidenS wc w (tcol X j))

/-- Widening keeps the signed field values. -/
theorem twWidenT_sval (wc w : ℕ) (hw : wc ≤ w) (X : List SVec) (j : ℕ) (hj : j < 24) (k : ℕ)
    (hk : k < 4096) : sval w (tcol (twWidenT wc w X) j) k = sval wc (tcol X j) k := by
  rw [twWidenT, tcol_range_map _ 24 j hj]
  simp only [sval, twWidenS]
  rw [twWiden_fld wc w hw 12 _ k hk, twWiden_fld wc w hw 12 _ k hk]

/-- Widening keeps the rational tensor. -/
theorem twWidenT_rat (wc w : ℕ) (hw : wc ≤ w) (X : List SVec) (D : ℚ) :
    tensorRat w (twWidenT wc w X) D = tensorRat wc X D := by
  funext k i
  simp only [tensorRat]
  rw [twWidenT_sval wc w hw X i.val i.isLt k.val k.isLt]

/-- Widened tensors satisfy the narrow field bound. -/
theorem twWidenT_bnd (wc w : ℕ) (hw : wc ≤ w) (X : List SVec) :
    TBnd w (2 ^ wc - 1) (twWidenT wc w X) := by
  intro j hj
  rw [twWidenT, tcol_range_map _ 24 j hj]
  refine ⟨twWiden_lt wc w hw 12 _, twWiden_lt wc w hw 12 _, fun k hk => ?_⟩
  simp only [twWidenS]
  rw [twWiden_fld wc w hw 12 _ k hk, twWiden_fld wc w hw 12 _ k hk]
  exact ⟨Nat.le_sub_one_of_lt (fld_lt wc _ k), Nat.le_sub_one_of_lt (fld_lt wc _ k)⟩

/-! ## Comparing packed tensors -/

/-- All columns of `A` (width `w`) are `c` times the columns of `L` (width `wc`): one equality of
packed numbers per column, `A⁺ + c L⁻ = A⁻ + c L⁺` with `L` widened to width `w`. -/
def twColCheck (w wc c : ℕ) (A L : List SVec) : Bool :=
  (List.range 24).all (fun j => Nat.beq ((tcol A j).1 + c * twWiden wc w 12 (tcol L j).2)
    ((tcol A j).2 + c * twWiden wc w 12 (tcol L j).1))

/-- Fields of `P + c Q` without carries. -/
theorem twFld_addMul (w c BA wc : ℕ) (P Q : ℕ) (hP : P < 2 ^ (w * 4096))
    (hPf : ∀ k < 4096, fld w P k ≤ BA) (hQ : Q < 2 ^ (w * 4096))
    (hQf : ∀ k < 4096, fld w Q k ≤ 2 ^ wc - 1) (hB : BA + c * (2 ^ wc - 1) < 2 ^ w)
    (k : ℕ) (hk : k < 4096) : fld w (P + c * Q) k = fld w P k + c * fld w Q k := by
  have hm := fld_mul w c 4096 Q hQ (fun i hi =>
    lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left c (hQf i hi)) (Nat.le_add_left _ _)) hB)
  have ha := fld_add w 4096 P (c * Q) hP hm.1 (fun i hi => by
    rw [hm.2 i hi]
    exact lt_of_le_of_lt (Nat.add_le_add (hPf i hi) (Nat.mul_le_mul_left c (hQf i hi))) hB)
  rw [ha.2 k hk, hm.2 k hk]

/-- A successful column check compares all signed field values. -/
theorem twColCheck_sval (w wc c BA : ℕ) (A L : List SVec) (hw : wc ≤ w) (hA : TBnd w BA A)
    (hB : BA + c * (2 ^ wc - 1) < 2 ^ w) (h : twColCheck w wc c A L = true)
    (j : ℕ) (hj : j < 24) (k : ℕ) (hk : k < 4096) :
    sval w (tcol A j) k = c * sval wc (tcol L j) k := by
  simp only [twColCheck, List.all_eq_true, List.mem_range] at h
  have he := Nat.eq_of_beq_eq_true (h j hj)
  obtain ⟨hA1, hA2, hAf⟩ := hA j hj
  have hW : ∀ P : ℕ, twWiden wc w 12 P < 2 ^ (w * 4096) := fun P => by
    have := twWiden_lt wc w hw 12 P
    norm_num at this ⊢
    exact this
  have hWf : ∀ P : ℕ, ∀ i < 4096, fld w (twWiden wc w 12 P) i ≤ 2 ^ wc - 1 := fun P i hi => by
    rw [twWiden_fld wc w hw 12 P i hi]
    exact Nat.le_sub_one_of_lt (fld_lt wc P i)
  have hk' : k < 2 ^ 12 := by norm_num; exact hk
  have hA1' : (tcol A j).1 < 2 ^ (w * 4096) := by norm_num at hA1; exact hA1
  have hA2' : (tcol A j).2 < 2 ^ (w * 4096) := by norm_num at hA2; exact hA2
  have e1 := twFld_addMul w c BA wc (tcol A j).1 (twWiden wc w 12 (tcol L j).2) hA1'
    (fun i hi => (hAf i (by norm_num; exact hi)).1) (hW _) (hWf _) hB k hk
  have e2 := twFld_addMul w c BA wc (tcol A j).2 (twWiden wc w 12 (tcol L j).1) hA2'
    (fun i hi => (hAf i (by norm_num; exact hi)).2) (hW _) (hWf _) hB k hk
  have e3 : fld w ((tcol A j).1 + c * twWiden wc w 12 (tcol L j).2) k =
      fld w ((tcol A j).2 + c * twWiden wc w 12 (tcol L j).1) k := by rw [he]
  rw [e1, e2, twWiden_fld wc w hw 12 _ k hk', twWiden_fld wc w hw 12 _ k hk'] at e3
  simp only [sval]
  have e4 : ((fld w (tcol A j).1 k + c * fld wc (tcol L j).2 k : ℕ) : ℤ) =
      ((fld w (tcol A j).2 k + c * fld wc (tcol L j).1 k : ℕ) : ℤ) := by rw [e3]
  push_cast at e4
  linarith

/-- A successful column check gives the equality of the rational tensors (with the scale in the
denominators). -/
theorem twColCheck_rat (w wc c BA : ℕ) (A L : List SVec) (hw : wc ≤ w) (hA : TBnd w BA A)
    (hB : BA + c * (2 ^ wc - 1) < 2 ^ w) (h : twColCheck w wc c A L = true)
    (D E : ℚ) (hc : (c : ℚ) ≠ 0) (hD : D = c * E) :
    tensorRat w A D = tensorRat wc L E := by
  funext k i
  simp only [tensorRat]
  rw [twColCheck_sval w wc c BA A L hw hA hB h i.val i.isLt k.val k.isLt, hD]
  push_cast
  rw [mul_div_mul_left _ _ hc]

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
