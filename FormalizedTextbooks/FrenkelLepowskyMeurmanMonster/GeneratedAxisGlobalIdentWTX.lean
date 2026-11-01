/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentRespace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiOp

/-! # Factory: normalized word-image tensors (gident2)

The packed tensors of word images (`tensorPlanF` / `tensorWordAll`) are expensive to evaluate in
the kernel, and every identification part that reads them evaluates them again.  The factory
stores the net field values of such a tensor as a compact literal: `k`-bit positive and negative
parts of the values divided by `2 ^ m`, re-spaced to field width `w` with the factor `2 ^ m`
restored (`respaceS`, grecip's `respace` with shifted leaves).  One cross-sum check per column
against the computed tensor (grecip's `tensorRat_eq_of_cross`) gives the same rational tensor
(`tensorN_ten`), so the parts evaluate no word image at all. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- Re-space `2 ^ d` fields of `k` bits into fields of `w` bits, each multiplied by `2 ^ m`. -/
def respaceS (k w m : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x <<< m
  | d + 1, x => respaceS k w m d (x % 2 ^ (k * 2 ^ d)) |||
      (respaceS k w m d (x >>> (k * 2 ^ d)) <<< (w * 2 ^ d))

/-- Bounds and fields of a shifted re-spaced number. -/
theorem respaceS_spec (k w m : ℕ) (hkw : k + m ≤ w) : ∀ (d x : ℕ), x < 2 ^ (k * 2 ^ d) →
    respaceS k w m d x < 2 ^ (w * 2 ^ d) ∧
      ∀ i, fld w (respaceS k w m d x) i = if i < 2 ^ d then fld k x i * 2 ^ m else 0
  | 0, x, hx => by
    simp only [respaceS, pow_zero, mul_one] at hx ⊢
    have hxm : x <<< m < 2 ^ w := by
      rw [Nat.shiftLeft_eq]
      calc x * 2 ^ m < 2 ^ k * 2 ^ m := Nat.mul_lt_mul_of_pos_right hx (by positivity)
        _ = 2 ^ (k + m) := by rw [pow_add]
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hkw
    refine ⟨hxm, fun i => ?_⟩
    split_ifs with hi
    · have : i = 0 := by omega
      subst this
      simp only [fld, mul_zero, pow_zero, Nat.div_one]
      rw [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hx, Nat.shiftLeft_eq]
    · exact fld_eq_zero_of_lt (m := 1) (by simpa using hxm) (by omega)
  | d + 1, x, hx => by
    have hlo : x % 2 ^ (k * 2 ^ d) < 2 ^ (k * 2 ^ d) := Nat.mod_lt _ (by positivity)
    have hhi : x >>> (k * 2 ^ d) < 2 ^ (k * 2 ^ d) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      calc x < 2 ^ (k * 2 ^ (d + 1)) := hx
        _ = 2 ^ (k * 2 ^ d + k * 2 ^ d) := by rw [pow_succ]; ring_nf
    obtain ⟨a1, a2⟩ := respaceS_spec k w m hkw d _ hlo
    obtain ⟨b1, b2⟩ := respaceS_spec k w m hkw d _ hhi
    simp only [respaceS]
    constructor
    · apply Nat.or_lt_two_pow
      · calc _ < 2 ^ (w * 2 ^ d) := a1
          _ ≤ 2 ^ (w * 2 ^ (d + 1)) := Nat.pow_le_pow_right (by norm_num)
              (Nat.mul_le_mul_left w (Nat.pow_le_pow_right (by norm_num) (by omega)))
      · rw [Nat.shiftLeft_eq]
        calc _ < 2 ^ (w * 2 ^ d) * 2 ^ (w * 2 ^ d) :=
              Nat.mul_lt_mul_of_pos_right b1 (by positivity)
          _ = 2 ^ (w * 2 ^ (d + 1)) := by rw [← pow_add, pow_succ]; ring_nf
    · intro i
      rw [fld_lor, fld_shiftLeft, a2, b2]
      by_cases h1 : i < 2 ^ d
      · have h2 : i < 2 ^ (d + 1) := by rw [pow_succ]; omega
        simp only [h1, h2, ↓reduceIte, show ¬ (2 ^ d ≤ i) by omega, Nat.or_zero]
        rw [fld_mod_pow h1]
      · simp only [h1, ↓reduceIte, show 2 ^ d ≤ i by omega, Nat.zero_or]
        by_cases h3 : i - 2 ^ d < 2 ^ d
        · have h2 : i < 2 ^ (d + 1) := by rw [pow_succ]; omega
          simp only [h3, h2, ↓reduceIte]
          rw [fld_shiftRight]
          congr 2
          omega
        · have h2 : ¬ i < 2 ^ (d + 1) := by rw [pow_succ]; omega
          simp only [h3, h2, ↓reduceIte]

/-- A column re-spaced from compact `k`-bit fields with the factor `2 ^ m`: bounds and values. -/
theorem respaceS_col {k w m : ℕ} (hkw : k + m ≤ w) {P N : ℕ} (hP : P < 2 ^ (k * 2 ^ 12))
    (hN : N < 2 ^ (k * 2 ^ 12)) :
    SBnd w (2 ^ 12) ((2 ^ k - 1) * 2 ^ m) (respaceS k w m 12 P, respaceS k w m 12 N) ∧
      ∀ t < 2 ^ 12, sval w (respaceS k w m 12 P, respaceS k w m 12 N) t =
        ((fld k P t : ℤ) - fld k N t) * 2 ^ m := by
  obtain ⟨p1, p2⟩ := respaceS_spec k w m hkw 12 _ hP
  obtain ⟨n1, n2⟩ := respaceS_spec k w m hkw 12 _ hN
  refine ⟨⟨p1, n1, fun t ht => ?_⟩, fun t ht => ?_⟩
  · simp only [p2, n2, ht, ↓reduceIte]
    have a := fld_lt k P t
    have b := fld_lt k N t
    have e : (2 ^ k - 1) * 2 ^ m = 2 ^ k * 2 ^ m - 2 ^ m := by
      rw [Nat.sub_mul, one_mul]
    constructor
    · calc fld k P t * 2 ^ m ≤ (2 ^ k - 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := le_refl _
    · calc fld k N t * 2 ^ m ≤ (2 ^ k - 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := le_refl _
  · simp only [sval, p2, n2, ht, ↓reduceIte]
    push_cast
    ring

/-- A normalized tensor: compact columns `P`, `N` (`k`-bit fields of the values divided by
`2 ^ m`) at field width `w`. -/
def tensorN (k w m : ℕ) (P N : List ℕ) : List SVec :=
  (List.range 24).map (fun j => (respaceS k w m 12 (P.getD j 0), respaceS k w m 12 (N.getD j 0)))

/-- The size check of the compact columns. -/
def tensorNSize (k : ℕ) (P N : List ℕ) : Bool :=
  (List.range 24).all (fun j => decide (P.getD j 0 < 2 ^ (k * 2 ^ 12)) &&
    decide (N.getD j 0 < 2 ^ (k * 2 ^ 12)))

/-- The field bound of a normalized tensor. -/
theorem tensorN_bnd {k w m : ℕ} (hkw : k + m ≤ w) {P N : List ℕ} (hs : tensorNSize k P N = true) :
    TBnd w ((2 ^ k - 1) * 2 ^ m) (tensorN k w m P N) := by
  intro j hj
  simp only [tensorNSize, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hs
  rw [tensorN, tcol_range_map _ 24 j hj]
  exact (respaceS_col hkw (hs j hj).1 (hs j hj).2).1

/-- The cross-sum check of a normalized tensor against a packed tensor. -/
def tensorNCross (w k m : ℕ) (P N : List ℕ) (X : List SVec) : Bool :=
  (List.range 24).all (fun j =>
    (tcol (tensorN k w m P N) j).1 + (tcol X j).2 == (tcol X j).1 + (tcol (tensorN k w m P N) j).2)

/-- A checked normalized tensor has the rational tensor of the packed tensor. -/
theorem tensorN_ten {k w m B : ℕ} (hkw : k + m ≤ w) {P N : List ℕ} {X : List SVec}
    (hs : tensorNSize k P N = true) (hX : TBnd w B X) (hkB : (2 ^ k - 1) * 2 ^ m ≤ B)
    (hB : 2 * B < 2 ^ w) (hc : tensorNCross w k m P N X = true) (D : ℚ) :
    tensorRat w (tensorN k w m P N) D = tensorRat w X D :=
  tensorRat_eq_of_cross (fun j hj => (tensorN_bnd hkw hs j hj).mono hkB) hX hB hc D

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
