/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BeattyOctalGame
public import MathlibExt.NumberTheory.BronzeMetallicIdentities
import MathlibExt.NumberTheory.DiophantineApproximation.ThreeGap
import Mathlib.Tactic.LinearCombination

/-!
# P-positions of the bronze game

For the Beatty octal game with ratios $(3+\sqrt{13})/2$ and $(5+\sqrt{13})/6$, the empty heap and
heaps of sizes $B_{2k+1}$, $C_{2k+2}$ and $D_{2k+2}$ ($k \ge 0$) form a stable and absorbing set.
Here $B$, $C$ and $D$ denote the bronze sequence and its first and second companion sequences.
Instead of the paper's numeration argument, we characterize the positive positions as strict
record lows of the fractional parts of $x(\sqrt{13}-3)/2$ for positive integers $x$.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Proposition 3 and Theorem 11.
* S. Beatty, *Problem 3173*, American Mathematical Monthly 33 (1926), no. 3, p. 159
  (the partition of the positive integers by complementary Beatty sequences).
* `MathlibExt.NumberTheory.DiophantineApproximation.ThreeGap`: the fractional-part lemmas
  `threeGap_fract_pos`, `threeGap_fract_sub_of_le`, and `threeGap_fract_sub_of_lt`.
-/

namespace MetaMathlibExt

local notation "B" => lucasU bronzeLucasParams
local notation "α" => ((3 + Real.sqrt 13) / 2)
local notation "β" => ((5 + Real.sqrt 13) / 6)
local notation "γ" => ((Real.sqrt 13 - 3) / 2)

private theorem gamma_bounds : 0 < γ ∧ γ < 1 / 3 := by
  have hlo : 3 < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 13 < 11 / 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

private theorem alpha_mul_gamma : α * γ = 1 := by
  linear_combination (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)) / 4

private theorem alpha_inv : α⁻¹ = γ :=
  inv_eq_of_mul_eq_one_right alpha_mul_gamma

private theorem beta_inv : β⁻¹ = 1 - γ := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -(Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)) / 12

private theorem gamma_irrational : Irrational γ := by
  have hs := (by decide : Nat.Prime 13).irrational_sqrt
  simpa using (hs.sub_intCast 3).div_ratCast (q := 2) (by norm_num)

private noncomputable def bronzeFract (x : ℤ) : ℝ := Int.fract ((x : ℝ) * γ)

-- Membership in the first sequence means the next integer above xγ is below (x+1)γ.
private theorem beatty_alpha_iff {x : ℤ} (hx : 0 < x) :
    (∃ k : ℤ, 0 < k ∧ beattySeq α k = x) ↔ 1 - γ < bronzeFract x := by
  have hα : 0 < α := by positivity
  have hinterval (k : ℤ) : beattySeq α k = x ↔
      (x : ℝ) * γ ≤ k ∧ (k : ℝ) < (x : ℝ) * γ + γ := by
    rw [beattySeq, Int.floor_eq_iff, ← div_le_iff₀ hα, ← lt_div_iff₀ hα,
      div_eq_mul_inv _ α, div_eq_mul_inv _ α, alpha_inv, add_mul, one_mul]
  let t : ℝ := (x : ℝ) * γ
  have hpos : 0 < t := mul_pos (by exact_mod_cast hx) gamma_bounds.1
  have hr : 0 < Int.fract t := threeGap_fract_pos γ gamma_irrational hx.ne'
  change (∃ k : ℤ, 0 < k ∧ beattySeq α k = x) ↔ 1 - γ < Int.fract t
  rw [← Int.self_sub_floor]
  constructor
  · rintro ⟨k, -, hk⟩
    obtain ⟨hle, hlt⟩ := (hinterval k).mp hk
    change t ≤ (k : ℝ) at hle
    change (k : ℝ) < t + γ at hlt
    have hfk : ⌊t⌋ < k := by
      rw [← Int.cast_lt (R := ℝ)]
      linarith only [hr, hle, Int.self_sub_floor t]
    have hfk' : (⌊t⌋ : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hfk)
    linarith only [hfk', hlt]
  · intro h
    refine ⟨⌊t⌋ + 1, by have := Int.floor_nonneg.mpr hpos.le; omega, (hinterval _).mpr ?_⟩
    change t ≤ ((⌊t⌋ + 1 : ℤ) : ℝ) ∧ ((⌊t⌋ + 1 : ℤ) : ℝ) < t + γ
    push_cast
    exact ⟨(Int.lt_floor_add_one t).le, by linarith only [h]⟩

private theorem beatty_beta_iff {x : ℤ} (hx : 0 < x) :
    (∃ k : ℤ, 0 < k ∧ beattySeq β k = x) ↔ bronzeFract x ≤ 1 - γ := by
  have hα : Irrational α := by
    convert gamma_irrational.add_intCast 3 using 1
    push_cast
    ring
  have hconj : Real.HolderConjugate α β := by
    refine Real.holderConjugate_iff.mpr ⟨?_, by rw [alpha_inv, beta_inv]; ring⟩
    linarith only [gamma_bounds.1]
  have h := (Set.ext_iff.mp (hα.beattySeq_symmDiff_beattySeq_pos hconj) x).mpr hx
  rw [Set.mem_symmDiff] at h
  change ((∃ k : ℤ, 0 < k ∧ beattySeq α k = x) ∧ ¬(∃ k : ℤ, 0 < k ∧ beattySeq β k = x)) ∨
    ((∃ k : ℤ, 0 < k ∧ beattySeq β k = x) ∧ ¬(∃ k : ℤ, 0 < k ∧ beattySeq α k = x)) at h
  rw [beatty_alpha_iff hx] at h
  rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · simp [hb, ha.not_ge]
  · simp [hb, le_of_not_gt ha]

private theorem bronze_ge_index (n : ℕ) : (n : ℤ) ≤ B n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n hn hn' =>
    rw [lucasU_bronzeLucasParams_add_two]
    push_cast at *
    omega

-- In each block, the two consecutive bronze approximants have signed errors e and -γe.
private theorem bronze_signed_errors (n : ℕ) :
    (B (2 * n + 1) : ℝ) * γ - B (2 * n) = γ ^ (2 * n + 1) ∧
      (B (2 * n + 2) : ℝ) * γ - B (2 * n + 1) = -γ ^ (2 * n + 1) * γ := by
  have h := (bronze_mul_metallic_identities n).1
  have hr := congrArg (fun z : ℤ => (z : ℝ)) (lucasU_bronzeLucasParams_add_two (2 * n))
  push_cast at hr
  constructor
  · linear_combination h + hr
  · linear_combination -γ * h + (B (2 * n + 1) : ℝ) * alpha_mul_gamma

private theorem bronze_block_cover {x : ℤ} (hx : 0 < x) :
    ∃ (n : ℕ) (k : ℤ), 0 ≤ k ∧ k < 3 ∧ B (2 * n + 1) + k * B (2 * n + 2) ≤ x ∧
      x < B (2 * n + 1) + (k + 1) * B (2 * n + 2) := by
  have hex : ∃ n : ℕ, x < B (2 * n + 3) := by
    refine ⟨x.toNat, ?_⟩
    have h := bronze_ge_index (2 * x.toNat + 3)
    omega
  let n := Nat.find hex
  have hu : x < B (2 * n + 3) := Nat.find_spec hex
  have hl : B (2 * n + 1) ≤ x := by
    by_contra! h
    cases hn : n with
    | zero =>
      have hone : B 1 = 1 := by decide
      norm_num [hn, hone] at h
      omega
    | succ j =>
      have he : 2 * n + 1 = 2 * j + 3 := by omega
      exact Nat.find_min hex (show j < n by omega) (he ▸ h)
  have hrec : B (2 * n + 3) = 3 * B (2 * n + 2) + B (2 * n + 1) :=
    lucasU_bronzeLucasParams_add_two (2 * n + 1)
  by_cases h₁ : x < B (2 * n + 1) + B (2 * n + 2)
  · exact ⟨n, 0, by norm_num, by norm_num, by simpa using hl, by simpa using h₁⟩
  by_cases h₂ : x < B (2 * n + 1) + 2 * B (2 * n + 2)
  · exact ⟨n, 1, by norm_num, by norm_num, by simpa using le_of_not_gt h₁, h₂⟩
  · exact ⟨n, 2, by norm_num, by norm_num, le_of_not_gt h₂, by omega⟩

-- The candidate p + kq minimizes the fractional part below p + (k+1)q, strictly away from itself.
private theorem bronze_block_min (n : ℕ) {k : ℤ} (hk₀ : 0 ≤ k) (hk₃ : k < 3) :
    let p := B (2 * n + 1)
    let q := B (2 * n + 2)
    0 < p + k * q ∧ ∀ x : ℤ, 0 < x → x < p + (k + 1) * q → x ≠ p + k * q →
      bronzeFract (p + k * q) < bronzeFract x := by
  let p := B (2 * n + 1)
  let q := B (2 * n + 2)
  let u := B (2 * n)
  let e : ℝ := γ ^ (2 * n + 1)
  change 0 < p + k * q ∧ ∀ x : ℤ, 0 < x → x < p + (k + 1) * q → x ≠ p + k * q → _
  have hp : 0 < p := (show (0 : ℤ) < (↑(2 * n + 1) : ℤ) by omega).trans_le (bronze_ge_index _)
  have hq : 0 < q := (show (0 : ℤ) < (↑(2 * n + 2) : ℤ) by omega).trans_le (bronze_ge_index _)
  have hγ := gamma_bounds.1
  have hγ' : γ < 1 := gamma_bounds.2.trans (by norm_num)
  have he : 0 < e := pow_pos hγ _
  have he' : e < 1 := pow_lt_one₀ hγ.le hγ' (by omega)
  have hk₀' : 0 ≤ (k : ℝ) := by exact_mod_cast hk₀
  have hk₂' : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
  have hw : 0 < 1 - (k : ℝ) * γ := by
    linarith only [gamma_bounds.2, mul_le_mul_of_nonneg_right hk₂' hγ.le]
  have hw' : 1 - (k : ℝ) * γ ≤ 1 := by linarith only [mul_nonneg hk₀' hγ.le]
  obtain ⟨hpγ, hqγ⟩ := bronze_signed_errors n
  change (p : ℝ) * γ - u = e at hpγ
  change (q : ℝ) * γ - p = -e * γ at hqγ
  have hfrac : bronzeFract (p + k * q) = e * (1 - k * γ) := by
    refine Int.fract_eq_iff.mpr ⟨(mul_pos he hw).le, ?_, u + k * p, ?_⟩
    · exact (mul_le_of_le_one_right he.le hw').trans_lt he'
    · push_cast
      linear_combination hpγ + (k : ℝ) * hqγ
  refine ⟨add_pos_of_pos_of_nonneg hp (mul_nonneg hk₀ hq.le), ?_⟩
  intro x hx hlt hne
  rw [hfrac]
  -- Cassini gives determinant one, so the indicated coefficients reconstruct both coordinates.
  let z : ℤ := ⌊(x : ℝ) * γ⌋
  have hd : p * p - q * u = 1 := by
    simpa only [bronzeLucasParams_q, (even_two_mul n).neg_pow, one_pow, sq, mul_comm q u]
      using lucasU_cassini bronzeLucasParams (2 * n)
  let a := p * x - q * z
  let b := p * z - u * x
  have hx' : x = a * p + b * q := by
    dsimp [a, b]
    linear_combination -x * hd
  have hz' : z = a * u + b * p := by
    dsimp [a, b]
    linear_combination -z * hd
  have herr : bronzeFract x = e * (a - b * γ) := by
    change (x : ℝ) * γ - z = _
    have hxR := congrArg (fun z : ℤ => (z : ℝ)) hx'
    have hzR := congrArg (fun z : ℤ => (z : ℝ)) hz'
    push_cast at hxR hzR
    linear_combination γ * hxR - hzR + (a : ℝ) * hpγ + (b : ℝ) * hqγ
  by_contra! hc
  rw [herr, mul_le_mul_iff_right₀ he] at hc
  have hpos : 0 < bronzeFract x := threeGap_fract_pos γ gamma_irrational hx.ne'
  rw [herr, mul_pos_iff_of_pos_left he] at hpos
  have ha : 1 ≤ a := by
    by_contra! ha
    have ha₀ : a ≤ 0 := by omega
    have haR : (a : ℝ) ≤ 0 := by exact_mod_cast ha₀
    have hb : b < 0 := by
      have hbγ : (b : ℝ) * γ < 0 := by linarith only [haR, hpos]
      exact_mod_cast (neg_of_mul_neg_left hbγ hγ.le)
    exact hx.not_ge (hx' ▸ add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha₀ hp.le)
      (mul_nonpos_of_nonpos_of_nonneg hb.le hq.le))
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb : k ≤ b := by
    by_contra! hb
    have hbR : (b : ℝ) < k := by exact_mod_cast hb
    linarith only [hc, haR, mul_lt_mul_of_pos_right hbR hγ]
  have hb' : k + 1 ≤ b := by
    by_contra! hb'
    have heq : b = k := by omega
    rw [heq] at hc
    have ha' : (a : ℝ) ≤ 1 := by linarith only [hc]
    have hae : a = 1 := le_antisymm (by exact_mod_cast ha') ha
    exact hne (by simpa only [hae, heq, one_mul] using hx')
  have hbound := add_le_add (le_mul_of_one_le_left hp.le ha) (mul_le_mul_of_nonneg_right hb' hq.le)
  exact hlt.not_ge (hx' ▸ hbound)

private def IsBronzeRecord (x : ℤ) : Prop :=
  0 < x ∧ ∀ y : ℤ, 0 < y → y < x → bronzeFract x < bronzeFract y

private theorem bronze_record_candidate (n : ℕ) {k : ℤ} (hk₀ : 0 ≤ k) (hk₃ : k < 3) :
    IsBronzeRecord (B (2 * n + 1) + k * B (2 * n + 2)) := by
  obtain ⟨hpos, hmin⟩ := bronze_block_min n hk₀ hk₃
  refine ⟨hpos, fun y hy hlt => hmin y hy ?_ hlt.ne⟩
  have hq := bronze_ge_index (2 * n + 2)
  rw [add_mul, one_mul]
  omega

private theorem bronze_record_iff (x : ℤ) : IsBronzeRecord x ↔
    ∃ n : ℕ, x = B (2 * n + 1) ∨ x = bronzeCompanionFirst (2 * n + 2) ∨
      x = bronzeCompanionSecond (2 * n + 2) := by
  constructor
  · rintro ⟨hx, hrecord⟩
    obtain ⟨n, k, hk₀, hk₃, hle, hu⟩ := bronze_block_cover hx
    obtain ⟨hpos, hmin⟩ := bronze_block_min n hk₀ hk₃
    have heq : x = B (2 * n + 1) + k * B (2 * n + 2) := by
      by_contra hne
      exact (hrecord _ hpos (lt_of_le_of_ne hle (Ne.symm hne))).not_gt (hmin _ hx hu hne)
    refine ⟨n, ?_⟩
    obtain ⟨hC, hD⟩ := bronzeCompanion_succ (2 * n + 1)
    interval_cases k
    · left; simpa using heq
    · right; left
      rw [hC, add_comm]
      simpa using heq
    · right; right
      rw [hD, add_comm]
      exact heq
  · rintro ⟨n, rfl | rfl | rfl⟩
    · simpa using bronze_record_candidate n (k := 0) (by norm_num) (by norm_num)
    · rw [(bronzeCompanion_succ (2 * n + 1)).1, add_comm]
      simpa using bronze_record_candidate n (k := 1) (by norm_num) (by norm_num)
    · rw [(bronzeCompanion_succ (2 * n + 1)).2, add_comm]
      exact bronze_record_candidate n (k := 2) (by norm_num) (by norm_num)

private theorem bronze_record_fract_le {x : ℤ} (hx : IsBronzeRecord x) : bronzeFract x ≤ γ := by
  have hone : bronzeFract 1 = γ := by
    simpa only [bronzeFract, Int.cast_one, one_mul] using
      Int.fract_eq_self.mpr ⟨gamma_bounds.1.le, gamma_bounds.2.trans (by norm_num : (1 : ℝ)/3 < 1)⟩
  by_cases h : x = 1
  · exact (h ▸ hone).le
  · rw [← hone]
    exact (hx.2 1 (by norm_num) (by have := hx.1; omega)).le

/-- **P-positions of the bronze game.** Let $\alpha = (3 + \sqrt{13})/2$ and
$\beta = (5 + \sqrt{13})/6$, let $B_n$ be the bronze numbers, and let $C_n$ and $D_n$ be the
companion bronze numbers of the first and second type. Let $P$ be the set of natural numbers
$x$ such that $x = 0$ or $x \in \{B_{2k+1}, C_{2k+2}, D_{2k+2}\}$ for some natural number $k$.
Then, in the Beatty octal game for $\alpha$ and $\beta$, no move takes a heap whose size lies
in $P$ to a heap whose size lies in $P$, and from every heap whose size is not in $P$ some move
leads to a heap whose size lies in $P$.

So $P$ is stable and absorbing for the moves of the game; since every move decreases the heap,
this determines $P$ as the set of P-positions, the heap sizes from which the previous player
wins: $0, B_1, C_2, D_2, B_3, C_4, D_4, \ldots$

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 11. -/
public theorem bronzeGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔ x = 0 ∨ ∃ k, (x : ℤ) = lucasU bronzeLucasParams (2 * k + 1) ∨
      (x : ℤ) = bronzeCompanionFirst (2 * k + 2) ∨ (x : ℤ) = bronzeCompanionSecond (2 * k + 2)) :
    (∀ x y, x ∈ P →
        beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y → y ∉ P) ∧
      ∀ x, x ∉ P →
        ∃ y, beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y ∧ y ∈ P := by
  have hP' (x : ℕ) : x ∈ P ↔ x = 0 ∨ IsBronzeRecord x :=
    (hP x).trans (or_congr_right (bronze_record_iff x).symm)
  have hzero : 0 ∈ P := (hP' 0).mpr (Or.inl rfl)
  constructor
  · intro x y hx hmove hy
    have hyx := beattyOctalMove_lt hmove
    have hxpos : 0 < x := by omega
    have hxr := ((hP' x).mp hx).resolve_left hxpos.ne'
    by_cases hyzero : y = 0
    · subst y
      have hx' : 0 < (x : ℤ) := by exact_mod_cast hxpos
      have ha := (beatty_alpha_iff hx').mp (beattyOctalMove_zero_iff.mp hmove).2
      linarith only [ha, bronze_record_fract_le hxr, gamma_bounds.2]
    · have hypos := Nat.pos_of_ne_zero hyzero
      have hyr := ((hP' y).mp hy).resolve_left hyzero
      have hxy := hxr.2 y hyr.1 (by exact_mod_cast hyx)
      have hb := (beattyOctalMove_pos_iff hypos).mp hmove |>.2
      rw [Int.ofNat_sub hyx.le] at hb
      have hsub : 0 < (x : ℤ) - y := by omega
      have hble := (beatty_beta_iff hsub).mp hb
      have hwrap : bronzeFract ((x : ℤ) - y) = 1 + bronzeFract x - bronzeFract y :=
        threeGap_fract_sub_of_lt γ x y hxy
      rw [hwrap] at hble
      have hpos : 0 < bronzeFract x := threeGap_fract_pos γ gamma_irrational hxr.1.ne'
      linarith only [hble, bronze_record_fract_le hyr, hpos]
  · intro x hx
    have hxne : x ≠ 0 := fun h => hx (h.symm ▸ hzero)
    have hxpos : 0 < (x : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hxne
    by_cases ha : 1 - γ < bronzeFract x
    · refine ⟨0, beattyOctalMove_zero_iff.mpr ⟨by exact_mod_cast hxpos, ?_⟩, hzero⟩
      exact (beatty_alpha_iff hxpos).mpr ha
    · obtain ⟨n, k, hk₀, hk₃, hl, hu⟩ := bronze_block_cover hxpos
      let z := B (2 * n + 1) + k * B (2 * n + 2)
      have hzr : IsBronzeRecord z := bronze_record_candidate n hk₀ hk₃
      let y := z.toNat
      have hyz : (y : ℤ) = z := Int.toNat_of_nonneg hzr.1.le
      have hy : y ∈ P := (hP' y).mpr (Or.inr (hyz.symm ▸ hzr))
      have hyx : y < x := (show y ≤ x by omega).lt_of_ne (fun h => hx (h ▸ hy))
      have hzne : (x : ℤ) ≠ z := by
        rw [← hyz]
        exact_mod_cast hyx.ne'
      have hdiff := (bronze_block_min n hk₀ hk₃).2 x hxpos hu hzne
      have hypos : 0 < y := by
        exact_mod_cast (hyz.symm ▸ hzr.1 : 0 < (y : ℤ))
      refine ⟨y, (beattyOctalMove_pos_iff hypos).mpr ⟨hyx, ?_⟩, hy⟩
      rw [Int.ofNat_sub hyx.le, hyz]
      have hsub : 0 < (x : ℤ) - z := by omega
      apply (beatty_beta_iff hsub).mpr
      have hfrac : bronzeFract ((x : ℤ) - z) = bronzeFract x - bronzeFract z :=
        threeGap_fract_sub_of_le γ x z hdiff.le
      rw [hfrac]
      have hpos : 0 < bronzeFract z := threeGap_fract_pos γ gamma_irrational hzr.1.ne'
      linarith only [le_of_not_gt ha, hpos]

end MetaMathlibExt
