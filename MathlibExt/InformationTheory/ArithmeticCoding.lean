/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.PrefixFree
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.Data.BitEncoding

/-!
# Arithmetic coding

Exact (non-asymptotic) arithmetic coding for a rational probability
assignment `q` on a finite ordered alphabet `ι`. Each symbol `i` owns the
half-open interval `[cum q i, cum q i + q i)` of `[0, 1)`, where `cum q i`
is the total mass of the symbols before `i`. The codeword `arithCode q i`
is the `codeLen q i`-bit binary expansion of the first dyadic interval of
that length inside the symbol's interval, where
`codeLen q i = ⌈log₂ (1 / q i)⌉ + 1`. The code is prefix-free, hence
injective and uniquely decodable, and every codeword has the stated length
bound.

Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to
Learning, Cambridge University Press, 2025, Chapter 13; Y. Polyanskiy and
Y. Wu, MIT 6.441 Information Theory course notes, Spring 2016, Section 9.1.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.ArithmeticCoding

set_option autoImplicit false

section

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (q : ι → ℚ)

/-- Cumulative mass of the symbols strictly before `i`. -/
noncomputable def cum (i : ι) : ℚ :=
  ∑ j ∈ Finset.univ.filter (· < i), q j

/-- Codeword length for symbol `i`: one bit more than the ceiling of the
binary surprisal. -/
noncomputable def codeLen (i : ι) : ℕ :=
  ⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ + 1

/-- The dyadic numerator of the codeword: the least integer whose dyadic
interval at scale `2 ^ codeLen q i` starts at or after `cum q i`. -/
noncomputable def codeInt (i : ι) : ℕ :=
  ⌈cum q i * 2 ^ codeLen q i⌉₊

/-- The arithmetic codeword of `i`: the `codeLen q i` binary digits of
`codeInt q i`, most significant bit first. It is the canonical fixed-width
big-endian codec `Nat.toBitsBE`. -/
noncomputable def arithCode (i : ι) : List Bool :=
  Nat.toBitsBE (codeLen q i) (codeInt q i)

/-- The binary-fraction value of a bit list, most significant bit first. -/
def fracVal : List Bool → ℚ
  | [] => 0
  | b :: t => (if b then 1 / 2 else 0) + fracVal t / 2
private theorem qi_le_one (hqpos : ∀ i, 0 < q i) (hqsum : ∑ i, q i = 1) (i : ι) :
    q i ≤ 1 := by
  have h := Finset.single_le_sum (fun k _ => le_of_lt (hqpos k)) (Finset.mem_univ i)
  rw [hqsum] at h
  exact h
private theorem qi_mul_two_pow_ge_two (hqpos : ∀ i, 0 < q i) (hqsum : ∑ i, q i = 1)
    (i : ι) : (2 : ℚ) ≤ q i * 2 ^ codeLen q i := by
  have hqi_pos : (0 : ℝ) < (q i : ℝ) := by exact_mod_cast hqpos i
  have hqi_le : (q i : ℝ) ≤ 1 := by exact_mod_cast qi_le_one q hqpos hqsum i
  have hx_pos : (0 : ℝ) < (q i : ℝ)⁻¹ := inv_pos.mpr hqi_pos
  have hx_ge : (1 : ℝ) ≤ (q i : ℝ)⁻¹ := (one_le_inv₀ hqi_pos).mpr hqi_le
  have hlog_nn : (0 : ℝ) ≤ Real.logb 2 (q i : ℝ)⁻¹ :=
    Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx_ge
  have hceil : Real.logb 2 (q i : ℝ)⁻¹ ≤ (⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hrpow_le : (2:ℝ) ^ (Real.logb 2 (q i : ℝ)⁻¹) ≤ (2:ℝ) ^ ((⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hceil
  have hlog_eq : (2:ℝ) ^ (Real.logb 2 (q i : ℝ)⁻¹) = (q i : ℝ)⁻¹ :=
    Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) hx_pos
  have hnat_eq : (2:ℝ) ^ (((⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℕ)) : ℝ) = (((2 ^ ⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  rw [hlog_eq, hnat_eq] at hrpow_le
  have hpow_succ : (2 : ℕ) ^ codeLen q i = 2 * (2 ^ ⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℕ) := by
    simp only [codeLen, pow_succ]
    ring
  have hcast : (((2 ^ codeLen q i : ℕ)) : ℝ) = 2 * (((2 ^ ⌈Real.logb 2 (q i : ℝ)⁻¹⌉₊ : ℕ)) : ℝ) := by
    rw [hpow_succ]
    norm_cast
  have h2le : (2 : ℝ) * (q i : ℝ)⁻¹ ≤ (((2 ^ codeLen q i : ℕ)) : ℝ) := by
    rw [hcast]
    have h := mul_le_mul_of_nonneg_left hrpow_le (le_of_lt (by norm_num : (0:ℝ) < 2))
    linarith
  have hqi_ne : (q i : ℝ) ≠ 0 := ne_of_gt hqi_pos
  have hmul : (2 : ℝ) ≤ (q i : ℝ) * (((2 ^ codeLen q i : ℕ)) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2le (le_of_lt hqi_pos)
    have heq : (q i : ℝ) * (2 * (q i : ℝ)⁻¹) = 2 := by field_simp
    linarith
  have hcast2 : (((q i * 2 ^ codeLen q i : ℚ)) : ℝ) = (q i : ℝ) * (((2 ^ codeLen q i : ℕ)) : ℝ) := by
    push_cast
    ring
  have hle : ((2 : ℚ) : ℝ) ≤ (((q i * 2 ^ codeLen q i : ℚ)) : ℝ) := by
    rw [hcast2]
    norm_cast at hmul ⊢
  exact_mod_cast hle
private theorem cum_nonneg (hqpos : ∀ i, 0 < q i) (i : ι) : 0 ≤ cum q i := by
  simp only [cum]
  apply Finset.sum_nonneg
  intro k _
  exact le_of_lt (hqpos k)
private theorem cum_add_le_one (hqpos : ∀ i, 0 < q i) (hqsum : ∑ i, q i = 1) (i : ι) :
    cum q i + q i ≤ 1 := by
  have hi : i ∉ Finset.univ.filter (· < i : ι → Prop) := by simp
  have hsub : Insert.insert i (Finset.univ.filter (· < i : ι → Prop)) ⊆ Finset.univ := by
    intro k _
    exact Finset.mem_univ k
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := q) hsub (fun k _ _ => le_of_lt (hqpos k))
  rw [Finset.sum_insert hi] at hsum
  simp only [cum] at hsum ⊢
  rw [hqsum] at hsum
  linarith
private theorem fracVal_append (l₁ l₂ : List Bool) :
    fracVal (l₁ ++ l₂) = fracVal l₁ + fracVal l₂ / 2 ^ l₁.length := by
  induction l₁ with
  | nil => simp [fracVal]
  | cons b s ih =>
    simp only [List.cons_append, fracVal, List.length_cons, pow_succ] at ih ⊢
    rw [ih]
    cases b <;> simp <;> ring
private theorem fracVal_nonneg (l : List Bool) : 0 ≤ fracVal l := by
  induction l with
  | nil => simp [fracVal]
  | cons b s ih =>
    simp only [fracVal]
    cases b <;> simp <;> linarith
private theorem fracVal_lt_one (l : List Bool) : fracVal l < 1 := by
  induction l with
  | nil => simp [fracVal]
  | cons b s ih =>
    have hnn := fracVal_nonneg s
    simp only [fracVal]
    cases b <;> simp <;> linarith

/-- The binary-fraction value of a bit list is its big-endian value over
`2 ^ l.length`. -/
theorem fracVal_eq_ofBitsBE (l : List Bool) :
    fracVal l = (Nat.ofBitsBE l : ℚ) / 2 ^ l.length := by
  induction l with
  | nil => simp [fracVal, Nat.ofBitsBE, BitVec.ofBoolListBE.eq_1]
  | cons b t ih =>
    have h2 : (2 : ℚ) ^ t.length ≠ 0 := by positivity
    simp only [fracVal, Nat.ofBitsBE, BitVec.ofBoolListBE.eq_2,
      BitVec.toNat_cons', Nat.shiftLeft_eq, Bool.toNat, List.length_cons, pow_succ]
    cases b <;> simp <;> rw [ih] <;> simp only [Nat.ofBitsBE] <;> field_simp

/-- Codewords have exactly the stated length, which is the concept's bound
`⌈log₂ (1 / q i)⌉ + 1`. -/
theorem arithCode_length (i : ι) :
    (arithCode q i).length = codeLen q i := by
  simp only [arithCode, Nat.length_toBitsBE]

/-- The dyadic numerator fits in `codeLen q i` bits. -/
theorem codeInt_lt_two_pow (hqpos : ∀ i, 0 < q i) (hqsum : ∑ i, q i = 1)
    (i : ι) :
    codeInt q i < 2 ^ codeLen q i := by
  have hcum_nn := cum_nonneg q hqpos i
  have hcum_le := cum_add_le_one q hqpos hqsum i
  have hqi_ge := qi_mul_two_pow_ge_two q hqpos hqsum i
  have hpos2 : (0:ℚ) < 2 ^ codeLen q i := by positivity
  have hx_nn : (0:ℚ) ≤ cum q i * 2 ^ codeLen q i := mul_nonneg hcum_nn (le_of_lt hpos2)
  have hceil_lt : ((⌈cum q i * 2 ^ codeLen q i⌉₊ : ℕ) : ℚ) < cum q i * 2 ^ codeLen q i + 1 :=
    Nat.ceil_lt_add_one hx_nn
  have hle : cum q i * 2 ^ codeLen q i + 1 ≤ ((2 ^ codeLen q i : ℕ) : ℚ) := by
    have h1 : cum q i ≤ 1 - q i := by linarith
    have h2 : cum q i * 2 ^ codeLen q i ≤ (1 - q i) * 2 ^ codeLen q i := by
      apply mul_le_mul_of_nonneg_right h1 (le_of_lt hpos2)
    have h3 : (1 - q i) * 2 ^ codeLen q i = 2 ^ codeLen q i - q i * 2 ^ codeLen q i := by ring
    rw [h3] at h2
    have h4 : ((2 ^ codeLen q i : ℕ) : ℚ) = 2 ^ codeLen q i := by norm_cast
    rw [h4]
    linarith
  have hlt : ((⌈cum q i * 2 ^ codeLen q i⌉₊ : ℕ) : ℚ) < ((2 ^ codeLen q i : ℕ) : ℚ) :=
    lt_of_lt_of_le hceil_lt hle
  have hlt_nat : ⌈cum q i * 2 ^ codeLen q i⌉₊ < 2 ^ codeLen q i := by exact_mod_cast hlt
  simpa [codeInt] using hlt_nat

/-- The codeword's binary-fraction value is its dyadic numerator over
`2 ^ codeLen q i`. -/
theorem fracVal_arithCode (hqpos : ∀ i, 0 < q i) (hqsum : ∑ i, q i = 1)
    (i : ι) :
    fracVal (arithCode q i) = codeInt q i / 2 ^ codeLen q i := by
  have hlt := codeInt_lt_two_pow q hqpos hqsum i
  simp only [arithCode, fracVal_eq_ofBitsBE, Nat.length_toBitsBE]
  rw [Nat.ofBitsBE_toBitsBE_of_lt]
  exact hlt

/-- The codeword's dyadic interval lies inside the symbol's cumulative
interval. -/
theorem arithCode_interval_subset (hqpos : ∀ i, 0 < q i)
    (hqsum : ∑ i, q i = 1) (i : ι) :
    cum q i ≤ fracVal (arithCode q i) ∧
      fracVal (arithCode q i) + 1 / 2 ^ codeLen q i ≤ cum q i + q i := by
  have hfrac := fracVal_arithCode q hqpos hqsum i
  rw [hfrac]
  have hpos : (0:ℚ) < 2 ^ codeLen q i := by positivity
  have hcum_nn := cum_nonneg q hqpos i
  have hx_nn : (0:ℚ) ≤ cum q i * 2 ^ codeLen q i := mul_nonneg hcum_nn (le_of_lt hpos)
  have hqi_ge := qi_mul_two_pow_ge_two q hqpos hqsum i
  have hcum_le := cum_add_le_one q hqpos hqsum i
  constructor
  · have hle : cum q i * 2 ^ codeLen q i ≤ ((codeInt q i : ℕ) : ℚ) := by
      have h := Nat.le_ceil (cum q i * 2 ^ codeLen q i)
      simpa [codeInt] using h
    rw [le_div_iff₀ hpos]
    simpa using hle
  · have hceil_lt : ((codeInt q i : ℕ) : ℚ) < cum q i * 2 ^ codeLen q i + 1 := by
      have h := Nat.ceil_lt_add_one hx_nn
      simpa [codeInt] using h
    have hle2 : ((codeInt q i : ℕ) : ℚ) + 1 ≤ (cum q i + q i) * 2 ^ codeLen q i := by
      have h1 : cum q i ≤ 1 - q i := by linarith
      have h2 : cum q i * 2 ^ codeLen q i ≤ (1 - q i) * 2 ^ codeLen q i := by
        apply mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      have h3 : (1 - q i) * 2 ^ codeLen q i = 2 ^ codeLen q i - q i * 2 ^ codeLen q i := by ring
      rw [h3] at h2
      have heq : (cum q i + q i) * 2 ^ codeLen q i = cum q i * 2 ^ codeLen q i + q i * 2 ^ codeLen q i := by ring
      rw [heq]
      linarith
    have hadd : ((codeInt q i : ℕ) : ℚ) / 2 ^ codeLen q i + 1 / 2 ^ codeLen q i =
        (((codeInt q i : ℕ) : ℚ) + 1) / 2 ^ codeLen q i :=
      (add_div _ _ _).symm
    rw [hadd, div_le_iff₀ hpos]
    exact hle2

/-- Cumulative intervals of distinct symbols are disjoint in order: for
`i < j`, `cum q i + q i ≤ cum q j`. -/
theorem cum_add_le_cum_of_lt (hqpos : ∀ i, 0 < q i) (i j : ι) (hij : i < j) :
    cum q i + q i ≤ cum q j := by
  have hi : i ∉ Finset.univ.filter (· < i : ι → Prop) := by
    simp
  have hsub : Insert.insert i (Finset.univ.filter (· < i : ι → Prop)) ⊆
      Finset.univ.filter (· < j : ι → Prop) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | hki
    · exact hij
    · exact lt_trans hki hij
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (s := Insert.insert i (Finset.univ.filter (· < i : ι → Prop)))
    (t := Finset.univ.filter (· < j : ι → Prop)) (f := q) hsub
    (fun k _ _ => le_of_lt (hqpos k))
  rw [Finset.sum_insert hi] at hsum
  simp only [cum] at hsum ⊢
  linarith

/-- The value of any extension of a codeword prefix stays in the prefix's
dyadic interval. -/
theorem fracVal_mem_dyadic_of_isPrefix (l₁ l₂ : List Bool)
    (h : l₁ <+: l₂) :
    fracVal l₁ ≤ fracVal l₂ ∧ fracVal l₂ < fracVal l₁ + 1 / 2 ^ l₁.length := by
  obtain ⟨t, rfl⟩ := h
  have happ := fracVal_append l₁ t
  have hnn := fracVal_nonneg t
  have hlt := fracVal_lt_one t
  have hpos : (0 : ℚ) < 2 ^ l₁.length := by positivity
  constructor
  · rw [happ]
    have hdiv : (0 : ℚ) ≤ fracVal t / 2 ^ l₁.length := div_nonneg hnn (le_of_lt hpos)
    linarith
  · rw [happ]
    have hdiv : fracVal t / (2 ^ l₁.length : ℚ) < 1 / (2 ^ l₁.length : ℚ) := by
      apply div_lt_div_of_pos_right hlt hpos
    linarith

/-- Arithmetic coding is prefix-free. -/
theorem arithCode_isPrefixFree (hqpos : ∀ i, 0 < q i)
    (hqsum : ∑ i, q i = 1) : IsPrefixFree (arithCode q) := by
  intro a₁ a₂ hne hpre
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hcum := cum_add_le_cum_of_lt q hqpos a₁ a₂ hij
    obtain ⟨h1l, h1r⟩ := arithCode_interval_subset q hqpos hqsum a₁
    obtain ⟨h2l, h2r⟩ := arithCode_interval_subset q hqpos hqsum a₂
    have hdyad := fracVal_mem_dyadic_of_isPrefix _ _ hpre
    rw [arithCode_length q a₁] at hdyad
    obtain ⟨hdl, hdr⟩ := hdyad
    linarith
  · have hji' : a₂ < a₁ := hji
    have hcum := cum_add_le_cum_of_lt q hqpos a₂ a₁ hji'
    obtain ⟨h1l, h1r⟩ := arithCode_interval_subset q hqpos hqsum a₁
    obtain ⟨h2l, h2r⟩ := arithCode_interval_subset q hqpos hqsum a₂
    have hdyad := fracVal_mem_dyadic_of_isPrefix _ _ hpre
    rw [arithCode_length q a₁] at hdyad
    obtain ⟨hdl, hdr⟩ := hdyad
    have hpos : (0:ℚ) < 1 / 2 ^ codeLen q a₂ := by positivity
    linarith

/-- Arithmetic coding is injective, hence decodable. -/
theorem arithCode_injective (hqpos : ∀ i, 0 < q i)
    (hqsum : ∑ i, q i = 1) : Function.Injective (arithCode q) := by
  exact IsPrefixFree.injective (arithCode_isPrefixFree q hqpos hqsum)

end

end MathlibExt.InformationTheory.ArithmeticCoding
