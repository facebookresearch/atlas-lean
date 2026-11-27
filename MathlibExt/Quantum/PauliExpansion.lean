/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PauliXZ
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pauli expansion of Hermitian matrices

Hermitian Pauli strings over `X^a Z^b`, trace orthogonality, expansion coefficients, coefficient bounds, and the labeled Pauli-test acceptance identity (Morimae-Nagaj-Schuch, arXiv:1510.06789, Sec. IV).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open MathlibExt.Quantum.PauliXZ
namespace MathlibExt.Quantum.PauliExpansion

set_option autoImplicit false

/-- Hermitian Pauli string σ_(a,b) = i^|a∧b| X^a Z^b built on merged MathlibExt.Quantum.PauliXZ.pauliXZ (no parallel Pauli encoding) -/
noncomputable def hermPauli {k : ℕ} (a b : Fin k → ZMod 2) : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ := Complex.I ^ (∑ i, (a i).val * (b i).val) • pauliXZ a b

/-- In `ZMod 2`, every element is `0` or `1` (by finite check). -/
private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  exact h x

/-- Nonzero elements of `ZMod 2` equal `1` (by finite check). -/
private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  have h : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  exact h x hx

/-- `(-1)^_` is multiplicative over `ZMod 2` addition. -/
private theorem neg_one_pow_zmod_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  rw [ZMod.val_add, (neg_one_pow_eq_pow_mod_two _).symm, pow_add]

/-- `(-1)^_` turns `ZMod 2` sums into `ℂ` products. -/
private theorem neg_one_pow_sum_val {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (-1 : ℂ) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : ℂ) ^ (f i).val := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : (0 : ZMod 2).val = 0 := by decide
    simp [Finset.sum_empty, Finset.prod_empty, h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_one_pow_zmod_add, ih]

/-- `(-1)^_` of a `ZMod 2` dot product as `(-1)^_` of the `ℕ` overlap sum. -/
private theorem neg_one_pow_dot_val {k : ℕ} (a b : Fin k → ZMod 2) :
    (-1 : ℂ) ^ (b ⬝ᵥ a).val = (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) := by
  have h1 : b ⬝ᵥ a = ∑ i, b i * a i := rfl
  rw [h1, neg_one_pow_sum_val]
  have h2 : ∀ i : Fin k, (-1 : ℂ) ^ ((b i * a i).val) = (-1 : ℂ) ^ ((a i).val * (b i).val) := by
    intro i
    have hm : ∀ x y : ZMod 2, (x * y).val = x.val * y.val := by decide
    rw [hm, mul_comm ((b i).val)]
  rw [Finset.prod_congr rfl (fun i _ => h2 i)]
  rw [← Finset.prod_pow_eq_pow_sum]

/-- `(-1)^m * (-1)^m = 1` over `ℂ`. -/
private theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rw [← mul_pow]
  have h : (-1 : ℂ) * (-1 : ℂ) = 1 := by ring
  rw [h, one_pow]

/-- Phase cancellation for `hermPauli_mul_self`: `(I^m * I^m) * (-1)^m = 1`. -/
private theorem phase_mul_self (m : ℕ) : (Complex.I ^ m * Complex.I ^ m) * (-1 : ℂ) ^ m = 1 := by
  have hI2 : Complex.I ^ 2 = -1 := by
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [pow_two]
    exact h
  have h1 : Complex.I ^ m * Complex.I ^ m = (-1 : ℂ) ^ m := by
    rw [← pow_add, ← two_mul, pow_mul, hI2]
  rw [h1, ← pow_add, ← two_mul, pow_mul]
  have h2 : (-1 : ℂ) ^ 2 = 1 := by ring
  rw [h2, one_pow]

/-- Pointwise doubling vanishes on bitstrings. -/
private theorem bit_add_self {k : ℕ} (a : Fin k → ZMod 2) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (a i)

/-- `a + a' = 0 ↔ a = a'` on bitstrings. -/
private theorem bit_add_eq_zero_iff {k : ℕ} (a a' : Fin k → ZMod 2) : a + a' = 0 ↔ a = a' := by
  constructor
  · intro h
    have haa : a' + a' = (0 : Fin k → ZMod 2) := bit_add_self a'
    have h1 : a + (a' + a') = a' := by
      rw [← add_assoc, h, zero_add]
    rw [haa, add_zero] at h1
    exact h1
  · intro h
    subst h
    exact bit_add_self a

/-- Cardinality of bitstrings. -/
private theorem card_bitstring (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  have h2 : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [Fintype.card_pi]
  simp [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Trace of the identity is `2^k`. -/
private theorem trace_one_bit (k : ℕ) :
    Matrix.trace (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) = (2 : ℂ) ^ k := by
  have hcard := card_bitstring k
  have h : Matrix.trace (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ)
      = (Fintype.card (Fin k → ZMod 2) : ℂ) := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.one_apply]
  rw [h, hcard]
  norm_cast

/-- A sum negated by a fixed-point-free involution `x ↦ x + e` vanishes. -/
private theorem sum_eq_zero_of_involution_neg {k : ℕ} (f : (Fin k → ZMod 2) → ℂ)
    (e : Fin k → ZMod 2) (hneg : ∀ x, f (x + e) = -f x) :
    ∑ x, f x = 0 := by
  have he : e + e = (0 : Fin k → ZMod 2) := by
    have h : ∀ y : ZMod 2, y + y = 0 := by decide
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact h (e i)
  have hg_inv : ∀ x : Fin k → ZMod 2, (x + e) + e = x := by
    intro x
    rw [add_assoc, he, add_zero]
  have hg_inj : Function.Injective (fun x : Fin k → ZMod 2 => x + e) := by
    intro x y h
    have h2 := congrArg (fun z : Fin k → ZMod 2 => z + e) h
    simp only at h2
    rw [hg_inv, hg_inv] at h2
    exact h2
  have hg_surj : Function.Surjective (fun x : Fin k → ZMod 2 => x + e) := by
    intro x
    exact ⟨x + e, hg_inv x⟩
  have hg_bij : Function.Bijective (fun x : Fin k → ZMod 2 => x + e) := ⟨hg_inj, hg_surj⟩
  have hsum : (∑ x : Fin k → ZMod 2, f x) = ∑ x : Fin k → ZMod 2, f (x + e) := by
    have hbij := Fintype.sum_bijective (fun x : Fin k → ZMod 2 => x + e) hg_bij f
      (fun y : Fin k → ZMod 2 => f (y + e)) (fun x => by rw [hg_inv])
    exact hbij
  have hneg_sum : (∑ x : Fin k → ZMod 2, f (x + e)) = -∑ x : Fin k → ZMod 2, f x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact hneg x
  have hself : (∑ x : Fin k → ZMod 2, f x) = -∑ x : Fin k → ZMod 2, f x :=
    hsum.trans hneg_sum
  have h2 : (∑ x : Fin k → ZMod 2, f x) + (∑ x : Fin k → ZMod 2, f x) = 0 := by
    linear_combination hself
  have h3 : (2 : ℂ) * (∑ x : Fin k → ZMod 2, f x) = 0 := by
    rw [two_mul]
    exact h2
  have hne : (2 : ℂ) ≠ 0 := by norm_num
  cases mul_eq_zero.mp h3 with
  | inl h0 => exact absurd h0 hne
  | inr h0 => exact h0

/-- Dot product against a single-site basis vector picks out one coordinate. -/
private theorem dot_basis_single {k : ℕ} (b : Fin k → ZMod 2) (i : Fin k) :
    b ⬝ᵥ (fun j => if j = i then 1 else 0) = b i := by
  have hdef : b ⬝ᵥ (fun j => if j = i then 1 else 0) = ∑ j, b j * (if j = i then 1 else 0) := rfl
  rw [hdef]
  have hpt : ∀ j : Fin k, b j * (if j = i then (1 : ZMod 2) else 0) = (if j = i then b j else 0) := by
    intro j
    by_cases hj : j = i <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hpt j)]
  rw [Finset.sum_ite_eq' Finset.univ i (fun j => b j)]
  simp

/-- Character sums over bitstrings: `∑_x (-1)^(b·x)` is `2^k` if `b = 0`, else `0`. -/
private theorem char_sum {k : ℕ} (b : Fin k → ZMod 2) :
    (∑ x, (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) = (if b = 0 then (2 : ℂ) ^ k else 0) := by
  by_cases hb : b = 0
  · subst hb
    have h1 : ∀ x : Fin k → ZMod 2, (-1 : ℂ) ^ (((0 : Fin k → ZMod 2) ⬝ᵥ x).val) = 1 := by
      intro x
      rw [zero_dotProduct, ZMod.val_zero, pow_zero]
    simp only [h1]
    have hsum : (∑ _x : Fin k → ZMod 2, (1 : ℂ)) = (2 : ℂ) ^ k := by
      have h : (∑ _x : Fin k → ZMod 2, (1 : ℂ)) = (Fintype.card (Fin k → ZMod 2) : ℂ) := by simp
      rw [h, card_bitstring]
      norm_cast
    simp only [ite_true]
    exact hsum
  · rw [if_neg hb]
    have hex : ∃ i, b i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hb (funext hcon)
    obtain ⟨i, hi⟩ := hex
    have hbi : b i = 1 := zmod2_eq_one_of_ne_zero hi
    let e : Fin k → ZMod 2 := fun j => if j = i then 1 else 0
    have hbe : b ⬝ᵥ e = 1 := by
      rw [dot_basis_single, hbi]
    have hneg : ∀ x : Fin k → ZMod 2, (-1 : ℂ) ^ ((b ⬝ᵥ (x + e)).val) = -(-1 : ℂ) ^ ((b ⬝ᵥ x).val) := by
      intro x
      rw [dotProduct_add, hbe]
      have hadd := neg_one_pow_zmod_add (b ⬝ᵥ x) 1
      rw [ZMod.val_one, pow_one] at hadd
      rw [hadd, mul_neg, mul_one]
    exact sum_eq_zero_of_involution_neg (fun x => (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) e hneg

/-- Trace of merged `pauliXZ`: `2^k` at `(0,0)`, else `0`. -/
private theorem trace_pauliXZ {k : ℕ} (a b : Fin k → ZMod 2) :
    Matrix.trace (pauliXZ a b) = (if a = 0 ∧ b = 0 then (2 : ℂ) ^ k else 0) := by
  have htrace : Matrix.trace (pauliXZ a b) = ∑ x, pauliXZ a b x x := by
    simp [Matrix.trace, Matrix.diag_apply]
  rw [htrace]
  simp only [pauliXZ_apply]
  by_cases ha : a = 0
  · subst ha
    simp only [add_zero, ↓reduceIte, true_and]
    exact char_sum b
  · have hfalse : ∀ x : Fin k → ZMod 2, ¬(x = x + a) := by
      intro x hx
      exact ha ((left_eq_add).mp hx)
    have hsum : (∑ x : Fin k → ZMod 2, (if x = x + a then (-1 : ℂ) ^ ((b ⬝ᵥ x).val) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg (hfalse x)]
    have hcond : ¬(a = 0 ∧ b = 0) := by simp [ha]
    rw [hsum, if_neg hcond]

/-- Merged `pauliXZ 0 0` is the identity. -/
private theorem pauliXZ_zero_zero {k : ℕ} : pauliXZ (0 : Fin k → ZMod 2) (0 : Fin k → ZMod 2) = 1 := by
  ext y x
  rw [pauliXZ_apply, add_zero]
  have hdot : ∀ x : Fin k → ZMod 2, (0 : Fin k → ZMod 2) ⬝ᵥ x = 0 := zero_dotProduct
  rw [hdot, ZMod.val_zero, pow_zero]
  by_cases h : y = x <;> simp [h, Matrix.one_apply]

/-- `star` fixes `(-1)^n` over `ℂ`. -/
private theorem star_neg_one_pow (n : ℕ) : star ((-1 : ℂ) ^ n) = (-1 : ℂ) ^ n := by
  rw [star_pow]
  have hs1 : star (-1 : ℂ) = -1 := by rw [star_neg, star_one]
  rw [hs1]

/-- The Hermitian Pauli string `hermPauli a b` is Hermitian: the phase `i^|a∧b|` makes `X^a Z^b` self-adjoint. -/
theorem hermPauli_isHermitian {k : ℕ} (a b : Fin k → ZMod 2) : (hermPauli a b).IsHermitian := by
  unfold Matrix.IsHermitian
  ext y x
  rw [Matrix.conjTranspose_apply]
  unfold hermPauli
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, pauliXZ_apply, pauliXZ_apply]
  have haa : a + a = (0 : Fin k → ZMod 2) := bit_add_self a
  have hiff : (x = y + a) ↔ (y = x + a) := by
    constructor
    · intro h
      have h2 : (y + a) + a = y := by rw [add_assoc, haa, add_zero]
      rw [← h] at h2
      exact h2.symm
    · intro h
      have h2 : (x + a) + a = x := by rw [add_assoc, haa, add_zero]
      rw [← h] at h2
      exact h2.symm
  by_cases h : y = x + a
  · have hx : x = y + a := hiff.mpr h
    rw [if_pos hx, if_pos h]
    have hby : b ⬝ᵥ y = b ⬝ᵥ x + b ⬝ᵥ a := by rw [h, dotProduct_add]
    rw [hby, neg_one_pow_zmod_add, star_mul, star_mul, star_neg_one_pow, star_neg_one_pow]
    have hstar_pow : star (Complex.I ^ (∑ i, (a i).val * (b i).val)) =
        (-Complex.I) ^ (∑ i, (a i).val * (b i).val) := by
      rw [star_pow, Complex.star_def, Complex.conj_I]
    rw [hstar_pow]
    have hneg_pow : (-Complex.I) ^ (∑ i, (a i).val * (b i).val) =
        (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val) := by
      have hni : (-Complex.I) = (-1 : ℂ) * Complex.I := by ring
      rw [hni, mul_pow]
    rw [hneg_pow]
    have hphase : (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ a).val) = 1 := by
      rw [neg_one_pow_dot_val]
      exact neg_one_pow_mul_self _
    calc (-1 : ℂ) ^ ((b ⬝ᵥ a).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val) *
          (((-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val)))
        = (Complex.I ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) *
          ((-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ a).val)) := by ring
      _ = (Complex.I ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) * 1 := by rw [hphase]
      _ = Complex.I ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val) := by rw [mul_one]
  · have hx : ¬(x = y + a) := fun hh => h (hiff.mp hh)
    rw [if_neg hx, if_neg h]
    simp [mul_zero, star_zero]

/-- ±1 parity outcomes; via merged pauliXZ_mul -/
theorem hermPauli_mul_self {k : ℕ} (a b : Fin k → ZMod 2) : hermPauli a b * hermPauli a b = 1 := by
  unfold hermPauli
  rw [smul_mul_smul_comm, pauliXZ_mul]
  have ha : a + a = (0 : Fin k → ZMod 2) := bit_add_self a
  have hb : b + b = (0 : Fin k → ZMod 2) := bit_add_self b
  rw [ha, hb, pauliXZ_zero_zero, ← mul_smul]
  have hphase : (Complex.I ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val)) *
      (-1 : ℂ) ^ ((b ⬝ᵥ a).val) = 1 := by
    rw [neg_one_pow_dot_val]
    exact phase_mul_self _
  rw [hphase, one_smul]

/-- Hilbert-Schmidt orthogonality -/
theorem trace_hermPauli_mul_hermPauli {k : ℕ} (a b a' b' : Fin k → ZMod 2) : Matrix.trace (hermPauli a b * hermPauli a' b') = if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0 := by
  unfold hermPauli
  rw [smul_mul_smul_comm, pauliXZ_mul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hequiv : (a + a' = 0 ∧ b + b' = 0) ↔ (a = a' ∧ b = b') := by
    constructor
    · intro hcon
      have ha : a = a' := (bit_add_eq_zero_iff a a').mp hcon.1
      have hb : b = b' := (bit_add_eq_zero_iff b b').mp hcon.2
      exact ⟨ha, hb⟩
    · intro hcon
      obtain ⟨rfl, rfl⟩ := hcon
      exact ⟨bit_add_self a, bit_add_self b⟩
  have htr := trace_pauliXZ (a + a') (b + b')
  by_cases h : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h
    have hcond : a + a = (0 : Fin k → ZMod 2) ∧ b + b = (0 : Fin k → ZMod 2) :=
      ⟨bit_add_self a, bit_add_self b⟩
    rw [if_pos hcond] at htr
    rw [htr]
    have hphase : (Complex.I ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val)) *
        (-1 : ℂ) ^ ((b ⬝ᵥ a).val) = 1 := by
      rw [neg_one_pow_dot_val]
      exact phase_mul_self _
    rw [hphase, one_mul, if_pos ⟨rfl, rfl⟩]
  · have hneg : ¬(a + a' = 0 ∧ b + b' = 0) := fun hh => h (hequiv.mp hh)
    rw [if_neg hneg] at htr
    rw [htr, mul_zero, if_neg h]

/-- `(-1)^n = -1` when `n` is odd. -/
private theorem neg_one_pow_eq_neg_one_of_odd {n : ℕ} (h : n % 2 = 1) : (-1 : ℂ) ^ n = -1 := by
  conv_lhs => rw [← Nat.div_add_mod n 2, h, pow_add, pow_mul]
  have h2 : (-1 : ℂ) ^ 2 = 1 := by ring
  rw [h2, one_pow, pow_one, one_mul]

/-- Single-coordinate sign flip when `ai ≠ ui + xi`. -/
private theorem coord_flip {ai ui xi bi : ZMod 2} (hne : ai ≠ ui + xi) :
    (-1 : ℂ) ^ (ai.val * ((bi + 1).val)) * (-1 : ℂ) ^ (((bi + 1) * ui).val) * (-1 : ℂ) ^ (((bi + 1) * xi).val)
    = -((-1 : ℂ) ^ (ai.val * (bi.val)) * (-1 : ℂ) ^ ((bi * ui).val) * (-1 : ℂ) ^ ((bi * xi).val)) := by
  have hval_add := ZMod.val_add ui xi
  have hinj : ∀ x y : ZMod 2, x.val = y.val → x = y := by decide
  have hne_val : ai.val ≠ (ui + xi).val := fun heq => hne (hinj _ _ heq)
  have hle1 : ai.val ≤ 1 := by
    have h : ∀ x : ZMod 2, x.val ≤ 1 := by decide
    exact h ai
  have hle2 : (ui + xi).val ≤ 1 := by
    have h : ∀ x : ZMod 2, x.val ≤ 1 := by decide
    exact h (ui + xi)
  have hsum1 : ai.val + (ui + xi).val = 1 := by omega
  have hodd : (ai.val + ui.val + xi.val) % 2 = 1 := by omega
  have hg1 : (-1 : ℂ) ^ (ai.val * (1 : ZMod 2).val) * (-1 : ℂ) ^ (((1 : ZMod 2) * ui).val) *
      (-1 : ℂ) ^ (((1 : ZMod 2) * xi).val) = -1 := by
    rw [ZMod.val_one, mul_one, one_mul, one_mul, ← pow_add, ← pow_add]
    exact neg_one_pow_eq_neg_one_of_odd hodd
  have hg0 : (-1 : ℂ) ^ (ai.val * (0 : ZMod 2).val) * (-1 : ℂ) ^ (((0 : ZMod 2) * ui).val) *
      (-1 : ℂ) ^ (((0 : ZMod 2) * xi).val) = 1 := by
    rw [ZMod.val_zero, mul_zero, zero_mul, zero_mul, ZMod.val_zero,
      pow_zero, mul_one, mul_one]
  rcases zmod2_eq_zero_or_one bi with rfl | rfl
  · have h01 : (0 : ZMod 2) + 1 = 1 := zero_add _
    rw [h01, hg1, hg0]
  · have h10 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [h10, hg0, hg1, neg_neg]

/-- Inner character sum over `b` with overlap phase: `2^k` if `a = u + x`, else `0`. -/
private theorem inner_sum_b {k : ℕ} (a u x : Fin k → ZMod 2) :
    (∑ b, (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val))
    = (if a = u + x then (2 : ℂ) ^ k else 0) := by
  by_cases h : a = u + x
  · subst h
    have h1 : ∀ b : Fin k → ZMod 2,
        (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) *
          (-1 : ℂ) ^ ((b ⬝ᵥ x).val) = 1 := by
      intro b
      have hdot : b ⬝ᵥ u + b ⬝ᵥ x = b ⬝ᵥ (u + x) := (dotProduct_add b u x).symm
      have hmul : (-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val) =
          (-1 : ℂ) ^ ((b ⬝ᵥ (u + x)).val) := by
        rw [← neg_one_pow_zmod_add, hdot]
      have hdot_eq : (-1 : ℂ) ^ ((b ⬝ᵥ (u + x)).val) =
          (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) := by
        have hdef : b ⬝ᵥ (u + x) = ∑ i, b i * (u + x) i := rfl
        rw [hdef, neg_one_pow_sum_val]
        have h2 : ∀ i : Fin k, (-1 : ℂ) ^ ((b i * (u + x) i).val) =
            (-1 : ℂ) ^ (((u + x) i).val * (b i).val) := by
          intro i
          have hm : ∀ p q : ZMod 2, (p * q).val = p.val * q.val := by decide
          rw [hm, mul_comm]
        rw [Finset.prod_congr rfl (fun i _ => h2 i), ← Finset.prod_pow_eq_pow_sum]
      calc (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) *
            (-1 : ℂ) ^ ((b ⬝ᵥ x).val)
          = (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) *
            ((-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) := by ring
        _ = (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ (u + x)).val) := by rw [hmul]
        _ = (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) *
            (-1 : ℂ) ^ (∑ i, ((u + x) i).val * (b i).val) := by rw [hdot_eq]
        _ = 1 := neg_one_pow_mul_self _
    simp only [h1]
    have hsum : (∑ _b : Fin k → ZMod 2, (1 : ℂ)) = (2 : ℂ) ^ k := by
      have hc : (∑ _b : Fin k → ZMod 2, (1 : ℂ)) = (Fintype.card (Fin k → ZMod 2) : ℂ) := by simp
      rw [hc, card_bitstring]
      norm_cast
    rw [if_pos trivial]
    exact hsum
  · rw [if_neg h]
    have hex : ∃ i, a i ≠ (u + x) i := by
      by_contra hcon
      push_neg at hcon
      exact h (funext hcon)
    obtain ⟨i, hi⟩ := hex
    have hpi : a i ≠ (u i + x i) := by
      have hpx : (u + x) i = u i + x i := Pi.add_apply u x i
      rw [hpx] at hi
      exact hi
    let e : Fin k → ZMod 2 := fun j => if j = i then 1 else 0
    have he_pts : ∀ j : Fin k, ∀ b : Fin k → ZMod 2, ((b + e) j = if j = i then b j + 1 else b j) := by
      intro j b
      simp only [Pi.add_apply, e]
      by_cases hj : j = i <;> simp [hj]
    apply sum_eq_zero_of_involution_neg _ e
    intro b
    have hprod1 : (-1 : ℂ) ^ (∑ j, (a j).val * ((b + e) j).val) =
        ∏ j, (-1 : ℂ) ^ ((a j).val * ((b + e) j).val) := by
      rw [← Finset.prod_pow_eq_pow_sum]
    have hprod1b : (-1 : ℂ) ^ (∑ j, (a j).val * (b j).val) =
        ∏ j, (-1 : ℂ) ^ ((a j).val * (b j).val) := by
      rw [← Finset.prod_pow_eq_pow_sum]
    have hdefu : b ⬝ᵥ u = ∑ j, b j * u j := rfl
    have hdefu' : (b + e) ⬝ᵥ u = ∑ j, (b + e) j * u j := rfl
    have hdefx : b ⬝ᵥ x = ∑ j, b j * x j := rfl
    have hdefx' : (b + e) ⬝ᵥ x = ∑ j, (b + e) j * x j := rfl
    rw [hprod1, hprod1b, hdefu, hdefu', hdefx, hdefx', neg_one_pow_sum_val, neg_one_pow_sum_val,
      neg_one_pow_sum_val, neg_one_pow_sum_val, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have hsplit : ∀ g : (Fin k → ZMod 2) → Fin k → ℂ,
        (∏ j, g b j) = g b i * ∏ j ∈ Finset.univ.erase i, g b j := by
      intro g
      exact (Finset.mul_prod_erase Finset.univ (fun j => g b j) (Finset.mem_univ i)).symm
    have hsame : ∀ j ∈ Finset.univ.erase i,
        ((-1 : ℂ) ^ ((a j).val * ((b + e) j).val) * (-1 : ℂ) ^ (((b + e) j * u j).val) *
          (-1 : ℂ) ^ (((b + e) j * x j).val))
        = ((-1 : ℂ) ^ ((a j).val * (b j).val) * (-1 : ℂ) ^ ((b j * u j).val) *
          (-1 : ℂ) ^ ((b j * x j).val)) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hbe : (b + e) j = b j := by
        rw [he_pts j b, if_neg hji]
      rw [hbe]
    have hflip : ((-1 : ℂ) ^ ((a i).val * ((b + e) i).val) * (-1 : ℂ) ^ (((b + e) i * u i).val) *
          (-1 : ℂ) ^ (((b + e) i * x i).val))
        = -((-1 : ℂ) ^ ((a i).val * (b i).val) * (-1 : ℂ) ^ ((b i * u i).val) *
          (-1 : ℂ) ^ ((b i * x i).val)) := by
      have hbei : (b + e) i = b i + 1 := by
        rw [he_pts i b, if_pos rfl]
      rw [hbei]
      exact coord_flip hpi
    rw [hsplit (fun c j => (-1 : ℂ) ^ ((a j).val * ((c + e) j).val) * (-1 : ℂ) ^ (((c + e) j * u j).val) *
        (-1 : ℂ) ^ (((c + e) j * x j).val))]
    rw [hsplit (fun c j => (-1 : ℂ) ^ ((a j).val * (c j).val) * (-1 : ℂ) ^ ((c j * u j).val) *
        (-1 : ℂ) ^ ((c j * x j).val))]
    have hrest : (∏ j ∈ Finset.univ.erase i, ((-1 : ℂ) ^ ((a j).val * ((b + e) j).val) *
          (-1 : ℂ) ^ (((b + e) j * u j).val) * (-1 : ℂ) ^ (((b + e) j * x j).val)))
        = ∏ j ∈ Finset.univ.erase i, ((-1 : ℂ) ^ ((a j).val * (b j).val) *
          (-1 : ℂ) ^ ((b j * u j).val) * (-1 : ℂ) ^ ((b j * x j).val)) :=
      Finset.prod_congr rfl hsame
    rw [hrest, hflip, neg_mul]

/-- `v = u + a ↔ a = v + u` on bitstrings. -/
private theorem eq_add_iff {k : ℕ} (v u a : Fin k → ZMod 2) : (v = u + a) ↔ (a = v + u) := by
  have huu : u + u = (0 : Fin k → ZMod 2) := bit_add_self u
  have haa : a + a = (0 : Fin k → ZMod 2) := bit_add_self a
  constructor
  · intro h
    have h1 : (u + a) + u = v + u := by rw [← h]
    rw [add_assoc, add_comm a u, ← add_assoc, huu, zero_add] at h1
    exact h1
  · intro h
    have h1 : (v + u) + u = a + u := by rw [← h]
    rw [add_assoc, huu, add_zero, add_comm a u] at h1
    exact h1

/-- Entrywise orthogonality of Hermitian Pauli strings. -/
private theorem entry_orth {k : ℕ} (v u y x : Fin k → ZMod 2) :
    (∑ a, ∑ b, hermPauli (k := k) a b v u * hermPauli (k := k) a b y x)
    = (if v = x ∧ u = y then (2 : ℂ) ^ k else 0) := by
  have hexpand : ∀ a b : Fin k → ZMod 2,
      hermPauli a b v u * hermPauli a b y x =
      (if v = u + a ∧ y = x + a then
        (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)
      else 0) := by
    intro a b
    unfold hermPauli
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, pauliXZ_apply, pauliXZ_apply]
    have hsq : Complex.I ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val) =
        (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) := by
      have hI2 : Complex.I ^ 2 = -1 := by
        have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
        rw [pow_two]; exact h
      rw [← pow_add, ← two_mul, pow_mul, hI2]
    by_cases hv : v = u + a <;> by_cases hy : y = x + a
    · rw [if_pos hv, if_pos hy, if_pos ⟨hv, hy⟩]
      calc (Complex.I ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val)) *
            (Complex.I ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val))
          = (Complex.I ^ (∑ i, (a i).val * (b i).val) * Complex.I ^ (∑ i, (a i).val * (b i).val)) *
            ((-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)) := by ring
        _ = (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) *
            (-1 : ℂ) ^ ((b ⬝ᵥ x).val) := by rw [hsq]; ring
    · rw [if_pos hv, if_neg hy, if_neg (fun hcon => hy hcon.2), mul_zero, mul_zero]
    · rw [if_neg hv, if_pos hy, if_neg (fun hcon => hv hcon.1), mul_zero, zero_mul]
    · rw [if_neg hv, if_neg hy, if_neg (fun hcon => hv hcon.1), mul_zero, zero_mul]
  simp only [hexpand]
  have hsum_b : ∀ a : Fin k → ZMod 2,
      (∑ b, (if v = u + a ∧ y = x + a then
        (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)
      else 0))
      = (if v = u + a ∧ y = x + a ∧ a = u + x then (2 : ℂ) ^ k else 0) := by
    intro a
    by_cases hcond : v = u + a ∧ y = x + a
    · simp only [if_pos hcond]
      have hinner := inner_sum_b (k := k) a u x
      by_cases hax : a = u + x
      · rw [if_pos hax] at hinner
        have h3 : v = u + a ∧ y = x + a ∧ a = u + x := ⟨hcond.1, hcond.2, hax⟩
        rw [if_pos h3]; exact hinner
      · rw [if_neg hax] at hinner
        have h3 : ¬(v = u + a ∧ y = x + a ∧ a = u + x) := fun hh => hax hh.2.2
        rw [if_neg h3]; exact hinner
    · have hsum0 : (∑ b : Fin k → ZMod 2, (if v = u + a ∧ y = x + a then
          (-1 : ℂ) ^ (∑ i, (a i).val * (b i).val) * (-1 : ℂ) ^ ((b ⬝ᵥ u).val) * (-1 : ℂ) ^ ((b ⬝ᵥ x).val)
        else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro b _; rw [if_neg hcond]
      have h3 : ¬(v = u + a ∧ y = x + a ∧ a = u + x) := fun hh => hcond ⟨hh.1, hh.2.1⟩
      rw [hsum0, if_neg h3]
  simp only [hsum_b]
  have hiff : ∀ a : Fin k → ZMod 2, (v = u + a ∧ y = x + a ∧ a = u + x) ↔
      (a = v + u ∧ a = y + x ∧ a = u + x) := by
    intro a
    constructor
    · intro hh; exact ⟨(eq_add_iff v u a).mp hh.1, (eq_add_iff y x a).mp hh.2.1, hh.2.2⟩
    · intro hh; exact ⟨(eq_add_iff v u a).mpr hh.1, (eq_add_iff y x a).mpr hh.2.1, hh.2.2⟩
  by_cases h : v = x ∧ u = y
  · obtain ⟨hvx, huy⟩ := h
    have hvx' := hvx.symm
    have huy' := huy.symm
    subst hvx'
    subst huy'
    have hsame : ∀ a : Fin k → ZMod 2, (a = x + y ∧ a = y + x ∧ a = y + x) ↔ a = x + y := by
      intro a
      constructor
      · intro hh; exact hh.1
      · intro ha; subst ha; simp [add_comm]
    have hsum : (∑ a : Fin k → ZMod 2, (if x = y + a ∧ y = x + a ∧ a = y + x then (2 : ℂ) ^ k else 0)) =
        (2 : ℂ) ^ k := by
      have hcongr : ∀ a : Fin k → ZMod 2, (if x = y + a ∧ y = x + a ∧ a = y + x then (2 : ℂ) ^ k else 0) =
          (if a = x + y then (2 : ℂ) ^ k else 0) := by
        intro a
        by_cases ha : a = x + y
        · have h3 : x = y + a ∧ y = x + a ∧ a = y + x := by
            subst ha
            have e1 : x = y + (x + y) := (eq_add_iff x y (x + y)).mpr rfl
            have e2 : y = x + (x + y) := by
              have e : x + y = y + x := add_comm _ _
              rw [e]; exact (eq_add_iff y x (y + x)).mpr rfl
            exact ⟨e1, e2, add_comm _ _⟩
          rw [if_pos h3, if_pos ha]
        · have h3 : ¬(x = y + a ∧ y = x + a ∧ a = y + x) := by
            intro hh
            exact ha (((hiff a).mp hh).1)
          rw [if_neg h3, if_neg ha]
      rw [Finset.sum_congr rfl (fun a _ => hcongr a)]
      rw [Finset.sum_ite_eq' Finset.univ (x + y) (fun _ => (2 : ℂ) ^ k)]
      simp
    rw [if_pos ⟨rfl, rfl⟩]
    exact hsum
  · have hsum0 : (∑ a : Fin k → ZMod 2, (if v = u + a ∧ y = x + a ∧ a = u + x then (2 : ℂ) ^ k else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro hh
      have h3 := (hiff a).mp hh
      have e1 : v + u = u + x := h3.1.symm.trans h3.2.2
      have e2 : y + x = u + x := h3.2.1.symm.trans h3.2.2
      have hvx : v = x := by
        rw [add_comm u x] at e1
        exact add_right_cancel e1
      have huy : y = u := by
        have h4 : y + x = u + x := e2
        exact add_right_cancel h4
      exact h ⟨hvx, huy.symm⟩
    rw [hsum0, if_neg h]

/-- c_l = Tr(P_l H_j)/2^k (contract) -/
noncomputable def pauliCoeff {k : ℕ} (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) (a b : Fin k → ZMod 2) : ℂ := Matrix.trace (hermPauli a b * A) / 2 ^ k

/-- A4 reconstruction, per term (MNS: H_m = Σ_S c^m_S S) -/
theorem sum_pauliCoeff_smul_hermPauli {k : ℕ} (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) : ∑ a, ∑ b, pauliCoeff A a b • hermPauli a b = A := by
  have hne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  ext y x
  have hentry : ((∑ a, ∑ b, pauliCoeff A a b • hermPauli a b) y x)
      = ∑ a, ∑ b, ∑ v, ∑ u, (hermPauli a b v u * A u v * hermPauli a b y x) / 2 ^ k := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold pauliCoeff
    have htr : Matrix.trace (hermPauli a b * A) = ∑ v, ∑ u, hermPauli a b v u * A u v := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [htr, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hentry]
  have hfactor : ∀ a b v u : Fin k → ZMod 2,
      (hermPauli a b v u * A u v * hermPauli a b y x) / 2 ^ k =
      A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k) := by
    intro a b v u
    field_simp
  simp only [hfactor, ← Finset.mul_sum]
  have hswap1 : ∀ a : Fin k → ZMod 2, (∑ b, ∑ v, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k))
      = (∑ v, ∑ b, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k)) := fun a => Finset.sum_comm
  simp only [hswap1]
  have hswap2 : (∑ a, ∑ v, ∑ b, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k))
      = (∑ v, ∑ a, ∑ b, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k)) := Finset.sum_comm
  rw [hswap2]
  have hswap3 : ∀ v : Fin k → ZMod 2, (∑ a, ∑ b, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k))
      = (∑ u, ∑ a, ∑ b, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k)) := by
    intro v
    have h1 : (∑ a, ∑ b, ∑ u, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k))
        = (∑ a, ∑ u, ∑ b, A u v * ((hermPauli a b v u * hermPauli a b y x) / 2 ^ k)) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    rw [h1]
    exact Finset.sum_comm
  simp only [hswap3, ← Finset.mul_sum]
  have hinner : ∀ v u : Fin k → ZMod 2,
      (∑ a, ∑ b, (hermPauli a b v u * hermPauli a b y x) / 2 ^ k)
      = (if v = x ∧ u = y then (1 : ℂ) else 0) := by
    intro v u
    have horth := entry_orth (k := k) v u y x
    have hdiv : (∑ a, ∑ b, (hermPauli a b v u * hermPauli a b y x) / 2 ^ k)
        = (∑ a, ∑ b, hermPauli a b v u * hermPauli a b y x) / 2 ^ k := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.sum_div _ _ _).symm
    rw [hdiv, horth]
    by_cases hcon : v = x ∧ u = y
    · rw [if_pos hcon, if_pos hcon, div_self hne]
    · rw [if_neg hcon, if_neg hcon, zero_div]
  simp only [hinner]
  have hfinal : (∑ v, ∑ u, A u v * (if v = x ∧ u = y then (1 : ℂ) else 0)) = A y x := by
    have hinner2 : ∀ v : Fin k → ZMod 2, (∑ u, A u v * (if v = x ∧ u = y then (1 : ℂ) else 0))
        = (if v = x then A y x else 0) := by
      intro v
      by_cases hv : v = x
      · have hv' := hv.symm
        subst hv'
        have hcongr : ∀ u : Fin k → ZMod 2, A u x * (if x = x ∧ u = y then (1 : ℂ) else 0) =
            (if u = y then A u x else 0) := by
          intro u
          by_cases hu : u = y
          · subst hu; simp
          · have hcond : ¬(x = x ∧ u = y) := fun hh => hu hh.2
            rw [if_neg hcond, if_neg hu, mul_zero]
        rw [Finset.sum_congr rfl (fun u _ => hcongr u)]
        rw [Finset.sum_ite_eq' Finset.univ y (fun u => A u x)]
        simp
      · have h0 : (∑ u : Fin k → ZMod 2, A u v * (if v = x ∧ u = y then (1 : ℂ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro u _
          have hcond : ¬(v = x ∧ u = y) := fun hh => hv hh.1
          rw [if_neg hcond, mul_zero]
        rw [h0, if_neg hv]
    rw [Finset.sum_congr rfl (fun v _ => hinner2 v)]
    rw [Finset.sum_ite_eq' Finset.univ x (fun _ => A y x)]
    simp
  exact hfinal
/-- uniqueness of coefficients -/
theorem pauliCoeff_eq_of_sum_eq {k : ℕ} (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) (c : (Fin k → ZMod 2) → (Fin k → ZMod 2) → ℂ) (h : ∑ a, ∑ b, c a b • hermPauli a b = A) (a b : Fin k → ZMod 2) : c a b = pauliCoeff A a b := by
  unfold pauliCoeff
  have hne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hTr : Matrix.trace (hermPauli a b * A) = c a b * 2 ^ k := by
    rw [← h]
    simp only [Finset.mul_sum, Matrix.mul_smul]
    simp only [Matrix.trace_sum]
    simp only [Matrix.trace_smul]
    have hcollapse : (∑ a', ∑ b', c a' b' * Matrix.trace (hermPauli a b * hermPauli a' b'))
        = c a b * 2 ^ k := by
      have horth : ∀ a' b' : Fin k → ZMod 2, Matrix.trace (hermPauli a b * hermPauli a' b')
          = (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0) :=
        fun a' b' => trace_hermPauli_mul_hermPauli a b a' b'
      simp only [horth]
      have hinner : ∀ a' : Fin k → ZMod 2,
          (∑ b', c a' b' * (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0))
          = (if a' = a then c a b * 2 ^ k else 0) := by
        intro a'
        by_cases ha' : a' = a
        · cases ha'
          have hcongr : ∀ b' : Fin k → ZMod 2,
              c a b' * (if a = a ∧ b = b' then (2 : ℂ) ^ k else 0) =
              (if b' = b then c a b' * 2 ^ k else 0) := by
            intro b'
            by_cases hb' : b' = b
            · subst hb'; simp
            · have hcond : ¬(a = a ∧ b = b') := by
                intro hh; exact hb' (eq_comm.mp hh.2)
              rw [if_neg hcond, if_neg hb', mul_zero]
          rw [Finset.sum_congr rfl (fun b' _ => hcongr b')]
          rw [Finset.sum_ite_eq' Finset.univ b (fun b' => c a b' * 2 ^ k)]
          simp
        · have h0 : (∑ b' : Fin k → ZMod 2, c a' b' * (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro b' _
            have hcond : ¬(a = a' ∧ b = b') := fun hh => ha' (eq_comm.mp hh.1)
            rw [if_neg hcond, mul_zero]
          rw [h0, if_neg ha']
      rw [Finset.sum_congr rfl (fun a' _ => hinner a')]
      rw [Finset.sum_ite_eq' Finset.univ a (fun _ => c a b * 2 ^ k)]
      simp
    exact hcollapse
  rw [hTr]
  field_simp

/-- "real for Hermitian H_j" -/
theorem im_pauliCoeff_eq_zero {k : ℕ} {A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ} (hA : A.IsHermitian) (a b : Fin k → ZMod 2) : (pauliCoeff A a b).im = 0 := by
  unfold pauliCoeff
  have hP := hermPauli_isHermitian (k := k) a b
  have hPe : Matrix.conjTranspose (hermPauli (k := k) a b) = hermPauli a b := hP
  have hAe : Matrix.conjTranspose A = A := hA
  have hstar : star (Matrix.trace (hermPauli a b * A)) = Matrix.trace (hermPauli a b * A) := by
    have h1 : star (Matrix.trace (hermPauli a b * A))
        = Matrix.trace (Matrix.conjTranspose (hermPauli a b * A)) :=
      (Matrix.trace_conjTranspose _).symm
    rw [h1, Matrix.conjTranspose_mul, hPe, hAe, Matrix.trace_mul_comm]
  have him_tr : (Matrix.trace (hermPauli a b * A)).im = 0 := by
    have hcongr := congrArg Complex.im hstar
    have hsim : (star (Matrix.trace (hermPauli a b * A))).im = -(Matrix.trace (hermPauli a b * A)).im :=
      Complex.conj_im _
    rw [hsim] at hcongr
    linarith
  have hTr_eq : Matrix.trace (hermPauli a b * A) = ((Matrix.trace (hermPauli a b * A)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him_tr]
  have h2k_cast : (2 : ℂ) ^ k = (((2 ^ k : ℝ)) : ℂ) := by norm_cast
  rw [hTr_eq, h2k_cast, ← Complex.ofReal_div, Complex.ofReal_im]

/-- `star z * z = ‖z‖^2` as a complex cast (via `Complex.sq_abs` and `ext`). -/
private theorem star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have hstar : star z = (starRingEnd ℂ) z := rfl
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hstar]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, hsq]
    ring
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- Parseval in the Pauli basis -/
theorem sum_norm_sq_pauliCoeff {k : ℕ} (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) : ∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 = (∑ x, ∑ y, ‖A x y‖ ^ 2) / 2 ^ k := by
  have hne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hrec := sum_pauliCoeff_smul_hermPauli (k := k) A
  have hAh : Matrix.conjTranspose A = ∑ a, ∑ b, star (pauliCoeff A a b) • hermPauli a b := by
    conv_lhs => rw [← hrec]
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hPe : Matrix.conjTranspose (hermPauli (k := k) a b) = hermPauli a b :=
      hermPauli_isHermitian a b
    rw [Matrix.conjTranspose_smul, hPe]
  have hTr : Matrix.trace (Matrix.conjTranspose A * A)
      = (2 : ℂ) ^ k * ∑ a, ∑ b, ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) := by
    have hprod : Matrix.conjTranspose A * A
        = (∑ a, ∑ b, star (pauliCoeff A a b) • hermPauli a b)
          * (∑ a, ∑ b, pauliCoeff A a b • hermPauli a b) := by
      rw [hAh]
      congr 1
      exact hrec.symm
    have horth : ∀ (a b a' b' : Fin k → ZMod 2),
        Matrix.trace (hermPauli a b * hermPauli a' b')
          = (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0) :=
      fun a b a' b' => trace_hermPauli_mul_hermPauli a b a' b'
    have hcollapse : ∀ (a b : Fin k → ZMod 2),
        (∑ a', ∑ b', (star (pauliCoeff A a b) * pauliCoeff A a' b')
            * Matrix.trace (hermPauli a b * hermPauli a' b'))
          = (2 : ℂ) ^ k * ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) := by
      intro a b
      have hinner : ∀ a' : Fin k → ZMod 2,
          (∑ b', (star (pauliCoeff A a b) * pauliCoeff A a' b')
            * (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0))
          = (if a' = a then (2 : ℂ) ^ k * ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) else 0) := by
        intro a'
        by_cases ha' : a' = a
        · cases ha'
          have hcongr : ∀ b' : Fin k → ZMod 2,
              (star (pauliCoeff A a b) * pauliCoeff A a b')
              * (if a = a ∧ b = b' then (2 : ℂ) ^ k else 0) =
              (if b' = b then (star (pauliCoeff A a b) * pauliCoeff A a b') * 2 ^ k else 0) := by
            intro b'
            by_cases hb' : b' = b
            · subst hb'; simp
            · have hcond : ¬(a = a ∧ b = b') := by
                intro hh; exact hb' (eq_comm.mp hh.2)
              rw [if_neg hcond, if_neg hb', mul_zero]
          rw [Finset.sum_congr rfl (fun b' _ => hcongr b')]
          rw [Finset.sum_ite_eq' Finset.univ b
            (fun b' => (star (pauliCoeff A a b) * pauliCoeff A a b') * 2 ^ k)]
          simp only [Finset.mem_univ, eq_self_iff_true, if_true]
          rw [star_mul_self_eq_norm_sq]
          ring
        · have h0 : (∑ b' : Fin k → ZMod 2, (star (pauliCoeff A a b) * pauliCoeff A a' b')
              * (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro b' _
            have hcond : ¬(a = a' ∧ b = b') := fun hh => ha' (eq_comm.mp hh.1)
            rw [if_neg hcond, mul_zero]
          rw [h0, if_neg ha']
      have hstep : (∑ a', ∑ b', (star (pauliCoeff A a b) * pauliCoeff A a' b')
            * Matrix.trace (hermPauli a b * hermPauli a' b'))
          = ∑ a', ∑ b', (star (pauliCoeff A a b) * pauliCoeff A a' b')
            * (if a = a' ∧ b = b' then (2 : ℂ) ^ k else 0) := by
        apply Finset.sum_congr rfl
        intro a' _
        apply Finset.sum_congr rfl
        intro b' _
        rw [horth a b a' b']
      rw [hstep]
      rw [Finset.sum_congr rfl (fun a' _ => hinner a')]
      rw [Finset.sum_ite_eq' Finset.univ a
        (fun _ => (2 : ℂ) ^ k * ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ))]
      simp
    have hexpand : Matrix.trace (Matrix.conjTranspose A * A)
        = ∑ a, ∑ b, ∑ a', ∑ b', (star (pauliCoeff A a b) * pauliCoeff A a' b')
          * Matrix.trace (hermPauli a b * hermPauli a' b') := by
      rw [hprod]
      rw [Finset.sum_mul]
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro a' _
      rw [Finset.mul_sum]
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro b' _
      rw [smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    have hrhs : (2 : ℂ) ^ k * ∑ a, ∑ b, ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ)
        = ∑ a, ∑ b, (2 : ℂ) ^ k * ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    rw [hexpand, hrhs]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact hcollapse a b
  have hFrob : Matrix.trace (Matrix.conjTranspose A * A) = ∑ x, ∑ y, ((‖A x y‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact star_mul_self_eq_norm_sq (A x y)
  have hcast : (∑ a, ∑ b, ((‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ)) =
      (((∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 : ℝ)) : ℂ) := by
    simp [Complex.ofReal_sum]
  have hcast2 : (∑ x, ∑ y, ((‖A x y‖ ^ 2 : ℝ) : ℂ)) =
      (((∑ x, ∑ y, ‖A x y‖ ^ 2 : ℝ)) : ℂ) := by
    simp [Complex.ofReal_sum]
  rw [hcast] at hTr
  rw [hcast2] at hFrob
  have heq : ((∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) =
      ((∑ x, ∑ y, ‖A x y‖ ^ 2 : ℝ) : ℂ) / 2 ^ k := by
    have h2 : Matrix.trace (Matrix.conjTranspose A * A)
        = (2 : ℂ) ^ k * ((∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 : ℝ) : ℂ) := hTr
    rw [hFrob] at h2
    rw [eq_div_iff hne, h2]
    ring
  have h2k_cast : (2 : ℂ) ^ k = (((2 ^ k : ℝ)) : ℂ) := by norm_cast
  rw [h2k_cast, ← Complex.ofReal_div] at heq
  exact Complex.ofReal_injective heq

/-- Frobenius sum is at most `2 ^ k` for `0 ≤ A ≤ 1`, via positivity of `A - A * A` and eigenvalue traces. -/
private theorem frob_le_two_pow {k : ℕ} {A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ}
    (h0 : A.PosSemidef) (h1 : (1 - A).PosSemidef) :
    (∑ x, ∑ y, ‖A x y‖ ^ 2) ≤ 2 ^ k := by
  have hA : A.IsHermitian := h0.1
  have hAc : Matrix.conjTranspose A = A := hA
  have hentry : ∀ i j : Fin k → ZMod 2, A i j * A j i = ((‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    have h1c : Matrix.conjTranspose A j i = A j i :=
      congrArg (fun M : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ => M j i) hAc
    rw [Matrix.conjTranspose_apply] at h1c
    rw [h1c.symm, mul_comm, star_mul_self_eq_norm_sq]
  have hFrob : Matrix.trace (A * A) = ∑ x, ∑ y, ((‖A x y‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hentry x y
  have hcast : (∑ x, ∑ y, ((‖A x y‖ ^ 2 : ℝ) : ℂ)) =
      (((∑ x, ∑ y, ‖A x y‖ ^ 2 : ℝ)) : ℂ) := by
    simp [Complex.ofReal_sum]
  rw [hcast] at hFrob
  have hFrobre : (∑ x, ∑ y, ‖A x y‖ ^ 2) = (Matrix.trace (A * A)).re := by
    rw [hFrob, Complex.ofReal_re]
  have hAA : (A - A * A).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · show Matrix.conjTranspose (A - A * A) = A - A * A
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hAc]
    · intro x
      have g1 : (0 : ℂ) ≤ star (Matrix.mulVec A x) ⬝ᵥ (1 - A).mulVec (Matrix.mulVec A x) :=
        h1.dotProduct_mulVec_nonneg (Matrix.mulVec A x)
      have g2 : (0 : ℂ) ≤ star (x - Matrix.mulVec A x) ⬝ᵥ A.mulVec (x - Matrix.mulVec A x) :=
        h0.dotProduct_mulVec_nonneg (x - Matrix.mulVec A x)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at g1
      rw [Matrix.mulVec_sub, star_sub] at g2
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      have heq : star x ⬝ᵥ (Matrix.mulVec A x - Matrix.mulVec A (Matrix.mulVec A x))
          = (star x - star (Matrix.mulVec A x)) ⬝ᵥ
            (Matrix.mulVec A x - Matrix.mulVec A (Matrix.mulVec A x))
            + star (Matrix.mulVec A x) ⬝ᵥ
            (Matrix.mulVec A x - Matrix.mulVec A (Matrix.mulVec A x)) := by
        rw [← add_dotProduct, sub_add_cancel]
      rw [heq]
      exact add_nonneg g2 g1
  have hT1 : (Matrix.trace (A - A * A)).re = ∑ i, hAA.1.eigenvalues i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hAA.1]
    simp
  have hnn1 : 0 ≤ (Matrix.trace (A - A * A)).re := by
    rw [hT1]
    exact Finset.sum_nonneg (fun i _ => hAA.eigenvalues_nonneg i)
  have hT2 : (Matrix.trace (1 - A)).re = ∑ i, h1.1.eigenvalues i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues h1.1]
    simp
  have hnn2 : 0 ≤ (Matrix.trace (1 - A)).re := by
    rw [hT2]
    exact Finset.sum_nonneg (fun i _ => h1.eigenvalues_nonneg i)
  have hsub1 : Matrix.trace (A - A * A) = Matrix.trace A - Matrix.trace (A * A) :=
    Matrix.trace_sub _ _
  have hsub2 : Matrix.trace (1 - A) = Matrix.trace 1 - Matrix.trace A := Matrix.trace_sub _ _
  have h1r : (Matrix.trace (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ)).re = 2 ^ k := by
    rw [trace_one_bit]
    have hcast2 : (2 : ℂ) ^ k = (((2 ^ k : ℝ)) : ℂ) := by norm_cast
    rw [hcast2, Complex.ofReal_re]
  rw [hsub1, Complex.sub_re] at hnn1
  rw [hsub2, Complex.sub_re, h1r] at hnn2
  rw [hFrobre]
  linarith

/-- per-coefficient bound under the promise 0 ≤ H_j ≤ I -/
theorem norm_pauliCoeff_le_one {k : ℕ} {A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ} (h0 : A.PosSemidef) (h1 : (1 - A).PosSemidef) (a b : Fin k → ZMod 2) : ‖pauliCoeff A a b‖ ≤ 1 := by
  have hparse := sum_norm_sq_pauliCoeff (k := k) A
  have hF := frob_le_two_pow (k := k) h0 h1
  have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
  have hPl : (∑ x, ∑ y, ‖A x y‖ ^ 2) / 2 ^ k ≤ 1 := by
    rw [div_le_one h2k_pos]
    exact hF
  rw [← hparse] at hPl
  have h_single : ‖pauliCoeff A a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 := by
    have h1b : ‖pauliCoeff A a b‖ ^ 2 ≤ ∑ b', ‖pauliCoeff A a b'‖ ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun b' => ‖pauliCoeff A a b'‖ ^ 2) (a := b)
        (fun b' _ => by positivity) (Finset.mem_univ b)
    have h2b : (∑ b', ‖pauliCoeff A a b'‖ ^ 2) ≤ ∑ a', ∑ b', ‖pauliCoeff A a' b'‖ ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun a' => ∑ b', ‖pauliCoeff A a' b'‖ ^ 2) (a := a)
        (fun a' _ => Finset.sum_nonneg (fun b' _ => by positivity)) (Finset.mem_univ a)
    exact le_trans h1b h2b
  have h_le : ‖pauliCoeff A a b‖ ^ 2 ≤ 1 := le_trans h_single hPl
  have hnn : 0 ≤ ‖pauliCoeff A a b‖ := norm_nonneg _
  nlinarith [h_le, hnn, sq_nonneg (‖pauliCoeff A a b‖ - 1)]

/-- per-term half of "Λ ≤ 4^k m" -/
theorem sum_norm_pauliCoeff_le_four_pow {k : ℕ} {A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ} (h0 : A.PosSemidef) (h1 : (1 - A).PosSemidef) : ∑ a, ∑ b, ‖pauliCoeff A a b‖ ≤ 4 ^ k := by
  have h1c : ∀ a b : Fin k → ZMod 2, ‖pauliCoeff A a b‖ ≤ 1 :=
    fun a b => norm_pauliCoeff_le_one h0 h1 a b
  have hle : (∑ a, ∑ b, ‖pauliCoeff A a b‖) ≤ ∑ a : Fin k → ZMod 2, ∑ _b : Fin k → ZMod 2, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact h1c a b
  have hcard : (∑ _a : Fin k → ZMod 2, (1 : ℝ)) = 2 ^ k := by
    have hc : (∑ _a : Fin k → ZMod 2, (1 : ℝ)) = (Fintype.card (Fin k → ZMod 2) : ℝ) := by simp
    rw [hc, card_bitstring]
    norm_cast
  have hsum1 : (∑ a : Fin k → ZMod 2, ∑ _b : Fin k → ZMod 2, (1 : ℝ)) = (2 ^ k) * (2 ^ k) := by
    simp only [hcard, Finset.sum_const, Finset.card_univ, card_bitstring, nsmul_eq_mul]
    norm_cast
  have h4 : (4 : ℝ) ^ k = (2 ^ k) * (2 ^ k) := by
    have h44 : (4 : ℝ) = 2 * 2 := by norm_num
    rw [h44, mul_pow]
  rw [h4]
  exact le_trans hle (le_of_eq hsum1)

/-- Cauchy-Schwarz half of "Λ ≤ 2m for valid Atlas 2-local Frobenius terms" (k = 2, Frobenius ≤ 1 gives Σ|c| ≤ 2) -/
theorem sq_sum_norm_pauliCoeff_le {k : ℕ} (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) : (∑ a, ∑ b, ‖pauliCoeff A a b‖) ^ 2 ≤ 2 ^ k * ∑ x, ∑ y, ‖A x y‖ ^ 2 := by
  have hparse := sum_norm_sq_pauliCoeff (k := k) A
  have hcard : (∑ _a : Fin k → ZMod 2, (1 : ℝ)) = 2 ^ k := by
    have hc : (∑ _a : Fin k → ZMod 2, (1 : ℝ)) = (Fintype.card (Fin k → ZMod 2) : ℝ) := by simp
    rw [hc, card_bitstring]
    norm_cast
  have hinner : ∀ a : Fin k → ZMod 2, (∑ b, ‖pauliCoeff A a b‖) ^ 2 ≤ 2 ^ k * ∑ b, ‖pauliCoeff A a b‖ ^ 2 := by
    intro a
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun _ : Fin k → ZMod 2 => (1 : ℝ))
      (g := fun b => ‖pauliCoeff A a b‖)
    simp only [one_mul, one_pow] at hcs
    rw [hcard] at hcs
    exact hcs
  have houter : (∑ a, ∑ b, ‖pauliCoeff A a b‖) ^ 2 ≤ 2 ^ k * ∑ a, (∑ b, ‖pauliCoeff A a b‖) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun _ : Fin k → ZMod 2 => (1 : ℝ))
      (g := fun a => ∑ b, ‖pauliCoeff A a b‖)
    simp only [one_mul, one_pow] at hcs
    rw [hcard] at hcs
    exact hcs
  have hsum_le : (∑ a, (∑ b, ‖pauliCoeff A a b‖) ^ 2) ≤ 2 ^ k * ∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2 := by
    have hpt : ∀ a : Fin k → ZMod 2, (∑ b, ‖pauliCoeff A a b‖) ^ 2 ≤ 2 ^ k * ∑ b, ‖pauliCoeff A a b‖ ^ 2 :=
      hinner
    have hle : (∑ a, (∑ b, ‖pauliCoeff A a b‖) ^ 2) ≤ ∑ a, (2 ^ k * ∑ b, ‖pauliCoeff A a b‖ ^ 2) :=
      Finset.sum_le_sum (fun a _ => hpt a)
    rw [← Finset.mul_sum] at hle
    exact hle
  have h2k_nn : (0 : ℝ) ≤ 2 ^ k := by positivity
  calc (∑ a, ∑ b, ‖pauliCoeff A a b‖) ^ 2
      ≤ 2 ^ k * ∑ a, (∑ b, ‖pauliCoeff A a b‖) ^ 2 := houter
    _ ≤ 2 ^ k * (2 ^ k * ∑ a, ∑ b, ‖pauliCoeff A a b‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hsum_le h2k_nn
    _ = 2 ^ k * ∑ x, ∑ y, ‖A x y‖ ^ 2 := by
        rw [hparse]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp

/-- "Λ = 0 then H = 0 by reconstruction" (consumed later by qma-lh--edge-cases) -/
theorem eq_zero_of_sum_norm_pauliCoeff_eq_zero {k : ℕ} {A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ} (h : ∑ a, ∑ b, ‖pauliCoeff A a b‖ = 0) : A = 0 := by
  have hnn : ∀ a b : Fin k → ZMod 2, 0 ≤ ‖pauliCoeff A a b‖ := fun a b => norm_nonneg _
  have houter : ∀ a : Fin k → ZMod 2, ∑ b, ‖pauliCoeff A a b‖ = 0 := by
    have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun a : Fin k → ZMod 2 => ∑ b, ‖pauliCoeff A a b‖)
    have hnn_out : ∀ a ∈ Finset.univ, 0 ≤ ∑ b, ‖pauliCoeff A a b‖ := by
      intro a _
      apply Finset.sum_nonneg
      intro b _
      exact hnn a b
    rw [hiff hnn_out] at h
    intro a
    exact h a (Finset.mem_univ a)
  have hpt : ∀ a b : Fin k → ZMod 2, ‖pauliCoeff A a b‖ = 0 := by
    intro a b
    have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun b' : Fin k → ZMod 2 => ‖pauliCoeff A a b'‖)
    have hnn_in : ∀ b' ∈ Finset.univ, 0 ≤ ‖pauliCoeff A a b'‖ := fun b' _ => hnn a b'
    have ha := houter a
    rw [hiff hnn_in] at ha
    exact ha b (Finset.mem_univ b)
  have hc0 : ∀ a b : Fin k → ZMod 2, pauliCoeff A a b = 0 := fun a b => norm_eq_zero.mp (hpt a b)
  have hrec := sum_pauliCoeff_smul_hermPauli (k := k) A
  have hsum0 : (∑ a, ∑ b, pauliCoeff A a b • hermPauli a b) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [hc0 a b, zero_smul]
  rw [hsum0] at hrec
  exact hrec.symm

/-- sign(0) = +1 rule -/
noncomputable def signOne (c : ℝ) : ℝ := if 0 ≤ c then 1 else -1

/-- sign/normalization -/
theorem signOne_mul_abs (c : ℝ) : signOne c * |c| = c := by
  unfold signOne
  by_cases hc : 0 ≤ c
  · rw [if_pos hc, abs_of_nonneg hc, one_mul]
  · rw [if_neg hc]
    have hlt : c < 0 := lt_of_not_ge hc
    rw [abs_of_neg hlt]
    ring

/-- labeled-unmerged MNS eqs. (4)-(5): label mass |c_l|/Λ (zero-coefficient labels get mass 0), accept iff sign(c_l)·parity = -1, e l = ⟨ψ|P_l|ψ⟩; RHS = 1/2 - E/(2Λ) once E = Σ_l c_l e_l; e l are Pauli expectation values, hence |e l| ≤ 1, so each acceptance factor (1 - signOne (c l) * e l) / 2 lies in [0, 1] -/
theorem pauliTest_acceptance_eq {L : Type*} [Fintype L] (c e : L → ℝ) (hΛ : 0 < ∑ l, |c l|) (he : ∀ l, |e l| ≤ 1) : ∑ l, |c l| / (∑ l', |c l'|) * ((1 - signOne (c l) * e l) / 2) = 1 / 2 - (∑ l, c l * e l) / (2 * ∑ l, |c l|) := by
  have hne : (∑ l, |c l|) ≠ 0 := ne_of_gt hΛ
  have h2ne : (2 : ℝ) * ∑ l, |c l| ≠ 0 := by
    apply mul_ne_zero _ hne
    norm_num
  have hterm : ∀ l : L, |c l| / (∑ l', |c l'|) * ((1 - signOne (c l) * e l) / 2)
      = (|c l| * (1 - signOne (c l) * e l)) / (2 * ∑ l, |c l|) := by
    intro l
    field_simp
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  simp only [← div_eq_mul_inv]
  have hnum : (∑ l, |c l| * (1 - signOne (c l) * e l)) = (∑ l, |c l|) - ∑ l, c l * e l := by
    have hexpand : ∀ l : L, |c l| * (1 - signOne (c l) * e l) = |c l| - c l * e l := by
      intro l
      have hs := signOne_mul_abs (c l)
      have hcomm : |c l| * signOne (c l) = c l := by rw [mul_comm]; exact hs
      calc |c l| * (1 - signOne (c l) * e l)
          = |c l| - |c l| * (signOne (c l) * e l) := by ring
        _ = |c l| - (|c l| * signOne (c l)) * e l := by ring
        _ = |c l| - c l * e l := by rw [hcomm]
    rw [Finset.sum_congr rfl (fun l _ => hexpand l)]
    rw [Finset.sum_sub_distrib]
  rw [hnum]
  field_simp

/-- labeled-unmerged reconstruction H = Σ_l c_l P_l through arbitrary linear embeddings (labels may repeat an embedded operator); the k-local-encoding P_emb instantiates emb -/
theorem sum_linearMap_eq_sum_pauliCoeff {k : ℕ} {J V : Type*} [Fintype J] [AddCommGroup V] [Module ℂ V] (emb : J → Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ →ₗ[ℂ] V) (A : J → Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) : ∑ j, emb j (A j) = ∑ j, ∑ a, ∑ b, pauliCoeff (A j) a b • emb j (hermPauli a b) := by
  -- Blueprint adaptation by linearity: each local term reconstructs in the Pauli basis
  -- (MNS Sec. IV), and the embedding passes through the sums by linearity.
  apply Finset.sum_congr rfl
  intro j _
  have hrec := sum_pauliCoeff_smul_hermPauli (k := k) (A j)
  conv_lhs => rw [← hrec]
  rw [map_sum (emb j)]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum (emb j)]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul (emb j)]

end MathlibExt.Quantum.PauliExpansion
