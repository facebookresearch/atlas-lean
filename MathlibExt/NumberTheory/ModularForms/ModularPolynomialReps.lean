/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Representatives for the modular polynomial

For a positive integer `N` let `C_N` (`WLight.modularPolynomialReps N`) be the finite set of
integer matrices `!![a, b; 0, d]` with `a > 0`, `0 ≤ b < d`, `a d = N` and
`gcd(a, b, d) = 1`. These index the roots `j(Mτ)` of the modular polynomial
$\Phi_N(X) = \prod_{M \in C_N} (X - j(M\tau))$.

This file proves the matrix combinatorics behind the `SL₂(ℤ)`-invariance of the coefficients of
that product:

* every integer matrix of determinant `N` whose entries have no common non-unit divisor is
  `γ M` with `γ ∈ SL₂(ℤ)` and `M ∈ C_N` (`WLight.exists_eq_mul_of_det`), and `M` is unique
  (`WLight.modularPolynomialReps_eq_of_mul_eq`); this is Hermite normal form;
* hence for each `γ ∈ SL₂(ℤ)` right multiplication by `γ` permutes the orbits `SL₂(ℤ) M`,
  `M ∈ C_N`: there are a permutation `σ` of `C_N` and `δ : C_N → SL₂(ℤ)` with
  `M γ = δ(M) σ(M)` (`WLight.modularPolynomialReps_exists_equiv_mul_eq`);
* for a prime `p`, `C_p` consists of `!![p, 0; 0, 1]` and the `p` matrices `!![1, b; 0, p]`,
  `0 ≤ b < p` (`WLight.modularPolynomialReps_prime`), so it has `p + 1` elements
  (`WLight.card_modularPolynomialReps_prime`).

Sources: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Lemma 5.13
and Remark 5.14, p. 72; Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT,
Fall 2025, Lecture 19, Lemma 19.16 and the proof of Theorem 19.17, pp. 7–8.
-/

@[expose] public section

set_option autoImplicit false

open Matrix MatrixGroups

namespace WLight

/-- The set `C_N` of integer matrices `!![a, b; 0, d]` with `1 ≤ a`, `0 ≤ b < d`, `a d = N` and
`gcd(gcd(a, b), d) = 1`, as a finite set (the bounds `a, d ≤ N`, `b < N` that make it finite
follow from the other conditions when `N > 0`; for `N = 0` the set is empty).

Source: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Lemma 5.13,
p. 72, normal form "ad = n, a ≥ 1, 0 ≤ b < d"; the condition `gcd(a, b, d) = 1` selects the
primitive matrices. For prime `N` these are the matrices of Sutherland, *18.783 Elliptic Curves*,
MIT, Fall 2025, Lecture 19, proof of Theorem 19.17, p. 8, where
"jN(γk τ) = j((τ + k)/N)" and "jN(τ) = j(Nτ)". -/
def modularPolynomialReps (N : ℕ) : Finset (Matrix (Fin 2) (Fin 2) ℤ) :=
  ((Finset.Icc (1 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N ×ˢ Finset.Icc (1 : ℤ) N).filter
      fun t => t.1 * t.2.2 = (N : ℤ) ∧ t.2.1 < t.2.2 ∧
        Int.gcd (Int.gcd t.1 t.2.1) t.2.2 = 1).image
    fun t => !![t.1, t.2.1; 0, t.2.2]

/-- Membership in `C_N`: `M ∈ C_N` if and only if `M 1 0 = 0`, `0 < M 0 0`,
`0 ≤ M 0 1 < M 1 1`, `M 0 0 * M 1 1 = N` and `gcd(gcd(M 0 0, M 0 1), M 1 1) = 1`.

Source: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Lemma 5.13,
p. 72. -/
theorem mem_modularPolynomialReps {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} :
    M ∈ modularPolynomialReps N ↔ M 1 0 = 0 ∧ 0 < M 0 0 ∧ 0 ≤ M 0 1 ∧ M 0 1 < M 1 1 ∧
      M 0 0 * M 1 1 = N ∧ Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 1) = 1 := by
  constructor
  · intro h
    simp only [modularPolynomialReps, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Ico] at h
    obtain ⟨⟨a, b, d⟩, ⟨⟨⟨ha1, -⟩, ⟨hb0, -⟩, ⟨hd1, -⟩⟩, hN, hbd, hg⟩, rfl⟩ := h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    exact ⟨trivial, by omega, hb0, hbd, hN, hg⟩
  · rintro ⟨h10, h00, h01, h0111, hN, hg⟩
    have h11 : 0 < M 1 1 := lt_of_le_of_lt h01 h0111
    simp only [modularPolynomialReps, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Ico]
    refine ⟨(M 0 0, M 0 1, M 1 1), ⟨⟨⟨?_, ?_⟩, ⟨h01, ?_⟩, ⟨?_, ?_⟩⟩, hN, h0111, hg⟩, ?_⟩ <;>
      dsimp only
    · omega
    · nlinarith
    · nlinarith
    · omega
    · nlinarith
    · rw [← h10]
      exact (Matrix.eta_fin_two M).symm

/-- A common divisor of all entries of `B` divides all entries of `A * B`. -/
private theorem dvd_mul_entries {A B : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ}
    (h : ∀ i j, n ∣ B i j) (i j : Fin 2) : n ∣ (A * B) i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add (dvd_mul_of_dvd_right (h 0 j) _) (dvd_mul_of_dvd_right (h 1 j) _)

/-- A common divisor of all entries of `A` divides all entries of `A * B`. -/
private theorem dvd_mul_entries' {A B : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ}
    (h : ∀ i j, n ∣ A i j) (i j : Fin 2) : n ∣ (A * B) i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add (dvd_mul_of_dvd_left (h i 0) _) (dvd_mul_of_dvd_left (h i 1) _)

private theorem isUnit_of_gcd {a b d n : ℤ} (hg : Int.gcd (Int.gcd a b) d = 1) (ha : n ∣ a)
    (hb : n ∣ b) (hd : n ∣ d) : IsUnit n := by
  have h1 : n ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd ha hb
  have h2 : n ∣ (Int.gcd (Int.gcd a b) d : ℤ) := Int.dvd_coe_gcd h1 hd
  rw [hg] at h2
  exact isUnit_of_dvd_one h2

private theorem gcd_of_isUnit {a b d : ℤ}
    (h : ∀ n : ℤ, n ∣ a → n ∣ b → n ∣ d → IsUnit n) : Int.gcd (Int.gcd a b) d = 1 := by
  have h1 : (Int.gcd (Int.gcd a b) d : ℤ) ∣ a :=
    (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have h2 : (Int.gcd (Int.gcd a b) d : ℤ) ∣ b :=
    (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have h3 : (Int.gcd (Int.gcd a b) d : ℤ) ∣ d := Int.gcd_dvd_right _ _
  have hu := h _ h1 h2 h3
  rw [Int.isUnit_iff] at hu
  omega

/-- **Hermite normal form, existence.** Let `N > 0` and let `A` be an integer `2 × 2` matrix with
`det A = N` whose entries have no common divisor other than `±1`. Then `A = γ M` for some
`γ ∈ SL₂(ℤ)` and some `M ∈ C_N`.

Source: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Lemma 5.13,
p. 72: "Let A be a 2 × 2 matrix with coefficients in Z and determinant n. Then there is an
invertible matrix U in M₂(Z) such that U · A = (a b; 0 d) with ad = n, a ≥ 1, 0 ≤ b < d."
Here `γ = U⁻¹` lies in `SL₂(ℤ)`, and the primitivity of `A` gives `gcd(a, b, d) = 1`. -/
theorem exists_eq_mul_of_det {N : ℕ} (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = N)
    (hN : 0 < N) (hprim : ∀ n : ℤ, (∀ i j, n ∣ A i j) → IsUnit n) :
    ∃ γ : SL(2, ℤ), ∃ M ∈ modularPolynomialReps N, A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * M := by
  rw [Matrix.det_fin_two] at hA
  set x := A 0 0
  set y := A 1 0
  set g : ℤ := (Int.gcd x y : ℤ) with hgdef
  have hg0 : 0 < g := by
    rw [hgdef]
    have : Int.gcd x y ≠ 0 := by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      rw [h.1, h.2] at hA
      simp at hA
      omega
    exact_mod_cast Nat.pos_of_ne_zero this
  obtain ⟨x', hx'⟩ : g ∣ x := Int.gcd_dvd_left _ _
  obtain ⟨y', hy'⟩ : g ∣ y := Int.gcd_dvd_right _ _
  have hbez : x' * x.gcdA y + y' * x.gcdB y = 1 := by
    have h := Int.gcd_eq_gcd_ab x y
    rw [← hgdef] at h
    have : g * (x' * x.gcdA y + y' * x.gcdB y) = g * 1 := by
      linear_combination (-1 : ℤ) * h - x.gcdA y * hx' - x.gcdB y * hy'
    exact mul_left_cancel₀ hg0.ne' this
  set u := x.gcdA y
  set v := x.gcdB y
  set d := x' * A 1 1 - y' * A 0 1 with hd
  set b0 := u * A 0 1 + v * A 1 1 with hb0
  have hgd : g * d = N := by
    rw [← hA, hd]
    linear_combination (-A 1 1) * hx' + A 0 1 * hy'
  have hd0 : 0 < d := by
    have : (0 : ℤ) < g * d := by rw [hgd]; exact_mod_cast hN
    exact pos_of_mul_pos_right this hg0.le
  set k := b0 / d
  set r := b0 % d
  have hkr : b0 = d * k + r := by
    have := Int.mul_ediv_add_emod b0 d
    linarith
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hd0.ne'
  have hrd : r < d := Int.emod_lt_of_pos _ hd0
  let γ : SL(2, ℤ) := ⟨!![x', x' * k - v; y', y' * k + u], by
    rw [Matrix.det_fin_two_of]
    linear_combination hbez⟩
  have heq : A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![g, r; 0, d] := by
    rw [show r = b0 - d * k by omega]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hx'
    · linear_combination (-A 0 1) * hbez - x' * hb0 + v * hd
    · linear_combination hy'
    · linear_combination (-A 1 1) * hbez - y' * hb0 - u * hd
  refine ⟨γ, !![g, r; 0, d], ?_, heq⟩
  rw [mem_modularPolynomialReps]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  refine ⟨trivial, hg0, hr0, hrd, hgd, gcd_of_isUnit fun n hn1 hn2 hn3 => hprim n ?_⟩
  have hall : ∀ i j, n ∣ (!![g, r; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hn1, hn2, hn3]
  intro i j
  rw [heq]
  exact dvd_mul_entries hall i j

private theorem coe_inv_mul (g : SL(2, ℤ)) :
    ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

private theorem coe_mul_inv (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

/-- **Hermite normal form, uniqueness.** If `M, M' ∈ C_N`, `γ ∈ SL₂(ℤ)` and `γ M = M'`, then
`M = M'` and `γ = 1`. So distinct elements of `C_N` lie in distinct orbits of `SL₂(ℤ)` acting by
left multiplication.

Source: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Lemma 5.13,
p. 72: "Moreover, the integers a, b, d are uniquely determined." -/
theorem modularPolynomialReps_eq_of_mul_eq {N : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ modularPolynomialReps N) (hM' : M' ∈ modularPolynomialReps N) (γ : SL(2, ℤ))
    (h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * M = M') : M = M' ∧ γ = 1 := by
  rw [mem_modularPolynomialReps] at hM hM'
  obtain ⟨a10, a00, a01, a0111, -, -⟩ := hM
  obtain ⟨b10, b00, b01, b0111, -, -⟩ := hM'
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, a10, mul_zero, add_zero] at e00 e01 e10 e11
  set g00 := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set g01 := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set g10 := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set g11 := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hr : g10 = 0 := by
    rw [b10] at e10
    exact (mul_eq_zero.mp e10).resolve_right a00.ne'
  rw [hr, mul_zero, sub_zero] at hdet
  rw [hr, zero_mul, zero_add] at e11
  have hp : g00 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h1 | h1
    · exact h1
    · rw [h1] at e00
      linarith
  rw [hp, one_mul] at hdet
  rw [hp, one_mul] at e00 e01
  rw [hdet, one_mul] at e11
  have hq : g01 = 0 := by
    rcases lt_trichotomy g01 0 with hq | hq | hq
    · nlinarith
    · exact hq
    · nlinarith
  rw [hq, zero_mul, add_zero] at e01
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · simp [a10, b10]
    · exact e11
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa using hp
    · simpa using hq
    · simpa using hr
    · simpa using hdet

private theorem mul_mem_aux {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ modularPolynomialReps N) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), ∃ M' ∈ modularPolynomialReps N,
      M * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * M' := by
  obtain ⟨h10, h00, h01, h0111, hN, hg⟩ := mem_modularPolynomialReps.mp hM
  have hNpos : 0 < N := by
    have : (0 : ℤ) < N := hN ▸ mul_pos h00 (lt_of_le_of_lt h01 h0111)
    exact_mod_cast this
  refine exists_eq_mul_of_det _ ?_ hNpos ?_
  · rw [Matrix.det_mul, γ.det_coe, mul_one, Matrix.det_fin_two, h10, mul_zero, sub_zero, hN]
  · intro n hn
    have hall : ∀ i j, n ∣ M i j := by
      intro i j
      have := dvd_mul_entries' (B := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) hn i j
      rwa [Matrix.mul_assoc, coe_mul_inv, Matrix.mul_one] at this
    exact isUnit_of_gcd hg (hall 0 0) (hall 0 1) (hall 1 1)

/-- **`SL₂(ℤ)` permutes the orbits `SL₂(ℤ) M`, `M ∈ C_N`.** For every `γ ∈ SL₂(ℤ)` there are a
permutation `σ` of `C_N` and a map `δ : C_N → SL₂(ℤ)` with `M γ = δ(M) σ(M)` for all `M ∈ C_N`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.11, p. 5: "multiplication on the right by γ permutes the cosets",
used for the coefficients of `Φ_N` after Definition 19.15, p. 7; here stated for the
representatives `C_N` of the `SL₂(ℤ)`-orbits of primitive integer matrices of determinant `N`
(J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Remark 5.14, p. 72). -/
theorem modularPolynomialReps_exists_equiv_mul_eq (N : ℕ) (γ : SL(2, ℤ)) :
    ∃ σ : modularPolynomialReps N ≃ modularPolynomialReps N,
      ∃ δ : modularPolynomialReps N → SL(2, ℤ), ∀ M : modularPolynomialReps N,
        (M : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
          (δ M : Matrix (Fin 2) (Fin 2) ℤ) * (σ M : Matrix (Fin 2) (Fin 2) ℤ) := by
  choose δ f hf hfeq using fun M : modularPolynomialReps N => mul_mem_aux M.2 γ
  let F : modularPolynomialReps N → modularPolynomialReps N := fun M => ⟨f M, hf M⟩
  have hinj : Function.Injective F := by
    intro M1 M2 h
    have h' : f M1 = f M2 := congrArg Subtype.val h
    have r1 : (M1 : Matrix (Fin 2) (Fin 2) ℤ) = (δ M1 : Matrix (Fin 2) (Fin 2) ℤ) * f M1 *
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← hfeq M1, Matrix.mul_assoc, coe_mul_inv, Matrix.mul_one]
    have r2 : (M2 : Matrix (Fin 2) (Fin 2) ℤ) = (δ M2 : Matrix (Fin 2) (Fin 2) ℤ) * f M2 *
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← hfeq M2, Matrix.mul_assoc, coe_mul_inv, Matrix.mul_one]
    have key : ((δ M2 * (δ M1)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M1 = M2 := by
      rw [r1, r2, h', show ((δ M2 * (δ M1)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ M2 : Matrix (Fin 2) (Fin 2) ℤ) * (((δ M1)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        from rfl]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((δ M1)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), coe_inv_mul,
        Matrix.one_mul]
    exact Subtype.ext (modularPolynomialReps_eq_of_mul_eq M1.2 M2.2 _ key).1
  exact ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.mp hinj), δ, hfeq⟩

/-- **`C_p` for a prime `p`.** For prime `p`, `C_p` consists of `!![p, 0; 0, 1]` and the
matrices `!![1, b; 0, p]` with `0 ≤ b < p`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, pp. 7–8: for the coset representatives `1` and `γk = S Tᵏ`,
`0 ≤ k < N`, of Lemma 19.16, "jN(γk τ) = j(N γk τ) = … = j((τ + k)/N)" and
`jN(τ) = j(Nτ)`; so the roots of `Φ_N` are `j(Mτ)` for exactly these matrices `M`. -/
theorem modularPolynomialReps_prime {p : ℕ} (hp : p.Prime) :
    modularPolynomialReps p = insert !![(p : ℤ), 0; 0, 1]
      ((Finset.range p).image fun b : ℕ => !![1, (b : ℤ); 0, (p : ℤ)]) := by
  ext M
  rw [mem_modularPolynomialReps, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨h10, h00, h01, h0111, hN, -⟩
    have hdvd : (M 0 0).natAbs ∣ p :=
      ⟨(M 1 1).natAbs, by rw [← Int.natAbs_mul, hN, Int.natAbs_natCast]⟩
    have habs : ((M 0 0).natAbs : ℤ) = M 0 0 := Int.natAbs_of_nonneg h00.le
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · rw [h1, Nat.cast_one] at habs
      rw [← habs, one_mul] at hN
      right
      refine ⟨(M 0 1).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [← habs, h10, hN, Int.toNat_of_nonneg h01]
    · rw [h1] at habs
      rw [← habs] at hN
      have h11 : M 1 1 = 1 := by
        have : (p : ℤ) * M 1 1 = p * 1 := by rw [hN, mul_one]
        exact mul_left_cancel₀ hp0.ne' this
      have h01' : M 0 1 = 0 := by omega
      left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← habs, h10, h11, h01']
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · simp [hp.pos]
    · rw [Finset.mem_range] at hb
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one]
      exact ⟨trivial, one_pos, Int.natCast_nonneg b, by exact_mod_cast hb, one_mul _, by simp⟩

/-- **`|C_p| = p + 1`** for a prime `p`, the index `ψ(p) = p + 1` of `Γ₀(p)` in `SL₂(ℤ)`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.16, p. 7: the right cosets of `Γ₀(N)` are "Γ₀(N) ∪ {Γ₀(N)STᵏ : 0 ≤ k < N}";
and Lecture 20, Theorem 20.7, p. 3: "for prime N the polynomial ΦN(X, Y) has degree N + 1". -/
theorem card_modularPolynomialReps_prime {p : ℕ} (hp : p.Prime) :
    (modularPolynomialReps p).card = p + 1 := by
  rw [modularPolynomialReps_prime hp, Finset.card_insert_of_notMem,
    Finset.card_image_of_injective, Finset.card_range]
  · intro b b' h
    have := congrFun (congrFun h 0) 1
    simpa using this
  · rw [Finset.mem_image]
    rintro ⟨b, -, h⟩
    have := congrFun (congrFun h 0) 0
    simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one] at this
    have := hp.one_lt
    omega

end WLight
