/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

namespace MetaMathlibExt

@[expose] public section

open UpperHalfPlane MatrixGroups ArithmeticFunction

/-- The normalized Fourier coefficient `λ_f(n) = a_f(n) / n^{(k-1)/2}` of a level-one cusp form
`f` of weight `k`, where `a_f(n)` is the `n`-th coefficient of the `q`-expansion
`f(z) = ∑ a_f(n) e(nz)`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1 (Fourier expansion of `f ∈ H_k^*`). -/
public noncomputable def cuspFormNormalizedCoeff {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n / (((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)

/-- `λ_f(1)` is the first `q`-expansion coefficient.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem cuspFormNormalizedCoeff_one {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    cuspFormNormalizedCoeff f 1 = (qExpansion 1 f).coeff 1 := by
  simp [cuspFormNormalizedCoeff]

/-- A level-one cusp form `f` lies in `H_k^*` (is a normalized Hecke eigenform) when
`λ_f(1) = 1` and its normalized coefficients satisfy the Hecke relation (1) of the paper,
`λ_f(m) λ_f(n) = ∑_{d ∣ (m,n)} λ_f(mn/d²)`. At level one this is equivalent to `f` being a
simultaneous eigenform of all Hecke operators normalized by `a_f(1) = 1`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1, Equation (1). -/
public def IsNormalizedHeckeEigenform {k : ℤ} (f : CuspForm 𝒮ℒ k) : Prop :=
  cuspFormNormalizedCoeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      cuspFormNormalizedCoeff f m * cuspFormNormalizedCoeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, cuspFormNormalizedCoeff f (m * n / d ^ 2)

/-- For a normalized Hecke eigenform and a prime `p`, `λ_f(p)² = λ_f(p²) + 1`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Equation (1) with `m = n = p`. -/
public theorem IsNormalizedHeckeEigenform.normalizedCoeff_prime_sq {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {p : ℕ} (hp : p.Prime) :
    cuspFormNormalizedCoeff f p ^ 2 = cuspFormNormalizedCoeff f (p ^ 2) + 1 := by
  have h := hf.2 p p hp.pos hp.pos
  rw [Nat.gcd_self, hp.divisors, Finset.sum_insert (by simpa using hp.one_lt.ne)] at h
  have hp0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  simp only [one_pow, Nat.div_one, Finset.sum_singleton] at h
  rw [show p * p / p ^ 2 = 1 by rw [← sq, Nat.div_self (Nat.pos_of_ne_zero hp0)], hf.1] at h
  rw [sq, h, sq]

/-- The Rankin–Selberg coefficients `λ_{f×f}(n) = ∑_{l² m = n} λ_f(m)²`, i.e. the Dirichlet
coefficients of `L(f × f, s) = ζ(2s) ∑ λ_f(n)² n^{-s}`, as an arithmetic function (so that its
`w`-th power under Dirichlet convolution is `λ_{w,f×f}`).

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1 (definition of `λ_{f×f}` and
`λ_{w,f×f}`). -/
public noncomputable def rankinSelbergCoeff {k : ℤ} (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  ⟨fun n => ∑ d ∈ n.divisors with IsSquare d, cuspFormNormalizedCoeff f (n / d) ^ 2, by simp⟩

/-- Unfolding `λ_{f×f}(n) = ∑_{d ∣ n, d a square} λ_f(n/d)²`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_apply {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    rankinSelbergCoeff f n =
      ∑ d ∈ n.divisors with IsSquare d, cuspFormNormalizedCoeff f (n / d) ^ 2 := rfl

/-- `λ_{f×f}(1) = λ_f(1)²`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_one {k : ℤ} (f : CuspForm 𝒮ℒ k) :
    rankinSelbergCoeff f 1 = cuspFormNormalizedCoeff f 1 ^ 2 := by
  rw [rankinSelbergCoeff_apply, Nat.divisors_one, Finset.filter_singleton]
  simp [show IsSquare (1 : ℕ) from ⟨1, rfl⟩]

/-- For a prime `p`, `λ_{f×f}(p) = λ_f(p)²`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Section 1. -/
public theorem rankinSelbergCoeff_prime {k : ℤ} (f : CuspForm 𝒮ℒ k) {p : ℕ} (hp : p.Prime) :
    rankinSelbergCoeff f p = cuspFormNormalizedCoeff f p ^ 2 := by
  have hns : ¬ IsSquare p := fun h => by
    obtain ⟨r, hr⟩ := h
    have := hp.eq_one_or_self_of_dvd r ⟨r, hr⟩
    rcases this with h1 | h1
    · subst h1; simp at hr; exact hp.one_lt.ne' hr
    · rw [h1] at hr
      have : p * 1 = p * p := by simpa using hr
      have := Nat.eq_of_mul_eq_mul_left hp.pos this
      exact hp.one_lt.ne' this.symm
  rw [rankinSelbergCoeff_apply, hp.divisors, Finset.filter_insert, Finset.filter_singleton]
  simp [show IsSquare (1 : ℕ) from ⟨1, rfl⟩, hns]

/-- **Theorem 1.1** (quoted from Zou et al., [52, Theorem 1]). Let `f ∈ H_k^*`, `j ≥ 2`, and
`δ_2 = 92/597`, `δ_j = 92/(69(j-1)(j+3)+247)` for `j ≥ 3`. For primes `q`, residues `l` coprime
to `q`, and real `x ≥ 1` with `q ≤ x^{3δ_j/4}`,
`∑_{n ≤ x, n ≡ l (mod q)} λ_f(n^j)² = c x/φ(q) + O_{f,ε}(q x^{1 - 3δ_j/2 + ε})` with `c > 0`.
The constant `c` is allowed to depend on `q` (a weaker reading; the main term is the residue
of the `χ_0`-twisted series); the implied constant depends only on `f`, `j`, `ε`. The record's
trailing introduction text is not part of the statement.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.1 (`integers-2024-A3-thm-1-1`). -/
public theorem_wanted sum_cuspFormNormalizedCoeff_pow_sq_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {j : ℕ} (hj : 2 ≤ j) :
    let δ : ℝ := if j = 2 then 92 / 597 else 92 / (69 * ((j : ℝ) - 1) * ((j : ℝ) + 3) + 247)
    ∃ c : ℕ → ℝ, (∀ q : ℕ, q.Prime → 0 < c q) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ (3 / 4 * δ) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], cuspFormNormalizedCoeff f (n ^ j) ^ 2)
              - ((c q * x / (q.totient : ℝ) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * δ + ε)

/-- **Theorem 1.2.** Let `f ∈ H_k^*` and `η = 23/261`. For primes `q`, residues `l` coprime to
`q`, and real `x ≥ 1` with `q ≤ x^η`,
`∑_{n ≤ x, n ≡ l (mod q)} λ_{f×f}(n)² = (x/φ(q)) P(log x) + O_{f,ε}(q x^{1 - 3η/2 + ε})`,
where `P` has degree `1` and positive leading coefficient. `q ≪ x^η` is read as `q ≤ x^η`;
`P` may depend on `q` (it is the residue of the `χ_0`-twisted series, Proposition 3.2); the
implied constant depends only on `f` and `ε`. The stray "`j ≥ 1`" of the printed statement is
dropped (no `j` occurs).

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.2 (`integers-2024-A3-thm-1-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((23 : ℝ) / 261) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], rankinSelbergCoeff f n ^ 2)
              - ((x / (q.totient : ℝ) * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * ((23 : ℝ) / 261) + ε)

/-- **Theorem 1.3.** Let `f ∈ H_k^*`, `w ≥ 2`, and `ϑ_w = 92/(247w+10)`. For primes `q`,
residues `l` coprime to `q`, and real `x ≥ 1` with `q ≤ x^{ϑ_w}`,
`∑_{n ≤ x, n ≡ l (mod q)} λ_{w,f×f}(n) = (x/φ(q)) P_{w-1}(log x) + O_{f,ε}(q x^{1 - 3ϑ_w/2 + ε})`,
where `λ_{w,f×f}` is the `w`-fold Dirichlet convolution power of `λ_{f×f}` and `P_{w-1}` has
degree `w - 1` and positive leading coefficient. `q ≪ x^{ϑ_w}` is read as `q ≤ x^{ϑ_w}`; the
polynomial may depend on `q`; the implied constant depends only on `f`, `w`, `ε`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Theorem 1.3 (`integers-2024-A3-thm-1-3`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_arithmeticProgression {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w) :
    ∃ P : ℕ → Polynomial ℝ,
      (∀ q : ℕ, q.Prime → (P q).natDegree = w - 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ l : ℕ, Nat.Coprime l q →
        ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((92 : ℝ) / (247 * w + 10)) →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n ≡ l [MOD q], (rankinSelbergCoeff f ^ w) n)
              - ((x / (q.totient : ℝ) * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
            C * q * x ^ (1 - 3 / 2 * ((92 : ℝ) / (247 * w + 10)) + ε)

/-- **Proposition 3.1.** Let `f ∈ H_k^*`, `χ` a primitive Dirichlet character modulo a prime
`q`, and `η = 23/261`. For real `x ≥ 1` with `q ≤ x^η`,
`∑_{n ≤ x} λ_{f×f}(n)² χ(n) = O_{f,ε}(q x^{1 - 3η/2 + ε})`, the implied constant depending only
on `f` and `ε`. `q ≪ x^η` is read as `q ≤ x^η`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 3.1 (`integers-2024-A3-prop-3-1`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_mul_primitive_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((23 : ℝ) / 261) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, rankinSelbergCoeff f n ^ 2 * χ n‖ ≤
          C * q * x ^ (1 - 3 / 2 * ((23 : ℝ) / 261) + ε)

/-- **Proposition 3.2.** Let `f ∈ H_k^*` and `χ_0` the principal character modulo a prime `q`.
For `q ≤ x`, `∑_{n ≤ x} λ_{f×f}(n)² χ_0(n) = x P(log x) + O_{f,ε}(x^{179/209 + ε})` with `P` of
degree `1` and positive leading coefficient. `q ≪ x` is read as `q ≤ x`; `P` may depend on `q`;
the implied constant depends only on `f` and `ε`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 3.2 (`integers-2024-A3-prop-3-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_sq_mul_principal_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = 1 ∧ 0 < (P q).leadingCoeff) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ x : ℝ, (q : ℝ) ≤ x →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, rankinSelbergCoeff f n ^ 2 * (1 : DirichletCharacter ℂ q) n)
            - ((x * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
          C * x ^ ((179 : ℝ) / 209 + ε)

/-- **Proposition 4.1.** Let `f ∈ H_k^*`, `w ≥ 2`, `χ` a primitive Dirichlet character modulo a
prime `q`, and `ϑ_w = 92/(247w+10)`. For real `x ≥ 1` with `q ≤ x^{ϑ_w}`,
`∑_{n ≤ x} λ_{w,f×f}(n) χ(n) = O_{f,ε}(q x^{1 - 3ϑ_w/2 + ε})`, the implied constant depending
only on `f`, `w`, `ε`. `q ≪ x^{ϑ_w}` is read as `q ≤ x^{ϑ_w}`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 4.1 (`integers-2024-A3-prop-4-1`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_mul_primitive_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ≤ x ^ ((92 : ℝ) / (247 * w + 10)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinSelbergCoeff f ^ w) n * χ n‖ ≤
          C * q * x ^ (1 - 3 / 2 * ((92 : ℝ) / (247 * w + 10)) + ε)

/-- **Proposition 4.2.** Let `f ∈ H_k^*`, `w ≥ 2`, and `χ_0` the principal character modulo a
prime `q`. For `q ≤ x`,
`∑_{n ≤ x} λ_{w,f×f}(n) χ_0(n) = x P_{w-1}(log x) + O_{f,ε}(x^{ϑ̃_w + ε})` with
`ϑ̃_w = 1 - 210/(317w+115)` and `P_{w-1}` of degree `w - 1`. `q ≪ x` is read as `q ≤ x`; the
polynomial may depend on `q`; the implied constant depends only on `f`, `w`, `ε`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Proposition 4.2 (`integers-2024-A3-prop-4-2`). -/
public theorem_wanted sum_rankinSelbergCoeff_pow_mul_principal_character {k : ℤ}
    {f : CuspForm 𝒮ℒ k} (hf : IsNormalizedHeckeEigenform f) {w : ℕ} (hw : 2 ≤ w) :
    ∃ P : ℕ → Polynomial ℝ, (∀ q : ℕ, q.Prime → (P q).natDegree = w - 1) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, q.Prime → ∀ x : ℝ, (q : ℝ) ≤ x →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinSelbergCoeff f ^ w) n * (1 : DirichletCharacter ℂ q) n)
            - ((x * (P q).eval (Real.log x) : ℝ) : ℂ)‖ ≤
          C * x ^ (1 - (210 : ℝ) / (317 * w + 115) + ε)

end

end MetaMathlibExt
