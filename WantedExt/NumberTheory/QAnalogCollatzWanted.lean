/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- Division by `q` in `𝔽₂[[q]]` after discarding the constant term:
`qShift x = ∑ₙ x_{n+1} qⁿ`, so `qShift (q * y) = y`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (the quotients `x/q` and `(Ax+B)/q` in the
definition of `T_{A,B}`). -/
noncomputable def qShift (x : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => coeff (n + 1) x

/-- `qShift (q * y) = y`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (division by `q`). -/
theorem qShift_X_mul (y : PowerSeries (ZMod 2)) : qShift (X * y) = y := by
  ext n
  simp [qShift, coeff_succ_X_mul]

/-- The `q`-analog `T_{A,B}` of the `3x+1` map on `𝔽₂[[q]]`:
`T_{A,B}(x) = x/q` if `q ∣ x`, and `(Ax + B)/q` otherwise. For odd `A, B` (constant term `1`)
the numerator `Ax + B` is divisible by `q` whenever `x` is odd, so `qShift` is exact division.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
noncomputable def qCollatz (A B x : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  if constantCoeff x = 0 then qShift x else qShift (A * x + B)

/-- On even arguments, `T_{A,B}(q y) = y`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
theorem qCollatz_X_mul (A B y : PowerSeries (ZMod 2)) : qCollatz A B (X * y) = y := by
  simp [qCollatz, qShift_X_mul]

/-- `T_{A,B}(0) = 0`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
theorem qCollatz_zero (A B : PowerSeries (ZMod 2)) : qCollatz A B 0 = 0 := by
  simpa using qCollatz_X_mul A B 0

/-- A `2`-adic integer whose residue modulo `2` vanishes is divisible by `2`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (parity in `ℤ₂`, so that `T` is a self-map). -/
theorem two_dvd_of_toZMod_eq_zero {y : ℤ_[2]} (h : PadicInt.toZMod y = 0) :
    (2 : ℤ_[2]) ∣ y := by
  have hy : y ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hy
  exact_mod_cast hy

/-- For odd `x ∈ ℤ₂`, `3x + 1` is even.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem toZMod_three_mul_add_one_of_odd {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) :
    PadicInt.toZMod (3 * x + 1) = 0 := by
  have key : ∀ a : ZMod 2, a ≠ 0 → 3 * a + 1 = 0 := by decide
  have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 3 := map_ofNat _ 3
  rw [map_add, map_mul, map_one, h3]
  exact key _ h

/-- The `3x+1` map `T : ℤ₂ → ℤ₂`, `T(x) = x/2` for even `x` and `(3x+1)/2` for odd `x`
(exact division by `2` in `ℤ₂`; see `two_mul_twoAdicCollatz_of_even` and
`two_mul_twoAdicCollatz_of_odd`).

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T` extended to `ℤ₂`). -/
noncomputable def twoAdicCollatz (x : ℤ_[2]) : ℤ_[2] :=
  if h : PadicInt.toZMod x = 0 then (two_dvd_of_toZMod_eq_zero h).choose
  else (two_dvd_of_toZMod_eq_zero (toZMod_three_mul_add_one_of_odd h)).choose

/-- Even branch: `2 T(x) = x`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem two_mul_twoAdicCollatz_of_even {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) :
    2 * twoAdicCollatz x = x := by
  simp only [twoAdicCollatz, h, dite_true]
  exact (two_dvd_of_toZMod_eq_zero h).choose_spec.symm

/-- Odd branch: `2 T(x) = 3x + 1`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem two_mul_twoAdicCollatz_of_odd {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) :
    2 * twoAdicCollatz x = 3 * x + 1 := by
  simp only [twoAdicCollatz, h, dite_false]
  exact (two_dvd_of_toZMod_eq_zero (toZMod_three_mul_add_one_of_odd h)).choose_spec.symm

/-- `T(1) = 2` and `T(2) = 1`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem twoAdicCollatz_one_two : twoAdicCollatz 1 = 2 ∧ twoAdicCollatz 2 = 1 := by
  have h1 : (PadicInt.toZMod (1 : ℤ_[2]) : ZMod 2) ≠ 0 := by simp
  have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := by
    rw [map_ofNat]; decide
  have h20 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  refine ⟨mul_left_cancel₀ h20 ?_, mul_left_cancel₀ h20 ?_⟩
  · rw [two_mul_twoAdicCollatz_of_odd h1]; norm_num
  · rw [two_mul_twoAdicCollatz_of_even h2]; norm_num

/-- The parity vector `PV_{A,B}(x) = ∑ₖ xₖ 2ᵏ ∈ ℤ₂`, where `xₖ ∈ {0, 1}` is the parity (constant
coefficient) of `T_{A,B}^k(x)`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Definition 10. -/
noncomputable def qCollatzParityVector (A B x : PowerSeries (ZMod 2)) : ℤ_[2] :=
  ∑' k : ℕ, ((constantCoeff ((qCollatz A B)^[k] x)).val : ℤ_[2]) * 2 ^ k

/-- `PV_{A,B}(0) = 0`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Definition 10. -/
theorem qCollatzParityVector_zero (A B : PowerSeries (ZMod 2)) :
    qCollatzParityVector A B 0 = 0 := by
  have h : ∀ k, (qCollatz A B)^[k] 0 = 0 := fun k =>
    Function.iterate_fixed (qCollatz_zero A B) k
  simp [qCollatzParityVector, h]

/-- For odd `A, B ∈ 𝔽₂[[q]]`, `T_{A,B}` is conjugate to the `2`-adic `3x+1` map `T`: there is a
bijection `h : ℤ₂ → 𝔽₂[[q]]` with `h⁻¹ ∘ T_{A,B} ∘ h = T`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 2 (`jis-2025-25.6.8-thm-2`). -/
public theorem_wanted qCollatz_conjugate_twoAdicCollatz (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz A B (h x)) = twoAdicCollatz x

/-- The map `T_q = T_{1+q,1}`, `T_q(x) = x/q` or `((1+q)x + 1)/q`, is conjugate to the `2`-adic
`3x+1` map `T`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 3 (`jis-2025-25.6.8-cor-3`). -/
public theorem_wanted qCollatz_one_add_X_conjugate_twoAdicCollatz :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz (1 + X) 1 (h x)) = twoAdicCollatz x

/-- For `T = T_{1,1+q²}`: the `T`-orbit of every polynomial reaches the `2`-cycle `{1, q}` or
one of the fixed points `0`, `1 + q`; and `T(x)` is a polynomial if and only if `x` is.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 5 (`jis-2025-25.6.8-thm-5`). -/
public theorem_wanted qCollatz_one_one_add_X_sq_polynomial :
    (∀ p : Polynomial (ZMod 2), ∃ k : ℕ,
      (qCollatz 1 (1 + X ^ 2))^[k] (p : PowerSeries (ZMod 2)) ∈
        ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2)))) ∧
    ∀ x : PowerSeries (ZMod 2),
      (∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2) x = p) ↔
        ∃ p : Polynomial (ZMod 2), x = p

/-- For odd `A, B`, `n ∈ ℕ` and `U, V ∈ 𝔽₂[[q]]` with `V` odd,
`T_{A,B}(U + q^{n+1} V) = T_{A,B}(U) + qⁿ W` for some odd `W`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 7 (`jis-2025-25.6.8-lem-7`). -/
public theorem_wanted qCollatz_add_X_pow_mul (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
      qCollatz A B (U + X ^ (n + 1) * V) = qCollatz A B U + X ^ n * W

/-- For odd `A, B`, `n ∈ ℕ`, `U, V ∈ 𝔽₂[[q]]` with `V` odd, and every `k ≤ n + 1`,
`T_{A,B}^k(U + q^{n+1} V) = T_{A,B}^k(U) + q^{n+1-k} W_k` for some odd `W_k`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 8 (`jis-2025-25.6.8-cor-8`). -/
public theorem_wanted qCollatz_iterate_add_X_pow_mul (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
      (qCollatz A B)^[k] (U + X ^ (n + 1) * V) =
        (qCollatz A B)^[k] U + X ^ (n + 1 - k) * W

/-- For odd `A, B`, `n ∈ ℕ`, and `U, V ∈ 𝔽₂[[q]]` with `V` odd, `T_{A,B}^n(U + qⁿ V)` and
`T_{A,B}^n(U)` have opposite parity.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 9 (`jis-2025-25.6.8-cor-9`). -/
public theorem_wanted qCollatz_iterate_parity_flip (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    constantCoeff ((qCollatz A B)^[n] (U + X ^ n * V)) ≠
      constantCoeff ((qCollatz A B)^[n] U)

/-- For odd `A, B`, `n ∈ ℕ` and `a, b ∈ 𝔽₂[[q]]`:
`PV(a) ≡ PV(b) (mod 2^{n+1})` if and only if `a ≡ b (mod q^{n+1})`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 11 (`jis-2025-25.6.8-thm-11`). -/
public theorem_wanted qCollatzParityVector_modEq_iff (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (a b : PowerSeries (ZMod 2)) :
    PadicInt.toZModPow (n + 1) (qCollatzParityVector A B a) =
        PadicInt.toZModPow (n + 1) (qCollatzParityVector A B b) ↔
      X ^ (n + 1) ∣ a - b

/-- For odd `A, B` and `n ≥ 1`, the map `[a] ↦ [PV(a)]` is a well-defined bijection from
`𝔽₂[[q]]/(qⁿ)` to `ℤ₂/2ⁿ ≅ ℤ/2ⁿ`.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 12 (`jis-2025-25.6.8-cor-12`). -/
public theorem_wanted qCollatzParityVector_quotient_bijection (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ n}) ≃ ZMod (2 ^ n),
      ∀ a, e (Ideal.Quotient.mk _ a) = PadicInt.toZModPow n (qCollatzParityVector A B a)

/-- For odd `A, B`, the fixed points of `T_{A,B}` are `0` and `B/(A+q)`, and its unique
`2`-cycle is `{B/(A+q²), qB/(A+q²)}`: an element `x` satisfies `T(T(x)) = x ≠ T(x)` exactly when
it is one of these two.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 13 (`jis-2025-25.6.8-lem-13`). -/
public theorem_wanted qCollatz_fixedPoints_and_twoCycle (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    (∀ x, qCollatz A B x = x ↔ x = 0 ∨ x = B * (A + X)⁻¹) ∧
    ∀ x, (qCollatz A B (qCollatz A B x) = x ∧ qCollatz A B x ≠ x) ↔
      x = B * (A + X ^ 2)⁻¹ ∨ x = X * (B * (A + X ^ 2)⁻¹)

end

end MetaMathlibExt
