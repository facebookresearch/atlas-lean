/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# The minimax property of the Chebyshev polynomials

Among all monic real polynomials of degree `n`, the scaled Chebyshev polynomial
`2^{1-n} T_n` has the smallest maximum modulus on `[-1, 1]`, namely `2^{1-n}`, and it is
the unique polynomial with this property (Chebyshev, 1853/54).

This is the extremal fact behind every Chebyshev-type convergence bound in numerical linear
algebra: the conjugate gradient bound `2 ((√κ - 1) / (√κ + 1))^k`, Chebyshev acceleration
and Chebyshev semi-iterative methods, and the polynomial view of Krylov methods
(Driscoll, Toh and Trefethen, 1998). It is also why Chebyshev points are good interpolation
nodes: the node polynomial `∏ (x - x_j)` of the `n` Chebyshev roots is `2^{1-n} T_n`, so it
attains this minimal maximum.

Here `(2 : ℝ) ^ (n - 1)` uses natural subtraction, so the bound reads `1` when `n = 0`
(the monic polynomial `1`), which is correct.

## Main results

* `chebyshevMonic`: the monic Chebyshev polynomial `2^{1-n} T_n`.
* `chebyshevMonic_monic`, `natDegree_chebyshevMonic`, `abs_eval_chebyshevMonic_le`:
  it is monic of degree `n` and bounded by `2^{1-n}` on `[-1, 1]`.
* `inv_two_pow_le_of_forall_abs_eval_le`: every monic polynomial of degree `n` bounded by
  `M` on `[-1, 1]` has `2^{1-n} ≤ M` (the minimax property).
* `eq_chebyshevMonic_of_forall_abs_eval_le`: equality forces `p = 2^{1-n} T_n`.

The proofs reduce to Mathlib's extremal property of the leading coefficient of `T_n`
(`Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one`, by Yuval Filmus).

## References

* P. L. Chebyshev, *Théorie des mécanismes connus sous le nom de parallélogrammes*,
  Mém. Acad. Sci. Pétersb. 7 (1854), 539–568.
* Encyclopedia of Mathematics, *Extremal properties of polynomials*,
  https://encyclopediaofmath.org/wiki/Extremal_properties_of_polynomials (first paragraph).
* L. N. Trefethen, *Approximation Theory and Approximation Practice*, SIAM, 2013,
  Chapters 3 and 10 (Chebyshev polynomials; equioscillation and best approximation).
* T. A. Driscoll, K.-C. Toh, L. N. Trefethen, *From potential theory to matrix iterations in
  six steps*, SIAM Rev. 40 (1998), 547–578.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace MathlibExt.Analysis.Approximation.ChebyshevMinimax

/-- The monic Chebyshev polynomial `2^{1-n} T_n` of degree `n` (equal to `1` for `n = 0`). -/
noncomputable def chebyshevMonic (n : ℕ) : ℝ[X] :=
  Polynomial.C ((2 : ℝ) ^ (n - 1))⁻¹ * T ℝ n

lemma leadingCoeff_T_nat (n : ℕ) : (T ℝ n).leadingCoeff = 2 ^ (n - 1) := by
  simp

lemma natDegree_T_nat (n : ℕ) : (T ℝ n).natDegree = n := by
  simp

/-- `2^{1-n} T_n` is monic. -/
theorem chebyshevMonic_monic (n : ℕ) : (chebyshevMonic n).Monic := by
  have h2 : ((2 : ℝ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [Monic, chebyshevMonic, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.2 (inv_ne_zero h2)),
    leadingCoeff_T_nat, inv_mul_cancel₀ h2]

/-- `2^{1-n} T_n` has degree `n`. -/
theorem natDegree_chebyshevMonic (n : ℕ) : (chebyshevMonic n).natDegree = n := by
  have h2 : ((2 : ℝ) ^ (n - 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ two_ne_zero)
  rw [chebyshevMonic, natDegree_C_mul h2, natDegree_T_nat]

/-- `|2^{1-n} T_n(x)| ≤ 2^{1-n}` on `[-1, 1]`. -/
theorem abs_eval_chebyshevMonic_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(chebyshevMonic n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹ := by
  have hx' : |x| ≤ 1 := abs_le.2 hx
  rw [chebyshevMonic, eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  have := abs_eval_T_real_le_one (n : ℤ) hx'
  calc ((2 : ℝ) ^ (n - 1))⁻¹ * |(T ℝ n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹ * 1 := by
        gcongr
    _ = _ := mul_one _

/-- The bound `2^{1-n}` is attained: `|2^{1-n} T_n(1)| = 2^{1-n}`. -/
theorem abs_eval_one_chebyshevMonic (n : ℕ) :
    |(chebyshevMonic n).eval 1| = ((2 : ℝ) ^ (n - 1))⁻¹ := by
  rw [chebyshevMonic, eval_mul, eval_C]
  have : (T ℝ (n : ℤ)).eval 1 = 1 := T_eval_one ℝ (n : ℤ)
  simp [this]

private lemma pos_of_forall_abs_eval_le {p : ℝ[X]} (hp : p.Monic) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) : 0 < M := by
  have h0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 ⟨by norm_num, le_rfl⟩)
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hroot : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.IsRoot x := fun x hx =>
      abs_nonpos_iff.1 (h ▸ hM x hx)
    have hinf : (Set.Icc (-1 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
    have : p = 0 := eq_zero_of_infinite_isRoot p (hinf.mono fun x hx => hroot x hx)
    exact hp.ne_zero this

/-- **Minimax property of the Chebyshev polynomials.** If `p` is a monic real polynomial of
degree `n` with `|p(x)| ≤ M` for every `x ∈ [-1, 1]`, then `2^{1-n} ≤ M`. -/
theorem inv_two_pow_le_of_forall_abs_eval_le {p : ℝ[X]} {n : ℕ} (hp : p.Monic)
    (hdeg : p.natDegree = n) {M : ℝ} (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    ((2 : ℝ) ^ (n - 1))⁻¹ ≤ M := by
  have hMpos := pos_of_forall_abs_eval_le hp hM
  set P : ℝ[X] := Polynomial.C M⁻¹ * p with hP
  have hPdeg : P.degree ≤ n := by
    rw [hP]
    exact degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans hdeg.le)
  have hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 := by
    intro x hx
    rw [hP, eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.2 hMpos)]
    calc M⁻¹ * |p.eval x| ≤ M⁻¹ * M := by gcongr; exact hM x hx
      _ = 1 := inv_mul_cancel₀ hMpos.ne'
  have hcoeff := coeff_le_of_forall_abs_le_one hPdeg hPbnd
  have : P.coeff n = M⁻¹ := by
    rw [hP, coeff_C_mul, ← hdeg, hp.coeff_natDegree, mul_one]
  rw [this] at hcoeff
  rw [inv_le_comm₀ (by positivity) hMpos]
  exact hcoeff

/-- **Uniqueness of the Chebyshev minimax polynomial.** A monic real polynomial of degree `n`
with `|p(x)| ≤ 2^{1-n}` on `[-1, 1]` equals `2^{1-n} T_n`. -/
theorem eq_chebyshevMonic_of_forall_abs_eval_le {p : ℝ[X]} {n : ℕ} (hp : p.Monic)
    (hdeg : p.natDegree = n)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) :
    p = chebyshevMonic n := by
  have hc : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  set P : ℝ[X] := Polynomial.C ((2 : ℝ) ^ (n - 1)) * p with hP
  have hPdeg : P.degree ≤ n := by
    rw [hP]
    exact degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans hdeg.le)
  have hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 := by
    intro x hx
    rw [hP, eval_mul, eval_C, abs_mul, abs_of_pos hc]
    calc (2 : ℝ) ^ (n - 1) * |p.eval x| ≤ 2 ^ (n - 1) * ((2 : ℝ) ^ (n - 1))⁻¹ := by
          gcongr; exact hM x hx
      _ = 1 := mul_inv_cancel₀ hc.ne'
  have hcoeff : P.coeff n = 2 ^ (n - 1) := by
    rw [hP, coeff_C_mul, ← hdeg, hp.coeff_natDegree, mul_one]
  have hPT : P = T ℝ n := (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).1 hcoeff
  rw [chebyshevMonic, ← hPT, hP, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc.ne',
    Polynomial.C_1, one_mul]

/-- The minimal maximum modulus on `[-1, 1]` over monic polynomials of degree `n` is exactly
`2^{1-n}`, attained by `2^{1-n} T_n`: it is a lower bound for every monic `p` of degree `n`,
and `2^{1-n} T_n` meets it. -/
theorem isLeast_chebyshevMonic (n : ℕ) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = n ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M} ((2 : ℝ) ^ (n - 1))⁻¹ :=
  ⟨⟨chebyshevMonic n, chebyshevMonic_monic n, natDegree_chebyshevMonic n,
      fun _ hx => abs_eval_chebyshevMonic_le n hx⟩,
    fun _ ⟨_, hp, hdeg, hM⟩ => inv_two_pow_le_of_forall_abs_eval_le hp hdeg hM⟩

end MathlibExt.Analysis.Approximation.ChebyshevMinimax
