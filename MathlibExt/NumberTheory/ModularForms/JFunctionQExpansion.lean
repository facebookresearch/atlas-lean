/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.LevelNAlgebra
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.JExpansion

/-!
# The integral q-expansion of the j-function

For $\tau$ in the upper half-plane and $q = e^{2\pi i\tau}$, the level-one $j$-function
$j = E_4^3/\Delta$ (`WLight.jFunction`) has the expansion

$$j(\tau) = \frac{1}{q} + 744 + \sum_{n \ge 1} c_n q^n$$

with integers $c_n$, the series converging absolutely, and $c_1 = 196884$
(`WLight.jFunction_qExpansion_int`).

The integrality and the expansion itself come from `ModularCurve.hasSum_jNum_qParam`: the function
$q j$ is the sum of the integer power series `ModularCurve.jNum`, the expansion of
$q E_4^3/\eta^{24} = E_4^3 \prod_{n \ge 1} (1 - q^n)^{-24}$, evaluated at $q$. This file adds the
values of its first three coefficients, $1$, $744$ and $196884$, recorded for the Laurent series
`ModularCurve.jq` (that is, $q^{-1}$ times `jNum`) as `ModularCurve.coeff_jq_zero` and
`ModularCurve.coeff_jq_one`; absolute convergence follows because in `ℂ` a summable series is
absolutely summable (`summable_norm_iff`).

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.5 and Corollary 19.6.
-/

@[expose] public section

set_option autoImplicit false

open Complex UpperHalfPlane Filter Topology PowerSeries

open scoped PowerSeries.WithPiTopology

namespace ModularCurve

/-! ### The first coefficients of `jNum` -/

/-- A coefficient of `etaProd` is a coefficient of any long enough finite partial product. -/
private theorem coeff_etaProd_eq_coeff_prod_range {m N : ℕ} (hmN : m < N) :
    coeff m etaProd = coeff m (∏ i ∈ Finset.range N, (1 - X ^ (i + 1) : PowerSeries ℤ)) := by
  have hlim : Tendsto (fun N => coeff m
      (∏ i ∈ Finset.range N, (1 - X ^ (i + 1) : PowerSeries ℤ))) atTop
      (𝓝 (coeff m etaProd)) :=
    ((WithPiTopology.continuous_coeff ℤ m).tendsto _).comp
      (WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd.tendsto_prod_nat
  have hconst : ∀ N', N ≤ N' →
      coeff m (∏ i ∈ Finset.range N', (1 - X ^ (i + 1) : PowerSeries ℤ)) =
        coeff m (∏ i ∈ Finset.range N, (1 - X ^ (i + 1) : PowerSeries ℤ)) := by
    intro N' hle
    induction N', hle using Nat.le_induction with
    | base => rfl
    | succ N' hle ih =>
      rw [Finset.prod_range_succ, mul_sub, mul_one, map_sub, coeff_mul_X_pow']
      split_ifs with h
      · omega
      · rw [sub_zero, ih]
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun N' h => (hconst N' h).symm⟩))

private theorem coeff_etaProd : coeff 1 etaProd = -1 ∧ coeff 2 etaProd = -1 := by
  have h : (∏ i ∈ Finset.range 3, (1 - X ^ (i + 1) : PowerSeries ℤ)) =
      1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    ring
  rw [coeff_etaProd_eq_coeff_prod_range (N := 3) (by norm_num),
    coeff_etaProd_eq_coeff_prod_range (m := 2) (N := 3) (by norm_num), h]
  simp [coeff_X_pow, coeff_X, coeff_one]

/-- The coefficients of `X` and `X²` in a power of a power series with constant term `1`. -/
private theorem coeff_pow_of_constantCoeff_eq_one {f : PowerSeries ℤ} (hf : constantCoeff f = 1)
    (n : ℕ) : coeff 0 (f ^ n) = 1 ∧ coeff 1 (f ^ n) = n * coeff 1 f ∧
      coeff 2 (f ^ n) = n * coeff 2 f + (n.choose 2 : ℕ) * coeff 1 f ^ 2 := by
  have hf0 : coeff 0 f = 1 := by rwa [coeff_zero_eq_constantCoeff_apply]
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h0, h1, h2, hf0,
      Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    refine ⟨trivial, ?_, ?_⟩ <;> ring

private theorem coeff_eisenstein4 : coeff 1 eisenstein4 = 240 ∧ coeff 2 eisenstein4 = 2160 := by
  refine ⟨?_, ?_⟩ <;> simp only [eisenstein4, coeff_mk] <;> decide

private theorem coeff_jNum : coeff 0 jNum = 1 ∧ coeff 1 jNum = 744 ∧ coeff 2 jNum = 196884 := by
  have hrel : jNum * dedekindEtaUnit = eisenstein4 ^ 3 := by
    rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one]
  obtain ⟨e1, e2⟩ := coeff_etaProd
  obtain ⟨a1, a2⟩ := coeff_eisenstein4
  obtain ⟨-, u1, u2⟩ := coeff_pow_of_constantCoeff_eq_one constantCoeff_etaProd 24
  obtain ⟨-, b1, b2⟩ := coeff_pow_of_constantCoeff_eq_one constantCoeff_eisenstein4 3
  have hu0 : coeff 0 dedekindEtaUnit = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit]
  have hj0 : coeff 0 jNum = 1 := by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum]
  rw [show etaProd ^ 24 = dedekindEtaUnit from rfl, e1] at u1
  rw [show etaProd ^ 24 = dedekindEtaUnit from rfl, e1, e2] at u2
  rw [a1] at b1
  rw [a1, a2] at b2
  norm_num [Nat.choose_two_right] at u1 u2 b1 b2
  have r1 := congrArg (coeff 1) hrel
  have r2 := congrArg (coeff 2) hrel
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, hu0, hj0, u1, u2, b1, b2] at r1 r2
  norm_num at r1 r2
  refine ⟨hj0, by linarith, by linarith⟩

/-- `jq` at `n - 1` is the coefficient of `Xⁿ` in `jNum`. -/
private theorem coeff_jq_sub_one (n : ℕ) :
    jq.coeff ((n : ℤ) - 1) = ((coeff n jNum : ℤ) : ℚ) := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul,
    show ((n : ℤ) - 1 - (-1) : ℤ) = ((n : ℕ) : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff, jNumQ, coeff_map]
  simp

/-- **The constant term of the `j` Laurent series is `744`.** The coefficient of `q⁰` in
`ModularCurve.jq = q⁻¹ · jNum`, where `jNum = E₄³ · ∏_{n ≥ 1} (1 - qⁿ)⁻²⁴`, the expansion of
`q E₄³ / Δ`, is the integer power series
`eisenstein4 ^ 3 * dedekindEtaUnitInv`, is `744`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Corollary 19.6, p. 3: "With q = e^{2πiτ} we have
j(τ) = 1/q + 744 + ∑_{n=1}^∞ aₙqⁿ, where the aₙ are integers". By
`ModularCurve.hasSum_jq_qParam` the series `jq` sums to `E₄³ / Δ`; that this is the source's
`j = 1728 g₂³ / Δ` is not proved here. -/
theorem coeff_jq_zero : jq.coeff 0 = 744 := by
  have h := coeff_jq_sub_one 1
  rw [coeff_jNum.2.1] at h
  simpa using h

/-- **The coefficient of `q` in the `j` Laurent series is `196884`.** The coefficient of `q¹`
in `ModularCurve.jq = q⁻¹ · jNum` is `196884`.

Source: J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017), Theorem 4.22:
"j(z) = 1/q + 744 + 196 884q + 21 493 760q² + c(3)q³ + c(4)q⁴ + ⋯, q = e^{2πiz}, where
c(n) ∈ ℤ for all n". There `j = 1728 g₂³ / Δ` is defined from the lattice invariants `g₂`, `g₃`;
that this is the function whose expansion is `jq` is not proved here, and the coefficient
`21493760` is not proved here either. -/
theorem coeff_jq_one : jq.coeff 1 = 196884 := by
  have h := coeff_jq_sub_one 2
  rw [coeff_jNum.2.2] at h
  norm_num at h
  exact h

end ModularCurve

namespace WLight

open ModularCurve

/-- **The integral `q`-expansion of the `j`-function.** For `τ` in the upper half-plane let
`q = e^{2πiτ}` (`Function.Periodic.qParam 1 τ`). There are integers `c₀, c₁, …` with
`c₀ = 196884` such that, for every `τ`, the series `∑ cₙ q^{n+1}` converges absolutely and

$$j(\tau) = \frac{1}{q} + 744 + \sum_{n \ge 0} c_n q^{n+1},$$

where `j = E₄³ / Δ` is `WLight.jFunction`. So `cₙ` is the coefficient of `q^{n+1}`; in the
source's indexing `a_{n+1} = cₙ`. That `j` is also `1728 g₂³ / (g₂³ - 27 g₃²)` for the
lattice `ℤ + ℤτ` is not proved here.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 19, Corollary 19.6, p. 3: "With q = e^{2πiτ} we have
j(τ) = 1/q + 744 + ∑_{n=1}^∞ aₙqⁿ, where the aₙ are integers", proved from Lemma 19.5; the
value `196884` of the first coefficient is in J. S. Milne, *Modular Functions and Modular Forms*,
version 1.31 (2017), Theorem 4.22. -/
theorem jFunction_qExpansion_int :
    ∃ c : ℕ → ℤ, c 0 = 196884 ∧ ∀ τ : ℍ,
      Summable (fun n : ℕ => ‖(c n : ℂ) * Function.Periodic.qParam 1 τ ^ (n + 1)‖) ∧
      jFunction τ = (Function.Periodic.qParam 1 τ)⁻¹ + 744 +
        ∑' n : ℕ, (c n : ℂ) * Function.Periodic.qParam 1 τ ^ (n + 1) := by
  obtain ⟨g0, g1, g2⟩ := coeff_jNum
  refine ⟨fun n => coeff (n + 2) jNum, g2, fun τ => ?_⟩
  set q := Function.Periodic.qParam 1 τ with hqdef
  have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have h2 := (hasSum_nat_add_iff' 2).mpr (hasSum_jNum_qParam τ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, g0, g1, pow_zero, pow_one,
    zero_add, Int.cast_one, one_mul, ← hqdef] at h2
  have h3 := h2.div_const q
  have hterm : ∀ n : ℕ, ((coeff (n + 2) jNum : ℤ) : ℂ) * q ^ (n + 2) / q =
      ((coeff (n + 2) jNum : ℤ) : ℂ) * q ^ (n + 1) := by
    intro n
    field_simp
    ring
  simp only [hterm] at h3
  refine ⟨summable_norm_iff.mpr h3.summable, ?_⟩
  change ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ = _
  rw [h3.tsum_eq]
  field_simp
  push_cast
  ring

end WLight
