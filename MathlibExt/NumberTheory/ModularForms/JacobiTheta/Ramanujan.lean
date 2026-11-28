/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Complex
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

/-!
# Ramanujan's general theta function

This file defines Ramanujan's general theta function in its two multiplicative parameters

  `f(a,b) = ∑_{n ∈ ℤ} a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)`,

with classical (absolute) convergence on `‖a * b‖ < 1`. The raw sum
`ramanujanThetaRaw` is Mathlib's total `tsum`, which is `0` for a nonsummable family.
The canonical `ramanujanTheta` therefore requires an explicit summability witness.

## Main definitions

* `ramanujanThetaTerm a b n` — the `n`th summand.
* `ramanujanThetaRaw a b` — the unrestricted total `tsum`.
* `ramanujanTheta a b h` — the theta sum with summability evidence `h`.

## Main results

* `ramanujanThetaTerm_neg` and `ramanujanTheta_symm`: `f(a,b) = f(b,a)` via `n ↦ -n`.
* `ramanujanThetaRaw_eq_qPochhammerInfRaw`: the Jacobi triple product for `|a * b| < 1`.

## References

* Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's Function*,
  INTEGERS 26 (2026), Article A41, pp. 1–7, Section 1 (definition and triple product).
* C. Adiga, B. C. Berndt, S. Bhargava, and G. N. Watson, *Chapter 16 of Ramanujan's Second
  Notebook: Theta-Functions and q-Series*, Mem. Amer. Math. Soc. 53 (1985), no. 315, pp. 1–85,
  Entry 19 (Jacobi triple product).

The nonzero-parameter proof is moved from `theta_product_of_ne_zero` and its helpers in
`MathlibExt.Combinatorics.Enumerative.Partition.SlaterOrderEighteenThetaRamanujanThetaEtaQuotients`.
The zero-parameter sum calculation is moved from `ramanujanThetaRaw_zero_left` in
`MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductSum`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Summand of Ramanujan's general theta function.** For complex numbers $a$, $b$ and an
integer $n$, this is the term $a^{n(n+1)/2} b^{n(n-1)/2}$ of index $n$ in Ramanujan's general
theta function $f(a,b) = \sum_{k \in \mathbb{Z}} a^{k(k+1)/2} b^{k(k-1)/2}$.

Both exponents $n(n+1)/2$ and $n(n-1)/2$ are nonnegative integers for every integer $n$, so
the term is a product of ordinary powers with natural-number exponents.

Source: the common definition in arXiv:2305.14988,
arXiv:2309.06689, arXiv:2312.15513, arXiv:2502.17312, and arXiv:2607.26471. -/
noncomputable def ramanujanThetaTerm (a b : ℂ) (n : ℤ) : ℂ :=
  a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

/-- **Raw Ramanujan theta sum.** For complex numbers $a$ and $b$, the raw Ramanujan theta sum is
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ when this series is summable, and $0$
otherwise.

The value $0$ for a non-summable series is a convention. Ramanujan's general theta function,
which requires the series to be summable, is the intended object. -/
noncomputable def ramanujanThetaRaw (a b : ℂ) : ℂ :=
  ∑' n : ℤ, ramanujanThetaTerm a b n

/-- **Ramanujan's general theta function.** For complex numbers $a$ and $b$ such that the series
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ is summable, Ramanujan's general theta
function is its sum $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$. -/
noncomputable def ramanujanTheta (a b : ℂ)
    (_h : Summable (ramanujanThetaTerm a b)) : ℂ :=
  ramanujanThetaRaw a b

@[simp]
theorem ramanujanThetaTerm_zero (a b : ℂ) :
    ramanujanThetaTerm a b 0 = 1 := by
  simp [ramanujanThetaTerm]

@[simp]
theorem ramanujanThetaTerm_one (a b : ℂ) :
    ramanujanThetaTerm a b 1 = a := by
  simp [ramanujanThetaTerm]

@[simp]
theorem ramanujanThetaTerm_neg_one (a b : ℂ) :
    ramanujanThetaTerm a b (-1) = b := by
  simp [ramanujanThetaTerm]

theorem ramanujanThetaTerm_neg (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b (-n) = ramanujanThetaTerm b a n := by
  unfold ramanujanThetaTerm
  have h₁ : (-n) * (-n + 1) / (2 : ℤ) = n * (n - 1) / 2 := by
    rw [show (-n) * (-n + 1) = n * (n - 1) by ring]
  have h₂ : (-n) * (-n - 1) / (2 : ℤ) = n * (n + 1) / 2 := by
    rw [show (-n) * (-n - 1) = n * (n + 1) by ring]
  rw [h₁, h₂, mul_comm]

theorem ramanujanTheta_summable_symm (a b : ℂ) :
    Summable (ramanujanThetaTerm a b) ↔ Summable (ramanujanThetaTerm b a) := by
  constructor
  · intro hab
    have h := (Equiv.neg ℤ).summable_iff.mpr hab
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h
  · intro hba
    have h := (Equiv.neg ℤ).summable_iff.mpr hba
    simpa [Function.comp_def, ramanujanThetaTerm_neg] using h

theorem ramanujanThetaRaw_symm (a b : ℂ) :
    ramanujanThetaRaw a b = ramanujanThetaRaw b a := by
  unfold ramanujanThetaRaw
  have h : ∀ n : ℤ, ramanujanThetaTerm a b n = ramanujanThetaTerm b a (-n) :=
    fun n => (ramanujanThetaTerm_neg b a n).symm
  calc
    ∑' n : ℤ, ramanujanThetaTerm a b n =
        ∑' n : ℤ, ramanujanThetaTerm b a (-n) := by simp_rw [h]
    _ = ∑' n : ℤ, ramanujanThetaTerm b a n :=
      Equiv.tsum_eq (Equiv.neg ℤ) (fun n => ramanujanThetaTerm b a n)

theorem ramanujanTheta_symm (a b : ℂ) (h : Summable (ramanujanThetaTerm a b)) :
    ramanujanTheta a b h =
      ramanujanTheta b a ((ramanujanTheta_summable_symm a b).mp h) := by
  simpa [ramanujanTheta] using ramanujanThetaRaw_symm a b

/-- **Ramanujan's theta series diverges at $a = b = 1$.** The series
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ of Ramanujan's general theta function is
not summable at $a = b = 1$, since every one of its terms equals $1$. -/
theorem not_summable_ramanujanThetaTerm_one_one :
    ¬Summable (ramanujanThetaTerm 1 1) := by
  intro h
  have hnorm : Summable (fun _ : ℤ => (1 : ℝ)) := by
    simpa [ramanujanThetaTerm] using h.norm
  exact @not_finite ℤ inferInstance (Finite.of_summable_const zero_lt_one hnorm)

/-- **The raw Ramanujan theta sum vanishes at $a = b = 1$.** The raw Ramanujan theta sum
$\sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$, which is assigned the value $0$ whenever
the series is not summable, equals $0$ at $a = b = 1$, because there every term equals $1$ and
the series is not summable. -/
theorem ramanujanThetaRaw_one_one : ramanujanThetaRaw 1 1 = 0 := by
  exact tsum_eq_zero_of_not_summable not_summable_ramanujanThetaTerm_one_one

open QPochhammer

local notation "P" => qPochhammerInfRaw

private lemma twice_triangle (n : ℤ) :
    2 * (((n * (n + 1) / 2).toNat : ℕ) : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self n)

private lemma theta_term (z r : ℂ) (hz : z ≠ 0) (n : ℤ) :
    ramanujanThetaTerm (z * r) (z⁻¹ * r) n = z ^ n * r ^ (n * n).toNat := by
  let u := (n * (n + 1) / 2).toNat
  let v := (n * (n - 1) / 2).toNat
  have hu : 2 * (u : ℤ) = n * (n + 1) := twice_triangle n
  have hv : 2 * (v : ℤ) = n * (n - 1) := by
    have he : -n * (-n + 1) = n * (n - 1) := by ring
    simpa only [he] using twice_triangle (-n)
  have hd : (u : ℤ) - v = n := by linarith only [hu, hv]
  have hs : u + v = (n * n).toNat := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_add, Int.toNat_of_nonneg (mul_self_nonneg n)]
    linarith only [hu, hv]
  change (z * r) ^ u * (z⁻¹ * r) ^ v = _
  rw [mul_pow, mul_pow, mul_mul_mul_comm, ← pow_add, hs,
    ← zpow_natCast z u, ← zpow_natCast z⁻¹ v, inv_zpow', ← zpow_add₀ hz,
    ← sub_eq_add_neg, hd]

open Analysis.SpecialFunctions.JacobiTripleProduct in
private lemma theta_product (z r : ℂ) (hz : z ≠ 0) (hr : ‖r‖ < 1) :
    ramanujanThetaRaw (z * r) (z⁻¹ * r) =
      P (r ^ 2) (r ^ 2) * P (-(z * r)) (r ^ 2) * P (-(z⁻¹ * r)) (r ^ 2) := by
  have h₂ : ‖r ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hr two_ne_zero
  obtain ⟨-, -, hj⟩ := jacobi_triple_product z r hz hr
  simp only [ramanujanThetaRaw, theta_term z r hz, hj]
  have hP (a : ℂ) : HasProd (fun n : ℕ => 1 - a * (r ^ 2) ^ n) (P a (r ^ 2)) := by
    rw [qPochhammerInfRaw_eq_tprod]
    exact (hasProd_qPochhammerInf a (r ^ 2) h₂).multipliable.hasProd
  have hp := ((hP (r ^ 2)).mul (hP (-(z * r)))).mul (hP (-(z⁻¹ * r)))
  apply (hp.congr_fun (fun n => ?_)).tprod_eq
  simp only [pow_add, pow_mul, pow_one]
  ring

private lemma theta_product_of_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b = P (a * b) (a * b) * P (-a) (a * b) * P (-b) (a * b) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a * b) zero_lt_two
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero ha hb) (by simpa using hr.symm)
  have hr1 : ‖r‖ < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mp (by
    rw [← norm_pow, hr]
    exact hab)
  have hza : a / r * r = a := div_mul_cancel₀ _ hr0
  have hzb : (a / r)⁻¹ * r = b := by
    rw [inv_div, div_mul_eq_mul_div, ← sq, hr, mul_div_cancel_left₀ _ ha]
  simpa only [hza, hzb, hr] using theta_product (a / r) r (div_ne_zero ha hr0) hr1

/-- **Ramanujan's theta function with first parameter zero.** For every complex number $b$,
$f(0,b) = 1 + b$: the only indices that contribute are $0$ and $-1$. -/
public theorem ramanujanThetaRaw_zero_left (b : ℂ) : ramanujanThetaRaw 0 b = 1 + b := by
  unfold ramanujanThetaRaw
  rw [tsum_eq_sum (s := {0, -1})]
  · simp
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hprod : 0 ≤ (n - 1) * (n + 2) := by
      rcases le_or_gt n (-2) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    have htwo : 2 ≤ n * (n + 1) := calc
      2 ≤ (n - 1) * (n + 2) + 2 := le_add_of_nonneg_left hprod
      _ = n * (n + 1) := by ring
    have hexp : (n * (n + 1) / 2).toNat ≠ 0 := by omega
    simp [ramanujanThetaTerm, zero_pow hexp]

private lemma pochhammer_zero_base (a : ℂ) : P a 0 = 1 - a := by
  rw [qPochhammerInfRaw_eq_tprod, tprod_eq_prod (s := {0})]
  · simp
  · intro n hn
    simp [zero_pow (by simpa using hn : n ≠ 0)]

private lemma theta_product_zero_left (b : ℂ) :
    ramanujanThetaRaw 0 b = P (0 * b) (0 * b) * P (-0) (0 * b) * P (-b) (0 * b) := by
  simp [ramanujanThetaRaw_zero_left, pochhammer_zero_base]

/-- **Jacobi triple product for Ramanujan's theta function.** For complex numbers $a$ and $b$
with $|ab| < 1$, the theta series $f(a,b)$ equals
$(ab;ab)_\infty (-a;ab)_\infty (-b;ab)_\infty$. -/
public theorem ramanujanThetaRaw_eq_qPochhammerInfRaw {a b : ℂ} (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b = P (a * b) (a * b) * P (-a) (a * b) * P (-b) (a * b) := by
  by_cases ha : a = 0
  · subst a
    exact theta_product_zero_left b
  by_cases hb : b = 0
  · subst b
    simpa only [zero_mul, mul_zero, mul_assoc, mul_comm (P (-a) 0),
      ← ramanujanThetaRaw_symm a 0] using theta_product_zero_left a
  exact theta_product_of_ne_zero ha hb hab

end MetaMathlibExt
