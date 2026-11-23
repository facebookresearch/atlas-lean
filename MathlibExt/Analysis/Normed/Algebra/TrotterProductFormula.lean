/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Order.Archimedean

@[expose] public section

namespace MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula

open Filter Topology

/-!
# The Trotter product formula for bounded operators

For elements `a b` of a complete normed algebra `𝔸` over `ℚ`,
`(exp (a / n) * exp (b / n)) ^ n → exp (a + b)` as `n → ∞`, in norm.
This is the Lie–Trotter product formula in its bounded form (H. F. Trotter,
*On the product of semi-groups of operators*, Proc. Amer. Math. Soc. 10
(1959), 545–551, DOI `10.1090/S0002-9939-1959-0108732-6`). In particular it
applies to bounded operators on a Banach space, where `exp` is the operator
exponential: `(exp (T / n) * exp (S / n)) ^ n → exp (T + S)` in operator
norm. The unbounded (Trotter–Kato) form for generators of semigroups is not
claimed here.

The scaling is written with rational scalars `(n : ℚ)⁻¹ • a`, matching the
`ℚ`-algebra structure that Mathlib's `NormedSpace.exp` is built on. In an
`ℝ`-algebra this is the usual `(1 / n) • a`. The operator form follows by applying `tendsto_trotter_product` to the
Banach algebra `E →L[𝕜] E`. For operators on a complex Banach space the
`ℚ`-algebra instance is not synthesized automatically; supply it with
`NormedAlgebra.restrictScalars ℚ ℂ _`.

The proof follows the classical estimate. Writing `R x = exp x - 1 - x`,
the series for `exp` gives `‖R x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖`, hence the
one-step estimate
`‖exp x * exp y - exp (x + y)‖ = O((‖x‖ + ‖y‖) ^ 2)`. Telescoping the
`n`-th power turns the `O (1 / n ^ 2)` one-step error into an `O (1 / n)`
error for the Trotter approximants, which tends to `0`.

Main results:

* `norm_exp_le_exp_norm`: `‖exp x‖ ≤ Real.exp ‖x‖`.
* `norm_exp_sub_one_sub_id_le`: `‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖`.
* `norm_exp_mul_exp_sub_exp_add_le`: the one-step estimate.
* `tendsto_trotter_product`: the Trotter product formula.
* `trotter_product_of_commute`: if `a` and `b` commute, the approximants are
  exactly `exp (a + b)` for every positive `n`.
-/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
  [NormOneClass 𝔸]

/-- The norm of a natural number cast into `ℚ`. -/
private lemma norm_natCast_rat (m : ℕ) : ‖((m : ℚ))‖ = (m : ℝ) := by
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, Rat.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg m)]

/-- The norm of a rational inverse scalar. -/
private lemma norm_inv_ratCast (m : ℕ) : ‖((m : ℚ)⁻¹ : ℚ)‖ = (m : ℝ)⁻¹ := by
  rw [norm_inv, norm_natCast_rat]

/-- The exponential series is summable in norm. -/
private lemma summable_norm_expSeries {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (x : 𝔸) :
    Summable (fun n : ℕ => ‖((n.factorial : ℚ))⁻¹ • x ^ n‖) :=
  NormedSpace.norm_expSeries_summable' x

/-- The exponential series is summable. -/
private lemma summable_expSeries {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [CompleteSpace 𝔸] (x : 𝔸) :
    Summable (fun n : ℕ => ((n.factorial : ℚ))⁻¹ • x ^ n) :=
  NormedSpace.expSeries_summable' x

/-- The exponential is bounded by the real exponential of the norm. -/
theorem norm_exp_le_exp_norm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormOneClass 𝔸] (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hexp : NormedSpace.exp x = ∑' n : ℕ, ((n.factorial : ℚ))⁻¹ • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℚ]
  have hreal : Real.exp ‖x‖ = ∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, hreal]
  calc ‖∑' n : ℕ, ((n.factorial : ℚ))⁻¹ • x ^ n‖
      ≤ ∑' n : ℕ, ‖((n.factorial : ℚ))⁻¹ • x ^ n‖ :=
        norm_tsum_le_tsum_norm (summable_norm_expSeries x)
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ) := by
        apply Summable.tsum_le_tsum
        · intro n
          rw [norm_smul, norm_inv_ratCast]
          calc ((n.factorial : ℝ))⁻¹ * ‖x ^ n‖
              ≤ ((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n :=
                mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by positivity)
            _ = ‖x‖ ^ n / (n.factorial : ℝ) := by rw [div_eq_mul_inv, mul_comm]
        · exact summable_norm_expSeries x
        · exact Real.summable_pow_div_factorial ‖x‖

/-- The Taylor remainder of `exp` at order one. -/
theorem norm_exp_sub_one_sub_id_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have hsum := summable_expSeries x
  have htail : Summable (fun n : ℕ => (((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)) :=
    hsum.comp_injective (fun a b h => Nat.add_right_cancel h)
  have htail_norm : Summable
      (fun n : ℕ => ‖(((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)‖) :=
    (summable_norm_expSeries x).comp_injective (fun a b h => Nat.add_right_cancel h)
  have hsplit : NormedSpace.exp x
      = 1 + x + ∑' n : ℕ, (((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2) := by
    rw [NormedSpace.exp_eq_tsum ℚ]
    show (∑' n : ℕ, ((n.factorial : ℚ))⁻¹ • x ^ n)
      = 1 + x + ∑' n : ℕ, (((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)
    rw [← Summable.sum_add_tsum_nat_add 2 hsum]
    simp [Finset.sum_range_succ, pow_zero, pow_one]
  have htail_eq : NormedSpace.exp x - 1 - x
      = ∑' n : ℕ, (((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2) := by
    rw [hsplit]
    abel
  have hreal : Real.exp ‖x‖ = ∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [htail_eq, hreal, ← tsum_mul_left]
  calc ‖∑' n : ℕ, (((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖(((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm htail_norm
    _ ≤ ∑' n : ℕ, ‖x‖ ^ 2 * (‖x‖ ^ n / (n.factorial : ℝ)) := by
        apply Summable.tsum_le_tsum
        · intro n
          calc ‖(((n + 2).factorial : ℚ))⁻¹ • x ^ (n + 2)‖
              = (((n + 2).factorial : ℝ))⁻¹ * ‖x ^ (n + 2)‖ := by
                rw [norm_smul, norm_inv_ratCast]
            _ ≤ (((n + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (n + 2) :=
                mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by positivity)
            _ = (((n + 2).factorial : ℝ))⁻¹ * (‖x‖ ^ 2 * ‖x‖ ^ n) := by
                rw [pow_add]; ring
            _ ≤ ‖x‖ ^ 2 * (‖x‖ ^ n / (n.factorial : ℝ)) := by
                have hfac : ((n.factorial : ℝ)) ≤ (((n + 2).factorial : ℝ)) := by
                  rw [Nat.cast_le]
                  exact Nat.factorial_le (Nat.le_add_right n 2)
                have hpos : (0 : ℝ) < ((n.factorial : ℝ)) := by positivity
                have hpos2 : (0 : ℝ) < (((n + 2).factorial : ℝ)) := by positivity
                have hinv : (((n + 2).factorial : ℝ))⁻¹ ≤ ((n.factorial : ℝ))⁻¹ :=
                  (inv_le_inv₀ hpos2 hpos).mpr hfac
                calc (((n + 2).factorial : ℝ))⁻¹ * (‖x‖ ^ 2 * ‖x‖ ^ n)
                    ≤ ((n.factorial : ℝ))⁻¹ * (‖x‖ ^ 2 * ‖x‖ ^ n) :=
                      mul_le_mul_of_nonneg_right hinv (by positivity)
                  _ = ‖x‖ ^ 2 * (‖x‖ ^ n / (n.factorial : ℝ)) := by
                      rw [div_eq_mul_inv, mul_comm, mul_assoc]
        · exact htail_norm
        · exact (Real.summable_pow_div_factorial ‖x‖).mul_left _

/-- The one-step Trotter estimate: `exp x * exp y` differs from
`exp (x + y)` by at most a quadratic expression in `‖x‖` and `‖y‖`. -/
theorem norm_exp_mul_exp_sub_exp_add_le (x y : 𝔸) :
    ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ ≤
      ‖x‖ * ‖y‖ + ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖ +
        (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖) +
        (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖) := by
  have hident : NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)
      = x * y + (NormedSpace.exp x - 1 - x) * NormedSpace.exp y +
        (1 + x) * (NormedSpace.exp y - 1 - y) -
        (NormedSpace.exp (x + y) - 1 - (x + y)) := by
    noncomm_ring
  have h1 : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le _ _
  have h2 : ‖(NormedSpace.exp x - 1 - x) * NormedSpace.exp y‖ ≤
      ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖ :=
    le_trans (norm_mul_le _ _)
      (mul_le_mul (norm_exp_sub_one_sub_id_le x) (norm_exp_le_exp_norm y)
        (norm_nonneg _) (by positivity))
  have h3 : ‖(1 + x) * (NormedSpace.exp y - 1 - y)‖ ≤
      (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖) := by
    refine le_trans (norm_mul_le _ _)
      (mul_le_mul ?_ (norm_exp_sub_one_sub_id_le y) (norm_nonneg _) (by positivity))
    calc ‖(1 : 𝔸) + x‖ ≤ ‖(1 : 𝔸)‖ + ‖x‖ := norm_add_le _ _
      _ = 1 + ‖x‖ := by rw [norm_one]
  have h4 : ‖NormedSpace.exp (x + y) - 1 - (x + y)‖ ≤
      (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖) := by
    refine le_trans (norm_exp_sub_one_sub_id_le (x + y)) ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
      (Real.exp_le_exp.mpr (norm_add_le _ _)) (by positivity) (by positivity)
  have htri : ‖x * y + (NormedSpace.exp x - 1 - x) * NormedSpace.exp y +
      (1 + x) * (NormedSpace.exp y - 1 - y) -
      (NormedSpace.exp (x + y) - 1 - (x + y))‖ ≤
      ‖x * y‖ + ‖(NormedSpace.exp x - 1 - x) * NormedSpace.exp y‖ +
        ‖(1 + x) * (NormedSpace.exp y - 1 - y)‖ +
        ‖NormedSpace.exp (x + y) - 1 - (x + y)‖ := by
    calc ‖x * y + (NormedSpace.exp x - 1 - x) * NormedSpace.exp y +
        (1 + x) * (NormedSpace.exp y - 1 - y) -
        (NormedSpace.exp (x + y) - 1 - (x + y))‖
        ≤ ‖x * y + (NormedSpace.exp x - 1 - x) * NormedSpace.exp y +
            (1 + x) * (NormedSpace.exp y - 1 - y)‖ +
            ‖NormedSpace.exp (x + y) - 1 - (x + y)‖ := norm_sub_le _ _
      _ ≤ (‖x * y‖ + ‖(NormedSpace.exp x - 1 - x) * NormedSpace.exp y‖ +
            ‖(1 + x) * (NormedSpace.exp y - 1 - y)‖) +
            ‖NormedSpace.exp (x + y) - 1 - (x + y)‖ :=
        le_trans (add_le_add (norm_add_le _ _) (le_refl _))
          (add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _))
      _ = ‖x * y‖ + ‖(NormedSpace.exp x - 1 - x) * NormedSpace.exp y‖ +
            ‖(1 + x) * (NormedSpace.exp y - 1 - y)‖ +
            ‖NormedSpace.exp (x + y) - 1 - (x + y)‖ := by ring
  rw [hident]
  linarith

/-- Powers differ at most linearly in the difference of the bases. The
`1` in the maximum is needed: without it the bound fails when the norms are
`< 1`. -/
theorem norm_pow_sub_pow_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    (X Y : 𝔸) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤ (n : ℝ) * ‖X - Y‖ * (max (max ‖X‖ ‖Y‖) 1) ^ n := by
  set M : ℝ := max (max ‖X‖ ‖Y‖) 1 with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hX : ‖X‖ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY : ‖Y‖ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : X ^ (n + 1) - Y ^ (n + 1)
        = X * (X ^ n - Y ^ n) + (X - Y) * Y ^ n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    rw [hstep]
    have h1 : ‖X * (X ^ n - Y ^ n)‖ ≤ M * ((n : ℝ) * ‖X - Y‖ * M ^ n) :=
      le_trans (norm_mul_le _ _)
        (mul_le_mul hX ih (norm_nonneg _) hM0)
    have h2 : ‖(X - Y) * Y ^ n‖ ≤ ‖X - Y‖ * M ^ n :=
      le_trans (norm_mul_le _ _)
        (mul_le_mul_of_nonneg_left
          (le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hY n))
          (norm_nonneg _))
    calc ‖X * (X ^ n - Y ^ n) + (X - Y) * Y ^ n‖
        ≤ ‖X * (X ^ n - Y ^ n)‖ + ‖(X - Y) * Y ^ n‖ := norm_add_le _ _
      _ ≤ M * ((n : ℝ) * ‖X - Y‖ * M ^ n) + ‖X - Y‖ * M ^ n := add_le_add h1 h2
      _ ≤ M * ((n : ℝ) * ‖X - Y‖ * M ^ n) + ‖X - Y‖ * M ^ (n + 1) :=
        add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 (Nat.le_succ n))
            (norm_nonneg (X - Y)))
      _ = ((n + 1 : ℕ) : ℝ) * ‖X - Y‖ * M ^ (n + 1) := by
          rw [pow_succ']
          push_cast
          ring

/-- `n • ((n : ℚ)⁻¹ • z) = z` for positive `n`. -/
private lemma nsmul_ratInv_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (m : ℕ) (hm : 0 < m) (z : 𝔸) :
    m • (((m : ℚ))⁻¹ • z) = z := by
  have hm0 : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  rw [nsmul_eq_mul, Algebra.smul_def, ← map_natCast (algebraMap ℚ 𝔸) m,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hm0, map_one, one_mul]

/-- The **Trotter product formula** for bounded elements of a complete normed
algebra: `(exp (a / n) * exp (b / n)) ^ n → exp (a + b)` in norm. -/
theorem tendsto_trotter_product (a b : 𝔸) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n : ℚ)⁻¹ • a) * NormedSpace.exp ((n : ℚ)⁻¹ • b)) ^ n)
      atTop (nhds (NormedSpace.exp (a + b))) := by
  set M : ℝ := ‖a‖ + ‖b‖ with hM
  set K : ℝ := ‖a‖ * ‖b‖ + ‖a‖ ^ 2 * Real.exp M +
      (1 + ‖a‖) * (‖b‖ ^ 2 * Real.exp M) + M ^ 2 * Real.exp M with hK
  set C : ℝ := K * Real.exp M with hC
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; exact mul_nonneg hK0 (Real.exp_nonneg _)
  -- Pointwise bound: the `m`-th approximant is within `C / m` of `exp (a + b)`.
  have hbound : ∀ m : ℕ, 0 < m →
      ‖(NormedSpace.exp ((m : ℚ)⁻¹ • a) * NormedSpace.exp ((m : ℚ)⁻¹ • b)) ^ m -
        NormedSpace.exp (a + b)‖ ≤ C / (m : ℝ) := by
    intro m hmpos
    set t : ℚ := (m : ℚ)⁻¹ with ht
    set x : 𝔸 := t • a with hx
    set y : 𝔸 := t • b with hy
    have hnorm_t : ‖(t : ℚ)‖ = (m : ℝ)⁻¹ := norm_inv_ratCast m
    have hnorm_x : ‖x‖ = (m : ℝ)⁻¹ * ‖a‖ := by rw [hx, norm_smul, hnorm_t]
    have hnorm_y : ‖y‖ = (m : ℝ)⁻¹ * ‖b‖ := by rw [hy, norm_smul, hnorm_t]
    have hsum : ‖x‖ + ‖y‖ = (m : ℝ)⁻¹ * M := by
      rw [hnorm_x, hnorm_y, ← mul_add, hM]
    have hle_t : (m : ℝ)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hmpos)
    have hxM : ‖x‖ ≤ M := by
      rw [hnorm_x]
      calc (m : ℝ)⁻¹ * ‖a‖ ≤ 1 * ‖a‖ := by
            apply mul_le_mul_of_nonneg_right hle_t (norm_nonneg _)
        _ = ‖a‖ := one_mul _
        _ ≤ M := by rw [hM]; exact le_add_of_nonneg_right (norm_nonneg _)
    have hyM : ‖y‖ ≤ M := by
      rw [hnorm_y]
      calc (m : ℝ)⁻¹ * ‖b‖ ≤ 1 * ‖b‖ := by
            apply mul_le_mul_of_nonneg_right hle_t (norm_nonneg _)
        _ = ‖b‖ := one_mul _
        _ ≤ M := by rw [hM]; exact le_add_of_nonneg_left (norm_nonneg _)
    -- One-step estimate, with the `1 / m ^ 2` factor made explicit.
    have hstep : ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ ≤
        ((m : ℝ)⁻¹) ^ 2 * K := by
      have h := norm_exp_mul_exp_sub_exp_add_le x y
      have h1 : ‖x‖ * ‖y‖ = ((m : ℝ)⁻¹) ^ 2 * (‖a‖ * ‖b‖) := by
        rw [hnorm_x, hnorm_y]; ring
      have h2 : ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖ ≤
          ((m : ℝ)⁻¹) ^ 2 * (‖a‖ ^ 2 * Real.exp M) := by
        have e2 : Real.exp ‖x‖ * Real.exp ‖y‖ ≤ Real.exp M := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr
            (by rw [hsum]; exact mul_le_of_le_one_left (by positivity) hle_t)
        calc ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖
            = ((m : ℝ)⁻¹) ^ 2 * ‖a‖ ^ 2 * (Real.exp ‖x‖ * Real.exp ‖y‖) := by
              rw [hnorm_x]; ring
          _ ≤ ((m : ℝ)⁻¹) ^ 2 * ‖a‖ ^ 2 * Real.exp M :=
              mul_le_mul_of_nonneg_left e2 (by positivity)
          _ = ((m : ℝ)⁻¹) ^ 2 * (‖a‖ ^ 2 * Real.exp M) := by ring
      have h3 : (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖) ≤
          ((m : ℝ)⁻¹) ^ 2 * ((1 + ‖a‖) * (‖b‖ ^ 2 * Real.exp M)) := by
        have e1 : ‖y‖ ^ 2 = ((m : ℝ)⁻¹) ^ 2 * ‖b‖ ^ 2 := by rw [hnorm_y]; ring
        have e2 : Real.exp ‖y‖ ≤ Real.exp M := Real.exp_le_exp.mpr hyM
        have e3 : (1 + ‖x‖) ≤ 1 + ‖a‖ := by
          have : ‖x‖ ≤ ‖a‖ := by
            rw [hnorm_x]
            calc (m : ℝ)⁻¹ * ‖a‖ ≤ 1 * ‖a‖ :=
                  mul_le_mul_of_nonneg_right hle_t (norm_nonneg _)
              _ = ‖a‖ := one_mul _
          linarith
        calc (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖)
            = (1 + ‖x‖) * (((m : ℝ)⁻¹) ^ 2 * ‖b‖ ^ 2 * Real.exp ‖y‖) := by rw [e1]
          _ ≤ (1 + ‖a‖) * (((m : ℝ)⁻¹) ^ 2 * ‖b‖ ^ 2 * Real.exp M) := by
              apply mul_le_mul e3 _ (by positivity) (by positivity)
              apply mul_le_mul_of_nonneg_left e2 (by positivity)
          _ = ((m : ℝ)⁻¹) ^ 2 * ((1 + ‖a‖) * (‖b‖ ^ 2 * Real.exp M)) := by ring
      have h4 : (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖) ≤
          ((m : ℝ)⁻¹) ^ 2 * (M ^ 2 * Real.exp M) := by
        have e2 : Real.exp ((m : ℝ)⁻¹ * M) ≤ Real.exp M := by
          apply Real.exp_le_exp.mpr
          calc (m : ℝ)⁻¹ * M ≤ 1 * M := mul_le_mul_of_nonneg_right hle_t (by positivity)
            _ = M := one_mul _
        rw [hsum, show ((m : ℝ)⁻¹ * M) ^ 2 = ((m : ℝ)⁻¹) ^ 2 * M ^ 2 from by ring]
        calc ((m : ℝ)⁻¹) ^ 2 * M ^ 2 * Real.exp ((m : ℝ)⁻¹ * M)
            ≤ ((m : ℝ)⁻¹) ^ 2 * M ^ 2 * Real.exp M :=
              mul_le_mul_of_nonneg_left e2 (by positivity)
          _ = ((m : ℝ)⁻¹) ^ 2 * (M ^ 2 * Real.exp M) := by ring
      calc ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖
          ≤ ‖x‖ * ‖y‖ + ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖ +
              (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖) +
              (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖) := h
        _ ≤ ((m : ℝ)⁻¹) ^ 2 * (‖a‖ * ‖b‖) +
              ((m : ℝ)⁻¹) ^ 2 * (‖a‖ ^ 2 * Real.exp M) +
              ((m : ℝ)⁻¹) ^ 2 * ((1 + ‖a‖) * (‖b‖ ^ 2 * Real.exp M)) +
              ((m : ℝ)⁻¹) ^ 2 * (M ^ 2 * Real.exp M) :=
            add_le_add (add_le_add (add_le_add h1.le h2) h3) h4
        _ = ((m : ℝ)⁻¹) ^ 2 * K := by rw [hK]; ring
    -- The target is the `m`-th power of the one-step approximant for `a + b`.
    have hxy : x + y = t • (a + b) := by rw [hx, hy, ← smul_add]
    have hpow : (NormedSpace.exp (t • (a + b))) ^ m = NormedSpace.exp (a + b) := by
      rw [← NormedSpace.exp_nsmul]
      congr 1
      exact nsmul_ratInv_smul m hmpos (a + b)
    -- Telescoping the powers: both bases have norm at most `exp (M / m)`.
    have hmax1 : ‖NormedSpace.exp x * NormedSpace.exp y‖ ≤ Real.exp ((m : ℝ)⁻¹ * M) := by
      calc ‖NormedSpace.exp x * NormedSpace.exp y‖
          ≤ ‖NormedSpace.exp x‖ * ‖NormedSpace.exp y‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖x‖ * Real.exp ‖y‖ :=
            mul_le_mul (norm_exp_le_exp_norm x) (norm_exp_le_exp_norm y)
              (norm_nonneg _) (by positivity)
        _ = Real.exp (‖x‖ + ‖y‖) := (Real.exp_add _ _).symm
        _ = Real.exp ((m : ℝ)⁻¹ * M) := by rw [hsum]
    have hmax2 : ‖NormedSpace.exp (t • (a + b))‖ ≤ Real.exp ((m : ℝ)⁻¹ * M) := by
      refine le_trans (norm_exp_le_exp_norm _) (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, hnorm_t]
      calc (m : ℝ)⁻¹ * ‖a + b‖ ≤ (m : ℝ)⁻¹ * (‖a‖ + ‖b‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
        _ = (m : ℝ)⁻¹ * M := by rw [hM]
    have hmax : max ‖NormedSpace.exp x * NormedSpace.exp y‖
        ‖NormedSpace.exp (t • (a + b))‖ ≤ Real.exp ((m : ℝ)⁻¹ * M) :=
      max_le hmax1 hmax2
    have hpowmax : (max (max ‖NormedSpace.exp x * NormedSpace.exp y‖
        ‖NormedSpace.exp (t • (a + b))‖) 1) ^ m ≤ Real.exp M := by
      have h1le : (1 : ℝ) ≤ Real.exp ((m : ℝ)⁻¹ * M) :=
        Real.one_le_exp (by positivity)
      have hmax' : max (max ‖NormedSpace.exp x * NormedSpace.exp y‖
          ‖NormedSpace.exp (t • (a + b))‖) 1 ≤ Real.exp ((m : ℝ)⁻¹ * M) :=
        max_le hmax h1le
      calc (max (max ‖NormedSpace.exp x * NormedSpace.exp y‖
            ‖NormedSpace.exp (t • (a + b))‖) 1) ^ m
          ≤ (Real.exp ((m : ℝ)⁻¹ * M)) ^ m :=
            pow_le_pow_left₀ (by positivity) hmax' m
        _ = Real.exp ((m : ℝ) * ((m : ℝ)⁻¹ * M)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp M := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel₀
              (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmpos)), one_mul]
    -- The one-step estimate for the rescaled pair, with `x + y = t • (a + b)`.
    have hstep' : ‖NormedSpace.exp x * NormedSpace.exp y -
        NormedSpace.exp (t • (a + b))‖ ≤ ((m : ℝ)⁻¹) ^ 2 * K := by
      rw [← hxy]
      exact hstep
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmpos)
    -- Combine: `O (1 / m ^ 2)` one-step error, telescoped over `m` powers.
    have hgoal : (NormedSpace.exp x * NormedSpace.exp y) ^ m - NormedSpace.exp (a + b)
        = (NormedSpace.exp x * NormedSpace.exp y) ^ m -
          (NormedSpace.exp (t • (a + b))) ^ m := by
      rw [hpow]
    rw [hgoal]
    calc ‖(NormedSpace.exp x * NormedSpace.exp y) ^ m -
            (NormedSpace.exp (t • (a + b))) ^ m‖
        ≤ (m : ℝ) * ‖NormedSpace.exp x * NormedSpace.exp y -
            NormedSpace.exp (t • (a + b))‖ *
            (max (max ‖NormedSpace.exp x * NormedSpace.exp y‖
              ‖NormedSpace.exp (t • (a + b))‖) 1) ^ m :=
          norm_pow_sub_pow_le _ _ m
      _ = (m : ℝ) * (‖NormedSpace.exp x * NormedSpace.exp y -
            NormedSpace.exp (t • (a + b))‖ *
            (max (max ‖NormedSpace.exp x * NormedSpace.exp y‖
              ‖NormedSpace.exp (t • (a + b))‖) 1) ^ m) := by rw [mul_assoc]
      _ ≤ (m : ℝ) * (((m : ℝ)⁻¹) ^ 2 * K * Real.exp M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hstep' hpowmax
            (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) m) (by positivity)
      _ = C / (m : ℝ) := by
          rw [hC]
          field_simp
  -- Conclude by the `ε`–`N` characterization of convergence.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (div_nonneg hC0 hε.le) hN
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le (by exact_mod_cast hNpos) hn
  rw [dist_eq_norm]
  calc ‖(NormedSpace.exp ((n : ℚ)⁻¹ • a) * NormedSpace.exp ((n : ℚ)⁻¹ • b)) ^ n -
          NormedSpace.exp (a + b)‖
      ≤ C / (n : ℝ) := hbound n hn1
    _ ≤ C / (N : ℝ) :=
        div_le_div_of_nonneg_left hC0 hNpos (by exact_mod_cast hn)
    _ < ε := by
        rw [div_lt_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < (N : ℝ))]
        have h := (div_lt_iff₀ hε).mp hN
        linarith

/-- If `a` and `b` commute, the Trotter approximants are exactly
`exp (a + b)` for every positive `n`. -/
theorem trotter_product_of_commute {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [CompleteSpace 𝔸] {a b : 𝔸} (h : Commute a b) {n : ℕ} (hn : 0 < n) :
    (NormedSpace.exp ((n : ℚ)⁻¹ • a) * NormedSpace.exp ((n : ℚ)⁻¹ • b)) ^ n =
      NormedSpace.exp (a + b) := by
  have hcomm : Commute (((n : ℚ))⁻¹ • a) (((n : ℚ))⁻¹ • b) :=
    (h.smul_left _).smul_right _
  rw [← NormedSpace.exp_add_of_commute hcomm, ← smul_add,
    ← NormedSpace.exp_nsmul]
  congr 1
  exact nsmul_ratInv_smul n hn (a + b)

end MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula
