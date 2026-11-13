/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith

/-!
# Multispecies reactive transport conservation

If `c_t + ∂ₓ J = S *ᵥ r(c)` and `lᵀ S = 0`, then the derivative of
`∫_Ω lᵀ c` equals minus the boundary integral `lᵀ J · n`. Here this is
proved on a one-dimensional box `[a, b]`, where the boundary term is
`l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a)`.

No ordering of `a` and `b` is assumed: the integrals are Mathlib's oriented
interval integrals `∫ x in a..b` and the pointwise hypotheses range over
`Set.uIcc a b`, so both results are signed oriented-interval identities, and
for `b < a` both sides change sign together. The physical reading as an
inventory over the box `[a, b]` with the boundary flux as written requires
`a ≤ b`.

## i. Overview

Integrate the PDE in `x`, weighted by the conservation vector `l`: the
reaction term vanishes by `lᵀ S = 0` after swapping finite sums and
integrals, and the flux term integrates by the fundamental theorem of
calculus per species. No-flux is not assumed; the boundary term is the
result. The PDE is assumed only on `[a, b]`, in a form that asserts that
the time derivative `c_t` exists there; the fluxes are assumed
differentiable in `x` on `[a, b]`. The derivative form assumes
differentiation under the integral sign per species (`hswap`) and
integrability of `c` at all times (`hc_all`) as explicit hypotheses.

## ii. Key results

- `EarthScience.multispecies_integrated`: the integrated `l`-weighted
  balance.
- `EarthScience.multispecies_mass_balance`: the derivative of the
  conserved inventory.

## iii. Table of contents

- A. Multispecies conservation on a box

## iv. References

- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
  (Mathlib).

## A. Multispecies conservation on a box
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-- Multispecies reactive-transport conservation on a one-dimensional box
`[a, b]`, at time `t`. Species concentrations are `c t x : Fin n → ℝ`,
fluxes `J t x : Fin n → ℝ`, the stoichiometric matrix is
`S : Fin n → Fin m → ℝ`, and `r : (Fin n → ℝ) → Fin m → ℝ` is the reaction
rate vector. Suppose that at every `x ∈ [a, b]` each concentration
`c_i(·, x)` has time derivative `(S *ᵥ r(c))_i - ∂ₓ J_i` at `t` (that is,
`c_t + ∂ₓ J = S *ᵥ r(c)` with `c_t` existing) and each flux `J_i(t, ·)` is
differentiable at `x`. If `l` is a conservation vector,
`∑ i, l i * S i j = 0` for every reaction `j`, then the integral of
`l ⬝ᵥ c_t` over `[a, b]` equals minus the boundary flux
`l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a)`; the reaction term drops out. Without
`a ≤ b` this is a signed identity for the oriented integral `∫ x in a..b`;
the box interpretation requires `a ≤ b`. -/
theorem multispecies_integrated (n m : ℕ) (c J : ℝ → ℝ → Fin n → ℝ)
    (S : Fin n → Fin m → ℝ) (r : (Fin n → ℝ) → Fin m → ℝ)
    (l : Fin n → ℝ) (a b t : ℝ)
    (hpde : ∀ x ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun t => c t x i)
      ((∑ j, S i j * r (c t x) j) - deriv (fun x => J t x i) x) t)
    (hcons : ∀ j, ∑ i, l i * S i j = 0)
    (ht_int : ∀ i, IntervalIntegrable (fun x => deriv (fun t => c t x i) t)
      MeasureTheory.volume a b)
    (hx_int : ∀ i, IntervalIntegrable (fun x => deriv (fun x => J t x i) x)
      MeasureTheory.volume a b)
    (hx_deriv : ∀ i, ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => J t x i) (deriv (fun x => J t x i) x) x) :
    (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t) =
      -((∑ i, l i * J t b i) - ∑ i, l i * J t a i) := by
  have ht_wint : ∀ i, IntervalIntegrable (fun x => l i * deriv (fun t => c t x i) t)
      MeasureTheory.volume a b :=
    fun i => (ht_int i).const_mul (l i)
  have hx_wint : ∀ i, IntervalIntegrable (fun x => l i * deriv (fun x => J t x i) x)
      MeasureTheory.volume a b :=
    fun i => (hx_int i).const_mul (l i)
  have hA_int : IntervalIntegrable (fun x => ∑ i, l i * deriv (fun t => c t x i) t)
      MeasureTheory.volume a b := by
    have h := IntervalIntegrable.sum Finset.univ (fun i _ => ht_wint i)
    have heq : (∑ i : Fin n, fun x => l i * deriv (fun t => c t x i) t)
        = (fun x => ∑ i, l i * deriv (fun t => c t x i) t) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hB_int : IntervalIntegrable (fun x => ∑ i, l i * deriv (fun x => J t x i) x)
      MeasureTheory.volume a b := by
    have h := IntervalIntegrable.sum Finset.univ (fun i _ => hx_wint i)
    have heq : (∑ i : Fin n, fun x => l i * deriv (fun x => J t x i) x)
        = (fun x => ∑ i, l i * deriv (fun x => J t x i) x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hpoint : ∀ x ∈ Set.uIcc a b, (∑ i, l i * deriv (fun t => c t x i) t) +
      (∑ i, l i * deriv (fun x => J t x i) x)
      = ∑ i, l i * (∑ j, S i j * r (c t x) j) := by
    intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add, (hpde x hx i).deriv, sub_add_cancel]
  have hadd : (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t)
      + (∫ x in a..b, ∑ i, l i * deriv (fun x => J t x i) x)
      = ∫ x in a..b, ∑ i, l i * (∑ j, S i j * r (c t x) j) := by
    rw [← intervalIntegral.integral_add hA_int hB_int]
    exact intervalIntegral.integral_congr fun x hx => hpoint x hx
  have hCreac : ∀ x, (∑ i, l i * (∑ j, S i j * r (c t x) j)) = 0 := by
    intro x
    simp_rw [Finset.mul_sum]
    simp_rw [← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp [hcons]
  have hC_int_zero : (∫ x in a..b, ∑ i, l i * (∑ j, S i j * r (c t x) j)) = 0 := by
    have hfun0 : (fun x => ∑ i, l i * (∑ j, S i j * r (c t x) j)) = fun _ => 0 :=
      funext hCreac
    rw [hfun0]
    simp
  have hflux_each : ∀ i, (∫ x in a..b, l i * deriv (fun x => J t x i) x)
      = l i * (J t b i - J t a i) := by
    intro i
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hx_deriv i x hx
    · exact hx_int i
  have hB_eq : (∫ x in a..b, ∑ i, l i * deriv (fun x => J t x i) x)
      = (∑ i, l i * J t b i) - ∑ i, l i * J t a i := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hx_wint i)]
    simp_rw [hflux_each]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hsum_zero : (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t)
      + (∫ x in a..b, ∑ i, l i * deriv (fun x => J t x i) x) = 0 := by
    rw [hadd, hC_int_zero]
  rw [hB_eq] at hsum_zero
  linarith

/-- Multispecies mass balance on a one-dimensional box `[a, b]`, at time
`t`. Under the hypotheses of `multispecies_integrated`, the conserved
inventory `t ↦ ∫ x in a..b, l ⬝ᵥ c t x` has derivative
`-(l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a))` at `t`: it changes only by the net boundary
flux. Two further hypotheses are explicit: `hswap`, differentiation under the
integral sign per species (each `t ↦ ∫ x in a..b, c t x i` has derivative
`∫ x in a..b, ∂ₜ c t x i` at `t`), and `hc_all`, interval integrability of
every species concentration on `[a, b]` at every time `t'`, which is used to
split the inventory into per-species integrals. Without `a ≤ b` this is a
signed identity for the oriented integral; the inventory interpretation
requires `a ≤ b`. -/
theorem multispecies_mass_balance (n m : ℕ)
    (c J : ℝ → ℝ → Fin n → ℝ)
    (S : Fin n → Fin m → ℝ) (r : (Fin n → ℝ) → Fin m → ℝ)
    (l : Fin n → ℝ) (a b t : ℝ)
    (hpde : ∀ x ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun t => c t x i)
      ((∑ j, S i j * r (c t x) j) - deriv (fun x => J t x i) x) t)
    (hcons : ∀ j, ∑ i, l i * S i j = 0)
    (ht_int : ∀ i, IntervalIntegrable (fun x => deriv (fun t => c t x i) t)
      MeasureTheory.volume a b)
    (hx_int : ∀ i, IntervalIntegrable (fun x => deriv (fun x => J t x i) x)
      MeasureTheory.volume a b)
    (hx_deriv : ∀ i, ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => J t x i) (deriv (fun x => J t x i) x) x)
    (hswap : ∀ i, HasDerivAt (fun t => ∫ x in a..b, c t x i)
      (∫ x in a..b, deriv (fun t => c t x i) t) t)
    (hc_all : ∀ t' i, IntervalIntegrable (fun x => c t' x i)
      MeasureTheory.volume a b) :
    HasDerivAt (fun t => ∫ x in a..b, ∑ i, l i * c t x i)
      (-((∑ i, l i * J t b i) - ∑ i, l i * J t a i)) t := by
  have ht_wint : ∀ i, IntervalIntegrable (fun x => l i * deriv (fun t => c t x i) t)
      MeasureTheory.volume a b :=
    fun i => (ht_int i).const_mul (l i)
  have hfun_eq : ∀ t', (∫ x in a..b, ∑ i, l i * c t' x i)
      = ∑ i, l i * (∫ x in a..b, c t' x i) := by
    intro t'
    have hcw : ∀ i, IntervalIntegrable (fun x => l i * c t' x i)
        MeasureTheory.volume a b :=
      fun i => (hc_all t' i).const_mul (l i)
    rw [intervalIntegral.integral_finsetSum (fun i _ => hcw i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
  have hderiv_each : ∀ i, HasDerivAt (fun t' => l i * (∫ x in a..b, c t' x i))
      (l i * (∫ x in a..b, deriv (fun t => c t x i) t)) t :=
    fun i => (hswap i).const_mul (l i)
  have hderiv_sum : HasDerivAt (fun t' => ∑ i, l i * (∫ x in a..b, c t' x i))
      (∑ i, l i * (∫ x in a..b, deriv (fun t => c t x i) t)) t := by
    have h : HasDerivAt (∑ i ∈ Finset.univ, fun t' => l i * (∫ x in a..b, c t' x i))
        (∑ i ∈ Finset.univ, l i * (∫ x in a..b, deriv (fun t => c t x i) t)) t :=
      HasDerivAt.sum (fun i _ => hderiv_each i)
    have heq_fun : (∑ i : Fin n, fun t' => l i * (∫ x in a..b, c t' x i))
        = (fun t' => ∑ i, l i * (∫ x in a..b, c t' x i)) := by
      funext t'
      simp only [Finset.sum_apply]
    rw [heq_fun] at h
    exact h
  have hderiv_val : (∑ i, l i * (∫ x in a..b, deriv (fun t => c t x i) t))
      = (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => ht_wint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
  have hint_eq : (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t)
      = -((∑ i, l i * J t b i) - ∑ i, l i * J t a i) :=
    multispecies_integrated n m c J S r l a b t hpde hcons ht_int hx_int hx_deriv
  have hfun_total : (fun t' => ∫ x in a..b, ∑ i, l i * c t' x i)
      = (fun t' => ∑ i, l i * (∫ x in a..b, c t' x i)) := funext hfun_eq
  rw [hderiv_val, hint_eq] at hderiv_sum
  rw [hfun_total]
  exact hderiv_sum

end EarthScience
