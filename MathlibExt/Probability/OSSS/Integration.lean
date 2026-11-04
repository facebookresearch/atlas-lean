/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.OrderClosed

/-!
# Integrating the Duminil-Copin–Raoufi–Tassion differential inequality: the mean-field side

Real-analysis lemmas for the "mean-field" half of the Duminil-Copin–Raoufi–Tassion argument.
For functions `f_i(β)` with partial sums `Σ_n = f_0 + ⋯ + f_{n-1}`, the differential inequality
`f_i' ≥ (i / Σ_i) f_i` gives, after dividing by `i` and telescoping the logarithms,
`(1 / log n) ∑_{i=1}^{n} f_i' / i ≥ (log Σ_{n+1} - log Σ_1) / log n`.
Integrating in `β` and passing to the limit gives a linear lower bound on the limit function.
Everything here is about real functions; no probability is involved.

## Main definitions

* `StatMech.OSSS.Integration.meanLogTerm`: `T_n(β) = (1 / log n) ∑_{i=1}^{n} f_i(β) / i`.

## Main results

* `StatMech.OSSS.Integration.slope_ge_of_deriv_ge`: `T' ≥ m` on `[a, b]` gives
  `T b - T a ≥ m (b - a)`.
* `StatMech.OSSS.Integration.logStep_sum_le_sum_deriv`: the telescoped logarithmic bound.
* `StatMech.OSSS.Integration.integrated_meanField`: the bound on `T_n(β) - T_n(β')`.
* `StatMech.OSSS.Integration.meanField_lower`: in the limit, `f(β) - f(β') ≥ β - β'`.

## References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and
  Potts models via decision trees*, Ann. of Math. 189 (2019), 75–99, §3.
-/

@[expose] public section

open scoped BigOperators
open Real Set Finset Filter Topology

namespace StatMech
namespace OSSS.Integration

/-- If `T` has derivative `T' ≥ m` on `[a, b]`, then `m (b - a) ≤ T b - T a`.

See also `Convex.mul_sub_le_image_sub_of_le_deriv` (Mathlib), the same bound under continuity and
differentiability on a convex set. -/
theorem slope_ge_of_deriv_ge (a b m : ℝ) (hab : a ≤ b) (T T' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt T (T' x) x)
    (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
    m * (b - a) ≤ T b - T a := by
  set h : ℝ → ℝ := fun x => T x - m * x with hh
  have hhderiv : ∀ x ∈ Icc a b, HasDerivAt h (T' x - m) x := by
    intro x hx
    have h2 : HasDerivAt (fun x : ℝ => m * x) m x := by
      simpa using (hasDerivAt_id x).const_mul m
    exact (hd x hx).sub h2
  have hmono : MonotoneOn h (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hhderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hhderiv x (mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hhderiv x (mem_Icc_of_Ioo hx)).deriv]
      have hmle : m ≤ T' x := hbound x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      linarith
  have hkey : h a ≤ h b := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  rw [hh] at hkey
  simp only [] at hkey
  nlinarith [hkey]

/-- `log (S + f) - log S ≤ f / S` for `S > 0`, `f ≥ 0`. -/
theorem logStep_le (S f : ℝ) (hS : 0 < S) (hf : 0 ≤ f) :
    Real.log (S + f) - Real.log S ≤ f / S := by
  have hSf : 0 < S + f := by linarith
  rw [← Real.log_div (ne_of_gt hSf) (ne_of_gt hS)]
  have h1 : Real.log ((S + f) / S) ≤ (S + f) / S - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (S + f) / S - 1 = f / S := by field_simp; ring
  linarith

/-- Telescoping: if `Σ_{i+1} = Σ_i + f_i`, `f_i ≥ 0`, `Σ_i > 0` and `(i / Σ_i) f_i ≤ f'_i` for `i ≥
1`, then `log Σ_{n+1} - log Σ_1 ≤ ∑_{i=1}^{n} f'_i / i`. -/
theorem logStep_sum_le_sum_deriv (fseq fpseq Sig : ℕ → ℝ) (n : ℕ)
    (hSrec : ∀ i, Sig (i + 1) = Sig i + fseq i)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i) * fseq i ≤ fpseq i) :
    Real.log (Sig (n + 1)) - Real.log (Sig 1)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i / (i : ℝ) := by
  have hstep : ∀ i ∈ Finset.Ico 1 (n + 1),
      (Real.log (Sig (i + 1)) - Real.log (Sig i)) ≤ fpseq i / (i : ℝ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : 1 ≤ i := hi.1
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hSi : 0 < Sig i := hSpos i hi1
    have hfi : 0 ≤ fseq i := hfnn i hi1
    have hlog : Real.log (Sig (i + 1)) - Real.log (Sig i) ≤ fseq i / Sig i := by
      rw [hSrec i]; exact logStep_le (Sig i) (fseq i) hSi hfi
    have hdi : fseq i / Sig i ≤ fpseq i / (i : ℝ) := by
      have hd := hdiff i hi1
      rw [div_mul_eq_mul_div, div_le_iff₀ hSi] at hd
      rw [div_le_div_iff₀ hSi hipos]
      nlinarith [hd]
    linarith
  refine le_trans ?_ (Finset.sum_le_sum hstep)
  have htel : ∑ i ∈ Finset.Ico 1 (n + 1), (Real.log (Sig (i + 1)) - Real.log (Sig i))
      = Real.log (Sig (n + 1)) - Real.log (Sig 1) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    have hcongr : ∀ x ∈ Finset.range n,
        (Real.log (Sig (1 + x + 1)) - Real.log (Sig (1 + x)))
          = (fun j => Real.log (Sig (j + 1 + 1)) - Real.log (Sig (j + 1))) x := by
      intro x _; ring_nf
    rw [Finset.sum_congr rfl hcongr]
    simpa using Finset.sum_range_sub (fun j => Real.log (Sig (j + 1))) n
  rw [htel]

/-- The averaged function `T_n(x) = (1 / log n) ∑_{i=1}^{n} f_i(x) / i`. -/
noncomputable def meanLogTerm (fseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fseq i x / (i : ℝ)

/-- Derivative of `meanLogTerm`. -/
theorem hasDerivAt_meanLogTerm (fseq fpseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ∀ i, HasDerivAt (fun x => fseq i x) (fpseq i x) x) :
    HasDerivAt (fun x => meanLogTerm fseq n x)
      ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ)) x := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (hf i).div_const (i : ℝ)

/-- The differential inequality bounds the derivative of `meanLogTerm` below by `(log Σ_{n+1} - log
Σ_1) / log n`. -/
theorem deriv_meanLogTerm_lower (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (x : ℝ) (hlogn : 0 < Real.log n)
    (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
    (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n
      ≤ (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ) := by
  have hnum := logStep_sum_le_sum_deriv (fun i => fseq i x) (fun i => fpseq i x)
    (fun i => Sig i x) n hSrec hfnn hSpos hdiff
  rw [div_eq_inv_mul, one_div]
  exact mul_le_mul_of_nonneg_left hnum (by positivity)

/-- Integrated form: if `(log Σ_{n+1} - log Σ_1) / log n ≥ m` on `[β', β]`, then `T_n(β) - T_n(β') ≥
(β - β') m`. -/
theorem integrated_meanField (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (β' β m : ℝ) (hββ : β' ≤ β) (hlogn : 0 < Real.log n)
    (hf : ∀ i x, x ∈ Icc β' β → HasDerivAt (fun x => fseq i x) (fpseq i x) x)
    (hSrec : ∀ i x, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 ≤ fseq i x)
    (hSpos : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, ∀ x, 1 ≤ i → x ∈ Icc β' β → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x)
    (hm : ∀ x ∈ Icc β' β, m ≤ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n) :
    (β - β') * m ≤ meanLogTerm fseq n β - meanLogTerm fseq n β' := by
  rw [mul_comm]
  apply slope_ge_of_deriv_ge β' β m hββ
    (fun x => meanLogTerm fseq n x)
    (fun x => (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ))
  · intro x hx
    exact hasDerivAt_meanLogTerm fseq fpseq n x (fun i => hf i x hx)
  · intro x hx
    refine le_trans (hm x hx) ?_
    exact deriv_meanLogTerm_lower fseq fpseq Sig n x hlogn
      (fun i => hSrec i x) (fun i hi => hfnn i x hi hx)
      (fun i hi => hSpos i x hi hx) (fun i hi => hdiff i x hi hx)

/-- Passing to the limit `n → ∞` in `(β - β') m_n ≤ T_n(β) - T_n(β')`. -/
theorem meanField_limit (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hm : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    (β - β') * m ≤ fβ - fβ' := by
  have hlhs : Tendsto (fun n => (β - β') * mseq n) atTop (𝓝 ((β - β') * m)) :=
    hm.const_mul (β - β')
  have hrhs : Tendsto (fun n => T n β - T n β') atTop (𝓝 (fβ - fβ')) := hTβ.sub hTβ'
  exact le_of_tendsto_of_tendsto hlhs hrhs hbound

/-- Mean-field lower bound in the limit: if `m_n → m ≥ 1` and the integrated bound holds eventually,
then `β - β' ≤ f(β) - f(β')`. -/
theorem meanField_lower (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' := by
  have hmain := meanField_limit T mseq β' β fβ fβ' m hTβ hTβ' hmlim hbound
  have hβsub : 0 ≤ β - β' := by linarith
  calc β - β' = (β - β') * 1 := by ring
    _ ≤ (β - β') * m := mul_le_mul_of_nonneg_left hm1 hβsub
    _ ≤ fβ - fβ' := hmain

end OSSS.Integration
end StatMech
