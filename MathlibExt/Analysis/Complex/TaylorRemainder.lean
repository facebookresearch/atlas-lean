/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Taylor expansion with a holomorphic remainder

If `f` is complex differentiable on a neighbourhood `U` of `a` (not necessarily open), then for
every `n` it can be written as `f s = ∑_{j < n} b j (s - a) ^ j + (s - a) ^ n g s` on `U`, with
`g` complex differentiable on `U`. The remainder comes from iterating `dslope`.

## Main statements

* `DifferentiableOn.exists_eq_sum_add_pow_mul`: the expansion above.
* `DifferentiableOn.eq_sum_iteratedDeriv_add_pow_mul`: the same, with the coefficients identified
  as the Taylor coefficients `b j = f^{(j)}(a) / j!`.
-/

@[expose] public section

/-- **Taylor expansion with a holomorphic remainder.** If `f` is complex differentiable on a
neighbourhood `U` of `a`, then for every `n` there are coefficients `b 0, …, b (n - 1)` and a
function `g` complex differentiable on `U` with
`f s = ∑_{j < n} b j * (s - a) ^ j + (s - a) ^ n * g s` for all `s ∈ U`. -/
theorem DifferentiableOn.exists_eq_sum_add_pow_mul {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : U ∈ nhds a) (n : ℕ) :
    ∃ b : ℕ → ℂ, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, f s = (∑ j ∈ Finset.range n, b j * (s - a) ^ j) + (s - a) ^ n * g s := by
  induction n with
  | zero => exact ⟨fun _ => 0, f, hf, fun s _ => by simp⟩
  | succ n ih =>
    obtain ⟨b, g, hg, hfg⟩ := ih
    refine ⟨Function.update b n (g a), dslope g a,
      (Complex.differentiableOn_dslope hU).mpr hg, fun s hs => ?_⟩
    have h : (s - a) * dslope g a s = g s - g a := by
      simpa using sub_smul_dslope g a s
    have hsum : ∑ j ∈ Finset.range (n + 1), (Function.update b n (g a)) j * (s - a) ^ j
        = (∑ j ∈ Finset.range n, b j * (s - a) ^ j) + g a * (s - a) ^ n := by
      rw [Finset.sum_range_succ, Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_range.mp hj).ne]
    rw [hsum, hfg s hs]
    linear_combination (-((s - a) ^ n)) * h

open Nat in
/-- **Taylor expansion with a holomorphic remainder**, with explicit coefficients. If `f` is complex
differentiable on a neighbourhood `U` of `a`, then for every `n` there is a function `g` complex
differentiable on `U` with `f s = ∑_{j < n} f^{(j)}(a) / j! * (s - a) ^ j + (s - a) ^ n * g s` for
all `s`. -/
theorem DifferentiableOn.eq_sum_iteratedDeriv_add_pow_mul {U : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : U ∈ nhds a) (n : ℕ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ s : ℂ,
      f s = (∑ j ∈ Finset.range n, iteratedDeriv j f a / (j ! : ℂ) * (s - a) ^ j)
        + (s - a) ^ n * g s := by
  obtain ⟨p, r, hp⟩ := (hf.analyticAt hU)
  set g : ℕ → ℂ → ℂ := fun j => (Function.swap dslope a)^[j] f with hg
  have hcoeff : ∀ j, g j a = iteratedDeriv j f a / (j ! : ℂ) := by
    intro j
    have h1 := (hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1
    have h2 := hp.factorial_smul 1 j
    rw [← iteratedDeriv_eq_iteratedFDeriv] at h2
    have h3 : (FormalMultilinearSeries.fslope^[j] p) 0 1 = p.coeff j := by
      rw [← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
        zero_add]
    rw [h3] at h1
    change (Function.swap dslope a)^[j] f a = _
    rw [← h1, ← h2, nsmul_eq_mul]
    have : (j ! : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
    rfl
  have hdiff : ∀ j, DifferentiableOn ℂ (g j) U := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      simp only [hg, Function.iterate_succ_apply'] at ih ⊢
      exact (Complex.differentiableOn_dslope hU).mpr ih
  have hrec : ∀ j s, g j s = g j a + (s - a) * g (j + 1) s := by
    intro j s
    have h : (s - a) * dslope (g j) a s = g j s - g j a := by
      simpa using sub_smul_dslope (g j) a s
    simp only [hg, Function.iterate_succ_apply'] at h ⊢
    linear_combination -h
  refine ⟨g n, hdiff n, fun s => ?_⟩
  induction n with
  | zero => simp [hg]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, hrec n s, hcoeff n]
    ring
