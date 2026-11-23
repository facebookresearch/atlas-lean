/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Zeros of real exponential sums

An exponential sum `f(a) = ∑_{u ∈ S} c_u exp(-a u)` over a finite set `S` of distinct real
rates that vanishes at `|S|` distinct real points has all coefficients zero; equivalently, the
generalized Vandermonde matrix `(exp(-a u))_{a ∈ P, u ∈ S}` has full column rank when
`|P| ≥ |S|`. This is the zero-counting half of Descartes' rule of signs for exponential sums
(an exponential sum with `r` terms has at most `r - 1` real zeros); Mathlib's
`Polynomial.RuleOfSigns` covers only integer exponents. The proof is the classical induction
with Rolle's theorem: multiply by `exp(a u₀)` and differentiate to remove one term.

## Main results

* `Real.eq_zero_of_sum_mul_exp_eq_zero`: the coefficients of an exponential sum vanishing at
  `|S|` distinct points are zero.

## References

* G. Pólya and G. Szegő, *Problems and Theorems in Analysis II*, Springer (1976), Part Five,
  Chapter 1 (Rolle's theorem and Descartes' rule of signs).
* G. J. O. Jameson, *Counting zeros of generalised polynomials: Descartes' rule of signs and
  Laguerre's extensions*, Math. Gazette 90 (2006), 223–234.
* A. Bhaskar and Y. S. Song, *Descartes' rule of signs and the identifiability of population
  demographic models from genomic variation data*, Ann. Statist. 42 (2014), 2469–2493.
-/

@[expose] public section

open Finset

namespace Real

/-- Rolle's theorem on a finite zero set: if a differentiable `f` vanishes on `P`, its
derivative vanishes on a set with at least `|P| - 1` points. -/
private lemma exists_deriv_zero_finset {f : ℝ → ℝ} (hf : Differentiable ℝ f) (P : Finset ℝ)
    (hP : ∀ a ∈ P, f a = 0) :
    ∃ Q : Finset ℝ, P.card ≤ Q.card + 1 ∧ ∀ q ∈ Q, deriv f q = 0 := by
  suffices H : ∀ P : Finset ℝ, (∀ a ∈ P, f a = 0) →
      ∃ Q : Finset ℝ, P.card ≤ Q.card + 1 ∧ ∀ q ∈ Q, deriv f q = 0 ∧ ∃ x ∈ P, q < x by
    obtain ⟨Q, hQ, hQ'⟩ := H P hP
    exact ⟨Q, hQ, fun q hq => (hQ' q hq).1⟩
  intro P
  induction P using Finset.induction_on_max with
  | empty => intro _; exact ⟨∅, by simp, by simp⟩
  | insert a P' hlt ih =>
    intro hz
    obtain ⟨Q', hQ'c, hQ'⟩ := ih fun x hx => hz x (mem_insert_of_mem hx)
    have ha : a ∉ P' := fun h => lt_irrefl a (hlt a h)
    rcases P'.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp⟩
    · set b := P'.max' hne
      have hb : b < a := hlt b (P'.max'_mem hne)
      obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero hb hf.continuous.continuousOn
        (by rw [hz b (mem_insert_of_mem (P'.max'_mem hne)), hz a (mem_insert_self a P')])
      have hξQ : ξ ∉ Q' := by
        intro h
        obtain ⟨_, x, hx, hqx⟩ := hQ' ξ h
        exact absurd (hqx.trans_le (P'.le_max' x hx)) (not_lt.2 hξ.1.le)
      refine ⟨insert ξ Q', ?_, ?_⟩
      · rw [card_insert_of_notMem ha, card_insert_of_notMem hξQ]; omega
      · intro q hq
        rcases mem_insert.1 hq with rfl | hq
        · exact ⟨hξ0, a, mem_insert_self a P', hξ.2⟩
        · obtain ⟨h0, x, hx, hqx⟩ := hQ' q hq
          exact ⟨h0, x, mem_insert_of_mem hx, hqx⟩

/-- The derivative of an exponential sum. -/
private lemma hasDerivAt_expSum (S : Finset ℝ) (c r : ℝ → ℝ) (a : ℝ) :
    HasDerivAt (fun x => ∑ u ∈ S, c u * Real.exp (-(x * r u)))
      (∑ u ∈ S, -(c u * r u) * Real.exp (-(a * r u))) a := by
  have h : ∀ u ∈ S, HasDerivAt (fun x => c u * Real.exp (-(x * r u)))
      (-(c u * r u) * Real.exp (-(a * r u))) a := by
    intro u _
    have h1 : HasDerivAt (fun x => -(x * r u)) (-r u) a := by
      have := ((hasDerivAt_id a).mul_const (r u)).fun_neg
      simpa using this
    convert (h1.exp).const_mul (c u) using 1
    ring
  exact HasDerivAt.fun_sum h

/-- **Exponential sums have full column rank.** If `∑_{u ∈ S} c_u exp(-a u)` vanishes at
`|S|` distinct points `a ∈ P` (the rates `u ∈ S` are distinct as elements of a `Finset`), every
coefficient is zero. Equivalently, the matrix `(exp(-a u))_{a ∈ P, u ∈ S}` has full column
rank when `|P| ≥ |S|`. -/
theorem eq_zero_of_sum_mul_exp_eq_zero {S P : Finset ℝ} (hSP : S.card ≤ P.card) (c : ℝ → ℝ)
    (h : ∀ a ∈ P, ∑ u ∈ S, c u * Real.exp (-(a * u)) = 0) :
    ∀ u ∈ S, c u = 0 := by
  induction hr : S.card generalizing S P c with
  | zero => intro u hu; simp_all
  | succ r ih =>
    have hS : S.Nonempty := card_pos.1 (by omega)
    set u₀ := S.min' hS
    have hu₀ : u₀ ∈ S := S.min'_mem hS
    -- shift the rates by `u₀`; the shifted sum also vanishes on `P`
    set S' := (S.erase u₀).image (· - u₀)
    have hinj : Set.InjOn (· - u₀) (S.erase u₀ : Set ℝ) := fun x _ y _ hxy => by
      simpa using hxy
    have hS'card : S'.card = r := by
      rw [card_image_of_injOn hinj, card_erase_of_mem hu₀, hr]; rfl
    set g : ℝ → ℝ := fun x => ∑ u ∈ S, c u * Real.exp (-(x * (u - u₀)))
    have hg : ∀ x, g x = Real.exp (x * u₀) * ∑ u ∈ S, c u * Real.exp (-(x * u)) := by
      intro x
      simp only [g, mul_sum]
      refine sum_congr rfl fun u _ => ?_
      rw [mul_left_comm, ← Real.exp_add]
      ring_nf
    have hgd : ∀ x, HasDerivAt g (∑ v ∈ S', -(c (v + u₀) * v) * Real.exp (-(x * v))) x := by
      intro x
      have := hasDerivAt_expSum S c (· - u₀) x
      convert this using 1
      rw [← add_sum_erase S _ hu₀, sub_self, mul_zero, neg_zero, zero_mul, zero_add,
        sum_image fun x hx y hy hxy => hinj hx hy hxy]
      simp only [sub_add_cancel]
    obtain ⟨Q, hQc, hQ⟩ := exists_deriv_zero_finset (f := g)
      (fun x => (hgd x).differentiableAt) P (fun a ha => by rw [hg, h a ha, mul_zero])
    have hc' := ih (S := S') (P := Q) (c := fun v => -(c (v + u₀) * v)) (by omega)
      (fun q hq => by rw [← (hgd q).deriv]; exact hQ q hq) hS'card
    have hrest : ∀ u ∈ S.erase u₀, c u = 0 := by
      intro u hu
      have := hc' (u - u₀) (mem_image_of_mem _ hu)
      have hne : u - u₀ ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hu)
      simp only [sub_add_cancel, neg_eq_zero, mul_eq_zero, hne, or_false] at this
      exact this
    obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by omega)
    have h0 := h a ha
    rw [← add_sum_erase S _ hu₀, sum_eq_zero fun u hu => by rw [hrest u hu, zero_mul],
      add_zero] at h0
    have hc0 : c u₀ = 0 := (mul_eq_zero.1 h0).resolve_right (Real.exp_ne_zero _)
    intro u hu
    by_cases hu' : u = u₀
    · rw [hu']; exact hc0
    · exact hrest u (mem_erase.2 ⟨hu', hu⟩)

end Real
