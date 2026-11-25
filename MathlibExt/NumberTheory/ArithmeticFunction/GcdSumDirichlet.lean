/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

@[expose] public section

namespace MetaMathlibExt

/-! # Dirichlet series of the gcd-sum
-/

private def phiRaw : ℕ → ℂ := fun n => (Nat.totient n : ℂ)

private def idRaw : ℕ → ℂ := fun n => (n : ℂ)

private def gcdRaw : ℕ → ℂ :=
  fun n => ∑ i ∈ Finset.range n, (Nat.gcd n (i + 1) : ℂ)

private lemma phiRaw_apply (n : ℕ) : phiRaw n = (Nat.totient n : ℂ) := rfl

private lemma idRaw_apply (n : ℕ) : idRaw n = (n : ℂ) := rfl

private lemma gcdRaw_apply (n : ℕ) :
    gcdRaw n = ∑ i ∈ Finset.range n, (Nat.gcd n (i + 1) : ℂ) := rfl

private lemma gcdRaw_zero : gcdRaw 0 = 0 := by simp [gcdRaw]

private lemma idRaw_summable (s : ℂ) (hs : 2 < s.re) : LSeriesSummable idRaw s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hs
  refine ⟨1, fun n hn => ?_⟩
  have h2 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [idRaw_apply, Complex.norm_natCast, h2, Real.rpow_one, one_mul]

private lemma phiRaw_summable (s : ℂ) (hs : 2 < s.re) : LSeriesSummable phiRaw s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hs
  refine ⟨1, fun n hn => ?_⟩
  have h2 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [phiRaw_apply, Complex.norm_natCast, h2, Real.rpow_one, one_mul]
  exact_mod_cast Nat.totient_le n

private lemma L_idRaw (s : ℂ) (hs : 2 < s.re) :
    LSeries idRaw s = riemannZeta (s - 1) := by
  have hs1 : 1 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  rw [← LSeries_one_eq_riemannZeta hs1]
  unfold LSeries
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, idRaw_apply]
    simp only [Pi.one_apply]
    have hx : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    have hcs : ((n : ℕ) : ℂ) ^ s
        = ((n : ℕ) : ℂ) ^ (s - 1) * ((n : ℕ) : ℂ) := by
      have h : s = (s - 1) + 1 := by ring
      conv_lhs => rw [h]
      rw [Complex.cpow_add _ _ hx, Complex.cpow_one]
    rw [hcs, div_eq_mul_inv, one_div, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel₀ hx, one_mul]

private lemma conv_one_phi :
    LSeries.convolution 1 phiRaw = idRaw := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.convolution_map_zero]
    simp [idRaw]
  · have h2 : n.divisors.sum (fun i => Nat.totient (n / i)) = n := by
      rw [Nat.sum_div_divisors n Nat.totient]
      exact Nat.sum_totient n
    have hcast : (∑ i ∈ n.divisors, phiRaw (n / i)) = ((n : ℕ) : ℂ) := by
      have e : (∑ i ∈ n.divisors, phiRaw (n / i))
          = ((((n.divisors.sum (fun i => Nat.totient (n / i))) : ℕ)) : ℂ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro d _
        exact phiRaw_apply _
      rw [e, h2]
    have e1 : LSeries.convolution (1 : ℕ → ℂ) phiRaw n
        = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * phiRaw p.2 := by
      rw [LSeries.convolution_def]
    have e2 : (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * phiRaw p.2)
        = ∑ d ∈ n.divisors, phiRaw (n / d) := by
      have h := Nat.sum_divisorsAntidiagonal
        (fun a b : ℕ => (1 : ℕ → ℂ) a * phiRaw b) (n := n)
      simpa using h
    rw [e1, e2, hcast]
    exact (idRaw_apply n).symm

private lemma gcdRaw_eq_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    gcdRaw n = ∑ d ∈ n.divisors, (d : ℂ) * phiRaw (n / d) := by
  have htot : ∀ k ∈ Finset.range n,
      ((Nat.gcd n (k + 1) : ℕ) : ℂ)
        = ∑ d ∈ (Nat.gcd n (k + 1)).divisors, phiRaw d := by
    intro k _
    have h := Nat.sum_totient (Nat.gcd n (k + 1))
    have e : (∑ d ∈ (Nat.gcd n (k + 1)).divisors, phiRaw d)
        = ((((Nat.gcd n (k + 1)).divisors.sum Nat.totient : ℕ)) : ℂ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact phiRaw_apply _
    rw [e, h]
  have hfilter : ∀ k ∈ Finset.range n,
      (Nat.gcd n (k + 1)).divisors
        = n.divisors.filter (fun d => d ∣ k + 1) := by
    intro k _
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨hdvd, -⟩ := h
      rw [Nat.dvd_gcd_iff] at hdvd
      exact ⟨⟨hdvd.1, hn⟩, hdvd.2⟩
    · intro h
      obtain ⟨⟨hdvd_n, -⟩, hdvd_k⟩ := h
      exact ⟨Nat.dvd_gcd_iff.mpr ⟨hdvd_n, hdvd_k⟩, Nat.gcd_ne_zero_left hn⟩
  calc gcdRaw n
      = ∑ k ∈ Finset.range n,
          ∑ d ∈ n.divisors.filter (fun d => d ∣ k + 1), phiRaw d := by
        rw [gcdRaw_apply]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hfilter k hk]
        exact htot k hk
    _ = ∑ d ∈ n.divisors,
          ∑ k ∈ (Finset.range n).filter (fun k => d ∣ k + 1), phiRaw d := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
    _ = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℂ) * phiRaw d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_const, Nat.card_multiples, nsmul_eq_mul]
    _ = ∑ d ∈ n.divisors, ((d : ℕ) : ℂ) * phiRaw (n / d) := by
        have hdiv : ∀ d ∈ n.divisors, n / (n / d) = d :=
          fun d hd => Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn
        calc (∑ d ∈ n.divisors, ((n / d : ℕ) : ℂ) * phiRaw d)
            = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℂ) * phiRaw (n / (n / d)) := by
              apply Finset.sum_congr rfl
              intro d hd
              rw [hdiv d hd]
          _ = ∑ d ∈ n.divisors, ((d : ℕ) : ℂ) * phiRaw (n / d) := by
              have hF := Nat.sum_div_divisors n
                (fun e => ((e : ℕ) : ℂ) * phiRaw (n / e))
              have e1 : (∑ d ∈ n.divisors, ((n / d : ℕ) : ℂ) * phiRaw (n / (n / d)))
                  = (∑ d ∈ n.divisors,
                    (fun e => ((e : ℕ) : ℂ) * phiRaw (n / e)) (n / d)) :=
                rfl
              have e2 : n.divisors.sum (fun e => ((e : ℕ) : ℂ) * phiRaw (n / e))
                  = (∑ d ∈ n.divisors, ((d : ℕ) : ℂ) * phiRaw (n / d)) :=
                rfl
              rw [e1, hF, e2]

private lemma conv_id_phi : LSeries.convolution idRaw phiRaw = gcdRaw := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.convolution_map_zero]
    exact gcdRaw_zero.symm
  · have e1 : LSeries.convolution idRaw phiRaw n
        = ∑ p ∈ n.divisorsAntidiagonal, idRaw p.1 * phiRaw p.2 := by
      rw [LSeries.convolution_def]
    have e2 : (∑ p ∈ n.divisorsAntidiagonal, idRaw p.1 * phiRaw p.2)
        = ∑ d ∈ n.divisors, idRaw d * phiRaw (n / d) :=
      Nat.sum_divisorsAntidiagonal (fun a b : ℕ => idRaw a * phiRaw b)
    rw [e1, e2, gcdRaw_eq_divisor_sum n hn]
    apply Finset.sum_congr rfl
    intro d _
    rw [idRaw_apply]

/--
**Dirichlet series of the gcd-sum function.** For $n \ge 1$ let
$g(n) = \sum_{i=1}^{n} \gcd(n, i)$. For every complex number $s$ with $\operatorname{Re} s > 2$,
the series $\sum_{n \ge 1} g(n)/n^s$ sums to $\zeta(s-1)^2/\zeta(s)$, where $\zeta$ is the
Riemann zeta function.

The function $g$ is the Dirichlet convolution of the identity function with Euler's totient
function $\varphi$, which gives the factorization $\zeta(s-1) \cdot (\zeta(s-1)/\zeta(s))$.

Proves `Wanted` entry `dirichlet_series_gcd_sum`.

Source: Kevin A. Broughan,
"The gcd-sum function,"
Journal of Integer Sequences 4 (2001), Article 01.2.2,
Theorem (unlabeled), equations (labels 12, 8), lines 336–349,
https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex
-/
theorem dirichlet_series_gcd_sum
    (s : ℂ) (hs : 2 < s.re) :
    (∑' n : ℕ, ((∑ i ∈ Finset.range (n + 1), (Nat.gcd (n + 1) (i + 1) : ℂ))
      / (((n + 1 : ℕ) : ℂ)) ^ s))
      = riemannZeta (s - 1) ^ 2 / riemannZeta s := by
  have hs1 : 1 < s.re := by linarith
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs1
  have hsumId : LSeriesSummable idRaw s := idRaw_summable s hs
  have hsumPhi : LSeriesSummable phiRaw s := phiRaw_summable s hs
  have hz : LSeries (1 : ℕ → ℂ) s = riemannZeta s :=
    LSeries_one_eq_riemannZeta hs1
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hLid : LSeries idRaw s = riemannZeta (s - 1) := L_idRaw s hs
  have hprod1 : LSeries idRaw s = LSeries 1 s * LSeries phiRaw s := by
    rw [← conv_one_phi]
    exact LSeries_convolution' hsum1 hsumPhi
  have hLphi : LSeries phiRaw s = riemannZeta (s - 1) / riemannZeta s := by
    have h : LSeries phiRaw s * riemannZeta s = riemannZeta (s - 1) := by
      rw [← hz, ← hLid, hprod1]
      exact mul_comm _ _
    rwa [eq_div_iff_mul_eq hzne]
  have hsumGcd : LSeriesSummable gcdRaw s := by
    have h := hsumId.convolution hsumPhi
    rwa [conv_id_phi] at h
  have hprodG : LSeries gcdRaw s = LSeries idRaw s * LSeries phiRaw s := by
    rw [← conv_id_phi]
    exact LSeries_convolution' hsumId hsumPhi
  have hL : (∑' n : ℕ, ((∑ i ∈ Finset.range (n + 1), (Nat.gcd (n + 1) (i + 1) : ℂ))
      / (((n + 1 : ℕ) : ℂ)) ^ s)) = LSeries gcdRaw s := by
    have hterm : ∀ n : ℕ, ((∑ i ∈ Finset.range (n + 1), (Nat.gcd (n + 1) (i + 1) : ℂ))
        / (((n + 1 : ℕ) : ℂ)) ^ s) = LSeries.term gcdRaw s (n + 1) := by
      intro n
      rw [LSeries.term_of_ne_zero (by omega : n + 1 ≠ 0), gcdRaw_apply]
    have htsum : (∑' n, LSeries.term gcdRaw s n)
        = LSeries.term gcdRaw s 0 + ∑' n, LSeries.term gcdRaw s (n + 1) :=
      Summable.tsum_eq_zero_add hsumGcd
    rw [LSeries.term_zero] at htsum
    change _ = ∑' n, LSeries.term gcdRaw s n
    rw [htsum, zero_add]
    exact tsum_congr hterm
  rw [hL, hprodG, hLid, hLphi]
  ring

end MetaMathlibExt
