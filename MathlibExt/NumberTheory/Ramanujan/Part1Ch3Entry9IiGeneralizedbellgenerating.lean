/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 9(ii)

Generalized Bell EGF sums to x·e^((a+b)y)·e^(x(e^(by)-1)).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9IiGeneralizedbellgenerating

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

/-- Exponential series for `Complex.exp`, via `NormedSpace.expSeries_hasSum_exp`. -/
private theorem hasSum_complex_pow_div_factorial (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (𝔸 := ℂ) z
  rw [← Complex.exp_eq_exp_ℂ] at h
  have heq : (fun n : ℕ => (NormedSpace.expSeries ℂ ℂ n) fun _ => z)
      = (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) := by
    funext n
    rw [NormedSpace.expSeries_apply_eq]
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rwa [heq] at h

/-- Exponential series for `Real.exp`, via `NormedSpace.expSeries_hasSum_exp`. -/
private theorem hasSum_real_pow_div_factorial (t : ℝ) :
    HasSum (fun n : ℕ => t ^ n / (Nat.factorial n : ℝ)) (Real.exp t) := by
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (𝔸 := ℝ) t
  rw [← Real.exp_eq_exp_ℝ] at h
  have heq : (fun n : ℕ => (NormedSpace.expSeries ℝ ℝ n) fun _ => t)
      = (fun n : ℕ => t ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    rw [NormedSpace.expSeries_apply_eq]
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rwa [heq] at h

/-- Double-series term: the `n`-th summand of the goal, with the `k`-sum pushed inside. -/
private noncomputable def auxTerm (y a b x : ℂ) (n k : ℕ) : ℂ :=
  y ^ n / (Nat.factorial n : ℂ) *
    ((a + b * ((k : ℂ) + 1)) ^ n * x ^ (k + 1) / (Nat.factorial k : ℂ))

/-- Nonnegative majorant for `auxTerm`, used to justify swapping the sums. -/
private noncomputable def auxMajor (y a b x : ℂ) (n k : ℕ) : ℝ :=
  ‖y‖ ^ n / (Nat.factorial n : ℝ) *
    ((‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ)) ^ n * ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ))

/-- **Exponential generating function of the generalized Bell function (Entry 9(ii)).** Let
$F(a, b, x; n)$ be Ramanujan's generalized Bell function. For all complex numbers $a$, $b$, $x$
and $y$, the series $\sum_{n=0}^{\infty} \frac{y^n}{n!} F(a, b, x; n)$ converges to
$x e^{(a+b)y} e^{x(e^{by} - 1)}$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (9.1) printed p.
    53/PDF p. 63 and Entry 9(ii), formula (9.4), printed p. 54/PDF p. 64.
Proves `Wanted` entry `ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating`. The source's
`F(a, b, x; n)` is `generalizedBellGenerating a b x n`.
-/
theorem ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating (a b x y : ℂ) :
    HasSum (fun n : ℕ => y ^ n / (Nat.factorial n : ℂ) * generalizedBellGenerating a b x n)
        (x * Complex.exp ((a + b) * y) * Complex.exp (x * (Complex.exp (b * y) - 1))) := by
  have hM_row : ∀ k : ℕ, Summable (fun n : ℕ => auxMajor y a b x n k) := by
    intro k
    have hD := Real.summable_pow_div_factorial (‖y‖ * (‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ)))
    have hC := hD.mul_left (‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ))
    refine hC.congr fun n => ?_
    rw [mul_pow]
    unfold auxMajor
    ring
  have hM_row_tsum : ∀ k : ℕ, (∑' n : ℕ, auxMajor y a b x n k)
      = ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ) *
        Real.exp (‖y‖ * (‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ))) := by
    intro k
    have h1 : (fun n : ℕ => auxMajor y a b x n k)
        = (fun n : ℕ => (‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ)) *
          ((‖y‖ * (‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ))) ^ n / (Nat.factorial n : ℝ))) := by
      funext n
      rw [mul_pow]
      unfold auxMajor
      ring
    rw [h1, tsum_mul_left]
    congr 1
    exact (hasSum_real_pow_div_factorial _).tsum_eq
  have hM_rowsum : Summable (fun k : ℕ => ∑' n : ℕ, auxMajor y a b x n k) := by
    have hexp : ∀ k : ℕ, (∑' n : ℕ, auxMajor y a b x n k)
        = Real.exp (‖y‖ * ‖a‖) *
          ((‖x‖ * Real.exp (‖y‖ * ‖b‖)) ^ (k + 1) / (Nat.factorial k : ℝ)) := by
      intro k
      rw [hM_row_tsum k]
      have e1 : ‖y‖ * (‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ))
          = ‖y‖ * ‖a‖ + ((k + 1 : ℕ) : ℝ) * (‖y‖ * ‖b‖) := by ring
      rw [e1, Real.exp_add, Real.exp_nat_mul]
      ring
    have hbase := Real.summable_pow_div_factorial (‖x‖ * Real.exp (‖y‖ * ‖b‖))
    have h3 : Summable
        (fun k : ℕ => (‖x‖ * Real.exp (‖y‖ * ‖b‖)) ^ (k + 1) / (Nat.factorial k : ℝ)) := by
      have h2 : (fun k : ℕ => (‖x‖ * Real.exp (‖y‖ * ‖b‖)) ^ (k + 1) / (Nat.factorial k : ℝ))
          = (fun k : ℕ => (‖x‖ * Real.exp (‖y‖ * ‖b‖)) *
            ((‖x‖ * Real.exp (‖y‖ * ‖b‖)) ^ k / (Nat.factorial k : ℝ))) := by
        funext k
        rw [pow_succ']
        ring
      rw [h2]
      exact hbase.mul_left _
    have h4 := h3.mul_left (Real.exp (‖y‖ * ‖a‖))
    refine h4.congr fun k => ?_
    rw [hexp k]
  have hMnn : ∀ n k : ℕ, 0 ≤ auxMajor y a b x n k := by
    intro n k
    unfold auxMajor
    positivity
  have hMnonneg : 0 ≤ Function.uncurry (fun k n => auxMajor y a b x n k) := by
    intro p
    obtain ⟨k, n⟩ := p
    exact hMnn n k
  have hMswap : Summable (Function.uncurry (fun k n => auxMajor y a b x n k)) := by
    have hrows : ∀ k : ℕ,
        Summable (fun n : ℕ => Function.uncurry (fun k n => auxMajor y a b x n k) (k, n)) := by
      intro k
      have h := hM_row k
      refine h.congr fun n => ?_
      rfl
    have hsums : Summable
        (fun k : ℕ => ∑' n : ℕ, Function.uncurry (fun k n => auxMajor y a b x n k) (k, n)) := by
      have h := hM_rowsum
      refine h.congr fun k => ?_
      apply tsum_congr
      intro n
      rfl
    exact (summable_prod_of_nonneg hMnonneg).mpr ⟨hrows, hsums⟩
  have hM' : Summable (Function.uncurry (fun n k => auxMajor y a b x n k)) := by
    have heq : Function.uncurry (fun k n => auxMajor y a b x n k)
        = (Function.uncurry (fun n k => auxMajor y a b x n k)) ∘ (Equiv.prodComm ℕ ℕ) := by
      funext p
      obtain ⟨k, n⟩ := p
      rfl
    have h2 := (Equiv.prodComm ℕ ℕ).summable_iff
      (f := Function.uncurry (fun n k => auxMajor y a b x n k))
    rw [← heq] at h2
    exact h2.mp hMswap
  have hbound : ∀ n k : ℕ, ‖auxTerm y a b x n k‖ ≤ auxMajor y a b x n k := by
    intro n k
    have hkn : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by
      rw [Nat.cast_add, Nat.cast_one]
    have h1 : ‖((k : ℂ) + 1)‖ = ((k + 1 : ℕ) : ℝ) := by
      rw [hkn, norm_natCast]
    have hZ : ‖a + b * ((k : ℂ) + 1)‖ ≤ ‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ) := by
      calc ‖a + b * ((k : ℂ) + 1)‖ ≤ ‖a‖ + ‖b * ((k : ℂ) + 1)‖ := norm_add_le _ _
        _ = ‖a‖ + ‖b‖ * ‖((k : ℂ) + 1)‖ := by rw [norm_mul]
        _ = ‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ) := by rw [h1]
    have hZn : ‖a + b * ((k : ℂ) + 1)‖ ^ n ≤ (‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hZ n
    have e1 : ‖auxTerm y a b x n k‖
        = (‖y‖ ^ n / (Nat.factorial n : ℝ)) *
          (‖a + b * ((k : ℂ) + 1)‖ ^ n * (‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ))) := by
      unfold auxTerm
      simp only [norm_mul, norm_div, norm_pow, norm_natCast]
      ring
    rw [e1]
    unfold auxMajor
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZn (by positivity)) (by positivity)
  have hNn : Summable (Function.uncurry (fun n k : ℕ => ‖auxTerm y a b x n k‖)) := by
    apply Summable.of_nonneg_of_le _ _ hM'
    · intro p
      obtain ⟨n, k⟩ := p
      exact norm_nonneg _
    · intro p
      obtain ⟨n, k⟩ := p
      exact hbound n k
  have hNnonneg : 0 ≤ Function.uncurry (fun n k : ℕ => ‖auxTerm y a b x n k‖) := by
    intro p
    obtain ⟨n, k⟩ := p
    exact norm_nonneg _
  have hS : Summable (Function.uncurry (fun n k => auxTerm y a b x n k)) :=
    hM'.of_norm_bounded (fun p => by obtain ⟨n, k⟩ := p; exact hbound n k)
  have hinj_row : ∀ n : ℕ, Function.Injective (fun k : ℕ => (n, k)) := by
    intro n a b h
    simpa using congrArg Prod.snd h
  have hg_row : ∀ n : ℕ, Summable (fun k : ℕ => auxTerm y a b x n k) := by
    intro n
    have h0 := hS.comp_injective (i := fun k : ℕ => (n, k)) (hinj_row n)
    have heq : ((Function.uncurry (fun n k => auxTerm y a b x n k)) ∘ (fun k : ℕ => (n, k)))
        = (fun k : ℕ => auxTerm y a b x n k) := by
      funext k
      rfl
    rw [heq] at h0
    exact h0
  have hNn_row : ∀ n : ℕ, Summable (fun k : ℕ => ‖auxTerm y a b x n k‖) := by
    intro n
    have h0 := hNn.comp_injective (i := fun k : ℕ => (n, k)) (hinj_row n)
    have heq : ((Function.uncurry (fun n k : ℕ => ‖auxTerm y a b x n k‖)) ∘ (fun k : ℕ => (n, k)))
        = (fun k : ℕ => ‖auxTerm y a b x n k‖) := by
      funext k
      rfl
    rw [heq] at h0
    exact h0
  have hIterNorm : Summable (fun n : ℕ => ∑' k : ℕ, ‖auxTerm y a b x n k‖) := by
    have h := (summable_prod_of_nonneg hNnonneg).mp hNn
    have h2 := h.2
    have heq :
        (fun n : ℕ => ∑' k : ℕ, Function.uncurry (fun n k : ℕ => ‖auxTerm y a b x n k‖) (n, k))
        = (fun n : ℕ => ∑' k : ℕ, ‖auxTerm y a b x n k‖) := by
      funext n
      apply tsum_congr
      intro k
      rfl
    rw [heq] at h2
    exact h2
  have hIter : Summable (fun n : ℕ => ∑' k : ℕ, auxTerm y a b x n k) := by
    apply hIterNorm.of_norm_bounded
    intro n
    exact norm_tsum_le_tsum_norm (hNn_row n)
  have hHasN : HasSum (fun n : ℕ => ∑' k : ℕ, auxTerm y a b x n k)
      (∑' p : ℕ × ℕ, Function.uncurry (fun n k => auxTerm y a b x n k) p) := by
    have heq := hS.tsum_prod_uncurry hg_row
    rw [heq]
    exact hIter.hasSum
  have hCol : ∀ k : ℕ, HasSum (fun n : ℕ => auxTerm y a b x n k)
      (x ^ (k + 1) / (Nat.factorial k : ℂ) * Complex.exp (y * (a + b * ((k : ℂ) + 1)))) := by
    intro k
    have hbase := hasSum_complex_pow_div_factorial (y * (a + b * ((k : ℂ) + 1)))
    have hmul := hbase.mul_left (x ^ (k + 1) / (Nat.factorial k : ℂ))
    refine hmul.congr_fun fun n => ?_
    rw [mul_pow]
    unfold auxTerm
    ring
  have hColSum : (∑' k : ℕ, ∑' n : ℕ, auxTerm y a b x n k)
      = x * Complex.exp ((a + b) * y) * Complex.exp (x * Complex.exp (b * y)) := by
    have h1 : ∀ k : ℕ, (∑' n : ℕ, auxTerm y a b x n k)
        = (x * Complex.exp ((a + b) * y)) *
          ((x * Complex.exp (b * y)) ^ k / (Nat.factorial k : ℂ)) := by
      intro k
      rw [(hCol k).tsum_eq]
      have e1 : y * (a + b * ((k : ℂ) + 1)) = (a + b) * y + (k : ℂ) * (b * y) := by ring
      rw [e1, Complex.exp_add, Complex.exp_nat_mul]
      ring
    rw [tsum_congr h1, tsum_mul_left, (hasSum_complex_pow_div_factorial _).tsum_eq]
  have hL : ∀ n : ℕ, y ^ n / (Nat.factorial n : ℂ) * generalizedBellGenerating a b x n
      = Complex.exp (-x) * ∑' k : ℕ, auxTerm y a b x n k := by
    intro n
    have eF : generalizedBellGenerating a b x n
        = Complex.exp (-x) *
          ∑' k : ℕ, ((a + b * ((k : ℂ) + 1)) ^ n * x ^ (k + 1) / (Nat.factorial k : ℂ)) := by
      simp [generalizedBellGenerating]
    have e2 : (y ^ n / (Nat.factorial n : ℂ)) *
        (∑' k : ℕ, ((a + b * ((k : ℂ) + 1)) ^ n * x ^ (k + 1) / (Nat.factorial k : ℂ)))
        = ∑' k : ℕ, auxTerm y a b x n k := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => rfl
    conv_lhs => rw [eF, ← mul_assoc, mul_comm (y ^ n / (Nat.factorial n : ℂ)) _, mul_assoc]
    exact congrArg (Complex.exp (-x) * ·) e2
  have hLHS : HasSum
      (fun n : ℕ => y ^ n / (Nat.factorial n : ℂ) * generalizedBellGenerating a b x n)
      (Complex.exp (-x) * (∑' p : ℕ × ℕ, Function.uncurry (fun n k => auxTerm y a b x n k) p)) := by
    have h := hHasN.mul_left (Complex.exp (-x))
    refine h.congr_fun fun n => ?_
    exact hL n
  have hSwap : (∑' p : ℕ × ℕ, Function.uncurry (fun n k => auxTerm y a b x n k) p)
      = (∑' k : ℕ, ∑' n : ℕ, auxTerm y a b x n k) := by
    have heq1 := hS.tsum_prod_uncurry hg_row
    have heq2 := hS.tsum_comm
    rw [heq1]
    exact heq2.symm
  rw [hSwap, hColSum] at hLHS
  have hexp :
      Complex.exp (-x) * (x * Complex.exp ((a + b) * y) * Complex.exp (x * Complex.exp (b * y)))
      = x * Complex.exp ((a + b) * y) * Complex.exp (x * (Complex.exp (b * y) - 1)) := by
    have e1 : x * (Complex.exp (b * y) - 1) = x * Complex.exp (b * y) + (-x) := by ring
    rw [e1, Complex.exp_add]
    ring
  rw [hexp] at hLHS
  exact hLHS

end Entry9IiGeneralizedbellgenerating

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
