/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import MathlibExt.Combinatorics.Enumerative.CatalanGeneratingFunction

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry14Cor1Catalanpowerseries

/-- Product `∏_{j ∈ Ico (k+1) (2k)} (n + j)`, syntactically the product in the Wanted term. -/
private noncomputable def rcatProd (n : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))

/-- Coefficient `e_k(n)`: `1` at `k = 0`, else `n * rcatProd n k / k!`. -/
private noncomputable def rcatCoeff (n : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else n * rcatProd n k / (Nat.factorial k : ℝ)

/-- Catalan power series over `ℝ`. -/
private noncomputable def rcatR : PowerSeries ℝ :=
  PowerSeries.map (Nat.castRingHom ℝ) PowerSeries.catalanSeries

/-- The power series `F_n(a) = ∑' k, rcatCoeff n k * a ^ k`. -/
private noncomputable def rcatF (n a : ℝ) : ℝ :=
  ∑' k : ℕ, rcatCoeff n k * a ^ k

/-- Polynomial version of `rcatCoeff · k`, used only for the real-exponent convolution. -/
private noncomputable def rcatPoly (k : ℕ) : Polynomial ℝ :=
  if k = 0 then 1
  else Polynomial.C (1 / (Nat.factorial k : ℝ)) * Polynomial.X *
    ∏ j ∈ Finset.Ico (k + 1) (2 * k), (Polynomial.X + Polynomial.C (j : ℝ))

private theorem rcatCoeff_zero_eq (n : ℝ) : rcatCoeff n 0 = 1 := by
  simp [rcatCoeff]

private theorem rcatCoeff_eq_of_ne_zero {n : ℝ} {k : ℕ} (hk : k ≠ 0) :
    rcatCoeff n k = n * rcatProd n k / (Nat.factorial k : ℝ) := by
  simp [rcatCoeff, hk]

private theorem rcatProd_one (n : ℝ) : rcatProd n 1 = 1 := by
  simp [rcatProd]

private theorem rcatCoeff_succ_succ (n : ℝ) (q : ℕ) :
    rcatCoeff (n + 1) (q + 1) = rcatCoeff n (q + 1) + rcatCoeff (n + 2) q := by
  have hq1 : q + 1 ≠ 0 := by omega
  rw [rcatCoeff_eq_of_ne_zero hq1, rcatCoeff_eq_of_ne_zero hq1]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e1 : rcatProd (n + 1) (0 + 1) = 1 := by simp [rcatProd]
    have e2 : rcatProd n (0 + 1) = 1 := by simp [rcatProd]
    have f1 : Nat.factorial (0 + 1) = 1 := by simp
    rw [e1, e2, rcatCoeff_zero_eq, f1]
    push_cast
    ring
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have eA : 2 * (q' + 1 + 1) - (q' + 1 + 1 + 1) = q' + 1 := by omega
    have eB : 2 * (q' + 1 + 1) - (q' + 1 + 1 + 1) = q' + 1 := by omega
    have eC : 2 * (q' + 1) - (q' + 1 + 1) = q' := by omega
    have hA : rcatProd (n + 1) (q' + 1 + 1)
        = (∏ i ∈ Finset.range q', (n + (q' : ℝ) + 4 + (i : ℝ))) *
          (n + 2 * ((q' : ℝ) + 2)) := by
      simp only [rcatProd]
      rw [Finset.prod_Ico_eq_prod_range, eA, Finset.prod_range_succ]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
      · push_cast
        ring
    have hB : rcatProd n (q' + 1 + 1)
        = (∏ i ∈ Finset.range q', (n + (q' : ℝ) + 4 + (i : ℝ))) *
          (n + ((q' : ℝ) + 3)) := by
      simp only [rcatProd]
      rw [Finset.prod_Ico_eq_prod_range, eB, Finset.prod_range_succ']
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
      · push_cast
        ring
    have hC : rcatProd (n + 2) (q' + 1)
        = (∏ i ∈ Finset.range q', (n + (q' : ℝ) + 4 + (i : ℝ))) := by
      simp only [rcatProd]
      rw [Finset.prod_Ico_eq_prod_range, eC]
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    have hfact : ((Nat.factorial (q' + 1 + 1) : ℕ) : ℝ)
        = ((q' : ℝ) + 2) * ((Nat.factorial (q' + 1) : ℕ) : ℝ) := by
      have h := Nat.factorial_succ (q' + 1)
      rw [h]
      push_cast
      ring
    have hf1 : ((Nat.factorial (q' + 1) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hq2 : ((q' : ℝ) + 2) ≠ 0 := by positivity
    rw [rcatCoeff_eq_of_ne_zero (by omega : q' + 1 ≠ 0), hA, hB, hC, hfact]
    field_simp
    ring

private theorem rcatR_eq : rcatR = 1 + PowerSeries.X * rcatR ^ 2 := by
  have h2 := congrArg (PowerSeries.map (Nat.castRingHom ℝ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h2
  have h : rcatR ^ 2 * PowerSeries.X + 1 = rcatR := h2
  calc rcatR = rcatR ^ 2 * PowerSeries.X + 1 := h.symm
    _ = 1 + PowerSeries.X * rcatR ^ 2 := by ring

private theorem rcat_coeff_catR_pow (N k : ℕ) :
    PowerSeries.coeff k (rcatR ^ N) = rcatCoeff (N : ℝ) k := by
  induction k generalizing N with
  | zero =>
    have hcr : PowerSeries.constantCoeff rcatR = 1 := by
      have h : PowerSeries.constantCoeff rcatR
          = Nat.castRingHom ℝ
            (PowerSeries.constantCoeff PowerSeries.catalanSeries) := by
        rw [rcatR, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_map]
      rw [h, PowerSeries.catalanSeries_constantCoeff, map_one]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcr, one_pow,
      rcatCoeff_zero_eq]
  | succ q ih =>
    induction N with
    | zero =>
      have hne : q + 1 ≠ 0 := by omega
      rw [pow_zero, rcatCoeff_eq_of_ne_zero hne]
      simp [PowerSeries.coeff_one]
    | succ M ihM =>
      have hexp : rcatR ^ (M + 1)
          = rcatR ^ M + PowerSeries.X * rcatR ^ (M + 2) := by
        calc rcatR ^ (M + 1) = rcatR ^ M * rcatR := pow_succ _ _
          _ = rcatR ^ M * (1 + PowerSeries.X * rcatR ^ 2) :=
            congrArg (rcatR ^ M * ·) rcatR_eq
          _ = rcatR ^ M + PowerSeries.X * rcatR ^ (M + 2) := by
            rw [pow_add]
            ring
      have hcast1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      have hcast2 : ((M + 2 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
      rw [hexp, map_add, PowerSeries.coeff_succ_X_mul, ihM, ih (M + 2),
        hcast1, hcast2]
      exact (rcatCoeff_succ_succ (M : ℝ) q).symm

private theorem rcatCoeff_conv_nat (N M k : ℕ) :
    (∑ p ∈ Finset.antidiagonal k, rcatCoeff (N : ℝ) p.1 * rcatCoeff (M : ℝ) p.2) =
      rcatCoeff ((N : ℝ) + (M : ℝ)) k := by
  have hcast : ((N : ℝ) + (M : ℝ)) = ((N + M : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have h := PowerSeries.coeff_mul k (rcatR ^ N) (rcatR ^ M)
  rw [← pow_add] at h
  have h2 : (∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff p.1 (rcatR ^ N)
      * PowerSeries.coeff p.2 (rcatR ^ M))
      = ∑ p ∈ Finset.antidiagonal k,
        rcatCoeff (N : ℝ) p.1 * rcatCoeff (M : ℝ) p.2 :=
    Finset.sum_congr rfl
      (fun p _ => by rw [rcat_coeff_catR_pow, rcat_coeff_catR_pow])
  rw [h2, rcat_coeff_catR_pow] at h
  exact h.symm

private theorem rcatCoeff_one_eq_catalan (k : ℕ) :
    rcatCoeff 1 k = (catalan k : ℝ) := by
  have e : PowerSeries.coeff k rcatR = (catalan k : ℝ) := by
    simp [rcatR, PowerSeries.coeff_map]
  have h := rcat_coeff_catR_pow 1 k
  rw [pow_one, e, Nat.cast_one] at h
  exact h.symm

private theorem rcatPoly_eq_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    rcatPoly k = Polynomial.C (1 / (Nat.factorial k : ℝ)) * Polynomial.X *
      ∏ j ∈ Finset.Ico (k + 1) (2 * k),
        (Polynomial.X + Polynomial.C (j : ℝ)) := by
  simp [rcatPoly, hk]

private theorem rcat_eval_poly (n : ℝ) (k : ℕ) :
    Polynomial.eval n (rcatPoly k) = rcatCoeff n k := by
  by_cases hk : k = 0
  · subst hk
    simp [rcatPoly, rcatCoeff]
  · rw [rcatPoly_eq_of_ne_zero hk, rcatCoeff_eq_of_ne_zero hk,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_prod]
    have hprod : (∏ j ∈ Finset.Ico (k + 1) (2 * k),
        Polynomial.eval n (Polynomial.X + Polynomial.C (j : ℝ)))
        = rcatProd n k := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [hprod]
    ring

-- Key one-variable lemma
private theorem rcat_conv_of_nat (m : ℝ) (k : ℕ)
    (h : ∀ N : ℕ, (∑ p ∈ Finset.antidiagonal k,
      rcatCoeff (N : ℝ) p.1 * rcatCoeff m p.2) = rcatCoeff ((N : ℝ) + m) k)
    (n : ℝ) :
    (∑ p ∈ Finset.antidiagonal k, rcatCoeff n p.1 * rcatCoeff m p.2)
      = rcatCoeff (n + m) k := by
  set P : Polynomial ℝ := ∑ p ∈ Finset.antidiagonal k,
    rcatPoly p.1 * Polynomial.C (rcatCoeff m p.2) with hP
  set Q : Polynomial ℝ := (rcatPoly k).comp
    (Polynomial.X + Polynomial.C m) with hQ
  have hevalP : ∀ t : ℝ, Polynomial.eval t P
      = ∑ p ∈ Finset.antidiagonal k, rcatCoeff t p.1 * rcatCoeff m p.2 := by
    intro t
    rw [hP, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Polynomial.eval_mul, Polynomial.eval_C, rcat_eval_poly]
  have hevalQ : ∀ t : ℝ, Polynomial.eval t Q = rcatCoeff (t + m) k := by
    intro t
    rw [hQ, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, rcat_eval_poly]
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hmem : ∀ N : ℕ, ((N : ℝ)) ∈ {x : ℝ |
        Polynomial.eval x P = Polynomial.eval x Q} := by
      intro N
      change Polynomial.eval (N : ℝ) P = Polynomial.eval (N : ℝ) Q
      rw [hevalP, hevalQ]
      exact h N
    exact Set.infinite_of_injective_forall_mem Nat.cast_injective hmem
  have hfin := congrArg (Polynomial.eval n) hPQ
  rw [hevalP, hevalQ] at hfin
  exact hfin

private theorem rcatCoeff_conv (n m : ℝ) (k : ℕ) :
    (∑ p ∈ Finset.antidiagonal k, rcatCoeff n p.1 * rcatCoeff m p.2) =
      rcatCoeff (n + m) k := by
  have step1 : ∀ (M : ℕ) (t : ℝ), (∑ p ∈ Finset.antidiagonal k,
      rcatCoeff t p.1 * rcatCoeff (M : ℝ) p.2) = rcatCoeff (t + (M : ℝ)) k := by
    intro M t
    apply rcat_conv_of_nat (M : ℝ) k
    intro N
    exact rcatCoeff_conv_nat N M k
  have hswap : ∀ N : ℕ, (∑ p ∈ Finset.antidiagonal k,
      rcatCoeff (N : ℝ) p.1 * rcatCoeff m p.2)
      = ∑ p ∈ Finset.antidiagonal k,
        rcatCoeff m p.1 * rcatCoeff (N : ℝ) p.2 := by
    intro N
    have h := Finset.Nat.sum_antidiagonal_swap
      (f := fun p : ℕ × ℕ => rcatCoeff (N : ℝ) p.1 * rcatCoeff m p.2) (n := k)
    rw [← h]
    apply Finset.sum_congr rfl
    intro p _
    change rcatCoeff (N : ℝ) p.2 * rcatCoeff m p.1
      = rcatCoeff m p.1 * rcatCoeff (N : ℝ) p.2
    ring
  have step2 : ∀ N : ℕ, (∑ p ∈ Finset.antidiagonal k,
      rcatCoeff (N : ℝ) p.1 * rcatCoeff m p.2)
      = rcatCoeff ((N : ℝ) + m) k := by
    intro N
    rw [hswap, ← add_comm (m : ℝ) ((N : ℕ) : ℝ)]
    exact step1 N m
  exact rcat_conv_of_nat m k step2 n

private theorem rcat_summable_catalan_quarter :
    Summable (fun k : ℕ => (catalan k : ℝ) * (1 / 4 : ℝ) ^ k) ∧
      ∀ k : ℕ, 0 ≤ (catalan k : ℝ) * (1 / 4 : ℝ) ^ k := by
  have hnonneg : ∀ k : ℕ, 0 ≤ (catalan k : ℝ) * (1 / 4 : ℝ) ^ k := by
    intro k
    apply mul_nonneg (Nat.cast_nonneg _)
    positivity
  have htele : ∀ k : ℕ, (catalan k : ℝ) * (1 / 4 : ℝ) ^ k
      = 2 * ((Nat.centralBinom k : ℝ) / 4 ^ k
        - (Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)) := by
    intro k
    have h1 : ((k + 1 : ℕ) : ℝ) * (catalan k : ℝ)
        = (Nat.centralBinom k : ℝ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    have h2 : ((k + 1 : ℕ) : ℝ) * (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    push_cast at h1 h2
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hu : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hC : (Nat.centralBinom k : ℝ)
        = ((k : ℝ) + 1) * (catalan k : ℝ) := h1.symm
    have hC' : (Nat.centralBinom (k + 1) : ℝ)
        = (2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ)) / ((k : ℝ) + 1) := by
      rw [eq_div_iff hk1]
      linear_combination h2
    have e4 : (4 : ℝ) ^ (k + 1) = 4 * (4 : ℝ) ^ k := by rw [pow_succ]; ring
    have hq : (1 / 4 : ℝ) ^ k = 1 / (4 : ℝ) ^ k := by rw [div_pow, one_pow]
    rw [hC', hC, hq, e4]
    field_simp
    ring
  have hsum : ∀ K : ℕ, ∑ k ∈ Finset.range K, (catalan k : ℝ) * (1 / 4 : ℝ) ^ k
      = 2 * (1 - (Nat.centralBinom K : ℝ) / 4 ^ K) := by
    intro K
    have e : ∀ k ∈ Finset.range K, (catalan k : ℝ) * (1 / 4 : ℝ) ^ k
        = 2 * ((Nat.centralBinom k : ℝ) / 4 ^ k
          - (Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)) :=
      fun k _ => htele k
    have htel_sum : (∑ k ∈ Finset.range K,
        ((Nat.centralBinom k : ℝ) / 4 ^ k
          - (Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)))
        = 1 - (Nat.centralBinom K : ℝ) / 4 ^ K := by
      have hsub := Finset.sum_range_sub
        (fun k : ℕ => (Nat.centralBinom k : ℝ) / 4 ^ k) K
      have hneg : (∑ k ∈ Finset.range K,
          ((Nat.centralBinom k : ℝ) / 4 ^ k
            - (Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)))
          = -(∑ k ∈ Finset.range K,
            ((Nat.centralBinom (k + 1) : ℝ) / 4 ^ (k + 1)
              - (Nat.centralBinom k : ℝ) / 4 ^ k)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      have hb0 : (Nat.centralBinom 0 : ℝ) / (4 : ℝ) ^ 0 = 1 := by
        simp [Nat.centralBinom_zero]
      rw [hneg, hsub, hb0]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, htel_sum]
  have hbound : ∀ K : ℕ,
      (∑ k ∈ Finset.range K, (catalan k : ℝ) * (1 / 4 : ℝ) ^ k) ≤ 2 := by
    intro K
    rw [hsum K]
    have hpos : (0 : ℝ) ≤ (Nat.centralBinom K : ℝ) / 4 ^ K := by positivity
    linarith
  exact ⟨summable_of_sum_range_le hnonneg hbound, hnonneg⟩

private theorem rcat_antidiagonal_pow (f g : ℕ → ℝ) (x : ℝ) (k : ℕ) :
    (∑ p ∈ Finset.antidiagonal k, (f p.1 * x ^ p.1) * (g p.2 * x ^ p.2))
      = (∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2) * x ^ k := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpm := Finset.mem_antidiagonal.mp hp
  have hxp : x ^ p.1 * x ^ p.2 = x ^ k := by rw [← pow_add, hpm]
  calc (f p.1 * x ^ p.1) * (g p.2 * x ^ p.2)
      = (f p.1 * g p.2) * (x ^ p.1 * x ^ p.2) := by ring
    _ = (f p.1 * g p.2) * x ^ k := by rw [hxp]

private theorem rcat_summable_norm_antidiagonal (f g : ℕ → ℝ) (x : ℝ)
    (hf : Summable (fun k => ‖f k * x ^ k‖))
    (hg : Summable (fun k => ‖g k * x ^ k‖)) :
    Summable (fun k => ‖(∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2) * x ^ k‖) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (f := fun k => f k * x ^ k) (g := fun k => g k * x ^ k) hf hg
  simp only [rcat_antidiagonal_pow] at h
  exact h

private theorem rcat_tsum_mul_tsum (f g : ℕ → ℝ) (x : ℝ)
    (hf : Summable (fun k => ‖f k * x ^ k‖))
    (hg : Summable (fun k => ‖g k * x ^ k‖)) :
    (∑' k, f k * x ^ k) * (∑' k, g k * x ^ k) =
      ∑' k, (∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2) * x ^ k := by
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun k => f k * x ^ k) (g := fun k => g k * x ^ k) hf hg
  simp only [rcat_antidiagonal_pow] at h
  exact h

private theorem rcat_hasSum_catalan (a : ℝ) (ha : |a| ≤ 1 / 4) :
    HasSum (fun k : ℕ => (catalan k : ℝ) * a ^ k)
      (2 / (1 + Real.sqrt (1 - 4 * a))) := by
  have hsum : Summable (fun k : ℕ => (catalan k : ℝ) * a ^ k) := by
    apply Summable.of_norm_bounded rcat_summable_catalan_quarter.1
    intro k
    have hcat : (0 : ℝ) ≤ (catalan k : ℝ) := Nat.cast_nonneg _
    have ha4 : |a| ^ k ≤ (1 / 4 : ℝ) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) ha k
    calc ‖(catalan k : ℝ) * a ^ k‖ = (catalan k : ℝ) * |a| ^ k := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
            abs_of_nonneg hcat]
      _ ≤ (catalan k : ℝ) * (1 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left ha4 hcat
  have hagree : ∀ t : ℝ, t ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4) →
      (∑' k : ℕ, (catalan k : ℝ) * t ^ k)
        = 2 / (1 + Real.sqrt (1 - 4 * t)) := by
    intro t ht
    have hmem := Set.mem_Ioo.mp ht
    rcases eq_or_ne t 0 with rfl | ht0
    · have h0 : (∑' k : ℕ, (catalan k : ℝ) * (0 : ℝ) ^ k) = 1 := by
        rw [tsum_eq_single 0]
        · simp [catalan_zero]
        · intro b hb
          rw [zero_pow hb, mul_zero]
      rw [h0]
      rw [show (1 : ℝ) - 4 * 0 = 1 by ring, Real.sqrt_one]
      norm_num
    · have hlt : |t| < 1 / 4 := by
        rw [abs_lt]
        constructor <;> linarith [hmem.1, hmem.2]
      have hgen :=
        MetaMathlibExt.CatalanGeneratingFunction.catalan_generating_function_sqrt
          t hlt ht0
      have hnn : (0 : ℝ) ≤ 1 - 4 * t := by linarith [hmem.2]
      have hs2 : (Real.sqrt (1 - 4 * t)) ^ 2 = 1 - 4 * t := Real.sq_sqrt hnn
      have ht0' : (2 : ℝ) * t ≠ 0 := mul_ne_zero two_ne_zero ht0
      have hs1 : (0 : ℝ) < 1 + Real.sqrt (1 - 4 * t) := by
        have hnn' := Real.sqrt_nonneg (1 - 4 * t)
        linarith
      have hmul : (1 - Real.sqrt (1 - 4 * t)) * (1 + Real.sqrt (1 - 4 * t))
          = 2 * (2 * t) := by
        have e : (1 - Real.sqrt (1 - 4 * t)) * (1 + Real.sqrt (1 - 4 * t))
            = 1 - (Real.sqrt (1 - 4 * t)) ^ 2 := by ring
        rw [e, hs2]
        ring
      rw [hgen]
      field_simp
      linear_combination hmul
  have hcont_tsum : ContinuousOn (fun t : ℝ => ∑' k, (catalan k : ℝ) * t ^ k)
      (Set.Icc (-1 / 4 : ℝ) (1 / 4)) := by
    have hf : ∀ k : ℕ, ContinuousOn (fun t : ℝ => (catalan k : ℝ) * t ^ k)
        (Set.Icc (-1 / 4 : ℝ) (1 / 4)) := by
      intro k
      exact (continuous_const.mul (continuous_id.pow k)).continuousOn
    apply continuousOn_tsum hf rcat_summable_catalan_quarter.1
    intro k t ht
    have hcat : (0 : ℝ) ≤ (catalan k : ℝ) := Nat.cast_nonneg _
    have ht4 : |t| ≤ 1 / 4 := by
      have hm := Set.mem_Icc.mp ht
      rw [abs_le]
      constructor <;> linarith [hm.1, hm.2]
    have ha4 : |t| ^ k ≤ (1 / 4 : ℝ) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) ht4 k
    calc ‖(catalan k : ℝ) * t ^ k‖ = (catalan k : ℝ) * |t| ^ k := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
            abs_of_nonneg hcat]
      _ ≤ (catalan k : ℝ) * (1 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left ha4 hcat
  have hcont_C : ContinuousOn
      (fun t : ℝ => 2 / (1 + Real.sqrt (1 - 4 * t)))
      (Set.Icc (-1 / 4 : ℝ) (1 / 4)) := by
    have hsqrt : Continuous (fun t : ℝ => Real.sqrt (1 - 4 * t)) :=
      Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_const.mul continuous_id))
    have hden : Continuous (fun t : ℝ => 1 + Real.sqrt (1 - 4 * t)) :=
      continuous_const.add hsqrt
    have hne : ∀ t : ℝ, (1 + Real.sqrt (1 - 4 * t)) ≠ 0 := by
      intro t
      have hnn := Real.sqrt_nonneg (1 - 4 * t)
      have hpos : (0 : ℝ) < 1 + Real.sqrt (1 - 4 * t) := by linarith
      exact ne_of_gt hpos
    exact (continuous_const.div hden (fun t => hne t)).continuousOn
  have heq : Set.EqOn (fun t : ℝ => ∑' k, (catalan k : ℝ) * t ^ k)
      (fun t => 2 / (1 + Real.sqrt (1 - 4 * t)))
      (Set.Icc (-1 / 4 : ℝ) (1 / 4)) := by
    have hsub : Set.Ioo (-1 / 4 : ℝ) (1 / 4) ⊆ Set.Icc (-1 / 4 : ℝ) (1 / 4) :=
      Set.Ioo_subset_Icc_self
    have hclo : Set.Icc (-1 / 4 : ℝ) (1 / 4)
        ⊆ closure (Set.Ioo (-1 / 4 : ℝ) (1 / 4)) := by
      rw [closure_Ioo (by norm_num : (-1 / 4 : ℝ) ≠ 1 / 4)]
    exact Set.EqOn.of_subset_closure (fun t ht => hagree t ht) hcont_tsum
      hcont_C hsub hclo
  have haIcc : a ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4) := by
    have h := abs_le.mp ha
    simp only [Set.mem_Icc]
    constructor <;> linarith [h.1, h.2]
  have hval : (∑' k : ℕ, (catalan k : ℝ) * a ^ k)
      = 2 / (1 + Real.sqrt (1 - 4 * a)) := heq haIcc
  rw [← hval]
  exact hsum.hasSum

private theorem rcat_cpsCoeff_nat_nonneg (M k : ℕ) : 0 ≤ rcatCoeff (M : ℝ) k := by
  by_cases hk : k = 0
  · subst hk
    rw [rcatCoeff_zero_eq]
    exact zero_le_one
  · rw [rcatCoeff_eq_of_ne_zero hk]
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply mul_nonneg (Nat.cast_nonneg _)
    simp only [rcatProd]
    apply Finset.prod_nonneg
    intro j _
    have h1 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith

private theorem rcat_summable_nat_quarter (M : ℕ) :
    Summable (fun k : ℕ => rcatCoeff (M : ℝ) k * (1 / 4 : ℝ) ^ k) := by
  induction M with
  | zero =>
    have h0 : ∀ b : ℕ, b ≠ 0 →
        rcatCoeff ((0 : ℕ) : ℝ) b * (1 / 4 : ℝ) ^ b = 0 := by
      intro b hb
      have hzb : rcatCoeff ((0 : ℕ) : ℝ) b = 0 := by
        rw [rcatCoeff_eq_of_ne_zero hb, Nat.cast_zero, zero_mul, zero_div]
      rw [hzb, zero_mul]
    exact (hasSum_single 0 h0).summable
  | succ M ih =>
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    have hdecomp : ∀ k : ℕ, rcatCoeff ((M + 1 : ℕ) : ℝ) k
        = ∑ p ∈ Finset.antidiagonal k,
          rcatCoeff (M : ℝ) p.1 * (catalan p.2 : ℝ) := by
      intro k
      have h := rcatCoeff_conv_nat M 1 k
      rw [Nat.cast_one] at h
      simp only [rcatCoeff_one_eq_catalan] at h
      rw [hcast]
      exact h.symm
    have hfnorm : Summable
        (fun k => ‖rcatCoeff (M : ℝ) k * (1 / 4 : ℝ) ^ k‖) := ih.norm
    have hgnorm : Summable (fun k => ‖(catalan k : ℝ) * (1 / 4 : ℝ) ^ k‖) :=
      rcat_summable_catalan_quarter.1.norm
    have hM := (rcat_summable_norm_antidiagonal _ _ _ hfnorm hgnorm).of_norm
    have hfin : (fun k : ℕ => rcatCoeff ((M + 1 : ℕ) : ℝ) k * (1 / 4 : ℝ) ^ k)
        = (fun k => (∑ p ∈ Finset.antidiagonal k,
          rcatCoeff (M : ℝ) p.1 * (catalan p.2 : ℝ)) * (1 / 4 : ℝ) ^ k) := by
      funext k
      rw [hdecomp k]
    rw [hfin]
    exact hM

private theorem rcatProd_zero (n : ℝ) : rcatProd n 0 = 1 := by
  simp [rcatProd]

private theorem rcat_abs_prod_le (n : ℝ) (M : ℕ) (hM : |n| ≤ M) (k : ℕ) :
    |rcatProd n k| ≤ rcatProd (M : ℝ) k := by
  simp only [rcatProd, Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
  intro j _
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hM' : |n| ≤ (M : ℝ) := hM
  calc |n + (j : ℝ)| ≤ |n| + |(j : ℝ)| := abs_add_le _ _
    _ = |n| + (j : ℝ) := by rw [abs_of_nonneg hj]
    _ ≤ (M : ℝ) + (j : ℝ) := by linarith

private theorem rcat_abs_coeff_le (n : ℝ) (M : ℕ) (hM : |n| ≤ M) (k : ℕ) :
    |rcatCoeff n k| ≤ rcatCoeff (M : ℝ) k := by
  by_cases hk : k = 0
  · subst hk
    rw [rcatCoeff_zero_eq, rcatCoeff_zero_eq, abs_one]
  · rw [rcatCoeff_eq_of_ne_zero hk, rcatCoeff_eq_of_ne_zero hk,
      abs_div, abs_mul]
    have hP := rcat_abs_prod_le n M hM k
    have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos k)
    rw [abs_of_pos hfk]
    have hle : |n| * |rcatProd n k| ≤ (M : ℝ) * rcatProd (M : ℝ) k :=
      mul_le_mul hM hP (abs_nonneg _) (by positivity)
    exact div_le_div_of_nonneg_right hle (le_of_lt hfk)

private theorem rcat_prod_div_le_coeff (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    rcatProd (M : ℝ) k / (Nat.factorial k : ℝ) ≤ rcatCoeff (M : ℝ) k := by
  by_cases hk : k = 0
  · subst hk
    rw [rcatProd_zero, rcatCoeff_zero_eq, Nat.factorial_zero, Nat.cast_one,
      div_one]
  · rw [rcatCoeff_eq_of_ne_zero hk]
    have hPnonneg : (0 : ℝ) ≤ rcatProd (M : ℝ) k / (Nat.factorial k : ℝ) := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      simp only [rcatProd]
      apply Finset.prod_nonneg
      intro j _
      have h1 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    calc rcatProd (M : ℝ) k / (Nat.factorial k : ℝ)
        = 1 * (rcatProd (M : ℝ) k / (Nat.factorial k : ℝ)) := (one_mul _).symm
      _ ≤ (M : ℝ) * (rcatProd (M : ℝ) k / (Nat.factorial k : ℝ)) :=
        mul_le_mul_of_nonneg_right hM1 hPnonneg
      _ = (M : ℝ) * rcatProd (M : ℝ) k / (Nat.factorial k : ℝ) := by ring

private theorem rcat_summable_norm_coeff (n a : ℝ) (ha : |a| ≤ 1 / 4) :
    Summable (fun k => ‖rcatCoeff n k * a ^ k‖) := by
  set M : ℕ := ⌈|n|⌉₊ with hM
  have hMn : |n| ≤ (M : ℝ) := Nat.le_ceil _
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _
    (rcat_summable_nat_quarter M)
  intro k
  have h1 : ‖rcatCoeff n k * a ^ k‖ = |rcatCoeff n k| * |a| ^ k := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  rw [h1]
  have h2 : |rcatCoeff n k| ≤ rcatCoeff (M : ℝ) k := rcat_abs_coeff_le n M hMn k
  have h3 : |a| ^ k ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ (abs_nonneg _) ha k
  have h4 : (0 : ℝ) ≤ |a| ^ k := pow_nonneg (abs_nonneg _) _
  have h5 : (0 : ℝ) ≤ rcatCoeff (M : ℝ) k := rcat_cpsCoeff_nat_nonneg M k
  calc |rcatCoeff n k| * |a| ^ k ≤ rcatCoeff (M : ℝ) k * |a| ^ k :=
        mul_le_mul_of_nonneg_right h2 h4
    _ ≤ rcatCoeff (M : ℝ) k * (1 / 4 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left h3 h5

private theorem rcatF_mul (n m a : ℝ) (ha : |a| ≤ 1 / 4) :
    rcatF n a * rcatF m a = rcatF (n + m) a := by
  simp only [rcatF]
  rw [rcat_tsum_mul_tsum _ _ _ (rcat_summable_norm_coeff n a ha)
    (rcat_summable_norm_coeff m a ha)]
  apply tsum_congr
  intro k
  rw [rcatCoeff_conv]

private theorem rcatF_zero (a : ℝ) : rcatF 0 a = 1 := by
  have h0 : ∀ b : ℕ, b ≠ 0 → rcatCoeff (0 : ℝ) b * a ^ b = 0 := by
    intro b hb
    have hzb : rcatCoeff (0 : ℝ) b = 0 := by
      rw [rcatCoeff_eq_of_ne_zero hb]
      simp
    rw [hzb, zero_mul]
  simp only [rcatF]
  rw [tsum_eq_single 0 h0]
  simp [rcatCoeff_zero_eq]

private theorem rcatF_one (a : ℝ) (ha : |a| ≤ 1 / 4) :
    rcatF 1 a = 2 / (1 + Real.sqrt (1 - 4 * a)) := by
  have h : (fun k : ℕ => rcatCoeff (1 : ℝ) k * a ^ k)
      = (fun k : ℕ => (catalan k : ℝ) * a ^ k) := by
    funext k
    rw [rcatCoeff_one_eq_catalan]
  simp only [rcatF]
  rw [h]
  exact (rcat_hasSum_catalan a ha).tsum_eq

private theorem rcatF_pos (n a : ℝ) (ha : |a| ≤ 1 / 4) : 0 < rcatF n a := by
  have hsq : rcatF n a = (rcatF (n / 2) a) ^ 2 := by
    have h := rcatF_mul (n / 2) (n / 2) a ha
    have e : n / 2 + n / 2 = n := by ring
    rw [e] at h
    rw [sq]
    exact h.symm
  have hnn : 0 ≤ rcatF n a := by
    rw [hsq]
    exact sq_nonneg _
  have hne : rcatF n a ≠ 0 := by
    have h := rcatF_mul n (-n) a ha
    have e : n + -n = 0 := by ring
    rw [e, rcatF_zero a] at h
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  exact lt_of_le_of_ne hnn (Ne.symm hne)

private theorem rcat_continuous_prod (k : ℕ) :
    Continuous (fun n : ℝ => rcatProd n k) := by
  simp only [rcatProd]
  exact continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)

private theorem rcat_continuous_F (a : ℝ) (ha : |a| ≤ 1 / 4) :
    Continuous (fun n : ℝ => rcatF n a) := by
  simp only [rcatF]
  rw [continuous_iff_continuousAt]
  intro n0
  have hMgt : |n0| < (⌈|n0|⌉₊ : ℝ) + 1 :=
    lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hnhds : Set.Icc (-((⌈|n0|⌉₊ : ℝ) + 1)) ((⌈|n0|⌉₊ : ℝ) + 1) ∈ nhds n0 := by
    have habs2 := abs_lt.mp hMgt
    exact Icc_mem_nhds habs2.1 habs2.2
  have hmajor : Summable (fun k =>
      rcatCoeff ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) k * (1 / 4 : ℝ) ^ k) :=
    rcat_summable_nat_quarter _
  have hcont : ContinuousOn (fun n : ℝ => ∑' k, rcatCoeff n k * a ^ k)
      (Set.Icc (-((⌈|n0|⌉₊ : ℝ) + 1)) ((⌈|n0|⌉₊ : ℝ) + 1)) := by
    have hf : ∀ k : ℕ, ContinuousOn (fun n : ℝ => rcatCoeff n k * a ^ k)
        (Set.Icc (-((⌈|n0|⌉₊ : ℝ) + 1)) ((⌈|n0|⌉₊ : ℝ) + 1)) := by
      intro k
      by_cases hk : k = 0
      · subst hk
        have hfun : (fun n : ℝ => rcatCoeff n 0 * a ^ 0) = fun _ => 1 := by
          funext n
          rw [rcatCoeff_zero_eq, pow_zero, mul_one]
        rw [hfun]
        exact continuousOn_const
      · have hfun : (fun n : ℝ => rcatCoeff n k * a ^ k)
            = fun n => n * rcatProd n k / (Nat.factorial k : ℝ) * a ^ k := by
          funext n
          rw [rcatCoeff_eq_of_ne_zero hk]
        rw [hfun]
        exact (((continuous_id.mul (rcat_continuous_prod k)).div_const _).mul_const
          _).continuousOn
    apply continuousOn_tsum hf hmajor
    intro k t ht
    have htM : |t| ≤ ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) := by
      have hm := Set.mem_Icc.mp ht
      have hcast : ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) = (⌈|n0|⌉₊ : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast, abs_le]
      constructor <;> linarith [hm.1, hm.2]
    have h1 : ‖rcatCoeff t k * a ^ k‖ = |rcatCoeff t k| * |a| ^ k := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    rw [h1]
    have h2 : |rcatCoeff t k| ≤ rcatCoeff ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) k :=
      rcat_abs_coeff_le t _ htM k
    have h3 : |a| ^ k ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ (abs_nonneg _) ha k
    have h4 : (0 : ℝ) ≤ |a| ^ k := pow_nonneg (abs_nonneg _) _
    have h5 : (0 : ℝ) ≤ rcatCoeff ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) k :=
      rcat_cpsCoeff_nat_nonneg _ k
    calc |rcatCoeff t k| * |a| ^ k
        ≤ rcatCoeff ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) k * |a| ^ k :=
          mul_le_mul_of_nonneg_right h2 h4
      _ ≤ rcatCoeff ((⌈|n0|⌉₊ + 1 : ℕ) : ℝ) k * (1 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h3 h5
  exact hcont.continuousAt hnhds

private theorem rcat_eq_rpow_of_continuous_of_map_add (G : ℝ → ℝ)
    (hcont : Continuous G) (hpos : ∀ x, 0 < G x)
    (hadd : ∀ x y, G (x + y) = G x * G y) (x : ℝ) :
    G x = (G 1) ^ x := by
  have hne : ∀ x, G x ≠ 0 := fun x => ne_of_gt (hpos x)
  have hlog_add : ∀ x y, Real.log (G (x + y)) = Real.log (G x) + Real.log (G y) := by
    intro x y
    rw [hadd, Real.log_mul (hne x) (hne y)]
  have hφcont : Continuous (fun x => Real.log (G x)) := hcont.log hne
  have hsmul : ∀ x : ℝ, Real.log (G x) = x • Real.log (G 1) := by
    intro x
    have h := map_real_smul
      (AddMonoidHom.mk' (fun x => Real.log (G x)) hlog_add) hφcont x 1
    simpa [smul_eq_mul] using h
  have hG1 : 0 < G 1 := hpos 1
  calc G x = Real.exp (Real.log (G x)) := (Real.exp_log (hpos x)).symm
    _ = Real.exp (x • Real.log (G 1)) := by rw [hsmul x]
    _ = Real.exp (Real.log (G 1) * x) := by rw [smul_eq_mul, mul_comm]
    _ = (G 1) ^ x := by rw [Real.rpow_def_of_pos hG1]

private theorem rcatF_eq_rpow (n a : ℝ) (ha : |a| ≤ 1 / 4) :
    rcatF n a = (2 / (1 + Real.sqrt (1 - 4 * a))) ^ n := by
  have h := rcat_eq_rpow_of_continuous_of_map_add (fun n => rcatF n a)
    (rcat_continuous_F a ha) (fun x => rcatF_pos x a ha)
    (fun x y => (rcatF_mul x y a ha).symm) n
  rw [rcatF_one a ha] at h
  exact h

/-- **Ramanujan's series for powers of the Catalan generating function.** Let $n$ and $a$ be real
numbers with $|a| \le 1/4$. For a natural number $k$ put $t_k = 0$ if $k < 2$, and
$$t_k = \frac{a^k}{k!} \prod_{j=k+1}^{2k-1} (n + j)$$
if $k \ge 2$. Then the series $\sum_k t_k$ is summable and
$$\left(\frac{2}{1 + \sqrt{1 - 4a}}\right)^{n} = 1 + n a + n \sum_{k=0}^{\infty} t_k.$$

Proves `Wanted` entry `ramanujan_part1_ch3_entry14_cor1_catalanpowerseries`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 14, Corollary 1, printed p.
    71; scan PDF p. 81.
-/
theorem ramanujan_part1_ch3_entry14_cor1_catalanpowerseries
    (n a : ℝ) (ha : |a| ≤ 1 / 4) :
    let term := fun k : ℕ => if k < 2 then 0 else
      (∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))) * a ^ k / (Nat.factorial k : ℝ)
    Summable term ∧
      Real.rpow (2 / (1 + Real.sqrt (1 - 4 * a))) n = 1 + n * a + n * ∑' k, term k := by
  intro term
  have hterm_eq : ∀ k : ℕ, term k = (if k < 2 then (0 : ℝ) else
      (∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))) * a ^ k /
        (Nat.factorial k : ℝ)) := fun k => rfl
  set M : ℕ := ⌈|n|⌉₊ + 1 with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    omega
  have hMn : |n| ≤ (M : ℝ) := by
    have h1 : |n| ≤ (⌈|n|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈|n|⌉₊ : ℝ) ≤ (M : ℝ) := by
      rw [hM]
      exact Nat.cast_le.mpr (Nat.le_succ _)
    exact h1.trans h2
  have hmaj : Summable (fun k => rcatCoeff (M : ℝ) k * (1 / 4 : ℝ) ^ k) :=
    rcat_summable_nat_quarter M
  have hterm_sum : Summable term := by
    apply Summable.of_norm_bounded hmaj
    intro k
    by_cases hk2 : k < 2
    · have e : term k = 0 := by simp only [hterm_eq k, hk2, ite_true]
      rw [e, norm_zero]
      exact mul_nonneg (rcat_cpsCoeff_nat_nonneg M k) (by positivity)
    · have e : term k
          = (∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))) * a ^ k /
            (Nat.factorial k : ℝ) := by
        simp only [hterm_eq k, hk2, ite_false]
      rw [e]
      have hP := rcat_abs_prod_le n M hMn k
      have ha4 : |a| ^ k ≤ (1 / 4 : ℝ) ^ k :=
        pow_le_pow_left₀ (abs_nonneg _) ha k
      have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) :=
        Nat.cast_pos.mpr (Nat.factorial_pos k)
      have hPMnn : (0 : ℝ) ≤ rcatProd (M : ℝ) k := by
        simp only [rcatProd]
        apply Finset.prod_nonneg
        intro j _
        have h1 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith
      have eP : (∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ)))
          = rcatProd n k := rfl
      have h1 : ‖(∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))) * a ^ k /
            (Nat.factorial k : ℝ)‖
          = |rcatProd n k| * |a| ^ k / (Nat.factorial k : ℝ) := by
        rw [eP, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hfk]
      rw [h1]
      calc |rcatProd n k| * |a| ^ k / (Nat.factorial k : ℝ)
          ≤ rcatProd (M : ℝ) k * |a| ^ k / (Nat.factorial k : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hfk)
            exact mul_le_mul_of_nonneg_right hP (pow_nonneg (abs_nonneg _) _)
        _ ≤ rcatProd (M : ℝ) k * (1 / 4 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hfk)
            exact mul_le_mul_of_nonneg_left ha4 hPMnn
        _ = rcatProd (M : ℝ) k / (Nat.factorial k : ℝ) * (1 / 4 : ℝ) ^ k := by
            ring
        _ ≤ rcatCoeff (M : ℝ) k * (1 / 4 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right (rcat_prod_div_le_coeff M hM1 k)
              (by positivity)
  refine ⟨hterm_sum, ?_⟩
  have eR : Real.rpow (2 / (1 + Real.sqrt (1 - 4 * a))) n = rcatF n a :=
    (rcatF_eq_rpow n a ha).symm
  rw [eR]
  have hFsumm : Summable (fun k => rcatCoeff n k * a ^ k) :=
    (rcat_summable_norm_coeff n a ha).of_norm
  have hrange2 : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.range 2, f i = f 0 + f 1 := by
    intro f
    have h23 : Finset.range 2 = ({0, 1} : Finset ℕ) := by decide
    rw [h23, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hFsplit2 : (∑' k, rcatCoeff n k * a ^ k)
      = (rcatCoeff n 0 * a ^ 0 + rcatCoeff n 1 * a ^ 1)
        + ∑' i, rcatCoeff n (i + 2) * a ^ (i + 2) := by
    have h := hFsumm.sum_add_tsum_nat_add 2
    rw [hrange2] at h
    exact h.symm
  have hTsplit2 : (∑' k, term k)
      = (term 0 + term 1) + ∑' i, term (i + 2) := by
    have h := hterm_sum.sum_add_tsum_nat_add 2
    rw [hrange2] at h
    exact h.symm
  have hF0 : rcatCoeff n 0 * a ^ 0 = 1 := by simp [rcatCoeff_zero_eq]
  have hF1 : rcatCoeff n 1 * a ^ 1 = n * a := by
    rw [rcatCoeff_eq_of_ne_zero one_ne_zero, rcatProd_one]
    simp
  have hT0 : term 0 = 0 := by simp [hterm_eq 0]
  have hT1 : term 1 = 0 := by simp [hterm_eq 1]
  have htail_term : ∀ k : ℕ, rcatCoeff n (k + 2) * a ^ (k + 2)
      = n * term (k + 2) := by
    intro k
    have h23 : ¬ ((k + 2 : ℕ) < 2) := by omega
    have e : term (k + 2)
        = (∏ j ∈ Finset.Ico (k + 2 + 1) (2 * (k + 2)), (n + (j : ℝ))) * a ^ (k + 2) /
          (Nat.factorial (k + 2) : ℝ) := by
      simp only [hterm_eq (k + 2), h23, ite_false]
    rw [e, rcatCoeff_eq_of_ne_zero (by omega : k + 2 ≠ 0)]
    simp only [rcatProd]
    ring
  have htail : (∑' i : ℕ, rcatCoeff n (i + 2) * a ^ (i + 2))
      = n * (∑' i : ℕ, term (i + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    exact htail_term k
  simp only [rcatF]
  rw [hFsplit2, hTsplit2, hF0, hF1, hT0, hT1, htail]
  ring

end Entry14Cor1Catalanpowerseries

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3

end
