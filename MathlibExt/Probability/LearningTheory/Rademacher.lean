/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-! # Massart's finite-class lemma

The expected supremum of a Rademacher process indexed by a finite
set `S` of vectors is at most `√(2 log |S|)` times the largest
Euclidean norm in `S`. This is the Massart core of roadmap package
ML-07 of the Atlas TCS canon roadmap; the Rademacher complexity API
and symmetrization bounds are follow-ups.

Source: P. Massart, "About the constants in Talagrand's
concentration inequalities for empirical processes", Annals of
Probability 28 (2000), 863--884, Lemma 2.2.
-/

open Finset

private lemma card_sign (m : ℕ) : Fintype.card (Fin m → Bool) = 2 ^ m := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma exp_t_sup_le {m : ℕ} {S : Finset (Fin m → ℝ)} (hS : S.Nonempty)
    (t : ℝ) (σ : Fin m → Bool) :
    Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) ≤
      ∑ v ∈ S, Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i)) := by
  obtain ⟨vstar, hvstar, hEq⟩ :=
    Finset.exists_mem_eq_sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)
  rw [hEq]
  exact Finset.single_le_sum
    (f := fun v => Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
    (fun _ _ => le_of_lt (Real.exp_pos _)) hvstar

private lemma mgf_factor {m : ℕ} (t : ℝ) (v : Fin m → ℝ) :
    (∑ σ : Fin m → Bool, Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i))) =
      ∏ i, (Real.exp (t * v i) + Real.exp (-(t * v i))) := by
  simp only [Finset.mul_sum, Real.exp_sum]
  rw [(Fintype.prod_sum (fun i b => Real.exp (t * ((if b = true then (1 : ℝ) else -1) * v i)))).symm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  congr 1
  · congr 1
    simp only [ite_true]
    ring
  · congr 1
    simp only [Bool.false_eq_true, ite_false]
    ring

private lemma exp_add_exp_neg_le {x : ℝ} :
    Real.exp x + Real.exp (-x) ≤ 2 * Real.exp (x ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq x
  have heq : Real.exp x + Real.exp (-x) = 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

private lemma mgf_vec_le {m : ℕ} (t R : ℝ) (v : Fin m → ℝ)
    (h : (∑ i, v i ^ 2) ≤ R ^ 2) :
    (∑ σ : Fin m → Bool, Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
      ≤ 2 ^ m * Real.exp (t ^ 2 * R ^ 2 / 2) := by
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ Real.exp (t * v i) + Real.exp (-(t * v i)) := by
    intro i _
    exact add_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Real.exp (t * v i) + Real.exp (-(t * v i)) ≤ 2 * Real.exp ((t * v i) ^ 2 / 2) := by
    intro i _
    exact exp_add_exp_neg_le
  have hprod := Finset.prod_le_prod₀ h0 h1
  have hsum : (∑ i, (t * v i) ^ 2 / 2) = t ^ 2 * (∑ i, v i ^ 2) / 2 := by
    have heq : ∀ i : Fin m, (t * v i) ^ 2 / 2 = (t ^ 2 / 2) * v i ^ 2 := fun i => by ring
    simp only [heq, ← Finset.mul_sum]
    ring
  have hclosed : (∏ i, (2 * Real.exp ((t * v i) ^ 2 / 2)))
      = 2 ^ m * Real.exp (t ^ 2 * (∑ i, v i ^ 2) / 2) := by
    calc (∏ i, (2 * Real.exp ((t * v i) ^ 2 / 2)))
        = (∏ _i : Fin m, (2 : ℝ)) * (∏ i, Real.exp ((t * v i) ^ 2 / 2)) :=
          Finset.prod_mul_distrib
      _ = 2 ^ m * Real.exp (∑ i, (t * v i) ^ 2 / 2) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Real.exp_sum]
      _ = 2 ^ m * Real.exp (t ^ 2 * (∑ i, v i ^ 2) / 2) := by rw [hsum]
  have hmono : 2 ^ m * Real.exp (t ^ 2 * (∑ i, v i ^ 2) / 2)
      ≤ 2 ^ m * Real.exp (t ^ 2 * R ^ 2 / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) m)
    rw [Real.exp_le_exp]
    have hmul : t ^ 2 * (∑ i, v i ^ 2) ≤ t ^ 2 * R ^ 2 :=
      mul_le_mul_of_nonneg_left h (sq_nonneg t)
    linarith
  calc (∑ σ : Fin m → Bool, Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
      = (∏ i, (Real.exp (t * v i) + Real.exp (-(t * v i)))) := mgf_factor t v
    _ ≤ (∏ i, (2 * Real.exp ((t * v i) ^ 2 / 2))) := hprod
    _ = 2 ^ m * Real.exp (t ^ 2 * (∑ i, v i ^ 2) / 2) := hclosed
    _ ≤ 2 ^ m * Real.exp (t ^ 2 * R ^ 2 / 2) := hmono

private lemma exp_avg_le_avg_exp {ι : Type} [Fintype ι] (g : ι → ℝ) (N : ℝ)
    (hcard : (Fintype.card ι : ℝ) = N) (hNpos : 0 < N) :
    Real.exp ((∑ i, g i) / N) ≤ (∑ i, Real.exp (g i)) / N := by
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hw0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ N⁻¹ := fun _ _ =>
    inv_nonneg.mpr (le_of_lt hNpos)
  have hw1 : ∑ _i ∈ (Finset.univ : Finset ι), N⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_inv_cancel₀ hNne]
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), g i ∈ (Set.univ : Set ℝ) := fun _ _ =>
    Set.mem_univ _
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => N⁻¹) (p := g)
    hw0 hw1 hmem
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (∑ i, g i) N⁻¹,
    mul_comm (∑ i, Real.exp (g i)) N⁻¹]
  exact hJ

private lemma mgf_bound {m : ℕ} {S : Finset (Fin m → ℝ)} (hS : S.Nonempty) (t : ℝ)
    (_ht : 0 < t) :
    t * ((∑ σ : Fin m → Bool,
      S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) / 2 ^ m) ≤
    Real.log S.card + t ^ 2 * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2 := by
  have hper : ∀ v ∈ S, (∑ σ : Fin m → Bool,
      Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
      ≤ 2 ^ m * Real.exp (t ^ 2
        * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2) := by
    intro v hv
    apply mgf_vec_le
    have hle : Real.sqrt (∑ i, v i ^ 2)
        ≤ S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2)) :=
      Finset.le_sup' (fun v => Real.sqrt (∑ i, v i ^ 2)) hv
    exact (Real.sqrt_le_iff.mp hle).2
  have htot : (∑ σ : Fin m → Bool,
      Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
      ≤ S.card * (2 ^ m * Real.exp (t ^ 2
        * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2)) := by
    calc (∑ σ : Fin m → Bool,
        Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
          ≤ (∑ σ : Fin m → Bool, ∑ v ∈ S,
            Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i))) :=
            Finset.sum_le_sum (fun σ _ => exp_t_sup_le hS t σ)
        _ = (∑ v ∈ S, ∑ σ : Fin m → Bool,
            Real.exp (t * (∑ i, (if σ i then (1 : ℝ) else -1) * v i))) :=
            Finset.sum_comm
        _ ≤ (∑ _v ∈ S, 2 ^ m * Real.exp (t ^ 2
            * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2)) :=
            Finset.sum_le_sum (fun v hv => hper v hv)
        _ = S.card * (2 ^ m * Real.exp (t ^ 2
            * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by
    rw [card_sign, Nat.cast_pow, Nat.cast_two]
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have hJ := exp_avg_le_avg_exp
    (fun σ : Fin m → Bool => t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i))
    ((2 : ℝ) ^ m) hcard hpos
  have hJ' : Real.exp ((∑ σ : Fin m → Bool,
      t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) / 2 ^ m)
      ≤ (∑ σ : Fin m → Bool,
        Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i))) / 2 ^ m := hJ
  have hsum : (∑ σ : Fin m → Bool,
      t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i))
      = t * (∑ σ : Fin m → Bool,
        S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) := by
    rw [Finset.mul_sum]
  rw [hsum, mul_div_assoc] at hJ'
  have hdiv : (∑ σ : Fin m → Bool,
      Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i))) / 2 ^ m
      ≤ S.card * Real.exp (t ^ 2
        * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2) := by
    rw [div_le_iff₀ hpos]
    calc (∑ σ : Fin m → Bool,
        Real.exp (t * S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)))
          ≤ S.card * (2 ^ m * Real.exp (t ^ 2
            * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2)) := htot
        _ = (S.card * Real.exp (t ^ 2
            * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2)) * 2 ^ m := by
            ring
  have hexp : Real.exp (t * ((∑ σ : Fin m → Bool,
      S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) / 2 ^ m))
      ≤ S.card * Real.exp (t ^ 2
        * (S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2))) ^ 2 / 2) :=
    hJ'.trans hdiv
  have hcardpos : (0 : ℝ) < S.card := by
    rw [Nat.cast_pos]
    exact Finset.card_pos.mpr hS
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  rw [Real.log_mul (ne_of_gt hcardpos) (ne_of_gt (Real.exp_pos _))] at hlog
  rw [Real.log_exp] at hlog
  exact hlog

private lemma optimize {E R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (h : ∀ t : ℝ, 0 < t → t * E ≤ L + t ^ 2 * R ^ 2 / 2) :
    E ≤ Real.sqrt (2 * L) * R := by
  have hEb : ∀ t : ℝ, 0 < t → E ≤ L / t + t * R ^ 2 / 2 := by
    intro t ht
    have h2 := h t ht
    have h3 : E * t ≤ L + t ^ 2 * R ^ 2 / 2 := by
      calc E * t = t * E := mul_comm _ _
        _ ≤ _ := h2
    have h4 : E ≤ (L + t ^ 2 * R ^ 2 / 2) / t := (le_div_iff₀ ht).mpr h3
    have htne : t ≠ 0 := ne_of_gt ht
    have heq : (L + t ^ 2 * R ^ 2 / 2) / t = L / t + t * R ^ 2 / 2 := by
      rw [add_div]
      congr 1
      field_simp
    rwa [heq] at h4
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · subst hR0
    rw [mul_zero]
    by_contra hcon
    push Not at hcon
    have hL1 : (0 : ℝ) < L + 1 := by linarith [hL]
    have hEne : E ≠ 0 := ne_of_gt hcon
    have hL1ne : L + 1 ≠ 0 := ne_of_gt hL1
    have hdiv0 : (L + 1) / E ≠ 0 := div_ne_zero hL1ne hEne
    have ht0pos : 0 < (L + 1) / E := div_pos hL1 hcon
    have hb := hEb ((L + 1) / E) ht0pos
    simp only [pow_two, mul_zero, zero_div, add_zero] at hb
    have hteq : L / ((L + 1) / E) = L * E / (L + 1) := by
      field_simp
    rw [hteq] at hb
    have hb' : E * (L + 1) ≤ L * E := (le_div_iff₀ hL1).mp hb
    have hring : E * (L + 1) = L * E + E := by ring
    rw [hring] at hb'
    have hEle : E ≤ 0 := by linarith [hb']
    linarith [hcon, hEle]
  · rcases eq_or_lt_of_le hL with hL0 | hLpos
    · subst hL0
      rw [mul_zero, Real.sqrt_zero, zero_mul]
      by_contra hcon
      push Not at hcon
      have hR2pos : (0 : ℝ) < R ^ 2 := pow_pos hRpos 2
      have hR2ne : R ^ 2 ≠ 0 := ne_of_gt hR2pos
      have ht0pos : 0 < E / R ^ 2 := div_pos hcon hR2pos
      have hb := hEb (E / R ^ 2) ht0pos
      simp only [zero_div, zero_add] at hb
      have hteq : (E / R ^ 2) * R ^ 2 / 2 = E / 2 := by
        field_simp
      rw [hteq] at hb
      linarith [hcon, hb]
    · set s : ℝ := Real.sqrt (2 * L) with hs
      have h2Lpos : (0 : ℝ) < 2 * L := by linarith [hLpos]
      have h2Lnn : (0 : ℝ) ≤ 2 * L := le_of_lt h2Lpos
      have hspos : 0 < s := by
        rw [hs]
        exact Real.sqrt_pos.mpr h2Lpos
      have hsq : s ^ 2 = 2 * L := by
        rw [hs]
        exact Real.sq_sqrt h2Lnn
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hRne : R ≠ 0 := ne_of_gt hRpos
      have hdiv : s / R ≠ 0 := div_ne_zero hsne hRne
      have ht0pos : 0 < s / R := div_pos hspos hRpos
      have hb := hEb (s / R) ht0pos
      have hs2 : L = s ^ 2 / 2 := by
        rw [hsq]
        ring
      have key : L * R / s = s * R / 2 := by
        have htmp : (s ^ 2 / 2) * R / s = s * R / 2 := by
          field_simp
        rwa [← hs2] at htmp
      have e1 : L / (s / R) = L * R / s := by
        field_simp
      have e2 : (s / R) * R ^ 2 / 2 = s * R / 2 := by
        field_simp
      have heq : L / (s / R) + (s / R) * R ^ 2 / 2 = s * R := by
        calc L / (s / R) + (s / R) * R ^ 2 / 2 = L * R / s + s * R / 2 := by rw [e1, e2]
          _ = s * R / 2 + s * R / 2 := by rw [key]
          _ = s * R := by ring
      rw [heq] at hb
      exact hb

/-- Massart's finite-class lemma: the expected supremum of a
Rademacher process indexed by a finite set `S` of vectors is at most
`√(2 log |S|)` times the largest Euclidean norm in `S`. The left side
is the uniform average over all sign vectors. -/
theorem massart_finite_class {m : ℕ} {S : Finset (Fin m → ℝ)} (hS : S.Nonempty) :
    (∑ σ : Fin m → Bool,
      S.sup' hS (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) / 2 ^ m ≤
    Real.sqrt (2 * Real.log S.card) *
      S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2)) := by
  have hR : 0 ≤ S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2)) := by
    have hScopy := hS
    obtain ⟨v0, hv0⟩ := hScopy
    have h2 : Real.sqrt (∑ i, v0 i ^ 2)
        ≤ S.sup' hS (fun v => Real.sqrt (∑ i, v i ^ 2)) :=
      Finset.le_sup' (fun v => Real.sqrt (∑ i, v i ^ 2)) hv0
    exact le_trans (Real.sqrt_nonneg _) h2
  have hc1N : 1 ≤ S.card := by
    have h := Finset.card_pos.mpr hS
    omega
  have hc1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hc1N
  have hL : 0 ≤ Real.log S.card := Real.log_nonneg hc1
  exact optimize hR hL (fun t ht => mgf_bound hS t ht)
