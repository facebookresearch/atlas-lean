/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! # Rademacher averages of a finite class

The empirical Rademacher average of a nonempty finite class of
Boolean functions on `m` sample points is at most
`√(2 log |H| / m)`: Massart's finite-class lemma specialized to
`±1`-valued vectors. This is the symmetrization input of roadmap
package ML-08 of the Atlas TCS canon roadmap; the generalization
theorem built on it is a follow-up. The general Massart lemma lives
in `MathlibExt/Probability/Rademacher.lean`.

Source: Shalev-Shwartz and Ben-David, Understanding Machine
Learning (2014), Lemma 26.2 (Massart).
-/

open Finset

/-- Number of sign patterns on `m` points. -/
private lemma card_fun_bool (m : ℕ) : Fintype.card (Fin m → Bool) = 2 ^ m := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- One-coordinate exponential sum equals `2 cosh t`, uniformly in `h i`. -/
private lemma per_coord_sum (t : ℝ) (m : ℕ) (h : Fin m → Bool) (i : Fin m) :
    (∑ b : Bool, Real.exp (t * ((if b then (1 : ℝ) else -1) *
      (if h i then (1 : ℝ) else -1)))) = 2 * Real.cosh t := by
  rw [Fintype.sum_bool]
  by_cases hb : h i = true
  · simp [hb, Real.cosh_eq]
    ring
  · simp [hb, Real.cosh_eq]
    ring

/-- MGF bound for a single `h`: the exponential moment factorizes over
coordinates, each contributing `2 cosh t ≤ 2 exp (t²/2)`. -/
private lemma mgf_per_h (t : ℝ) (m : ℕ) (h : Fin m → Bool) :
    (∑ σ : Fin m → Bool, Real.exp (t * (∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))) ≤
    (2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) := by
  have hterm : ∀ σ : Fin m → Bool, Real.exp (t * (∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) =
      ∏ i, Real.exp (t * ((if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1))) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
  simp only [hterm]
  have hfac := Fintype.prod_sum (fun (i : Fin m) (b : Bool) =>
    Real.exp (t * ((if b then (1 : ℝ) else -1) *
      (if h i then (1 : ℝ) else -1))))
  rw [← hfac]
  simp only [per_coord_sum]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcosh : Real.cosh t ≤ Real.exp (t ^ 2 / 2) :=
    Real.cosh_le_exp_half_sq t
  have hle : (2 : ℝ) * Real.cosh t ≤ 2 * Real.exp (t ^ 2 / 2) := by linarith
  have h0 : (0 : ℝ) ≤ 2 * Real.cosh t := by
    have hc := Real.cosh_pos t
    linarith
  have hpow := pow_le_pow_left₀ h0 hle m
  have hexp : ((2 : ℝ) * Real.exp (t ^ 2 / 2)) ^ m =
      (2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  exact hpow.trans hexp.le

/-- Jensen for `exp` over the uniform average on sign patterns. -/
private lemma exp_uniform_avg_le (m : ℕ) (t : ℝ) (Y : (Fin m → Bool) → ℝ) :
    Real.exp (t * ((∑ σ, Y σ) / (2 ^ m : ℝ))) ≤
    (∑ σ, Real.exp (t * Y σ)) / (2 ^ m : ℝ) := by
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 ^ m : ℝ) := by
    rw [card_fun_bool]
    norm_cast
  have h2mpos : (0 : ℝ) < 2 ^ m := by positivity
  have hcardpos : (0 : ℝ) < Fintype.card (Fin m → Bool) := by
    rw [hcard]
    exact h2mpos
  have hcardne : (Fintype.card (Fin m → Bool) : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin m → Bool)),
      0 ≤ ((Fintype.card (Fin m → Bool) : ℝ))⁻¹ := by
    intro i _
    exact inv_nonneg.mpr (le_of_lt hcardpos)
  have hw1 : (∑ _i ∈ (Finset.univ : Finset (Fin m → Bool)),
      ((Fintype.card (Fin m → Bool) : ℝ))⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcardne]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin m → Bool)),
      t * Y i ∈ (Set.univ : Set ℝ) := fun i _ => Set.mem_univ _
  have hJ := ConvexOn.map_sum_le convexOn_exp (t := Finset.univ)
    (w := fun _ => ((Fintype.card (Fin m → Bool) : ℝ))⁻¹)
    (p := fun σ => t * Y σ) hw0 hw1 hmem
  have hLHS : (∑ i ∈ (Finset.univ : Finset (Fin m → Bool)),
      (((Fintype.card (Fin m → Bool) : ℝ))⁻¹) • (t * Y i)) =
      t * ((∑ σ, Y σ) / (2 ^ m : ℝ)) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    rw [hcard, div_eq_mul_inv]
    ring
  have hRHS : (∑ i ∈ (Finset.univ : Finset (Fin m → Bool)),
      (((Fintype.card (Fin m → Bool) : ℝ))⁻¹) • Real.exp (t * Y i)) =
      (∑ σ, Real.exp (t * Y σ)) / (2 ^ m : ℝ) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    rw [hcard, div_eq_mul_inv]
    ring
  rw [hLHS, hRHS] at hJ
  exact hJ

/-- Combined MGF inequality: `t * avg ≤ log |H| + m * t²/2` for all `t`. -/
private lemma mgf_inequality (m : ℕ) (H : Finset (Fin m → Bool)) (hH : H.Nonempty)
    (t : ℝ) :
    t * ((∑ σ : Fin m → Bool, H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) /
      (2 ^ m : ℝ)) ≤
    Real.log H.card + (m : ℝ) * (t ^ 2 / 2) := by
  have h2mpos : (0 : ℝ) < 2 ^ m := by positivity
  have hJ : Real.exp (t * ((∑ σ : Fin m → Bool, H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) /
      (2 ^ m : ℝ))) ≤
      (∑ σ : Fin m → Bool, Real.exp (t * H.sup' hH (fun h => ∑ i,
        ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))) /
      (2 ^ m : ℝ) :=
    exp_uniform_avg_le m t (fun σ => H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))
  have hper : ∀ σ ∈ (Finset.univ : Finset (Fin m → Bool)),
      Real.exp (t * H.sup' hH (fun h => ∑ i,
        ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) ≤
      ∑ h ∈ H, Real.exp (t * (∑ i,
        ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) := by
    intro σ _
    obtain ⟨hstar, hhstar, hsup⟩ := Finset.exists_mem_eq_sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))
    have hnn : ∀ h ∈ H, (0 : ℝ) ≤ Real.exp (t * (∑ i,
        ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) :=
      fun h _ => le_of_lt (Real.exp_pos _)
    rw [hsup]
    exact Finset.single_le_sum hnn hhstar
  have hperH : ∀ h ∈ H, (∑ σ : Fin m → Bool, Real.exp (t * (∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))) ≤
      (2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) :=
    fun h _ => mgf_per_h t m h
  have hcombined : (∑ σ : Fin m → Bool, Real.exp (t * H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))) ≤
      (H.card : ℝ) * ((2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2))) := by
    calc (∑ σ : Fin m → Bool, Real.exp (t * H.sup' hH (fun h => ∑ i,
              ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))))
          ≤ ∑ σ : Fin m → Bool, ∑ h ∈ H, Real.exp (t * (∑ i,
            ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) :=
            Finset.sum_le_sum hper
        _ = ∑ h ∈ H, ∑ σ : Fin m → Bool, Real.exp (t * (∑ i,
            ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) :=
            Finset.sum_comm
        _ ≤ ∑ _h ∈ H, ((2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2))) :=
            Finset.sum_le_sum hperH
        _ = (H.card : ℝ) * ((2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hdiv : (∑ σ : Fin m → Bool, Real.exp (t * H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1))))) /
      (2 ^ m : ℝ) ≤ (H.card : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) := by
    rw [div_le_iff₀ h2mpos]
    calc (∑ σ : Fin m → Bool, Real.exp (t * H.sup' hH (fun h => ∑ i,
              ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))))
          ≤ (H.card : ℝ) * ((2 ^ m : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2))) :=
            hcombined
        _ = ((H.card : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2))) * 2 ^ m := by ring
  have hexp_le : Real.exp (t * ((∑ σ : Fin m → Bool, H.sup' hH (fun h => ∑ i,
      ((if σ i then (1 : ℝ) else -1) * (if h i then (1 : ℝ) else -1)))) /
      (2 ^ m : ℝ))) ≤ (H.card : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) :=
    hJ.trans hdiv
  have hcardpos : (0 : ℝ) < H.card := by
    have h1 : 0 < H.card := Finset.card_pos.mpr hH
    exact Nat.cast_pos.mpr h1
  have hpos : (0 : ℝ) < (H.card : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 / 2)) :=
    mul_pos hcardpos (Real.exp_pos _)
  have hlog := (Real.le_log_iff_exp_le hpos).mpr hexp_le
  rw [Real.log_mul (ne_of_gt hcardpos) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp] at hlog
  exact hlog

/-- Finite-class Rademacher bound: for a nonempty finite class `H`
of Boolean functions on `m` sample points (each `h : Fin m → Bool`
read through its values on the sample, encoded as `±1`), the
empirical Rademacher average is at most `√(2 log |H| / m)`. -/
theorem rademacher_finite_class {m : ℕ} (hm : 0 < m)
    {H : Finset (Fin m → Bool)} (hH : H.Nonempty) :
    (∑ σ : Fin m → Bool,
      H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1))) / 2 ^ m / m ≤
    Real.sqrt (2 * Real.log H.card / m) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmnonneg : (0 : ℝ) ≤ m := le_of_lt hmpos
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hcard1 : 1 ≤ H.card := Finset.card_pos.mpr hH
  have hLnonneg : (0 : ℝ) ≤ Real.log H.card := by
    apply Real.log_nonneg
    exact_mod_cast hcard1
  by_cases hA : (∑ σ : Fin m → Bool,
      H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1))) / 2 ^ m ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hA hmnonneg).trans (Real.sqrt_nonneg _)
  · push Not at hA
    set u : ℝ := (∑ σ : Fin m → Bool,
      H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1))) / 2 ^ m / m with hu
    have hMGF : u * ((∑ σ : Fin m → Bool,
        H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ m) ≤
        Real.log H.card + (m : ℝ) * (u ^ 2 / 2) :=
      mgf_inequality m H hH u
    have hAu : (∑ σ : Fin m → Bool,
        H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ m = u * (m : ℝ) := by
      rw [hu]
      exact (div_mul_cancel₀ _ hmne).symm
    have e1 : u * ((∑ σ : Fin m → Bool,
        H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ m) = u ^ 2 * (m : ℝ) := by
      rw [hAu]
      ring
    rw [e1] at hMGF
    have h2 : u ^ 2 * (m : ℝ) / 2 ≤ Real.log H.card := by linarith
    have hupos : (0 : ℝ) < u := by
      rw [hu]
      exact div_pos hA hmpos
    have htnonneg : (0 : ℝ) ≤ u := le_of_lt hupos
    have hrhsnonneg : (0 : ℝ) ≤ 2 * Real.log H.card / (m : ℝ) := by
      apply div_nonneg _ hmnonneg
      linarith
    rw [Real.le_sqrt htnonneg hrhsnonneg]
    rw [le_div_iff₀ hmpos]
    linarith
