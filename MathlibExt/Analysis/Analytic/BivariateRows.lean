/-
Copyright 2026 Anthropic, PBC

Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0

Adapted from Fermat's Last Theorem in Lean 4, source revision
6e837e75355538c7f80bab5b956861e86c4eacc2:
Source path (join the following two lines):
P2M/Sol/S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_
and_tsum_mul_eval_eq_of_tsum_mul_eval_eq.lean
The source's NOTICE attributes this development to Anthropic, PBC; no
individual author is identified there. The analytic helpers and row proof
are adapted from that file. Mathlib results are used by import, not copied.
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial numerators of rows of a bivariate series

The first denominator may vanish, even identically. A second denominator
nonzero at zero gives a single second-variable radius valid for every
complex first coordinate.
-/

open Finset FormalMultilinearSeries
open scoped Topology NNReal ENNReal

/-- The reciprocal of a polynomial nonzero at zero has an absolutely
convergent scalar series on a positive disk. -/
private theorem inv_poly_series (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0) :
    ∃ (c : ℕ → ℂ) (R : ℝ), 0 < R ∧
      (∀ Y : ℂ, ‖Y‖ < R → D.eval Y ≠ 0) ∧
      ∀ Y : ℂ, ‖Y‖ < R →
        Summable (fun n => ‖c n * Y ^ n‖) ∧
          ∑' n, c n * Y ^ n = (D.eval Y)⁻¹ := by
  have hcont : ContinuousAt (fun Y : ℂ => D.eval Y) 0 :=
    D.differentiable.continuous.continuousAt
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hcont.eventually_ne hD)
  have hne : ∀ Y : ℂ, ‖Y‖ ≤ ε / 2 → D.eval Y ≠ 0 := fun Y hY =>
    hball Y (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  let R : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hRpos : 0 < R := by
    rw [← NNReal.coe_lt_coe]
    exact half_pos hε
  let f : ℂ → ℂ := fun Y => (D.eval Y)⁻¹
  have hdiff : DifferentiableOn ℂ f
      (closure (Metric.ball (0 : ℂ) R)) := by
    refine D.differentiable.differentiableOn.inv ?_
    intro Y hY
    have hY' := Metric.closure_ball_subset_closedBall hY
    rw [Metric.mem_closedBall, dist_zero_right] at hY'
    exact hne Y hY'
  have hps := hdiff.diffContOnCl.hasFPowerSeriesOnBall hRpos
  refine ⟨fun n => (cauchyPowerSeries f 0 R).coeff n, ε / 2,
    half_pos hε, fun Y hY => hne Y hY.le, fun Y hY => ?_⟩
  have hYR : ‖Y‖₊ < R := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact hY
  have hYball : Y ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    exact hYR
  have hterm (n : ℕ) : (cauchyPowerSeries f 0 R n fun _ => Y) =
      (cauchyPowerSeries f 0 R).coeff n * Y ^ n := by
    rw [apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  constructor
  · exact ((cauchyPowerSeries f 0 R).summable_norm_apply
      (Metric.eball_subset_eball hps.r_le hYball)).congr
        fun n => by rw [hterm]
  · rw [show (∑' n, (cauchyPowerSeries f 0 R).coeff n * Y ^ n) =
        ∑' n, cauchyPowerSeries f 0 R n fun _ => Y from
          tsum_congr fun n => (hterm n).symm,
      (hps.hasSum hYball).tsum_eq, zero_add]

private theorem poly_decomp (P : MvPolynomial (Fin 2) ℂ) :
    ∃ (d : ℕ) (pc : ℕ → Polynomial ℂ), (∀ i, d < i → pc i = 0) ∧
      ∀ X Y : ℂ, MvPolynomial.eval ![X, Y] P =
        ∑ i ∈ range (d + 1), (pc i).eval X * Y ^ i := by
  classical
  refine ⟨P.support.sup (fun s => s 1),
    fun i => ∑ s ∈ P.support with s 1 = i,
      Polynomial.monomial (s 0) (P.coeff s), ?_, ?_⟩
  · intro i hi
    refine Finset.sum_eq_zero fun s hs => ?_
    exfalso
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    have := Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s 1) hs1
    omega
  · intro X Y
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, Finset.sum_mul]
    symm
    calc ∑ i ∈ range (P.support.sup (fun s => s 1) + 1),
            ∑ s ∈ P.support with s 1 = i,
              P.coeff s * X ^ (s 0) * Y ^ i
        = ∑ i ∈ range (P.support.sup (fun s => s 1) + 1),
            ∑ s ∈ P.support with s 1 = i,
              P.coeff s * X ^ (s 0) * Y ^ (s 1) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun s hs => ?_
          rw [(Finset.mem_filter.mp hs).2]
      _ = ∑ s ∈ P.support,
          P.coeff s * X ^ (s 0) * Y ^ (s 1) := by
          refine Finset.sum_fiberwise_of_maps_to (fun s hs => ?_) _
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le
            (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s 1) hs))
      _ = ∑ s ∈ P.support,
          P.coeff s * (X ^ (s 0) * Y ^ (s 1)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          ring

private theorem rows (A : ℕ × ℕ → ℂ) (X z : ℂ)
    (hS : Summable fun m : ℕ × ℕ => ‖A m * X ^ m.1 * z ^ m.2‖) :
    (∀ j, Summable fun m => ‖A (m, j) * X ^ m * z ^ j‖) ∧
    Summable (fun j => ‖(∑' m, A (m, j) * X ^ m) * z ^ j‖) ∧
    ∑' j, (∑' m, A (m, j) * X ^ m) * z ^ j =
      ∑' m, A m * X ^ m.1 * z ^ m.2 := by
  let g : ℕ × ℕ → ℂ := fun p => A (p.2, p.1) * X ^ p.2 * z ^ p.1
  have hgn : Summable fun p => ‖g p‖ :=
    ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hS).congr fun _ => rfl
  have hg : Summable g := hgn.of_norm
  have hrow (j : ℕ) : HasSum (fun m => g (j, m)) (∑' m, g (j, m)) :=
    (hg.prod_factor j).hasSum
  have hfib := hg.hasSum.prod_fiberwise hrow
  have hswap : ∑' p, g p = ∑' m, A m * X ^ m.1 * z ^ m.2 :=
    (Equiv.prodComm ℕ ℕ).tsum_eq
      (fun m : ℕ × ℕ => A m * X ^ m.1 * z ^ m.2)
  have hinner (j : ℕ) : ∑' m, g (j, m) =
      (∑' m, A (m, j) * X ^ m) * z ^ j := by
    dsimp [g]
    exact tsum_mul_right
  refine ⟨fun j => hgn.prod_factor j, ?_, ?_⟩
  · have hN : Summable fun j => ∑' m, ‖g (j, m)‖ := hgn.prod
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => ?_) hN
    rw [← hinner]
    exact norm_tsum_le_tsum_norm (hgn.prod_factor j)
  · simp_rw [← hinner]
    rw [hfib.tsum_eq, hswap]

private theorem coeff_unique (a b : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖a n * z ^ n‖)
    (hb : ∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖b n * z ^ n‖)
    (hab : ∀ z : ℂ, ‖z‖ < ρ →
      ∑' n, a n * z ^ n = ∑' n, b n * z ^ n) : a = b := by
  have hrad (e : ℕ → ℂ)
      (he : ∀ z : ℂ, ‖z‖ < ρ → Summable fun n => ‖e n * z ^ n‖) :
      0 < (ofScalars ℂ e).radius := by
    let ρ' : ℝ≥0 := ⟨ρ / 2, (half_pos hρ).le⟩
    have hρ'pos : 0 < ρ' := by
      rw [← NNReal.coe_pos]
      exact half_pos hρ
    have hz : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      linarith
    have hle : (ρ' : ℝ≥0∞) ≤ (ofScalars ℂ e).radius := by
      refine le_radius_of_summable (p := ofScalars ℂ e) (r := ρ')
        ((he _ hz).congr fun n => ?_)
      rw [ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      rfl
    exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hρ'pos) hle
  have hpa := ((ofScalars ℂ a).hasFPowerSeriesOnBall
    (hrad a ha)).hasFPowerSeriesAt
  have hpb := ((ofScalars ℂ b).hasFPowerSeriesOnBall
    (hrad b hb)).hasFPowerSeriesAt
  have heq : ∀ᶠ z in nhds (0 : ℂ),
      (ofScalars ℂ a).sum z = (ofScalars ℂ b).sum z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) hρ)
      fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right] at hz
    change ofScalarsSum a z = ofScalarsSum b z
    rw [ofScalars_sum_eq, ofScalars_sum_eq]
    simp only [smul_eq_mul]
    exact hab z hz
  exact ofScalars_series_injective ℂ ℂ
    (hpa.eq_formalMultilinearSeries_of_eventually hpb heq)

private theorem row_numerators (D : Polynomial ℂ)
    (P : MvPolynomial (Fin 2) ℂ) (hD : D.eval 0 ≠ 0) :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      (∀ Y : ℂ, ‖Y‖ < R → D.eval Y ≠ 0) ∧
      ∀ X Y : ℂ, ‖Y‖ < R →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D.eval Y =
          MvPolynomial.eval ![X, Y] P := by
  classical
  obtain ⟨c, R, hR, hDne, hc⟩ := inv_poly_series D hD
  obtain ⟨d, pc, hpc0, hP⟩ := poly_decomp P
  refine ⟨fun j => ∑ i ∈ range (j + 1),
    pc i * Polynomial.C (c (j - i)), R, hR, hDne, ?_⟩
  intro X Y hY
  obtain ⟨hcs, hct⟩ := hc Y hY
  have hu0 (i : ℕ) (hi : i ∉ range (d + 1)) :
      (pc i).eval X * Y ^ i = 0 := by
    rw [hpc0 i (by simpa using hi), Polynomial.eval_zero, zero_mul]
  have hus : Summable (fun i => ‖(pc i).eval X * Y ^ i‖) :=
    (hasSum_sum_of_ne_finset_zero (s := range (d + 1))
      (f := fun i => ‖(pc i).eval X * Y ^ i‖)
      (fun i hi => by simp only [hu0 i hi, norm_zero])).summable
  have hut : ∑' i, (pc i).eval X * Y ^ i =
      MvPolynomial.eval ![X, Y] P := by
    rw [(hasSum_sum_of_ne_finset_zero
      (s := range (d + 1)) hu0).tsum_eq, hP]
  have hqj (j : ℕ) :
      (∑ i ∈ range (j + 1),
        pc i * Polynomial.C (c (j - i))).eval X * Y ^ j =
      ∑ i ∈ range (j + 1),
        ((pc i).eval X * Y ^ i) * (c (j - i) * Y ^ (j - i)) := by
    rw [Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      ← pow_mul_pow_sub Y hij]
    ring
  have hnorm := summable_norm_sum_mul_range_of_summable_norm
    (f := fun i => (pc i).eval X * Y ^ i)
    (g := fun l => c l * Y ^ l) hus hcs
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (f := fun i => (pc i).eval X * Y ^ i)
    (g := fun l => c l * Y ^ l) hus hcs
  refine ⟨hnorm.congr (fun j => by rw [hqj]), ?_⟩
  simp_rw [hqj]
  rw [← hprod, hut, hct, mul_assoc, inv_mul_cancel₀ (hDne Y hY),
    mul_one]

/-- The rows of an absolutely convergent bivariate series with separated
polynomial denominators have polynomial numerators. The second denominator
must be nonzero at zero; there is no nonvanishing condition on the first.
The second-variable radius is uniform over all complex first coordinates. -/
public theorem MvPolynomial.exists_polynomial_rows
    (A : ℕ × ℕ → ℂ) (D₁ D₂ : Polynomial ℂ)
    (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hD₂ : D₂.eval 0 ≠ 0) (hr : 0 < r)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A m * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A m * X ^ m.1 * Y ^ m.2) *
        (D₁.eval X * D₂.eval Y) = MvPolynomial.eval ![X, Y] P) :
    ∃ (q : ℕ → Polynomial ℂ) (r₂ : ℝ), 0 < r₂ ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
        Summable (fun m : ℕ => ‖A (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, A (m, j) * X ^ m) * D₁.eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < r₂ →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D₂.eval Y =
          MvPolynomial.eval ![X, Y] P) := by
  obtain ⟨q, R, hR, hD₂ne, hII⟩ := row_numerators D₂ P hD₂
  refine ⟨q, R, hR, ?_, hII⟩
  intro j X hX
  have hY₀ : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  have hY₀ne : ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (half_pos hr).ne'
  obtain ⟨hrows0, -, -⟩ := rows A X _ (h X _ hX hY₀).1
  have hrow : Summable (fun m : ℕ => ‖A (m, j) * X ^ m‖) := by
    refine ((hrows0 j).mul_right
      (‖((r / 2 : ℝ) : ℂ) ^ j‖⁻¹)).congr fun m => ?_
    rw [norm_mul, mul_assoc, mul_inv_cancel₀ (by
      rw [norm_pow]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hY₀ne)), mul_one]
  refine ⟨hrow, ?_⟩
  let a : ℕ → ℂ := fun n => (∑' m, A (m, n) * X ^ m) * D₁.eval X
  have hEA : ∀ z : ℂ, ‖z‖ < min r R →
      Summable (fun n => ‖a n * z ^ n‖) ∧
      (∑' n, a n * z ^ n) * D₂.eval z =
        MvPolynomial.eval ![X, z] P := by
    intro z hz
    obtain ⟨hS, hE⟩ := h X z hX (lt_of_lt_of_le hz (min_le_left _ _))
    obtain ⟨-, hN, hT⟩ := rows A X z hS
    constructor
    · refine (hN.mul_right ‖D₁.eval X‖).congr fun n => ?_
      dsimp [a]
      simp only [norm_mul]
      ring
    · have ht : (∑' n, a n * z ^ n) =
          (∑' n, (∑' m, A (m, n) * X ^ m) * z ^ n) * D₁.eval X := by
        rw [← tsum_mul_right]
        refine tsum_congr fun n => ?_
        dsimp [a]
        ring
      rw [ht, hT, mul_assoc, hE]
  have hab : a = fun n => (q n).eval X :=
    coeff_unique a (fun n => (q n).eval X) (min r R) (lt_min hr hR)
      (fun z hz => (hEA z hz).1)
      (fun z hz => (hII X z (lt_of_lt_of_le hz (min_le_right _ _))).1)
      (fun z hz => mul_right_cancel₀
        (hD₂ne z (lt_of_lt_of_le hz (min_le_right _ _)))
        ((hEA z hz).2.trans
          (hII X z (lt_of_lt_of_le hz (min_le_right _ _))).2.symm))
  exact congrFun hab j
