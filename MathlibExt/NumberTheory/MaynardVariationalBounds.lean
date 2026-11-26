/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GPYMaynardSieveReduction
import MathlibExt.Probability.Distributions.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.Tuple

/-!
# `M₁₀₅ > 4`

Maynard's Proposition 4.3(2) (J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015),
383-413; numbering of arXiv:1311.4600v3): the variational quantity
`MathlibExt.NumberTheory.GPYMaynard.maynardM` satisfies `M₁₀₅ > 4` (`four_lt_maynardM_105`).
That definition takes the supremum over bounded measurable profiles vanishing off the simplex, a
class containing an a.e.-equivalent, with the same `I_k` and `J_k^{(m)}`, of each of Maynard's
Riemann-integrable profiles; the two suprema agree because `I_k` and every `J_k^{(m)}` are
continuous for the `L²` norm on the simplex and Riemann-integrable profiles are dense there.

## Proof

Maynard (Section 8, display (8.15)) takes for `F` a polynomial in `∑ tᵢ` and `∑ tᵢ²`, a linear
combination of the `42` monomials `(1 - ∑ tᵢ)ᵇ (∑ tᵢ²)ᶜ` with `b + 2c ≤ 11` whose coefficients come
from a computer eigenvector calculation, and finds that the largest ratio on this family is
`4.0020697…`. We use instead the profile `Φ(t) = ∏ᵢ tᵢ^(-2/5) (1 - ∑ᵢ tᵢ)` on the open simplex
`Δ = {t ∈ ℝ¹⁰⁵ : tᵢ > 0, ∑ tᵢ < 1}`, whose functionals are Dirichlet integrals
(`ProbabilityTheory.lintegral_dirichletDensity`):

* `I₁₀₅(Φ) = ∫_Δ ∏ tᵢ^(-4/5) (1 - ∑ tᵢ)² dt = Γ(1/5)¹⁰⁵ Γ(3) / Γ(24)`;
* along each line in the direction `m`,
  `∫₀¹ Φ dtₘ = (25/24) ∏_{i ≠ m} tᵢ^(-2/5) (1 - ∑_{i ≠ m} tᵢ)^(8/5)`, so
  `J₁₀₅^{(m)}(Φ) = (625/576) Γ(1/5)¹⁰⁴ Γ(21/5) / Γ(25)`.

Since `Γ(21/5) = (1056/625) Γ(1/5)`, the ratio `(∑ₘ J₁₀₅^{(m)}(Φ)) / I₁₀₅(Φ)` is
`1155/288 > 4`. The profile `Φ` is unbounded, so we pass to the bounded truncations `min(Φ, M)`:
`I₁₀₅` can only decrease, and each `J₁₀₅^{(m)}` converges by dominated convergence, so some
truncation is an admissible profile with ratio above `4`. Finally `J_k^{(m)}(F) ≤ I_k(F)` for
bounded measurable `F` (Cauchy–Schwarz in `tₘ`, then Fubini), so the ratios are bounded by `k` and
the supremum `M_k` is not Mathlib's junk value `0`.
-/

@[expose] public section

namespace WantedExt.NumberTheory.MaynardVariationalBounds

open MathlibExt.NumberTheory.GPYMaynard MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

/-- The unbounded test function `∏ xᵢ^(-2/5) (1 - ∑ xᵢ)` on the open simplex. -/
private noncomputable def testFn {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  if (∀ i, 0 < x i) ∧ ∑ i, x i < 1 then (∏ i, x i ^ (-(2 / 5 : ℝ))) * (1 - ∑ i, x i) else 0

/-- Dirichlet parameters `(1/5, …, 1/5, a)`. -/
private noncomputable def dirParam (N : ℕ) (a : ℝ) : Fin (N + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (fun _ => (1 / 5 : ℝ)) a

private theorem dirParam_pos (N : ℕ) {a : ℝ} (ha : 0 < a) (i : Fin (N + 1)) :
    0 < dirParam N a i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [dirParam] using ha
  · simp [dirParam]

private theorem ofReal_testFn_sq {N : ℕ} (x : Fin N → ℝ) :
    ENNReal.ofReal (testFn x ^ 2) = dirichletDensity (dirParam N 3) x := by
  unfold testFn dirichletDensity dirParam
  split_ifs with h
  · congr 1
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (h.1 i).le]
      norm_num
    · rw [← Real.rpow_natCast]
      norm_num
  · simp

private theorem multiBeta_dirParam (N : ℕ) (a : ℝ) :
    multiBeta (dirParam N a) =
      Real.Gamma (1 / 5) ^ N * Real.Gamma a / Real.Gamma (N / 5 + a) := by
  unfold multiBeta dirParam
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf

private theorem mem_Icc_of_simplex {N : ℕ} {x : Fin N → ℝ}
    (h : (∀ i, 0 < x i) ∧ ∑ i, x i < 1) : x ∈ Icc (0 : Fin N → ℝ) 1 := by
  refine ⟨fun i => (h.1 i).le, fun i => ?_⟩
  have := Finset.single_le_sum (fun j _ => (h.1 j).le) (Finset.mem_univ i)
  simp only [Pi.one_apply]
  linarith [h.2]

private theorem testFn_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ testFn x := by
  unfold testFn
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (h.1 i).le _)
      (by linarith [h.2])
  · exact le_rfl

private theorem measurable_testFn (N : ℕ) : Measurable (testFn (N := N)) := by
  refine Measurable.ite (measurableSet_cornerSimplex N) ?_ measurable_const
  fun_prop

private theorem integral_testFn_sq (N : ℕ) :
    ∫ x in Icc (0 : Fin N → ℝ) 1, testFn x ^ 2 = multiBeta (dirParam N 3) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
  · have h1 : ∀ x : Fin N → ℝ, testFn x ^ 2 = (dirichletDensity (dirParam N 3) x).toReal :=
      fun x => by rw [← ofReal_testFn_sq, ENNReal.toReal_ofReal (sq_nonneg _)]
    simp_rw [h1]
    rw [integral_toReal (measurable_dirichletDensity _).aemeasurable
      (ae_of_all _ fun x => by rw [← ofReal_testFn_sq]; exact ENNReal.ofReal_lt_top),
      lintegral_dirichletDensity (dirParam_pos N (by norm_num)),
      ENNReal.toReal_ofReal (multiBeta_pos (dirParam_pos N (by norm_num)) (by omega)).le]
  · unfold testFn
    rw [ite_eq_right fun h => hx (mem_Icc_of_simplex h)]
    simp

/-- The profile of the inner integral: `∏ yⱼ^(-2/5) (1 - ∑ yⱼ)^(8/5)` on the open simplex. -/
private noncomputable def psi {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  if (∀ j, 0 < y j) ∧ ∑ j, y j < 1 then
    (∏ j, y j ^ (-(2 / 5 : ℝ))) * (1 - ∑ j, y j) ^ (8 / 5 : ℝ) else 0

private theorem testFn_insertNth {n : ℕ} (m : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    testFn (Fin.insertNth m t y) =
      if (0 < t ∧ ∀ j, 0 < y j) ∧ t + ∑ j, y j < 1 then
        t ^ (-(2 / 5 : ℝ)) * (∏ j, y j ^ (-(2 / 5 : ℝ))) * (1 - (t + ∑ j, y j)) else 0 := by
  unfold testFn
  simp only [Fin.forall_iff_succAbove m, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Fin.sum_univ_succAbove _ m, Fin.prod_univ_succAbove _ m]

private theorem rpow_three_fifths {t : ℝ} (ht : 0 ≤ t) :
    t ^ (3 / 5 : ℝ) = t ^ (-(2 / 5 : ℝ)) * t := by
  rw [← Real.rpow_add_one' ht (by norm_num)]
  norm_num

private theorem testFn_insertNth_of_not {n : ℕ} (m : Fin (n + 1)) (y : Fin n → ℝ)
    (hy : ¬((∀ j, 0 < y j) ∧ ∑ j, y j < 1)) (t : ℝ) : testFn (Fin.insertNth m t y) = 0 := by
  rw [testFn_insertNth, ite_eq_right]
  rintro ⟨⟨ht, hpos⟩, hsum⟩
  exact hy ⟨hpos, by linarith⟩

/-- The line integral of the test function: for `y` in the open simplex,
`∫₀¹ testFn (insertNth m t y) dt = (25/24) ∏ yⱼ^(-2/5) (1 - ∑ yⱼ)^(8/5)`. -/
private theorem integral_testFn_insertNth {n : ℕ} (m : Fin (n + 1)) (y : Fin n → ℝ) :
    IntervalIntegrable (fun t => testFn (Fin.insertNth m t y)) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, testFn (Fin.insertNth m t y) = 25 / 24 * psi y := by
  by_cases hy : (∀ j, 0 < y j) ∧ ∑ j, y j < 1
  · set c := ∏ j, y j ^ (-(2 / 5 : ℝ)) with hc
    set w := 1 - ∑ j, y j with hw
    have hw0 : 0 < w := by rw [hw]; linarith [hy.2]
    have hsum0 : 0 ≤ ∑ j, y j := Finset.sum_nonneg fun j _ => (hy.1 j).le
    have hw1 : w ≤ 1 := by rw [hw]; linarith
    have key : ∀ t, testFn (Fin.insertNth m t y) =
        if 0 < t ∧ t < w then c * (t ^ (-(2 / 5 : ℝ)) * (w - t)) else 0 := by
      intro t
      rw [testFn_insertNth]
      by_cases ht : 0 < t ∧ t < w
      · rw [ite_eq_left ⟨⟨ht.1, hy.1⟩, by rw [hw] at ht; linarith [ht.2]⟩, ite_eq_left ht, hw]
        ring
      · rw [ite_eq_right ht, ite_eq_right]
        rintro ⟨⟨h1, _⟩, h2⟩
        exact ht ⟨h1, by rw [hw]; linarith⟩
    set g : ℝ → ℝ := fun t => c * w * t ^ (-(2 / 5 : ℝ)) - c * t ^ (3 / 5 : ℝ) with hg
    have hEq1 : EqOn (fun t => testFn (Fin.insertNth m t y)) g (uIcc 0 w) := by
      intro t ht
      rw [uIcc_of_le hw0.le] at ht
      simp only [key, hg]
      split_ifs with h
      · rw [rpow_three_fifths ht.1]
        ring
      · rcases eq_or_lt_of_le ht.1 with h0 | h0
        · subst h0
          rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
          ring
        · have hwt : t = w := le_antisymm ht.2 (not_lt.mp fun h' => h ⟨h0, h'⟩)
          subst hwt
          rw [rpow_three_fifths ht.1]
          ring
    have hEq2 : EqOn (fun t => testFn (Fin.insertNth m t y)) (fun _ => 0) (uIcc w 1) := by
      intro t ht
      rw [uIcc_of_le hw1] at ht
      simp only [key]
      rw [ite_eq_right]
      rintro ⟨_, h⟩
      linarith [ht.1]
    have hgi : IntervalIntegrable g volume 0 w :=
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul (c * w)).sub
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul c)
    have hi1 : IntervalIntegrable (fun t => testFn (Fin.insertNth m t y)) volume 0 w :=
      (intervalIntegrable_congr (hEq1.mono uIoc_subset_uIcc)).mpr hgi
    have hi2 : IntervalIntegrable (fun t => testFn (Fin.insertNth m t y)) volume w 1 :=
      (intervalIntegrable_congr (hEq2.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const
    refine ⟨hi1.trans hi2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      intervalIntegral.integral_congr hEq1, intervalIntegral.integral_congr hEq2,
      intervalIntegral.integral_zero, add_zero, hg,
      intervalIntegral.integral_sub
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul (c * w))
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num)), integral_rpow (Or.inl (by norm_num))]
    have hpsi : psi y = c * w ^ (8 / 5 : ℝ) := by
      unfold psi
      rw [ite_eq_left hy]
    rw [hpsi, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
    have e1 : w ^ (-(2 / 5 : ℝ) + 1) = w ^ (3 / 5 : ℝ) := by norm_num
    have e2 : w ^ ((3 / 5 : ℝ) + 1) = w ^ (3 / 5 : ℝ) * w := Real.rpow_add_one' hw0.le (by norm_num)
    have e3 : w ^ (8 / 5 : ℝ) = w ^ (3 / 5 : ℝ) * w := by
      rw [← e2]
      norm_num
    rw [e1, e2, e3]
    ring
  · have h0 : ∀ t, testFn (Fin.insertNth m t y) = 0 := testFn_insertNth_of_not m y hy
    simp_rw [h0]
    refine ⟨intervalIntegrable_const, ?_⟩
    unfold psi
    rw [ite_eq_right hy]
    simp

/-! ### The unit cube as a product of probability spaces -/

/-- Lebesgue measure on `[0, 1]`. -/
private noncomputable abbrev μ₁ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private theorem isProbabilityMeasure_μ₁ : IsProbabilityMeasure μ₁ :=
  ⟨by simp [Real.volume_Icc]⟩

attribute [local instance] isProbabilityMeasure_μ₁

private theorem restrict_Icc_eq_pi (N : ℕ) :
    volume.restrict (Icc (0 : Fin N → ℝ) 1) = Measure.pi fun _ => μ₁ := by
  have h : Icc (0 : Fin N → ℝ) 1 = Set.univ.pi fun _ => Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]
    rfl
  rw [h, volume_pi, Measure.restrict_pi_pi]

private theorem measurePreserving_removeNth {n : ℕ} (m : Fin (n + 1)) :
    MeasurePreserving (fun x : Fin (n + 1) → ℝ => Fin.removeNth m x)
      (Measure.pi fun _ => μ₁) (Measure.pi fun _ => μ₁) :=
  measurePreserving_snd.comp (measurePreserving_piFinSuccAbove (fun _ => μ₁) m)

private theorem integral_comp_removeNth {n : ℕ} (m : Fin (n + 1)) {K : (Fin n → ℝ) → ℝ}
    (hK : AEStronglyMeasurable K (Measure.pi fun _ => μ₁)) :
    ∫ x, K (Fin.removeNth m x) ∂(Measure.pi fun _ => μ₁) = ∫ y, K y ∂(Measure.pi fun _ => μ₁) := by
  have h := measurePreserving_removeNth m
  rw [← h.map_eq] at hK ⊢
  exact (integral_map h.measurable.aemeasurable hK).symm

/-- Measurability of a line integral in the direction `m`. -/
private theorem stronglyMeasurable_lineIntegral {n : ℕ} (m : Fin (n + 1))
    {H : (Fin (n + 1) → ℝ) → ℝ} (hH : Measurable H) :
    StronglyMeasurable fun x : Fin (n + 1) → ℝ => ∫ t, H (Function.update x m t) ∂μ₁ :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : (Fin (n + 1) → ℝ) × ℝ => H (Function.update p.1 m p.2))
    (hH.comp measurable_update').stronglyMeasurable

/-- Fubini in the direction `m` for a bounded measurable function on the cube. -/
private theorem integral_lineIntegral {n : ℕ} (m : Fin (n + 1)) {G : (Fin (n + 1) → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hC : ∀ x, |G x| ≤ C) :
    ∫ x, (∫ t, G (Function.update x m t) ∂μ₁) ∂(Measure.pi fun _ => μ₁) =
      ∫ x, G x ∂(Measure.pi fun _ => μ₁) := by
  set K : (Fin n → ℝ) → ℝ := fun y => ∫ t, G (Fin.insertNth m t y) ∂μ₁ with hK
  have hKm : StronglyMeasurable K :=
    StronglyMeasurable.integral_prod_right'
      (f := fun p : (Fin n → ℝ) × ℝ => G (Fin.insertNth m p.2 p.1))
      (hG.comp ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm.measurable.comp
        measurable_swap)).stronglyMeasurable
  have h1 : (fun x : Fin (n + 1) → ℝ => ∫ t, G (Function.update x m t) ∂μ₁) =
      fun x => K (Fin.removeNth m x) := by
    funext x
    simp only [hK, Fin.insertNth_removeNth]
  rw [h1, integral_comp_removeNth m hKm.aestronglyMeasurable]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ₁) m
  have h2 := hmp.integral_comp'
    (fun p => G ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h2
  rw [h2, integral_prod_symm]
  · rfl
  · refine Integrable.of_bound ((hG.comp (MeasurableEquiv.measurable _)).aestronglyMeasurable) C
      (ae_of_all _ fun p => ?_)
    simpa [Real.norm_eq_abs] using hC _

/-! ### `J_k^{(m)} ≤ I_k`, so the ratios defining `M_k` are bounded -/

/-- For `f` bounded and measurable, `(∫₀¹ f)² ≤ ∫₀¹ f²`. -/
private theorem sq_integral_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C) :
    (∫ t, f t ∂μ₁) ^ 2 ≤ ∫ t, f t ^ 2 ∂μ₁ := by
  have hfi : Integrable f μ₁ := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hC t)
  have hgi : Integrable ((fun x : ℝ => x ^ 2) ∘ f) μ₁ := Integrable.of_bound
    (hf.pow_const 2).aestronglyMeasurable (C ^ 2) (ae_of_all _ fun t => by
      simp only [Function.comp, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC t) 2)
  exact (even_two.convexOn_pow : ConvexOn ℝ univ fun x : ℝ => x ^ 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _) hfi hgi

private theorem intervalIntegral_eq_μ₁ (f : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, f t = ∫ t, f t ∂μ₁ := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

private theorem maynardJ_eq {n : ℕ} (m : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ) :
    maynardJ (n + 1) m F =
      ∫ x, (∫ t, F (Function.update x m t) ∂μ₁) ^ 2 ∂(Measure.pi fun _ => μ₁) := by
  unfold maynardJ
  simp_rw [intervalIntegral_eq_μ₁]
  rw [restrict_Icc_eq_pi]

private theorem maynardI_eq (N : ℕ) (F : (Fin N → ℝ) → ℝ) :
    maynardI N F = ∫ x, F x ^ 2 ∂(Measure.pi fun _ => μ₁) := by
  unfold maynardI
  rw [restrict_Icc_eq_pi]

/-- **`J_k^{(m)}(F) ≤ I_k(F)`** for bounded measurable `F` (Cauchy–Schwarz in the `m`-th
coordinate, then Fubini). -/
private theorem maynardJ_le_maynardI {n : ℕ} (m : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    maynardJ (n + 1) m F ≤ maynardI (n + 1) F := by
  rw [maynardJ_eq, maynardI_eq]
  have hC2 : ∀ x, |F x ^ 2| ≤ C ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  rw [← integral_lineIntegral m (hF.pow_const 2) hC2]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) ?_ (ae_of_all _ fun x => ?_)
  · refine Integrable.of_bound
      (stronglyMeasurable_lineIntegral m (hF.pow_const 2)).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun x => ?_)
    have h := norm_integral_le_of_norm_le_const (μ := μ₁)
      (f := fun t => F (Function.update x m t) ^ 2) (C := C ^ 2)
      (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hC2 _)
    simpa using h
  · exact sq_integral_le (hF.comp (measurable_update x)) (fun t => hC _)

private theorem maynardRatio_le {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : IsMaynardProfile (n + 1) F) : maynardRatio (n + 1) F ≤ n + 1 := by
  have hI := maynardI_pos hF
  obtain ⟨hFm, ⟨C, hC⟩, -, -, -⟩ := hF
  unfold maynardRatio
  rw [div_le_iff₀ hI]
  calc ∑ m, maynardJ (n + 1) m F ≤ ∑ _m : Fin (n + 1), maynardI (n + 1) F :=
        Finset.sum_le_sum fun m _ => maynardJ_le_maynardI m hFm hC
    _ = (n + 1) * maynardI (n + 1) F := by simp

private theorem bddAbove_maynardRatio (n : ℕ) :
    BddAbove (maynardRatio (n + 1) '' {F | IsMaynardProfile (n + 1) F}) := by
  refine ⟨n + 1, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact maynardRatio_le hF

/-! ### `J_k^{(m)}` of the test function -/

private theorem ofReal_psi_sq {n : ℕ} (y : Fin n → ℝ) :
    ENNReal.ofReal (psi y ^ 2) = dirichletDensity (dirParam n (21 / 5)) y := by
  unfold psi dirichletDensity dirParam
  split_ifs with h
  · congr 1
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (h.1 i).le]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [h.2])]
      norm_num
  · simp

private theorem integrable_psi_sq (n : ℕ) :
    Integrable (fun y : Fin n → ℝ => psi y ^ 2) := by
  have h1 : ∀ y : Fin n → ℝ, psi y ^ 2 = (dirichletDensity (dirParam n (21 / 5)) y).toReal :=
    fun y => by rw [← ofReal_psi_sq, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp_rw [h1]
  refine integrable_toReal_of_lintegral_ne_top (measurable_dirichletDensity _).aemeasurable ?_
  rw [lintegral_dirichletDensity (dirParam_pos n (by norm_num))]
  exact ENNReal.ofReal_ne_top

private theorem integral_psi_sq (n : ℕ) :
    ∫ y, psi y ^ 2 ∂(Measure.pi fun _ : Fin n => μ₁) = multiBeta (dirParam n (21 / 5)) := by
  rw [← restrict_Icc_eq_pi, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_]
  · have h1 : ∀ y : Fin n → ℝ, psi y ^ 2 = (dirichletDensity (dirParam n (21 / 5)) y).toReal :=
      fun y => by rw [← ofReal_psi_sq, ENNReal.toReal_ofReal (sq_nonneg _)]
    simp_rw [h1]
    rw [integral_toReal (measurable_dirichletDensity _).aemeasurable
      (ae_of_all _ fun y => by rw [← ofReal_psi_sq]; exact ENNReal.ofReal_lt_top),
      lintegral_dirichletDensity (dirParam_pos n (by norm_num)),
      ENNReal.toReal_ofReal (multiBeta_pos (dirParam_pos n (by norm_num)) (by omega)).le]
  · unfold psi
    rw [ite_eq_right fun h => hy (mem_Icc_of_simplex h)]
    simp

private theorem measurable_psi (n : ℕ) : Measurable (psi (n := n)) := by
  refine Measurable.ite (measurableSet_cornerSimplex n) ?_ measurable_const
  fun_prop

private theorem lineIntegral_testFn {n : ℕ} (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    ∫ t, testFn (Function.update x m t) ∂μ₁ = 25 / 24 * psi (Fin.removeNth m x) := by
  rw [← intervalIntegral_eq_μ₁, ← (integral_testFn_insertNth m (Fin.removeNth m x)).2]
  simp only [Fin.insertNth_removeNth]

private theorem maynardJ_testFn {n : ℕ} (m : Fin (n + 1)) :
    maynardJ (n + 1) m testFn = 625 / 576 * multiBeta (dirParam n (21 / 5)) := by
  rw [maynardJ_eq]
  simp_rw [lineIntegral_testFn]
  refine (integral_comp_removeNth m (K := fun y => (25 / 24 * psi y) ^ 2)
    (((measurable_psi n).const_mul _).pow_const 2).aestronglyMeasurable).trans ?_
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_psi_sq]
  norm_num

/-! ### Truncations of the test function -/

/-- The truncation `min (testFn x) M`, a bounded admissible profile. -/
private noncomputable def truncFn {N : ℕ} (M : ℕ) (x : Fin N → ℝ) : ℝ := min (testFn x) M

private theorem measurable_truncFn (N M : ℕ) : Measurable (truncFn (N := N) M) :=
  (measurable_testFn N).min measurable_const

private theorem truncFn_nonneg {N : ℕ} (M : ℕ) (x : Fin N → ℝ) : 0 ≤ truncFn M x :=
  le_min (testFn_nonneg x) (Nat.cast_nonneg M)

private theorem truncFn_le {N : ℕ} (M : ℕ) (x : Fin N → ℝ) : truncFn M x ≤ testFn x :=
  min_le_left _ _

private theorem abs_truncFn_le {N : ℕ} (M : ℕ) (x : Fin N → ℝ) : |truncFn M x| ≤ M := by
  rw [abs_of_nonneg (truncFn_nonneg M x)]
  exact min_le_right _ _

private theorem truncFn_eq_zero {N : ℕ} (M : ℕ) {x : Fin N → ℝ} (hx : x ∉ maynardSimplex N) :
    truncFn M x = 0 := by
  have h : testFn x = 0 := by
    unfold testFn
    rw [ite_eq_right]
    intro h
    exact hx ⟨fun i => (h.1 i).le, h.2.le⟩
  simp [truncFn, h]

private theorem tendsto_truncFn {N : ℕ} (x : Fin N → ℝ) :
    Tendsto (fun M : ℕ => truncFn M x) atTop (𝓝 (testFn x)) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop ⌈testFn x⌉₊] with M hM
  exact min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hM))

private theorem integrable_testFn_sq (N : ℕ) : Integrable (fun x : Fin N → ℝ => testFn x ^ 2) := by
  have h1 : ∀ x : Fin N → ℝ, testFn x ^ 2 = (dirichletDensity (dirParam N 3) x).toReal :=
    fun x => by rw [← ofReal_testFn_sq, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp_rw [h1]
  refine integrable_toReal_of_lintegral_ne_top (measurable_dirichletDensity _).aemeasurable ?_
  rw [lintegral_dirichletDensity (dirParam_pos N (by norm_num))]
  exact ENNReal.ofReal_ne_top

private theorem maynardI_truncFn_le (N M : ℕ) : maynardI N (truncFn M) ≤ maynardI N testFn := by
  unfold maynardI
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
    (integrable_testFn_sq N).integrableOn (ae_of_all _ fun x => ?_)
  exact pow_le_pow_left₀ (truncFn_nonneg M x) (truncFn_le M x) 2

private theorem integrable_psi_sq_pi (n : ℕ) :
    Integrable (fun y : Fin n → ℝ => psi y ^ 2) (Measure.pi fun _ => μ₁) := by
  rw [← restrict_Icc_eq_pi n]
  exact (integrable_psi_sq n).integrableOn

private theorem integrable_lineTestFn {n : ℕ} (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    Integrable (fun t => testFn (Function.update x m t)) μ₁ := by
  have h := (integral_testFn_insertNth m (Fin.removeNth m x)).1
  simp only [Fin.insertNth_removeNth] at h
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr h

/-- `J_k^{(m)}` of the truncations tends to `J_k^{(m)}` of the test function (dominated
convergence, first along each line and then on the cube). -/
private theorem tendsto_maynardJ_truncFn {n : ℕ} (m : Fin (n + 1)) :
    Tendsto (fun M : ℕ => maynardJ (n + 1) m (truncFn M)) atTop
      (𝓝 (maynardJ (n + 1) m testFn)) := by
  simp_rw [maynardJ_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun x => (∫ t, testFn (Function.update x m t) ∂μ₁) ^ 2) (fun M => ?_) ?_ (fun M => ?_) ?_
  · exact ((stronglyMeasurable_lineIntegral m (measurable_truncFn _ M)).pow 2).aestronglyMeasurable
  · simp_rw [lineIntegral_testFn]
    refine ((measurePreserving_removeNth m).integrable_comp
      (g := fun y => (25 / 24 * psi y) ^ 2)
      (((measurable_psi n).const_mul _).pow_const 2).aestronglyMeasurable).mpr ?_
    simp_rw [mul_pow]
    exact (integrable_psi_sq_pi n).const_mul _
  · refine ae_of_all _ fun x => ?_
    have h0 : 0 ≤ ∫ t, truncFn M (Function.update x m t) ∂μ₁ :=
      integral_nonneg fun t => truncFn_nonneg M _
    have h1 : ∫ t, truncFn M (Function.update x m t) ∂μ₁ ≤
        ∫ t, testFn (Function.update x m t) ∂μ₁ :=
      integral_mono (Integrable.of_bound
        ((measurable_truncFn _ M).comp (measurable_update x)).aestronglyMeasurable M
        (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using abs_truncFn_le M _))
        (integrable_lineTestFn m x) fun t => truncFn_le M _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  · refine ae_of_all _ fun x => Tendsto.pow ?_ 2
    refine tendsto_integral_of_dominated_convergence (fun t => testFn (Function.update x m t))
      (fun M => ((measurable_truncFn _ M).comp (measurable_update x)).aestronglyMeasurable)
      (integrable_lineTestFn m x) (fun M => ae_of_all _ fun t => ?_)
      (ae_of_all _ fun t => tendsto_truncFn _)
    rw [Real.norm_eq_abs, abs_of_nonneg (truncFn_nonneg M _)]
    exact truncFn_le M _

/-! ### The numerical inequality -/

/-- The numerical inequality `4 I₁₀₅(Φ) < 105 J₁₀₅^{(m)}(Φ)`: the ratio is `1155/288`. -/
private theorem key_inequality :
    4 * multiBeta (dirParam 105 3) < 105 * (625 / 576 * multiBeta (dirParam 104 (21 / 5))) := by
  rw [multiBeta_dirParam, multiBeta_dirParam]
  have h24 : ((105 : ℕ) : ℝ) / 5 + 3 = 24 := by norm_num
  have h25 : ((104 : ℕ) : ℝ) / 5 + 21 / 5 = 24 + 1 := by norm_num
  rw [h24, h25, Real.Gamma_add_one (s := 24) (by norm_num)]
  have hG3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have hG215 : Real.Gamma (21 / 5) = 1056 / 625 * Real.Gamma (1 / 5) := by
    rw [show (21 / 5 : ℝ) = 16 / 5 + 1 by norm_num, Real.Gamma_add_one (s := 16 / 5) (by norm_num),
      show (16 / 5 : ℝ) = 11 / 5 + 1 by norm_num, Real.Gamma_add_one (s := 11 / 5) (by norm_num),
      show (11 / 5 : ℝ) = 6 / 5 + 1 by norm_num, Real.Gamma_add_one (s := 6 / 5) (by norm_num),
      show (6 / 5 : ℝ) = 1 / 5 + 1 by norm_num, Real.Gamma_add_one (s := 1 / 5) (by norm_num)]
    ring
  rw [hG3, hG215]
  have hG : 0 < Real.Gamma (1 / 5) := Real.Gamma_pos_of_pos (by norm_num)
  have hG24 : 0 < Real.Gamma 24 := Real.Gamma_pos_of_pos (by norm_num)
  have hX : 0 < Real.Gamma (1 / 5) ^ 105 / Real.Gamma 24 := by positivity
  have e1 : 4 * (Real.Gamma (1 / 5) ^ 105 * 2 / Real.Gamma 24) =
      8 * (Real.Gamma (1 / 5) ^ 105 / Real.Gamma 24) := by ring
  have e2 : 105 * (625 / 576 * (Real.Gamma (1 / 5) ^ 104 * (1056 / 625 * Real.Gamma (1 / 5)) /
      (24 * Real.Gamma 24))) = 1155 / 144 * (Real.Gamma (1 / 5) ^ 105 / Real.Gamma 24) := by
    field_simp
    ring
  rw [e1, e2]
  linarith

/-- **`M₁₀₅ > 4`.** Maynard's variational quantity for `k = 105` exceeds `4` (Maynard, *Small gaps
between primes*, arXiv:1311.4600v3, Proposition 4.3(2)). -/
theorem four_lt_maynardM_105 : 4 < maynardM 105 := by
  set Ival := multiBeta (dirParam 105 3) with hIval
  set Jval := 625 / 576 * multiBeta (dirParam 104 (21 / 5)) with hJval
  have hI : maynardI 105 testFn = Ival := integral_testFn_sq 105
  have hJlim : ∀ m : Fin 105,
      Tendsto (fun M : ℕ => maynardJ 105 m (truncFn M)) atTop (𝓝 Jval) := fun m => by
    have h := tendsto_maynardJ_truncFn (n := 104) m
    rwa [maynardJ_testFn] at h
  have hJpos : 0 < Jval :=
    mul_pos (by norm_num) (multiBeta_pos (dirParam_pos 104 (by norm_num)) (by omega))
  have hsum : Tendsto (fun M : ℕ => ∑ m : Fin 105, maynardJ 105 m (truncFn M)) atTop
      (𝓝 (105 * Jval)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 105)) fun m _ => hJlim m
    simpa using h
  obtain ⟨M, hM1, hM2⟩ := ((hsum.eventually (lt_mem_nhds key_inequality)).and
    (eventually_all.2 fun m => (hJlim m).eventually (lt_mem_nhds hJpos))).exists
  have hIM : maynardI 105 (truncFn M) ≤ Ival := hI ▸ maynardI_truncFn_le 105 M
  have hIpos : 0 < maynardI 105 (truncFn M) := lt_of_lt_of_le (hM2 0)
    (maynardJ_le_maynardI (n := 104) 0 (measurable_truncFn _ M) (abs_truncFn_le M))
  have hprof : IsMaynardProfile 105 (truncFn M) :=
    ⟨measurable_truncFn _ M, ⟨M, abs_truncFn_le M⟩, fun x hx => truncFn_eq_zero M hx,
      hIpos.ne', fun m => (hM2 m).ne'⟩
  have hratio : 4 < maynardRatio 105 (truncFn M) := by
    unfold maynardRatio
    rw [lt_div_iff₀ hIpos]
    linarith
  exact lt_of_lt_of_le hratio (le_csSup (bddAbove_maynardRatio 104) ⟨truncFn M, hprof, rfl⟩)

end WantedExt.NumberTheory.MaynardVariationalBounds
