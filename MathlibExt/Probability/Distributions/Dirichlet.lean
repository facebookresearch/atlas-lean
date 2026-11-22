/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Dirichlet integral and the Dirichlet distribution

A probability vector `θ ∈ ℝⁿ⁺¹` is determined by its first `n` coordinates `x`, with
`θₙ = 1 - ∑ x`. The Dirichlet distribution `Dir(α)` with positive parameters `α : Fin (n + 1) → ℝ`
has density proportional to `∏ θᵢ^(αᵢ-1)` in these coordinates.

* `dirichletDensity α x`: the unnormalized density `∏ xᵢ^(αᵢ-1) (1 - ∑ x)^(αₙ-1)` on the open
  corner simplex `{x > 0, ∑ x < 1}`.
* `lintegral_dirichletDensity` (**the Dirichlet integral**): its integral is the multivariate Beta
  function `multiBeta α = ∏ Γ(αᵢ) / Γ(∑ α)`. The proof is by induction on `n`, integrating out
  the first coordinate `t` after rescaling the others by `1 - t` (`dirichletDensity_cons_smul`),
  which leaves a Beta integral (`lintegral_Ioo_rpow_mul_rpow`).
* `dirichletMeasure α`: the Dirichlet distribution on `Fin (n + 1) → ℝ`, a probability measure
  (`isProbabilityMeasure_dirichletMeasure`) concentrated on probability vectors with positive
  entries (`ae_dirichletMeasure`).
* `withDensity_prod_pow_dirichletMeasure` (**Dirichlet–multinomial conjugacy**, density form):
  weighting `Dir(α)` by the likelihood `∏ θᵢ^kᵢ` of counts `k` gives `B(α + k) / B(α) · Dir(α + k)`.
* `lintegral_dirichletMeasure_apply`: the mean `E[θᵢ] = αᵢ / ∑ α`.

For `n = 1` the density is the Beta density in `x₀` and `multiBeta ![a, b] = beta a b`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions, Vol. 1*,
  Wiley, 2000, Chapter 49.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §2.2.1.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Real Set
open scoped ENNReal

namespace ProbabilityTheory

/-- The **Beta integral** `∫₀¹ t^(a-1) (1-t)^(b-1) dt = B(a, b)`. -/
theorem lintegral_Ioo_rpow_mul_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) =
      ENNReal.ofReal (beta a b) := by
  have h := lintegral_betaPDF_eq_one ha hb
  rw [lintegral_betaPDF] at h
  have hB := beta_pos ha hb
  have h' : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / beta a b) *
      ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) = 1 := by
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [lintegral_const_mul _ (by fun_prop)] at h'
  rw [← ENNReal.eq_div_iff (by simp [hB]) ENNReal.ofReal_ne_top] at h'
  rw [h', ← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- The unnormalized **Dirichlet density** with parameters `α : Fin (n + 1) → ℝ`, written in the
first `n` coordinates `x` of a probability vector `(x, 1 - ∑ x)`:
`∏ xᵢ^(αᵢ-1) · (1 - ∑ x)^(αₙ-1)` on the open corner simplex `{x > 0, ∑ x < 1}`, and `0` off it. -/
noncomputable def dirichletDensity {n : ℕ} (α : Fin (n + 1) → ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  if (∀ i, 0 < x i) ∧ ∑ i, x i < 1 then
    ENNReal.ofReal ((∏ i, x i ^ (α (Fin.castSucc i) - 1)) * (1 - ∑ i, x i) ^ (α (Fin.last n) - 1))
  else 0

/-- The normalizing constant `∏ Γ(αᵢ) / Γ(∑ α)` of the Dirichlet distribution (the multivariate
Beta function). -/
noncomputable def multiBeta {n : ℕ} (α : Fin n → ℝ) : ℝ :=
  (∏ i, Gamma (α i)) / Gamma (∑ i, α i)

theorem multiBeta_pos {n : ℕ} {α : Fin n → ℝ} (hα : ∀ i, 0 < α i) (hn : n ≠ 0) :
    0 < multiBeta α := by
  have : 0 < ∑ i, α i := Finset.sum_pos (fun i _ ↦ hα i) (Finset.univ_nonempty_iff.mpr
    ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩)
  exact div_pos (Finset.prod_pos fun i _ ↦ Gamma_pos_of_pos (hα i)) (Gamma_pos_of_pos this)

theorem measurableSet_cornerSimplex (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 < x i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const (by fun_prop)
  have h2 : MeasurableSet {x : Fin n → ℝ | ∑ i, x i < 1} :=
    measurableSet_lt (f := fun x : Fin n → ℝ ↦ ∑ i, x i) (by fun_prop) measurable_const
  exact h1.inter h2

theorem measurable_dirichletDensity {n : ℕ} (α : Fin (n + 1) → ℝ) :
    Measurable (dirichletDensity α) := by
  refine Measurable.ite (measurableSet_cornerSimplex n) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem multiBeta_succ {n : ℕ} (α : Fin (n + 2) → ℝ) (hα : ∀ i, 0 < α i) :
    beta (α 0) (∑ j, α (Fin.succ j)) * multiBeta (fun j ↦ α (Fin.succ j)) = multiBeta α := by
  have hA : 0 < ∑ j : Fin (n + 1), α (Fin.succ j) :=
    Finset.sum_pos (fun j _ ↦ hα _) Finset.univ_nonempty
  have hG := (Gamma_pos_of_pos hA).ne'
  rw [beta, multiBeta, multiBeta]
  conv_rhs => rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  field_simp

/-- The Dirichlet integral in dimension `0`: one coordinate, density `1`. -/
theorem lintegral_dirichletDensity_zero {α : Fin 1 → ℝ} (hα : ∀ i, 0 < α i) :
    ∫⁻ x, dirichletDensity α x = ENNReal.ofReal (multiBeta α) := by
  have hd : ∀ x : Fin 0 → ℝ, dirichletDensity α x = 1 := fun x ↦ by
    simp [dirichletDensity]
  have hm : multiBeta α = 1 := by
    rw [multiBeta, Fin.prod_univ_one, Fin.sum_univ_one, div_self (Gamma_pos_of_pos (hα 0)).ne']
  simp only [hd, lintegral_const, one_mul, hm, ENNReal.ofReal_one]
  rw [volume_pi, Measure.pi_of_empty]
  simp

/-- Fubini over the first coordinate of `Fin (n + 1) → ℝ`. -/
theorem lintegral_fin_succ {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ t, ∫⁻ y, G (Fin.cons t y) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  rw [← h.lintegral_comp hG, Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- Rescaling the integration variable of a function on `Fin n → ℝ` by `c > 0`. -/
theorem lintegral_comp_smul_fin {n : ℕ} {F : (Fin n → ℝ) → ℝ≥0∞} (hF : Measurable F) {c : ℝ}
    (hc : 0 < c) : ∫⁻ y, F y = ENNReal.ofReal (c ^ n) * ∫⁻ u, F (c • u) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin n → ℝ)) hc.ne'
  rw [← lintegral_map hF (measurable_const_smul c), hmap, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, Module.finrank_fin_fun, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- The Dirichlet density with the first coordinate `t` fixed and the others rescaled by `1 - t`
is a Dirichlet density in the remaining coordinates. -/
theorem dirichletDensity_cons_smul {n : ℕ} (α : Fin (n + 2) → ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (u : Fin n → ℝ) :
    dirichletDensity α (Fin.cons t ((1 - t) • u)) =
      ENNReal.ofReal (t ^ (α 0 - 1) * (1 - t) ^ (∑ j, α (Fin.succ j) - 1 - n)) *
        dirichletDensity (fun j ↦ α (Fin.succ j)) u := by
  set c := 1 - t with hc_def
  have hc : 0 < c := sub_pos.mpr ht1
  have hcond : ((∀ i, 0 < (Fin.cons t (c • u) : Fin (n + 1) → ℝ) i) ∧
      ∑ i, (Fin.cons t (c • u) : Fin (n + 1) → ℝ) i < 1) ↔ ((∀ j, 0 < u j) ∧ ∑ j, u j < 1) := by
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    have hlt : t + c * ∑ j, u j < 1 ↔ ∑ j, u j < 1 := by
      constructor
      · intro h
        by_contra h'
        push Not at h'
        nlinarith
      · intro h
        nlinarith
    rw [hlt]
    exact ⟨fun ⟨⟨_, h⟩, hs⟩ ↦ ⟨fun j ↦ pos_of_mul_pos_right (h j) hc.le, hs⟩,
      fun ⟨h, hs⟩ ↦ ⟨⟨ht0, fun j ↦ mul_pos hc (h j)⟩, hs⟩⟩
  unfold dirichletDensity
  split_ifs with h1 h2 h2
  · have hu := hcond.mp h1
    have hS : 0 < 1 - ∑ j, u j := sub_pos.mpr hu.2
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, ← Fin.succ_last, ← Fin.succ_castSucc]
    have h1S : 1 - (t + c * ∑ j, u j) = c * (1 - ∑ j, u j) := by rw [hc_def]; ring
    rw [h1S, mul_rpow hc.le hS.le]
    simp_rw [mul_rpow hc.le (hu.1 _).le]
    rw [Finset.prod_mul_distrib, ← rpow_sum_of_pos hc]
    have hexp : ∑ j : Fin (n + 1), α (Fin.succ j) - 1 - n =
        ∑ j : Fin n, (α (Fin.succ (Fin.castSucc j)) - 1) + (α (Fin.succ (Fin.last n)) - 1) := by
      rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]
      simp
      ring
    rw [hexp, rpow_add hc]
    ring
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · simp

theorem dirichletDensity_cons_eq_zero {n : ℕ} (α : Fin (n + 2) → ℝ) {t : ℝ}
    (ht : t ∉ Ioo (0 : ℝ) 1) (y : Fin n → ℝ) : dirichletDensity α (Fin.cons t y) = 0 := by
  unfold dirichletDensity
  rw [ite_eq_right_iff]
  rintro ⟨hpos, hsum⟩
  exfalso
  refine ht ⟨by simpa using hpos 0, ?_⟩
  rw [Fin.sum_univ_succ, Fin.cons_zero] at hsum
  have : 0 ≤ ∑ j, (Fin.cons t y : Fin (n + 1) → ℝ) (Fin.succ j) :=
    Finset.sum_nonneg fun j _ ↦ (hpos j.succ).le
  linarith

/-- **The Dirichlet integral**: `∫ ∏ xᵢ^(αᵢ-1) (1 - ∑ x)^(αₙ-1) dx = ∏ Γ(αᵢ) / Γ(∑ α)` over the
corner simplex, for positive parameters. -/
theorem lintegral_dirichletDensity {n : ℕ} {α : Fin (n + 1) → ℝ} (hα : ∀ i, 0 < α i) :
    ∫⁻ x, dirichletDensity α x = ENNReal.ofReal (multiBeta α) := by
  induction n with
  | zero => exact lintegral_dirichletDensity_zero hα
  | succ n ih =>
    set α' : Fin (n + 1) → ℝ := fun j ↦ α (Fin.succ j) with hα'_def
    have hα' : ∀ j, 0 < α' j := fun j ↦ hα _
    set A := ∑ j, α' j with hA_def
    have hA : 0 < A := Finset.sum_pos (fun j _ ↦ hα' j) Finset.univ_nonempty
    have hmeas : ∀ t, Measurable fun y : Fin n → ℝ ↦ dirichletDensity α (Fin.cons t y) :=
      fun t ↦ (measurable_dirichletDensity α).comp (measurable_pi_iff.mpr fun i ↦ by
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [Fin.cons_zero]
          exact measurable_const
        · simp only [Fin.cons_succ]
          exact measurable_pi_apply j)
    have hinner : ∀ t, ∫⁻ y, dirichletDensity α (Fin.cons t y) =
        (Ioo (0 : ℝ) 1).indicator (fun t ↦ ENNReal.ofReal (t ^ (α 0 - 1) * (1 - t) ^ (A - 1))) t *
          ENNReal.ofReal (multiBeta α') := fun t ↦ by
      by_cases ht : t ∈ Ioo (0 : ℝ) 1
      · have hc : 0 < 1 - t := sub_pos.mpr ht.2
        rw [indicator_of_mem ht, lintegral_comp_smul_fin (hmeas t) hc]
        simp_rw [dirichletDensity_cons_smul α ht.1 ht.2]
        rw [lintegral_const_mul _ (measurable_dirichletDensity α'), ih hα', ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [← rpow_natCast, ← hA_def]
        rw [mul_left_comm, ← rpow_add hc]
        congr 2
        ring
      · rw [indicator_of_notMem ht, zero_mul]
        simp_rw [dirichletDensity_cons_eq_zero α ht]
        exact lintegral_zero
    rw [lintegral_fin_succ (measurable_dirichletDensity α), lintegral_congr fun t ↦ hinner t,
      lintegral_mul_const _ (Measurable.indicator (by fun_prop) measurableSet_Ioo),
      lintegral_indicator measurableSet_Ioo,
      lintegral_Ioo_rpow_mul_rpow (hα 0) hA, ← ENNReal.ofReal_mul (beta_pos (hα 0) hA).le,
      multiBeta_succ α hα]

/-! ### The Dirichlet distribution -/

/-- Completing the first `n` coordinates to a vector `(x, 1 - ∑ x)` summing to `1`. -/
def simplexCompletion {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x (1 - ∑ i, x i)

theorem measurable_simplexCompletion (n : ℕ) : Measurable (simplexCompletion (n := n)) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [simplexCompletion, Fin.snoc_last]
    fun_prop
  · simp only [simplexCompletion, Fin.snoc_castSucc]
    exact measurable_pi_apply j

theorem sum_simplexCompletion {n : ℕ} (x : Fin n → ℝ) : ∑ i, simplexCompletion x i = 1 := by
  simp [simplexCompletion, Fin.sum_univ_castSucc]

/-- The **Dirichlet distribution** `Dir(α)` on probability vectors in `Fin (n + 1) → ℝ`: the
normalized density `∏ θᵢ^(αᵢ-1) / B(α)` in the first `n` coordinates, with the last coordinate
`1 - ∑` of the others. -/
noncomputable def dirichletMeasure {n : ℕ} (α : Fin (n + 1) → ℝ) : Measure (Fin (n + 1) → ℝ) :=
  ((volume : Measure (Fin n → ℝ)).withDensity fun x ↦
    dirichletDensity α x / ENNReal.ofReal (multiBeta α)).map simplexCompletion

theorem lintegral_dirichletMeasure {n : ℕ} (α : Fin (n + 1) → ℝ)
    {f : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ θ, f θ ∂dirichletMeasure α =
      (∫⁻ x, dirichletDensity α x * f (simplexCompletion x)) / ENNReal.ofReal (multiBeta α) := by
  rw [dirichletMeasure, lintegral_map hf (measurable_simplexCompletion n),
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_dirichletDensity α).div_const _)
      (g := fun a ↦ f (simplexCompletion a)) (hf.comp (measurable_simplexCompletion n))]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  simp_rw [mul_right_comm _ _ (f _)]
  exact lintegral_mul_const _ ((measurable_dirichletDensity α).mul
    (hf.comp (measurable_simplexCompletion n)) : Measurable fun a ↦
      dirichletDensity α a * f (simplexCompletion a))

theorem isProbabilityMeasure_dirichletMeasure {n : ℕ} {α : Fin (n + 1) → ℝ}
    (hα : ∀ i, 0 < α i) : IsProbabilityMeasure (dirichletMeasure α) := by
  constructor
  rw [← setLIntegral_one, setLIntegral_univ, lintegral_dirichletMeasure α measurable_const]
  simp only [mul_one, lintegral_dirichletDensity hα]
  exact ENNReal.div_self (by simp [multiBeta_pos hα (Nat.succ_ne_zero n)]) ENNReal.ofReal_ne_top

/-- A `Dir(α)`-random vector is almost surely a probability vector with positive entries. -/
theorem ae_dirichletMeasure {n : ℕ} (α : Fin (n + 1) → ℝ) :
    ∀ᵐ θ ∂dirichletMeasure α, (∀ i, 0 < θ i) ∧ ∑ i, θ i = 1 := by
  rw [dirichletMeasure, ae_map_iff (measurable_simplexCompletion n).aemeasurable]
  · rw [ae_withDensity_iff ((measurable_dirichletDensity α).div_const _)]
    refine Filter.Eventually.of_forall fun x hx ↦ ⟨fun i ↦ ?_, sum_simplexCompletion x⟩
    have hx' : dirichletDensity α x ≠ 0 := fun h ↦ hx (by simp [h])
    unfold dirichletDensity at hx'
    split_ifs at hx' with h
    · refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [simplexCompletion, Fin.snoc_last]
        linarith [h.2]
      · simp only [simplexCompletion, Fin.snoc_castSucc]
        exact h.1 j
    · exact absurd rfl hx'
  · have h1 : MeasurableSet {θ : Fin (n + 1) → ℝ | ∀ i, 0 < θ i} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const (by fun_prop)
    have h2 : MeasurableSet {θ : Fin (n + 1) → ℝ | ∑ i, θ i = 1} :=
      measurableSet_eq_fun (f := fun θ : Fin (n + 1) → ℝ ↦ ∑ i, θ i) (by fun_prop)
        measurable_const
    exact h1.inter h2

/-- Multiplying the Dirichlet density by the likelihood `∏ θᵢ^kᵢ` of counts `k` adds the counts to
the parameters. -/
theorem dirichletDensity_mul_prod_pow {n : ℕ} (α : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℕ)
    (x : Fin n → ℝ) :
    dirichletDensity α x * ∏ i, ENNReal.ofReal (simplexCompletion x i) ^ k i =
      dirichletDensity (fun i ↦ α i + k i) x := by
  unfold dirichletDensity
  split_ifs with h
  · have hS : 0 < 1 - ∑ i, x i := sub_pos.mpr h.2
    have hθ : ∀ i, 0 ≤ simplexCompletion x i := fun i ↦ by
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [simplexCompletion, Fin.snoc_last]
        exact hS.le
      · simp only [simplexCompletion, Fin.snoc_castSucc]
        exact (h.1 j).le
    simp_rw [← ENNReal.ofReal_pow (hθ _)]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ pow_nonneg (hθ i) _,
      ← ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (h.1 j).le _)
        (rpow_nonneg hS.le _))]
    congr 1
    rw [Fin.prod_univ_castSucc]
    simp only [simplexCompletion, Fin.snoc_castSucc, Fin.snoc_last]
    have hx : ∀ j, x j ^ (α (Fin.castSucc j) - 1) * x j ^ k (Fin.castSucc j) =
        x j ^ (α (Fin.castSucc j) + k (Fin.castSucc j) - 1) := fun j ↦ by
      rw [← rpow_natCast, ← rpow_add (h.1 j)]
      ring_nf
    have hl : (1 - ∑ i, x i) ^ (α (Fin.last n) - 1) * (1 - ∑ i, x i) ^ k (Fin.last n) =
        (1 - ∑ i, x i) ^ (α (Fin.last n) + k (Fin.last n) - 1) := by
      rw [← rpow_natCast, ← rpow_add hS]
      ring_nf
    rw [← hl, ← Finset.prod_congr rfl fun j _ ↦ hx j, Finset.prod_mul_distrib]
    ring
  · exact zero_mul _

theorem measurable_prod_ofReal_pow {n : ℕ} (k : Fin (n + 1) → ℕ) :
    Measurable fun θ : Fin (n + 1) → ℝ ↦ ∏ i, ENNReal.ofReal (θ i) ^ k i :=
  Finset.measurable_prod _ fun i _ ↦
    (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).pow_const _

/-- **Dirichlet–multinomial conjugacy**, density form: weighting `Dir(α)` by the likelihood
`∏ θᵢ^kᵢ` of counts `k` gives `B(α + k) / B(α)` times `Dir(α + k)`. -/
theorem withDensity_prod_pow_dirichletMeasure {n : ℕ} {α : Fin (n + 1) → ℝ} (hα : ∀ i, 0 < α i)
    (k : Fin (n + 1) → ℕ) :
    (dirichletMeasure α).withDensity (fun θ ↦ ∏ i, ENNReal.ofReal (θ i) ^ k i) =
      ENNReal.ofReal (multiBeta (fun i ↦ α i + k i) / multiBeta α) •
        dirichletMeasure (fun i ↦ α i + k i) := by
  have hZ := multiBeta_pos hα (Nat.succ_ne_zero n)
  have hZk := multiBeta_pos (α := fun i ↦ α i + k i)
    (fun i ↦ by have := hα i; positivity) (Nat.succ_ne_zero n)
  ext s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← lintegral_indicator hs,
    ← lintegral_indicator_one hs,
    lintegral_dirichletMeasure α ((measurable_prod_ofReal_pow k).indicator hs),
    lintegral_dirichletMeasure _ (f := s.indicator 1) (measurable_one.indicator hs)]
  have hpt : ∀ x, dirichletDensity α x *
      s.indicator (fun θ ↦ ∏ i, ENNReal.ofReal (θ i) ^ k i) (simplexCompletion x) =
      dirichletDensity (fun i ↦ α i + k i) x * s.indicator 1 (simplexCompletion x) := fun x ↦ by
    by_cases hx : simplexCompletion x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one,
        dirichletDensity_mul_prod_pow]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]
  simp_rw [hpt]
  set I := ∫⁻ x, dirichletDensity (fun i ↦ α i + k i) x * s.indicator 1 (simplexCompletion x)
  set b := ENNReal.ofReal (multiBeta fun i ↦ α i + k i)
  have hb0 : b ≠ 0 := by simp [b, hZk]
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc I * (ENNReal.ofReal (multiBeta α))⁻¹
      = I * (b⁻¹ * b) * (ENNReal.ofReal (multiBeta α))⁻¹ := by
        rw [ENNReal.inv_mul_cancel hb0 ENNReal.ofReal_ne_top, mul_one]
    _ = b * (ENNReal.ofReal (multiBeta α))⁻¹ * (I * b⁻¹) := by ring

/-- The **mean of the Dirichlet distribution**: `E[θᵢ] = αᵢ / ∑ α`. -/
theorem lintegral_dirichletMeasure_apply {n : ℕ} {α : Fin (n + 1) → ℝ} (hα : ∀ i, 0 < α i)
    (i : Fin (n + 1)) :
    ∫⁻ θ, ENNReal.ofReal (θ i) ∂dirichletMeasure α = ENNReal.ofReal (α i / ∑ j, α j) := by
  classical
  set k : Fin (n + 1) → ℕ := Pi.single i 1 with hk
  have hprod : ∀ θ : Fin (n + 1) → ℝ, ∏ j, ENNReal.ofReal (θ j) ^ k j = ENNReal.ofReal (θ i) :=
    fun θ ↦ by
      rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [hk, hj]) (by simp)]
      simp [hk]
  have hαk : ∀ j, 0 < α j + k j := fun j ↦ by have := hα j; positivity
  have := isProbabilityMeasure_dirichletMeasure hαk
  have hmass := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ univ)
    (withDensity_prod_pow_dirichletMeasure hα k)
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hprod,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hmass
  rw [hmass]
  congr 1
  have hA : 0 < ∑ j, α j := Finset.sum_pos (fun j _ ↦ hα j) Finset.univ_nonempty
  have hsum : ∑ j, (α j + k j) = ∑ j, α j + 1 := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hk, hj]) (by simp)]
    simp [hk]
  have hG : ∀ j, Gamma (α j + k j) = (if j = i then α i else 1) * Gamma (α j) := fun j ↦ by
    by_cases hj : j = i
    · subst hj
      simp [hk, Gamma_add_one (hα j).ne']
    · simp [hk, hj]
  rw [multiBeta, multiBeta, hsum, Gamma_add_one hA.ne', Finset.prod_congr rfl fun j _ ↦ hG j,
    Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, ite_true]
  have h1 := Finset.prod_pos fun j (_ : j ∈ Finset.univ) ↦ Gamma_pos_of_pos (hα j)
  have h2 := Gamma_pos_of_pos hA
  field_simp

end ProbabilityTheory
