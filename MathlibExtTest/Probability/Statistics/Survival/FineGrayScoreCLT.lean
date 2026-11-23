/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGrayScoreCLT
import MathlibExt.Probability.BoundedInProbability
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.FineGrayAsymptotics
open MathlibExt.Probability.Statistics.FineGrayScoreCLT

namespace MathlibExtTest.Probability.Statistics.FineGrayScoreCLT

/-! ### A concrete product model with `σ² = 1/18 > 0`

A pair is `x = (x₁, x₂) ∈ Fin 4 × Fin 4`, uniform (`16` equally likely outcomes, so the two
members are independent). The covariate-`1` member's status is `statA x₁`: cause `0` for
`x₁ ∈ {0, 1}`, the competing cause `1` for `x₁ = 2`, censored for `x₁ = 3`. The covariate-`0`
member's status is `statB x₂`: cause `0` for `x₂ = 0`, cause `1` for `x₂ = 1`, censored otherwise.
So `p_a = 1/2`, `p_b = 1/4`, `β₀ = log 2` (`e^{β₀} p_b = p_a`), `m(β₀) = 2/3`, and a pair's score
contribution is `(1/3) 1[a] - (2/3) 1[b]`, of second moment `1/18 + 1/9 - 2 · (2/9) · (1/8) = 1/9`,
so `σ² = 1/18`. The information limit is `v = ((1/2 + 1/4) / 2) (2/3) (1/3) = 1/12`, and the
Fine–Gray estimator has limit variance `σ² / v² = 8`. All of these are computed from the
definitions below. -/

/-- Status of the covariate-`1` member. -/
def statA : Fin 4 → Option (Fin 2) := ![some 0, some 0, some 1, none]

/-- Status of the covariate-`0` member. -/
def statB : Fin 4 → Option (Fin 2) := ![some 0, some 1, none, none]

/-- Pair statuses as functions of the pair outcome. -/
def εA (x : Fin 4 × Fin 4) : Option (Fin 2) := statA x.1

/-- Pair statuses as functions of the pair outcome. -/
def εB (x : Fin 4 × Fin 4) : Option (Fin 2) := statB x.2

/-- The uniform law of a pair. -/
noncomputable def μU : Measure (Fin 4 × Fin 4) := Measure.uniformOfFinset univ

instance : IsProbabilityMeasure μU :=
  ⟨by
    rw [μU, Measure.uniformOfFinset_apply]
    simpa using ENNReal.div_self (by norm_num : (16 : ENNReal) ≠ 0) (by norm_num)⟩

theorem μU_real_singleton (x : Fin 4 × Fin 4) : μU.real {x} = 1 / 16 := by
  rw [measureReal_def, μU, Measure.uniformOfFinset_apply_singleton]
  simp

theorem μU_real (p : Fin 4 × Fin 4 → Prop) [DecidablePred p] :
    μU.real {x | p x} = (univ.filter p).card / 16 := by
  have hs : {x | p x} = ↑(univ.filter p) := by ext; simp
  rw [hs, ← sum_measureReal_singleton]
  simp [μU_real_singleton, div_eq_mul_inv]

theorem measurableSet_any (s : Set (Fin 4 × Fin 4)) : MeasurableSet s := .of_discrete

theorem pairProbA_U : pairProbA μU εA 0 = 1 / 2 := by
  rw [pairProbA, μU_real, show (univ.filter fun x => εA x = some 0).card = 8 by decide]
  norm_num

theorem pairProbB_U : pairProbB μU εB 0 = 1 / 4 := by
  rw [pairProbB, μU_real, show (univ.filter fun x => εB x = some 0).card = 4 by decide]
  norm_num

/-- The true coefficient `β₀ = log 2`. -/
noncomputable def β₀U : ℝ := log 2

/-- The proportional subdistribution-hazards relation `e^{β₀} p_b = p_a`. -/
theorem hβ₀U : exp β₀U * pairProbB μU εB 0 = pairProbA μU εA 0 := by
  rw [β₀U, exp_log two_pos, pairProbA_U, pairProbB_U]
  norm_num

theorem pairMean_β₀U : pairMean β₀U = 2 / 3 := by
  rw [pairMean, β₀U, exp_log two_pos]
  norm_num

/-- **`σ² = 1/18`, computed from the definition** `σ² = E[pairScore β₀ ²] / 2` by summing over the
`16` outcomes. -/
theorem pairσ2_U : pairσ2 μU εA εB 0 β₀U = 1 / 18 := by
  ext
  change (∫ x, pairScore εA εB 0 β₀U x ^ 2 ∂μU) / 2 = ((1 / 18 : NNReal) : ℝ)
  rw [integral_fintype _]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, μU_real_singleton, pairScore, εA, εB, statA,
    statB, pairMean_β₀U]
  · norm_num
  · exact Integrable.of_finite

/-- **The score variance is positive.** -/
theorem pairσ2_U_pos : 0 < pairσ2 μU εA εB 0 β₀U := by
  rw [pairσ2_U]
  norm_num

/-- The library's sufficient condition for `σ² > 0` also applies: with probability `3/8` the
covariate-`1` member fails from cause `0` and the covariate-`0` member does not. -/
example : 0 < pairσ2 μU εA εB 0 β₀U := by
  refine pairσ2_pos μU (measurableSet_any _) (measurableSet_any _) β₀U ?_
  rw [μU_real, show (univ.filter fun x => εA x = some 0 ∧ εB x ≠ some 0).card = 6 by decide]
  norm_num

/-- The information limit at `β₀`: `v = ((1/2 + 1/4) / 2) (2/3) (1/3) = 1/12`. -/
theorem pairV_U : pairV μU εA εB 0 β₀U = 1 / 12 := by
  ext
  change pairInfoLimit μU εA εB 0 β₀U = ((1 / 12 : NNReal) : ℝ)
  rw [pairInfoLimit, pairVarFn, pairMean_β₀U, pairProbA_U, pairProbB_U]
  norm_num

/-- The limit variance of the estimator, `σ² / v² = (1/18) / (1/12)² = 8`. -/
theorem pairσ2_div_pairV_sq_U : pairσ2 μU εA εB 0 β₀U / pairV μU εA εB 0 β₀U ^ 2 = 8 := by
  rw [pairσ2_U, pairV_U]
  ext
  norm_num

/-- The score limit `Z = id` under `N(0, σ²)`. -/
theorem hasLaw_id_U :
    HasLaw id (gaussianReal 0 (pairσ2 μU εA εB 0 β₀U)) (gaussianReal 0 (1 / 18)) := by
  rw [pairσ2_U]
  exact HasLaw.id

/-- **Score CLT in the concrete model**: `Uₙ(log 2) / √n ⟶ N(0, 1/18)`, here with the
censoring weight `G ≡ 1`. -/
theorem tendstoInDistribution_fgScore_U : TendstoInDistribution
    (fun (n : ℕ) ω ↦ fgScore (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1) (pairCov n) β₀U /
      √(n : ℝ)) atTop id (fun _ ↦ pairModel μU) (gaussianReal 0 (1 / 18)) :=
  tendstoInDistribution_fgScore_pair (fun _ _ _ => 1) (measurableSet_any _) (measurableSet_any _)
    hβ₀U hasLaw_id_U

/-- **Asymptotic normality at `σ² = 1/18 > 0`**: the Fine–Gray AN theorem instantiated in the
concrete product model. Any estimator that maximizes the weighted log partial likelihood whenever
a maximizer exists satisfies `√n (βhat n - log 2) ⟶ Z / v` with `Z / v ~ N(0, 8)`. -/
theorem tendstoInDistribution_fgMPLE_U (βhat : ℕ → (ℕ → Fin 4 × Fin 4) → ℝ)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1)
        (pairCov n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1)
          (pairCov n)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) (pairModel μU)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀U)) atTop
      (fun ω => id ω / ((1 / 12 : NNReal) : ℝ)) (fun _ ↦ pairModel μU) (gaussianReal 0 (1 / 18)) ∧
    HasLaw (fun ω => id ω / ((1 / 12 : NNReal) : ℝ)) (gaussianReal 0 8)
      (gaussianReal 0 (1 / 18)) := by
  have h := tendstoInDistribution_fgMPLE_pair (G := fun _ _ _ => 1) (measurableSet_any _)
    (measurableSet_any _) (by rw [pairProbB_U]; norm_num) hβ₀U (fun _ _ _ => zero_le_one)
    hasLaw_id_U hβhat hβhat_meas
  rwa [pairσ2_div_pairV_sq_U, pairV_U] at h

/-! ### A degenerate product model: `σ² = 0`

Every pair is `(0, 0)`, so both members fail from cause `0`: `p_a = p_b = 1`, `β₀ = 0`,
`m(0) = 1/2` and each pair contributes `(1 - 1/2) - 1/2 = 0` to the score. The pairs are still
independent (a product of Dirac measures), so the score CLT applies, but with `σ² = 0`; the
`σ² > 0` instance is not claimed, and the hypothesis of `pairσ2_pos` fails. -/

/-- The degenerate pair law. -/
noncomputable def μD : Measure (Fin 4 × Fin 4) := Measure.dirac (0, 0)

instance : IsProbabilityMeasure μD := by unfold μD; infer_instance

theorem hβ₀D : exp 0 * pairProbB μD εB 0 = pairProbA μD εA 0 := by
  rw [pairProbA, pairProbB, μD, measureReal_def, measureReal_def,
    Measure.dirac_apply_of_mem (s := {x : Fin 4 × Fin 4 | εA x = some 0}) (a := (0, 0)) rfl,
    Measure.dirac_apply_of_mem (s := {x : Fin 4 × Fin 4 | εB x = some 0}) (a := (0, 0)) rfl]
  simp

/-- **`σ² = 0`, computed from the definition.** -/
theorem pairσ2_D : pairσ2 μD εA εB 0 0 = 0 := by
  ext
  change (∫ x, pairScore εA εB 0 0 x ^ 2 ∂μD) / 2 = ((0 : NNReal) : ℝ)
  rw [μD, integral_dirac]
  simp [pairScore, εA, εB, statA, statB, pairMean]
  norm_num

/-- The degenerate model is not a `σ² > 0` instance. -/
example : ¬ 0 < pairσ2 μD εA εB 0 0 := by
  rw [pairσ2_D]
  exact lt_irrefl 0

/-- The sufficient condition of `pairσ2_pos` fails: the event "covariate-`1` member fails from
cause `0`, covariate-`0` member does not" is null. -/
example : μD.real {x | εA x = some 0 ∧ εB x ≠ some 0} = 0 := by
  simp [μD, εA, εB, statA, statB]

/-- The score CLT in the degenerate model only gives the degenerate limit `N(0, 0)`. -/
example : TendstoInDistribution
    (fun (n : ℕ) ω ↦ fgScore (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1) (pairCov n) 0 /
      √(n : ℝ)) atTop (fun _ : Unit => (0 : ℝ)) (fun _ ↦ pairModel μD) (Measure.dirac ()) :=
  tendstoInDistribution_fgScore_pair (fun _ _ _ => 1) (measurableSet_any _) (measurableSet_any _)
    hβ₀D (by rw [pairσ2_D]; exact ⟨aemeasurable_const, by simp [gaussianReal_zero_var]⟩)

/-! ### A dependent (non-product) model: no CLT

Under `pDiag` one uniform pair `x` is drawn and copied to every coordinate, `ω k = x`. Each
coordinate still has law `μU`, but the coordinates are not independent: `pDiag` is not the
product model. The score is then `(n / 2) · pairScore β₀ x`, of order `√n` after normalization,
and `Uₙ(β₀) / √n` converges in distribution to nothing. -/

/-- The diagonal (fully dependent) law on sequences of pairs. -/
noncomputable def pDiag : Measure (ℕ → Fin 4 × Fin 4) := μU.map fun x _ => x

theorem measurable_diag : Measurable fun (x : Fin 4 × Fin 4) (_ : ℕ) => x :=
  by fun_prop

instance : IsProbabilityMeasure pDiag := by
  unfold pDiag
  infer_instance

/-- `pDiag` is not the product model: the first two coordinates take the distinct values
`(0, 0)` and `(0, 1)` with probability `0` under `pDiag` and `1/256` under the product. -/
theorem pDiag_ne_pairModel : pDiag ≠ pairModel μU := by
  intro h
  have h1 := congrArg (fun P : Measure (ℕ → Fin 4 × Fin 4) =>
    P.map (fun ω => (ω 0, ω 1)) {((0, 0), (0, 1))}) h
  rw [Measure.infinitePi_map_eval_prod (by norm_num), pDiag,
    Measure.map_map (by fun_prop) measurable_diag,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod] at h1
  have h0 : ((fun ω : ℕ → Fin 4 × Fin 4 => (ω 0, ω 1)) ∘ fun x _ => x) ⁻¹'
      ({(0, 0)} ×ˢ {(0, 1)}) = (∅ : Set (Fin 4 × Fin 4)) := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h0 h1
    exact absurd (h0.symm.trans h1) (by decide)
  rw [h0, measure_empty] at h1
  have hs : ∀ y : Fin 4 × Fin 4, μU {y} ≠ 0 := fun y h => by
    have := μU_real_singleton y
    rw [measureReal_def, h] at this
    norm_num at this
  exact mul_ne_zero (hs _) (hs _) h1.symm

/-- **No CLT for the dependent model**: for every candidate limit `Z`, `Uₙ(log 2) / √n` does not
converge in distribution under `pDiag`. -/
theorem not_tendstoInDistribution_pDiag {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (Z : Ω' → ℝ) :
    ¬ TendstoInDistribution
      (fun (n : ℕ) ω ↦ fgScore (pairTime n) (pairStatus εA εB n ω) 0 (fun _ => 1) (pairCov n)
        β₀U / √(n : ℝ)) atTop Z (fun _ ↦ pDiag) P' := by
  intro h
  obtain ⟨K, hK⟩ := ProbabilityTheory.exists_forall_measure_lt_norm_le_of_tendstoInDistribution h
    (ε := ENNReal.ofReal (1 / 4)) (by norm_num)
  -- A sample size with `(n / 2) / (3 √n) > K`: `n = 2 m²`.
  set m : ℕ := ⌈6 * |K|⌉₊ + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hmK : 6 * |K| < m := by
    have := Nat.le_ceil (6 * |K|)
    rw [hm]
    push_cast
    linarith
  set n : ℕ := 2 * m ^ 2 with hn
  have hn2 : n / 2 = m ^ 2 := by omega
  have hsq : √(n : ℝ) = m * √2 := by
    rw [hn]
    push_cast
    rw [show (2 : ℝ) * m ^ 2 = m ^ 2 * 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hm0.le]
  have hval : ∀ x ∈ {x : Fin 4 × Fin 4 | εA x = some 0 ∧ εB x ≠ some 0},
      x ∈ (fun x _ => x) ⁻¹' {ω | K < ‖fgScore (pairTime n) (pairStatus εA εB n ω) 0
        (fun _ => 1) (pairCov n) β₀U / √(n : ℝ)‖} := fun x hx => by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [fgScore_pair, hn2, hsq]
    simp only [pairScore, hx.1, hx.2, ↓reduceIte, add_zero, sum_const, card_range, nsmul_eq_mul,
      pairMean_β₀U]
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : √(2 : ℝ) < 2 := by
      rw [Real.sqrt_lt' two_pos]
      norm_num
    rw [show (m : ℝ) ^ 2 * (1 - 2 / 3) / (m * √2) = m / (3 * √2) by field_simp; ring,
      lt_div_iff₀ (by positivity)]
    nlinarith [le_abs_self K, abs_nonneg K, Real.sqrt_nonneg 2]
  have hle := (measure_mono hval).trans ((Measure.le_map_apply measurable_diag.aemeasurable _).trans
    (hK n))
  rw [← ofReal_measureReal, μU_real, show
    (univ.filter fun x => εA x = some 0 ∧ εB x ≠ some 0).card = 6 by decide,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hle
  norm_num at hle

end MathlibExtTest.Probability.Statistics.FineGrayScoreCLT
