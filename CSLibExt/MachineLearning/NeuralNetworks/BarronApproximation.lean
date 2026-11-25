/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.NeuralNetworks.BarronSpace
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

/-!
# The direct approximation theorem for the Barron space

W. E, C. Ma and L. Wu (*The Barron space and the flow-induced function spaces for neural network
models*, Constr. Approx. 55 (2022), arXiv:1906.08039, Theorem 4): every `f` of finite Barron norm
is approximated in `L²(μ)`, for any probability measure `μ` carried by the cube `[0, 1]^d`, by a
two-layer ReLU network of width `m` with squared error at most `3 ‖f‖_B² / m` and path norm at
most `2 ‖f‖_B` (`barron_direct_approximation`).

The proof follows §2.5.3 of the source. Pick a representation `ρ` of `f` whose second moment
`M₂ = 𝔼_ρ |a|² (‖b‖₁ + |c|)²` is below `1.21 ‖f‖_B²`, and sample the `m` neurons i.i.d. from `ρ`
(the product measure `ρ^m`). For each `x` in the cube the expected squared error is the variance
of an i.i.d. sample mean, at most `M₂ / m` (`variance_sum_pi`); Tonelli integrates this over `μ`.
The expected path norm is `𝔼_ρ |a| (‖b‖₁ + |c|) ≤ √M₂` (Cauchy–Schwarz). Instead of Markov's
inequality on two events, the proof averages the single functional
`error / (3 ‖f‖_B² / m) + path norm / (2 ‖f‖_B)`, whose mean is below
`1.21 / 3 + 1.1 / 2 < 1`, so some sample makes it smaller than `1`, which gives both bounds. A
function of Barron norm `0` vanishes on the cube and is approximated by the zero network.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

/-- The real path weight `|a| (‖b‖₁ + |c|)` of one neuron. -/
private noncomputable def weight (θ : ℝ × (Fin d → ℝ) × ℝ) : ℝ :=
  |θ.1| * (∑ j, |θ.2.1 j| + |θ.2.2|)

private lemma weight_nonneg (θ : ℝ × (Fin d → ℝ) × ℝ) : 0 ≤ weight θ := by
  unfold weight
  exact mul_nonneg (abs_nonneg _) (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (abs_nonneg _))

private lemma enorm_weight (θ : ℝ × (Fin d → ℝ) × ℝ) :
    ‖θ.1‖ₑ * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) = ENNReal.ofReal (weight θ) := by
  simp only [weight, Real.enorm_eq_ofReal_abs]
  rw [ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]

private lemma abs_reluNeuron_le {x : Fin d → ℝ} (hx : x ∈ unitCube d)
    (θ : ℝ × (Fin d → ℝ) × ℝ) : |reluNeuron θ x| ≤ weight θ := by
  have hxj : ∀ j, |x j| ≤ 1 := fun j => by
    have h := hx j (Set.mem_univ j)
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  unfold reluNeuron weight
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : |max (∑ j, θ.2.1 j * x j + θ.2.2) 0| ≤ |∑ j, θ.2.1 j * x j + θ.2.2| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  refine h1.trans ((abs_add_le _ _).trans (add_le_add_left ?_ _))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hxj j)

private lemma enorm_reluNeuron_le {x : Fin d → ℝ} (hx : x ∈ unitCube d)
    (θ : ℝ × (Fin d → ℝ) × ℝ) : ‖reluNeuron θ x‖ₑ ≤ ENNReal.ofReal (weight θ) := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (abs_reluNeuron_le hx θ)

private lemma continuous_reluNeuron :
    Continuous fun p : (Fin d → ℝ) × (ℝ × (Fin d → ℝ) × ℝ) => reluNeuron p.2 p.1 := by
  unfold reluNeuron
  fun_prop

private lemma measurable_reluNeuron (x : Fin d → ℝ) :
    Measurable fun θ : ℝ × (Fin d → ℝ) × ℝ => reluNeuron θ x :=
  (continuous_reluNeuron.comp (Continuous.prodMk_right x)).measurable

private lemma measurable_weight : Measurable (weight (d := d)) := by
  unfold weight
  fun_prop

/-- Cauchy–Schwarz against the constant `1` for a probability measure. -/
private lemma lintegral_le_rpow_sq {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {g : α → ℝ≥0∞} (hg : AEMeasurable g ρ) :
    ∫⁻ a, g a ∂ρ ≤ (∫⁻ a, g a ^ 2 ∂ρ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, measure_univ,
    ENNReal.rpow_two] at h
  simpa using h

/-- **Monte Carlo error of an i.i.d. sample mean.** For `φ ∈ L²(ρ)` and `m ≥ 1` i.i.d. samples
`θ₁, …, θₘ ∼ ρ`, the mean squared error of `(1/m) ∑ₖ φ(θₖ)` as an estimate of `∫ φ dρ` is at most
`(1/m) ∫ φ² dρ`. -/
private lemma lintegral_sampleMean_sub_sq_le {Θ : Type*} [MeasurableSpace Θ] (ρ : Measure Θ)
    [IsProbabilityMeasure ρ] {m : ℕ} (hm : 0 < m) {φ : Θ → ℝ} (hφ : MemLp φ 2 ρ) :
    ∫⁻ ω, ‖(∫ θ, φ θ ∂ρ) - (m : ℝ)⁻¹ * ∑ k, φ (ω k)‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin m => ρ) ≤
      (m : ℝ≥0∞)⁻¹ * ∫⁻ θ, ‖φ θ‖ₑ ^ 2 ∂ρ := by
  set P := Measure.pi fun _ : Fin m => ρ with hP
  set X : (Fin m → Θ) → ℝ := fun ω => (m : ℝ)⁻¹ * ∑ k, φ (ω k) with hX
  have hcomp : ∀ k : Fin m, MemLp (fun ω : Fin m → Θ => φ (ω k)) 2 P := fun k =>
    hφ.comp_measurePreserving (measurePreserving_eval _ k)
  have hXmem : MemLp X 2 P := (memLp_finsetSum _ fun k _ => hcomp k).const_mul _
  have hint : ∀ k : Fin m, ∫ ω, φ (ω k) ∂P = ∫ θ, φ θ ∂ρ := by
    intro k
    have hmap := (measurePreserving_eval (fun _ : Fin m => ρ) k).map_eq
    have h := integral_map (μ := P) (measurable_pi_apply k).aemeasurable
      (hmap.symm ▸ hφ.aestronglyMeasurable : AEStronglyMeasurable φ (P.map fun ω => ω k))
    rw [hP, hmap] at h
    exact h.symm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmean : P[X] = ∫ θ, φ θ ∂ρ := by
    simp only [hX]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (hcomp k).integrable one_le_two]
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : variance X P = (m : ℝ)⁻¹ * variance φ ρ := by
    have h1 : variance X P = ((m : ℝ)⁻¹) ^ 2 * variance (fun ω => ∑ k, φ (ω k)) P :=
      variance_const_mul _ _ _
    have h2 : variance (fun ω : Fin m → Θ => ∑ k, φ (ω k)) P = m * variance φ ρ := by
      have h := variance_sum_pi (μ := fun _ : Fin m => ρ) (X := fun _ => φ) (fun _ => hφ)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      rw [← h, hP]
      congr 1
      funext ω
      simp [Finset.sum_apply]
    rw [h1, h2]
    field_simp
  calc ∫⁻ ω, ‖(∫ θ, φ θ ∂ρ) - X ω‖ₑ ^ 2 ∂P = evariance X P := by
        rw [evariance, hmean]
        congr 1
        funext ω
        rw [enorm_sub_rev]
    _ = ENNReal.ofReal (variance X P) := (ofReal_variance hXmem).symm
    _ = (m : ℝ≥0∞)⁻¹ * ENNReal.ofReal (variance φ ρ) := by
        rw [hvar, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hmpos,
          ENNReal.ofReal_natCast]
    _ = (m : ℝ≥0∞)⁻¹ * evariance φ ρ := by rw [ofReal_variance hφ]
    _ ≤ (m : ℝ≥0∞)⁻¹ * ∫⁻ θ, ‖φ θ‖ₑ ^ 2 ∂ρ := by
        gcongr
        rw [evariance_def' hφ.aestronglyMeasurable]
        exact tsub_le_self

private lemma second_moment_eq (ρ : Measure (ℝ × (Fin d → ℝ) × ℝ)) :
    ∫⁻ θ, ‖θ.1‖ₑ ^ 2 * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) ^ 2 ∂ρ =
      ∫⁻ θ, ENNReal.ofReal (weight θ) ^ 2 ∂ρ := by
  congr 1
  funext θ
  rw [← mul_pow, enorm_weight]

/-- A representation `ρ` bounds `|f(x)|` on the cube by its second moment. -/
private lemma enorm_le_of_isBarronRepresentation {f : (Fin d → ℝ) → ℝ}
    {ρ : Measure (ℝ × (Fin d → ℝ) × ℝ)} (h : IsBarronRepresentation f ρ) {x : Fin d → ℝ}
    (hx : x ∈ unitCube d) :
    ‖f x‖ₑ ≤ (∫⁻ θ, ‖θ.1‖ₑ ^ 2 * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) ^ 2 ∂ρ) ^ (1 / 2 : ℝ) := by
  have := h.1
  rw [(h.2 x hx).2, second_moment_eq]
  calc ‖∫ θ, reluNeuron θ x ∂ρ‖ₑ ≤ ∫⁻ θ, ‖reluNeuron θ x‖ₑ ∂ρ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ θ, ENNReal.ofReal (weight θ) ∂ρ := lintegral_mono fun θ => enorm_reluNeuron_le hx θ
    _ ≤ _ := lintegral_le_rpow_sq ρ measurable_weight.ennreal_ofReal.aemeasurable

private lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private lemma lt_of_mul_inv_lt_one {a c : ℝ≥0∞} (h : a * c⁻¹ < 1) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    a < c := by
  calc a = a * c⁻¹ * c := by rw [mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]
    _ < 1 * c := ENNReal.mul_lt_mul_left hc0 hct h
    _ = c := one_mul c

/-- **Direct approximation theorem for the Barron space** (W. E, C. Ma and L. Wu, *The Barron
space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022),
Theorem 4; Theorem 3.1 of E, Ma and Wu, *A priori estimates of the population risk for
two-layer neural networks*, Commun. Math. Sci. 17 (2019), is the analogous statement for networks
without bias on `[-1, 1]^d`). Let `f` have finite Barron norm, let
`μ` be a probability measure carried by the cube `[0, 1]^d`, and let `m ≥ 1`. There are neuron
parameters `θ₁, …, θₘ = (aₖ, bₖ, cₖ)` such that the network
`f_m(x) = (1/m) ∑ₖ aₖ σ(⟨bₖ, x⟩ + cₖ)` satisfies `‖f - f_m‖²_{L²(μ)} ≤ 3 ‖f‖_B² / m`, and its
path norm satisfies `(1/m) ∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|) ≤ 2 ‖f‖_B`. -/
theorem barron_direct_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : barronNorm f < ⊤) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (unitCube d)ᶜ = 0) {m : ℕ} (hm : 0 < m) :
    ∃ θ : Fin m → ℝ × (Fin d → ℝ) × ℝ,
      ∫⁻ x, ‖f x - (m : ℝ)⁻¹ * ∑ k, reluNeuron (θ k) x‖ₑ ^ 2 ∂μ ≤
          3 * barronNorm f ^ 2 / m ∧
        (m : ENNReal)⁻¹ * ∑ k, ‖(θ k).1‖ₑ * (∑ j, ‖(θ k).2.1 j‖ₑ + ‖(θ k).2.2‖ₑ) ≤
          2 * barronNorm f := by
  set B := barronNorm f with hBdef
  have hae : ∀ᵐ x ∂μ, x ∈ unitCube d := ae_iff.2 hμ
  rcases eq_or_ne B 0 with hB0 | hB0
  · -- A function of Barron norm zero vanishes on the cube; the zero network approximates it.
    refine ⟨fun _ => 0, ?_, by simp⟩
    have hzero : ∀ᵐ x ∂μ, ‖f x - (m : ℝ)⁻¹ *
        ∑ k, reluNeuron ((fun _ : Fin m => (0 : ℝ × (Fin d → ℝ) × ℝ)) k) x‖ₑ ^ 2 = 0 := by
      filter_upwards [hae] with x hx
      have hfx : ‖f x‖ₑ = 0 := by
        by_contra hne
        have hpos : B < ‖f x‖ₑ := hB0 ▸ pos_iff_ne_zero.2 hne
        obtain ⟨ρ, hρ⟩ := iInf_lt_iff.1 hpos
        obtain ⟨hrep, hlt⟩ := iInf_lt_iff.1 hρ
        exact absurd (enorm_le_of_isBarronRepresentation hrep hx) (not_le.2 hlt)
      rw [enorm_eq_zero] at hfx
      simp [hfx, reluNeuron]
    rw [lintegral_congr_ae hzero]
    simp
  -- From now on `0 < ‖f‖_B < ∞`.
  have hBtop : B ≠ ⊤ := hf.ne
  set b := B.toReal with hb_def
  have hb : 0 < b := ENNReal.toReal_pos hB0 hBtop
  have hBb : B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBtop).symm
  -- A representation whose second moment is within a factor `1.21` of `‖f‖_B²`.
  have hBlt : B < ENNReal.ofReal (11 / 10 * b) := by
    rw [hBb]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨ρ, hρ⟩ := iInf_lt_iff.1 hBlt
  obtain ⟨hrep, hlt⟩ := iInf_lt_iff.1 hρ
  have := hrep.1
  set M2 := ∫⁻ θ, ‖θ.1‖ₑ ^ 2 * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) ^ 2 ∂ρ with hM2_def
  set s := M2 ^ (1 / 2 : ℝ) with hs_def
  have hM2s : M2 = s ^ 2 := (rpow_half_sq M2).symm
  have hstop : s ≠ ⊤ := ne_top_of_lt hlt
  have hM2top : M2 ≠ ⊤ := by rw [hM2s]; exact ENNReal.pow_ne_top hstop
  set σ := s.toReal with hσ_def
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  have hσb : σ < 11 / 10 * b := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hsσ : s = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hstop).symm
  -- Square integrability of each neuron output on the cube.
  have hmem : ∀ x ∈ unitCube d, MemLp (fun θ => reluNeuron θ x) 2 ρ := by
    intro x hx
    refine (memLp_two_iff_integrable_sq (measurable_reluNeuron x).aestronglyMeasurable).2
      ⟨((measurable_reluNeuron x).pow_const 2).aestronglyMeasurable, ?_⟩
    change ∫⁻ θ, ‖reluNeuron θ x ^ 2‖ₑ ∂ρ < ⊤
    calc ∫⁻ θ, ‖reluNeuron θ x ^ 2‖ₑ ∂ρ ≤ ∫⁻ θ, ENNReal.ofReal (weight θ) ^ 2 ∂ρ :=
          lintegral_mono fun θ => by rw [enorm_pow]; gcongr; exact enorm_reluNeuron_le hx θ
      _ = M2 := (second_moment_eq ρ).symm
      _ < ⊤ := hM2top.lt_top
  -- The function represented by `ρ`, measurable in `x`.
  set F : (Fin d → ℝ) → ℝ := fun x => ∫ θ, reluNeuron θ x ∂ρ with hF_def
  have hFm : Measurable F :=
    (continuous_reluNeuron.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  set P := Measure.pi fun _ : Fin m => ρ with hP
  have hm0 : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  set E : (Fin m → ℝ × (Fin d → ℝ) × ℝ) → ℝ≥0∞ := fun ω =>
    ∫⁻ x, ‖f x - (m : ℝ)⁻¹ * ∑ k, reluNeuron (ω k) x‖ₑ ^ 2 ∂μ with hE_def
  set N : (Fin m → ℝ × (Fin d → ℝ) × ℝ) → ℝ≥0∞ := fun ω =>
    (m : ℝ≥0∞)⁻¹ * ∑ k, ‖(ω k).1‖ₑ * (∑ j, ‖(ω k).2.1 j‖ₑ + ‖(ω k).2.2‖ₑ) with hN_def
  -- (i) The expected squared error is at most `M2 / m`.
  have hEint : ∫⁻ ω, E ω ∂P ≤ (m : ℝ≥0∞)⁻¹ * M2 := by
    set h : (Fin m → ℝ × (Fin d → ℝ) × ℝ) → (Fin d → ℝ) → ℝ≥0∞ := fun ω x =>
      ‖F x - (m : ℝ)⁻¹ * ∑ k, reluNeuron (ω k) x‖ₑ ^ 2 with hh
    have hEh : ∀ ω, E ω = ∫⁻ x, h ω x ∂μ := fun ω => by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [hh, hF_def, (hrep.2 x hx).2]
    have hmeas : Measurable (Function.uncurry h) := by
      refine (((hFm.comp measurable_snd).sub ((Finset.measurable_sum _ fun k _ =>
        continuous_reluNeuron.measurable.comp (measurable_snd.prodMk
          ((measurable_pi_apply k).comp measurable_fst))).const_mul _)).enorm).pow_const 2
    calc ∫⁻ ω, E ω ∂P = ∫⁻ ω, ∫⁻ x, h ω x ∂μ ∂P := lintegral_congr fun ω => hEh ω
      _ = ∫⁻ x, ∫⁻ ω, h ω x ∂P ∂μ := lintegral_lintegral_swap hmeas.aemeasurable
      _ ≤ ∫⁻ _x, (m : ℝ≥0∞)⁻¹ * M2 ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          refine (lintegral_sampleMean_sub_sq_le ρ hm (hmem x hx)).trans ?_
          gcongr
          rw [hM2_def, second_moment_eq]
          refine lintegral_mono fun θ => ?_
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
            ← ENNReal.ofReal_pow (weight_nonneg θ)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _)
            (abs_reluNeuron_le hx θ) 2)
      _ = (m : ℝ≥0∞)⁻¹ * M2 := by simp
  -- (ii) The expected path norm is at most `s`.
  have hNmeas : Measurable N := by
    simp only [hN_def, enorm_weight]
    exact (Finset.measurable_sum _ fun k _ =>
      (measurable_weight.ennreal_ofReal).comp (measurable_pi_apply k)).const_mul _
  have hNint : ∫⁻ ω, N ω ∂P ≤ s := by
    simp only [hN_def, enorm_weight]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0),
      lintegral_finsetSum (f := fun k (ω : Fin m → ℝ × (Fin d → ℝ) × ℝ) =>
        ENNReal.ofReal (weight (ω k))) _ fun k _ =>
          measurable_weight.ennreal_ofReal.comp (measurable_pi_apply k)]
    have hk : ∀ k : Fin m, ∫⁻ ω, ENNReal.ofReal (weight (ω k)) ∂P =
        ∫⁻ θ, ENNReal.ofReal (weight θ) ∂ρ := fun k =>
      (measurePreserving_eval (fun _ : Fin m => ρ) k).lintegral_comp
        measurable_weight.ennreal_ofReal
    simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmtop, one_mul, hs_def, hM2_def,
      second_moment_eq]
    exact lintegral_le_rpow_sq ρ measurable_weight.ennreal_ofReal.aemeasurable
  -- (iii) A combined functional with mean less than `1`.
  set α : ℝ≥0∞ := 3 * B ^ 2 / m with hα_def
  set β : ℝ≥0∞ := 2 * B with hβ_def
  have hα0 : α ≠ 0 := by
    simp [hα_def, hB0, hmtop, ENNReal.div_eq_zero_iff]
  have hαtop : α ≠ ⊤ := by
    simp [hα_def, hBtop, hm0, ENNReal.div_eq_top, ENNReal.mul_eq_top]
  have hβ0 : β ≠ 0 := by simp [hβ_def, hB0]
  have hβtop : β ≠ ⊤ := by simp [hβ_def, hBtop, ENNReal.mul_eq_top]
  have hGint : ∫⁻ ω, (E ω * α⁻¹ + N ω * β⁻¹) ∂P ≤
      (m : ℝ≥0∞)⁻¹ * M2 * α⁻¹ + s * β⁻¹ := by
    rw [lintegral_add_right _ (hNmeas.mul_const _),
      lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hα0),
      lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hβ0)]
    gcongr
  have hbound : (m : ℝ≥0∞)⁻¹ * M2 * α⁻¹ + s * β⁻¹ < 1 := by
    have h3b : 0 < 3 * b ^ 2 := mul_pos (by norm_num) (pow_pos hb 2)
    have h2b : 0 < 2 * b := by linarith
    have hreal : σ ^ 2 / (3 * b ^ 2) + σ / (2 * b) < 1 := by
      have hsq : σ ^ 2 < 121 / 100 * b ^ 2 :=
        calc σ ^ 2 < (11 / 10 * b) ^ 2 := pow_lt_pow_left₀ hσb hσ0 two_ne_zero
          _ = 121 / 100 * b ^ 2 := by ring
      have t1 : σ ^ 2 / (3 * b ^ 2) < 121 / 300 := by
        rw [div_lt_iff₀ h3b]; linarith
      have t2 : σ / (2 * b) < 11 / 20 := by
        rw [div_lt_iff₀ h2b]; linarith
      linarith
    have h1 : (m : ℝ≥0∞)⁻¹ * M2 * α⁻¹ = ENNReal.ofReal (σ ^ 2 / (3 * b ^ 2)) := by
      rw [hα_def, hM2s, hsσ, hBb, ENNReal.div_eq_inv_mul,
        ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hmtop)) (Or.inl (ENNReal.inv_ne_top.2 hm0)),
        inv_inv, ← ENNReal.ofReal_pow hσ0, ← ENNReal.ofReal_pow hb.le,
        show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_div_of_pos h3b, div_eq_mul_inv]
      calc (m : ℝ≥0∞)⁻¹ * ENNReal.ofReal (σ ^ 2) * ((m : ℝ≥0∞) * (ENNReal.ofReal (3 * b ^ 2))⁻¹)
          = ((m : ℝ≥0∞)⁻¹ * m) * (ENNReal.ofReal (σ ^ 2) * (ENNReal.ofReal (3 * b ^ 2))⁻¹) := by
            ring
        _ = _ := by rw [ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
    have h2 : s * β⁻¹ = ENNReal.ofReal (σ / (2 * b)) := by
      rw [hβ_def, hsσ, hBb, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos h2b, div_eq_mul_inv]
    rw [h1, h2, ← ENNReal.ofReal_add (div_nonneg (sq_nonneg σ) h3b.le) (div_nonneg hσ0 h2b.le)]
    exact ENNReal.ofReal_lt_one.2 hreal
  -- (iv) Some sample beats the mean.
  obtain ⟨ω, hω⟩ : ∃ ω, E ω * α⁻¹ + N ω * β⁻¹ < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : ℝ≥0∞) ≤ ∫⁻ ω, (E ω * α⁻¹ + N ω * β⁻¹) ∂P :=
      calc (1 : ℝ≥0∞) = ∫⁻ _ω, 1 ∂P := by simp
        _ ≤ _ := lintegral_mono hcon
    exact absurd (h1.trans_lt (hGint.trans_lt hbound)) (lt_irrefl _)
  refine ⟨ω, ?_, ?_⟩
  · exact (lt_of_mul_inv_lt_one ((le_self_add).trans_lt hω) hα0 hαtop).le
  · exact (lt_of_mul_inv_lt_one ((le_add_self).trans_lt hω) hβ0 hβtop).le

end CSLibExt.MachineLearning.NeuralNetworks
