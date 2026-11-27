/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import MathlibExt.Probability.CramerDecomposition

/-!
# A reversible linear additive noise model is Gaussian

`gaussian_of_indepFun_backward` characterizes the marginal laws of a nondegenerate
linear additive noise model that admits an independent backward residual. We prove the
two-variable case of the Darmois–Skitovich argument using finite differences of the
logarithms of the characteristic function moduli, then apply Cramér's decomposition
theorem to independent symmetrizations.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace MathlibExt.ComputerScience.LinearNonGaussianIdentifiabilityWanted

-- Independence in the coordinates (A, B) and (A + B, aA + bB) gives this identity.
private def Factors (f g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ s t, f (s + a * t) * g (s + b * t) = (f s * g s) * (f (a * t) * g (b * t))

private lemma Factors.swap {f g : ℝ → ℝ} {a b : ℝ} (h : Factors f g a b) :
    Factors g f b a := fun s t => by simpa only [mul_comm] using h s t

-- A sufficiently small uniform step can be iterated to reach any real number.
private lemma of_small_steps {p : ℝ → Prop} (h₀ : p 0)
    (step : ∀ᶠ h in 𝓝 0, ∀ x, p x → p (x + h)) (x : ℝ) : p x := by
  have hs : ∀ᶠ n : ℕ in atTop, ∀ z, p z → p (z + x / n) :=
    (tendsto_const_div_atTop_nhds_zero_nat x).eventually step
  obtain ⟨n, hn, hstep⟩ := ((eventually_gt_atTop 0).and hs).exists
  have hi (k : ℕ) : p (k * (x / n)) := by
    induction k with
    | zero => simpa using h₀
    | succ k ih => simpa [Nat.cast_succ, add_mul] using hstep _ ih
  simpa [mul_div_cancel₀ x (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn.ne')] using hi n

private lemma Factors.nonzero {f g : ℝ → ℝ} {a b : ℝ} (h : Factors f g a b)
    (ha : a ≠ 0) (hb : b ≠ 0) (hf : Continuous f) (hg : Continuous g)
    (hf₀ : f 0 ≠ 0) (hg₀ : g 0 ≠ 0) (x : ℝ) : f x ≠ 0 ∧ g x ≠ 0 := by
  have near (c : ℝ) : ∀ᶠ u in 𝓝 0, f (a * (u / c)) * g (b * (u / c)) ≠ 0 := by
    have hc : Continuous (fun u => f (a * (u / c)) * g (b * (u / c))) := by fun_prop
    exact hc.continuousAt.eventually_ne (by simpa using mul_ne_zero hf₀ hg₀)
  apply of_small_steps (p := fun z => f z ≠ 0 ∧ g z ≠ 0) ⟨hf₀, hg₀⟩ _ x
  filter_upwards [near a, near b] with u hua hub
  intro z hz
  have extend (t : ℝ) (ht : f (a * t) * g (b * t) ≠ 0) :
      f (z + a * t) ≠ 0 ∧ g (z + b * t) ≠ 0 :=
    mul_ne_zero_iff.mp ((h z t).symm ▸ mul_ne_zero (mul_ne_zero hz.1 hz.2) ht)
  constructor
  · simpa [mul_div_cancel₀ _ ha] using (extend _ hua).1
  · simpa [mul_div_cancel₀ _ hb] using (extend _ hub).2

-- With one zero coefficient, the other modulus is identically one.
private lemma Factors.one_of_zero {f g : ℝ → ℝ} {a : ℝ} (h : Factors f g a 0)
    (ha : a ≠ 0) (hg : Continuous g) (hf₀ : f 0 = 1) (hg₀ : g 0 = 1)
    (he : ∀ x, f (-x) = f x) (hp : ∀ x, 0 ≤ f x) (x : ℝ) : f x = 1 := by
  apply of_small_steps (p := fun z => f z = 1) hf₀ _ x
  filter_upwards [hg.continuousAt.eventually_ne (hg₀ ▸ one_ne_zero)] with u hu
  have add (z : ℝ) : f (u + z) = f u * f z := by
    have hh := h u (z / a)
    simp only [mul_div_cancel₀ _ ha, zero_mul, add_zero, hg₀, mul_one] at hh
    exact mul_right_cancel₀ hu (hh.trans (by ring))
  have hsq := add (-u)
  rw [add_neg_cancel, hf₀, he] at hsq
  have hue : f u = 1 := by nlinarith [hp u]
  intro z hz
  rw [add_comm, add, hue, hz, one_mul]

-- Taking one difference in each independent coordinate eliminates both one-variable terms.
private lemma second_diff {F G H K : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b) (ha : a ≠ 0)
    (heq : ∀ s t, F (s + a * t) + G (s + b * t) = H s + K t)
    (he : ∀ x, F (-x) = F x) (h₀ : F 0 = 0) (x u : ℝ) :
    F (x + u + u) - 2 * F (x + u) + F x = 2 * F u := by
  let D (f : ℝ → ℝ) (z i j : ℝ) := f (z + i + j) - f (z + i) - f (z + j) + f z
  have mixed (s t i j : ℝ) :
      D F (s + a * t) i (a * j) + D G (s + b * t) i (b * j) = 0 := by
    dsimp [D]
    linear_combination (norm := ring_nf)
      heq (s + i) (t + j) - heq (s + i) t - heq s (t + j) + heq s t
  have at_zero (z : ℝ) : D F z u u + D G 0 u (b * (u / a)) = 0 := by
    let t := z / (a - b)
    have hzt : -(b * t) + a * t = z := by dsimp [t]; field_simp [sub_ne_zero.mpr hab]; ring
    simpa only [neg_mul, hzt, neg_add_cancel, mul_div_cancel₀ _ ha] using mixed (-b * t) t u (u / a)
  have hc := (at_zero x).trans (at_zero (-u)).symm
  dsimp [D] at hc
  simp only [neg_add_cancel, zero_add, he, h₀] at hc
  linarith

private lemma quadratic_of_second_diff {F : ℝ → ℝ} (hF : Continuous F)
    (h₀ : F 0 = 0) (he : ∀ x, F (-x) = F x)
    (h : ∀ x u, F (x + u + u) - 2 * F (x + u) + F x = 2 * F u)
    (x : ℝ) : F x = F 1 * x ^ 2 := by
  have nat_mul (u : ℝ) (n : ℕ) : F (n * u) = F u * n ^ 2 := by
    induction n using Nat.twoStepInduction with
    | zero => simp [h₀]
    | one => simp
    | more n ih ih' =>
      push_cast at ih' ⊢
      rw [add_mul, one_mul] at ih'
      rw [show ((n : ℝ) + 2) * u = n * u + u + u by ring]
      linarith [h (n * u) u]
  have int_val (z : ℤ) : F z = F 1 * (z : ℝ) ^ 2 := by
    cases z with
    | ofNat n => simpa using nat_mul 1 n
    | negSucc n =>
      rw [Int.cast_negSucc, he, neg_sq]
      simpa using nat_mul 1 (n + 1)
  refine Rat.denseRange_cast.induction_on (p := fun z : ℝ => F z = F 1 * z ^ 2) x
    (isClosed_eq hF (by fun_prop)) ?_
  intro q
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hq : (q.den : ℝ) * (q : ℝ) = q.num := by rw [Rat.cast_def]; field_simp
  have hn := nat_mul (q : ℝ) q.den
  rw [hq, int_val, ← hq] at hn
  apply mul_right_cancel₀ (pow_ne_zero 2 hden)
  linear_combination -hn

private lemma Factors.exp_quadratic {f g : ℝ → ℝ} {a b : ℝ} (h : Factors f g a b)
    (hab : a ≠ b) (ha : a ≠ 0) (hf : Continuous f) (hf₀ : f 0 = 1)
    (hp : ∀ x, 0 < f x) (hq : ∀ x, 0 < g x) (he : ∀ x, f (-x) = f x) (x : ℝ) :
    f x = Real.exp (Real.log (f 1) * x ^ 2) := by
  have eqn (s t : ℝ) :
      Real.log (f (s + a * t)) + Real.log (g (s + b * t)) =
        (Real.log (f s) + Real.log (g s)) + (Real.log (f (a * t)) + Real.log (g (b * t))) := by
    simpa only [Real.log_mul (mul_pos (hp _) (hq _)).ne' (mul_pos (hp _) (hq _)).ne',
      Real.log_mul (hp _).ne' (hq _).ne'] using congrArg Real.log (h s t)
  have even_log (u : ℝ) : Real.log (f (-u)) = Real.log (f u) := by rw [he]
  have log_zero : Real.log (f 0) = 0 := by simp [hf₀]
  rw [← Real.exp_log (hp x)]
  congr 1
  exact quadratic_of_second_diff (F := fun z => Real.log (f z))
    (hf.log fun z => (hp z).ne') log_zero even_log
    (second_diff (F := fun z => Real.log (f z)) (G := fun z => Real.log (g z))
      (H := fun s => Real.log (f s) + Real.log (g s))
      (K := fun t => Real.log (f (a * t)) + Real.log (g (b * t))) hab ha eqn even_log log_zero) x

-- Symmetrization removes the phase of the characteristic function. Once the difference
-- of independent copies is Gaussian, Cramér's theorem recovers its first summand.
private lemma isGaussian_of_modulus {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {k : ℝ} (hk : k ≤ 0) (h : ∀ t, ‖charFun μ t‖ = Real.exp (k * t ^ 2)) :
    IsGaussian μ := by
  let v : NNReal := ⟨-4 * k, by linarith⟩
  have hi : IndepFun Prod.fst (fun p : ℝ × ℝ => -p.2) (μ.prod μ) :=
    indepFun_prod (X := id) (Y := fun z : ℝ => -z) measurable_id measurable_id.neg
  have hsum : HasLaw (fun p : ℝ × ℝ => p.1 + -p.2) (gaussianReal 0 v) (μ.prod μ) := by
    refine ⟨by fun_prop, Measure.ext_of_charFun (funext fun t => ?_)⟩
    rw [hi.charFun_map_fun_add_eq_mul (by fun_prop) (by fun_prop), Pi.mul_apply]
    have hneg := charFun_map_mul_comp (μ := μ.prod μ) measurable_snd.aemeasurable (-1) t
    simp only [neg_one_mul, measurePreserving_snd.map_eq, charFun_neg] at hneg
    rw [measurePreserving_fst.map_eq, hneg, Complex.mul_conj', h, charFun_gaussianReal]
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
    congr 1
    rw [show (v : ℝ) = -4 * k from rfl]
    push_cast
    ring
  have hg := (MathlibExt.Probability.CramerDecompositionWanted.cramer_decomposition
    measurable_fst (by fun_prop) hi hsum.hasGaussianLaw).1
  simpa only [measurePreserving_fst.map_eq] using hg.isGaussian_map

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma nondegenerate_law {X : Ω → ℝ} (h : HasGaussianLaw X P)
    (hc : ∀ c : ℝ, ¬ X =ᵐ[P] fun _ => c) :
    ∃ (m : ℝ) (v : NNReal), v ≠ 0 ∧ P.map X = gaussianReal m v := by
  refine ⟨_, _, ?_, h.map_eq_gaussianReal⟩
  intro hv
  apply hc (∫ ω, X ω ∂P)
  apply ae_of_ae_map (p := fun x => x = ∫ ω, X ω ∂P) h.aemeasurable
  rw [h.map_eq_gaussianReal, hv, gaussianReal_zero_var]
  simp

private lemma not_unit_modulus {X : Ω → ℝ} (hX : Measurable X)
    (hc : ∀ c : ℝ, ¬ X =ᵐ[P] fun _ => c) : ¬ ∀ t, ‖charFun (P.map X) t‖ = 1 := by
  intro h
  have := isGaussian_of_modulus (μ := P.map X) (k := 0) le_rfl (by simpa using h)
  obtain ⟨m, v, hv, hlaw⟩ := nondegenerate_law (IsGaussian.hasGaussianLaw hX.aemeasurable) hc
  have h₁ := h 1
  rw [hlaw, charFun_gaussianReal, Complex.norm_exp, Real.exp_eq_one_iff] at h₁
  exact hv (by simpa using h₁)

private lemma charFun_linear {X N : Ω → ℝ} (hX : Measurable X) (hN : Measurable N)
    (hi : IndepFun X N P) (a b t : ℝ) :
    charFun (P.map (fun ω => a * X ω + b * N ω)) t =
      charFun (P.map X) (a * t) * charFun (P.map N) (b * t) := by
  have hi' : IndepFun (fun ω => a * X ω) (fun ω => b * N ω) P :=
    hi.comp (show Measurable (a * ·) by fun_prop) (show Measurable (b * ·) by fun_prop)
  rw [hi'.charFun_map_fun_add_eq_mul (by fun_prop) (by fun_prop), Pi.mul_apply,
    charFun_map_mul_comp hX.aemeasurable, charFun_map_mul_comp hN.aemeasurable]

private lemma modulus_factors {A B : Ω → ℝ} {a b : ℝ} (hA : Measurable A) (hB : Measurable B)
    (hi : IndepFun A B P)
    (hj : IndepFun (fun ω => A ω + B ω) (fun ω => a * A ω + b * B ω) P) :
    Factors (fun t => ‖charFun (P.map A) t‖) (fun t => ‖charFun (P.map B) t‖) a b := by
  intro s t
  have eqn := charFun_linear (by fun_prop) (by fun_prop) hj s t 1
  have heq : (fun ω => s * (A ω + B ω) + t * (a * A ω + b * B ω)) =
      (fun ω => (s + a * t) * A ω + (s + b * t) * B ω) := by funext ω; ring
  have hsum : (fun ω => A ω + B ω) = (fun ω => 1 * A ω + 1 * B ω) := by simp
  rw [heq, charFun_linear hA hB hi, hsum, charFun_linear hA hB hi, charFun_linear hA hB hi] at eqn
  simpa [norm_mul] using congrArg (‖·‖) eqn

end

private lemma Factors.coeff_ne_zero {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : ℝ}
    (h : Factors (fun t => ‖charFun μ t‖) (fun t => ‖charFun ν t‖) a b)
    (hab : a ≠ b) (hn : ¬ ∀ t, ‖charFun ν t‖ = 1) : a ≠ 0 := by
  rintro rfl
  exact hn (h.swap.one_of_zero hab.symm continuous_charFun.norm (by simp) (by simp)
    (by simp) (fun _ => norm_nonneg _))

private lemma Factors.isGaussian_left {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : ℝ}
    (h : Factors (fun t => ‖charFun μ t‖) (fun t => ‖charFun ν t‖) a b)
    (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) : IsGaussian μ := by
  have hn := h.nonzero ha hb continuous_charFun.norm continuous_charFun.norm (by simp) (by simp)
  exact isGaussian_of_modulus (Real.log_nonpos (norm_nonneg _) (norm_charFun_le_one _))
    (h.exp_quadratic hab ha continuous_charFun.norm (by simp)
      (fun t => lt_of_le_of_ne (norm_nonneg _) (hn t).1.symm)
      (fun t => lt_of_le_of_ne (norm_nonneg _) (hn t).2.symm) (by simp))

/-- **A reversible linear additive noise model is Gaussian** (Peters, Mooij, Janzing and
Schölkopf, *Causal discovery with continuous additive noise models*, JMLR 15 (2014), the "only
if" direction of Proposition 13, after Shimizu et al. 2006). Let `X` and `N` be independent
real random variables, neither almost surely constant, and let `Y = φ X + N` with `φ ≠ 0`. If
there is `ψ ∈ ℝ` such that `Ñ = X - ψ Y` is independent of `Y`, then `X` and `N` have
nondegenerate Gaussian laws. -/
theorem gaussian_of_indepFun_backward {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X N : Ω → ℝ} (hX : Measurable X)
    (hN : Measurable N) (hXN : IndepFun X N P) (hXc : ∀ c : ℝ, ¬ X =ᵐ[P] fun _ => c)
    (hNc : ∀ c : ℝ, ¬ N =ᵐ[P] fun _ => c) {φ : ℝ} (hφ : φ ≠ 0) {ψ : ℝ}
    (hback : IndepFun (fun ω => X ω - ψ * (φ * X ω + N ω)) (fun ω => φ * X ω + N ω) P) :
    (∃ (m : ℝ) (v : NNReal), v ≠ 0 ∧ P.map X = gaussianReal m v) ∧
      ∃ (m : ℝ) (v : NNReal), v ≠ 0 ∧ P.map N = gaussianReal m v := by
  -- Scale the cause so that the forward coefficients are both one.
  let A (ω : Ω) := φ * X ω
  let a := φ⁻¹ - ψ
  let b := -ψ
  have hA : Measurable A := measurable_const.mul hX
  have hAN : IndepFun A N P :=
    hXN.comp (show Measurable (φ * ·) by fun_prop) measurable_id
  have hAc (c : ℝ) (hc : A =ᵐ[P] fun _ => c) : False := by
    apply hXc (c / φ)
    filter_upwards [hc] with ω hω
    exact (eq_div_iff hφ).mpr ((mul_comm _ _).trans hω)
  have hab : a ≠ b := by
    intro he
    apply inv_ne_zero hφ
    dsimp [a, b] at he
    linarith
  have hres : (fun ω => X ω - ψ * (φ * X ω + N ω)) = (fun ω => a * A ω + b * N ω) := by
    funext ω
    dsimp [a, b, A]
    field_simp
    ring
  rw [hres] at hback
  have hf := modulus_factors hA hN hAN hback.symm
  have ha := hf.coeff_ne_zero hab (not_unit_modulus hN hNc)
  have hb := hf.swap.coeff_ne_zero hab.symm (not_unit_modulus hA hAc)
  have := hf.isGaussian_left hab ha hb
  have := hf.swap.isGaussian_left hab.symm hb ha
  have hGA := IsGaussian.hasGaussianLaw (P := P) hA.aemeasurable
  have hGX : HasGaussianLaw X P := by
    simpa [A, smul_eq_mul, ← mul_assoc, hφ] using hGA.fun_smul φ⁻¹
  exact ⟨nondegenerate_law hGX hXc,
    nondegenerate_law (IsGaussian.hasGaussianLaw hN.aemeasurable) hNc⟩

end MathlibExt.ComputerScience.LinearNonGaussianIdentifiabilityWanted
