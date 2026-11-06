/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Characteristic functions detect lattice support

If the characteristic function of a probability measure `μ` on `ℝ` takes the
value `1` at some nonzero frequency `l`, then `μ` is supported on the lattice
`(2π / l) ℤ`, and conversely. This is the mathematical content of the book's
definition of a lattice random variable: `φ_X(λ) = 1` for some `λ ≠ 0` means
`X` is supported on a lattice.

## Source

`v1/Atlas/TheoryOfProbability/code/LatticeRV.lean` (`IsLatticeRV`), for the
book target "Definition (lattice random variable)" (Lecture 17) in
`v1/Atlas/TheoryOfProbability/targets.yaml`. The v1 file only states the
definition; the characterization proved here is new.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExt.Probability.CharFunLattice

/-- **Lattice random variable.** A measure $\mu$ on $\mathbb{R}$ with characteristic function
$\varphi(t) = \int e^{itx} \, d\mu(x)$ is a lattice random variable if $\varphi(l) = 1$ for some
real $l \ne 0$ and $\varphi(t) \ne 1$ for some real $t$.

For a probability measure, the second condition says that $\mu$ is not the point mass at $0$. -/
def IsLatticeRV (μ : Measure ℝ) : Prop :=
  (∃ l : ℝ, l ≠ 0 ∧ charFun μ l = 1) ∧ ¬ (∀ t : ℝ, charFun μ t = 1)

/-- The integrand of the characteristic function at frequency `l` is
integrable against any probability measure, since it is continuous and
bounded by `1` in norm. -/
private lemma integrable_exp_mul_I (μ : Measure ℝ) [IsProbabilityMeasure μ] (l : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)) μ := by
  have hcont : Continuous
      (fun x : ℝ => Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)) := by
    apply Complex.continuous_exp.comp
    exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_id)).mul
      continuous_const
  exact Integrable.of_bound hcont.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])

/-- The real part of the characteristic-function integrand is the cosine:
`Re (exp (i l x)) = cos (l x)`. -/
private lemma re_exp_mul_I (l x : ℝ) :
    (Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)).re = Real.cos (l * x) := by
  have hexp : ((l : ℂ) * (x : ℂ) * Complex.I) = ((l * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.exp_ofReal_mul_I_re]

/-- The cosine is integrable against any probability measure, since it is
continuous and bounded by `1`. -/
private lemma integrable_cos_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] (l : ℝ) :
    Integrable (fun x : ℝ => Real.cos (l * x)) μ :=
  Integrable.of_bound
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)

/-- **A characteristic function equal to one detects lattice support.** Let $\mu$ be a
probability measure on $\mathbb{R}$ with characteristic function
$\varphi(t) = \int e^{itx} \, d\mu(x)$, and let $l \ne 0$ be real. Then $\varphi(l) = 1$ if and
only if $\mu$ gives mass $1$ to the lattice $\{(2\pi / l) k : k \in \mathbb{Z}\}$.

Forward direction: $\operatorname{Re} \varphi(l) = \int \cos(lx) \, d\mu(x) = 1$ forces
$\int (1 - \cos(lx)) \, d\mu(x) = 0$, hence $\cos(lx) = 1$ almost everywhere, hence
$lx \in 2\pi\mathbb{Z}$ almost everywhere. Backward direction: on the lattice the integrand
$e^{ilx}$ is identically $1$. -/
theorem charFun_eq_one_iff_measure_eq_one_of_lattice {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {l : ℝ} (hl : l ≠ 0) :
    charFun μ l = 1 ↔
      μ {x : ℝ | ∃ k : ℤ, x = (2 * Real.pi / l) * k} = 1 := by
  set S : Set ℝ := {x : ℝ | ∃ k : ℤ, x = (2 * Real.pi / l) * k} with hS
  have hS_meas : MeasurableSet S := by
    have hSeq : S = Set.range (fun k : ℤ => (2 * Real.pi / l) * k) := by
      ext x
      rw [hS]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, h⟩
        exact ⟨k, h.symm⟩
    rw [hSeq]
    exact (Set.countable_range _).measurableSet
  constructor
  · intro hchar
    have hint : Integrable
        (fun x : ℝ => Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)) μ :=
      integrable_exp_mul_I μ l
    -- The real part of the characteristic function is the integral of the cosine.
    have hre : (∫ x, Real.cos (l * x) ∂μ) = 1 := by
      have h1 : (∫ x, RCLike.re (Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)) ∂μ)
          = RCLike.re (∫ x, Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I) ∂μ) :=
        integral_re hint
      have h2 : (fun x : ℝ => RCLike.re (Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I)))
          = fun x : ℝ => Real.cos (l * x) :=
        funext fun x : ℝ => re_exp_mul_I l x
      rw [h2] at h1
      rw [h1, ← charFun_apply_real, hchar]
      simp
    -- Hence `1 - cos (l x)` has integral zero.
    have hcos_int : Integrable (fun x : ℝ => Real.cos (l * x)) μ :=
      integrable_cos_mul μ l
    have hzero : ∫ x, (1 - Real.cos (l * x)) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) hcos_int, integral_const, hre]
      simp
    have hnonneg : (0 : ℝ → ℝ) ≤ᵐ[μ] fun x => 1 - Real.cos (l * x) :=
      Filter.Eventually.of_forall fun x => by
        simp only [Pi.zero_apply]
        linarith [Real.cos_le_one (l * x)]
    have hae : (fun x : ℝ => 1 - Real.cos (l * x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg
        ((integrable_const 1).sub hcos_int)).mp hzero
    -- Almost every `x` lies in the lattice.
    have hmem : ∀ᵐ x ∂μ, x ∈ S := by
      filter_upwards [hae] with x hx
      have hcos : Real.cos (l * x) = 1 := by
        have h0 : 1 - Real.cos (l * x) = 0 := by
          have h := hx
          simpa using h
        linarith
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (l * x)).mp hcos
      refine ⟨k, ?_⟩
      -- `hk : (k : ℝ) * (2 * π) = l * x`, so `x = (2π / l) * k`.
      have hx : x = ((k : ℝ) * (2 * Real.pi)) / l := by
        rw [hk]
        exact (mul_div_cancel_left₀ x hl).symm
      rw [hx]
      ring
    rw [ae_mem_iff_measure_eq hS_meas.nullMeasurableSet] at hmem
    rw [hmem]
    simp
  · intro hmeas
    have hmem : ∀ᵐ x ∂μ, x ∈ S := by
      rw [ae_mem_iff_measure_eq hS_meas.nullMeasurableSet, hmeas]
      simp
    have hInt : (∫ x, Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I) ∂μ) = 1 := by
      have hae : (fun x : ℝ => Complex.exp ((l : ℂ) * (x : ℂ) * Complex.I))
          =ᵐ[μ] fun _ => 1 := by
        filter_upwards [hmem] with x hx
        obtain ⟨k, rfl⟩ := hx
        have hlx : (l : ℂ) * ((2 * Real.pi / l) * (k : ℝ) : ℝ) =
            (k : ℂ) * (2 * Real.pi) := by
          have h2 : l * ((2 * Real.pi / l) * (k : ℝ)) = (k : ℝ) * (2 * Real.pi) := by
            calc l * ((2 * Real.pi / l) * (k : ℝ))
                = 2 * Real.pi * (k : ℝ) := by field_simp
              _ = (k : ℝ) * (2 * Real.pi) := by ring
          exact_mod_cast h2
        have hexp : (l : ℂ) * (((2 * Real.pi / l) * (k : ℝ) : ℝ) : ℂ) * Complex.I
            = (k : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [hlx]
          ring
        rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
      rw [integral_congr_ae hae, integral_const]
      simp
    rw [charFun_apply_real]
    exact hInt

/-- **Lattice random variables are supported on a lattice.** Let $\mu$ be a probability measure
on $\mathbb{R}$ that is a lattice random variable. Then there is a real number $h \ne 0$ such
that $\mu$ gives mass $1$ to the lattice $\{hk : k \in \mathbb{Z}\}$.

One can take $h = 2\pi / l$ for a nonzero frequency $l$ at which the characteristic function of
$\mu$ equals $1$. The condition that the characteristic function is not identically $1$ is not
needed. -/
theorem IsLatticeRV.exists_lattice_support {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsLatticeRV μ) : ∃ hstep : ℝ, hstep ≠ 0 ∧
      μ {x : ℝ | ∃ k : ℤ, x = hstep * k} = 1 := by
  obtain ⟨⟨l, hl, hchar⟩, -⟩ := h
  refine ⟨2 * Real.pi / l, ?_, ?_⟩
  · exact div_ne_zero (by positivity) hl
  · exact (charFun_eq_one_iff_measure_eq_one_of_lattice hl).mp hchar

end MathlibExt.Probability.CharFunLattice
