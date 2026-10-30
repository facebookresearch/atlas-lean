/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FiniteAbelianDFT
public import MathlibExt.Analysis.FunctionalAnalysis.RieszThorin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Measure.Count

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hausdorff–Young inequality on a finite abelian group

For a function `f : G → ℂ` on a finite abelian group `G`, the discrete
Fourier transform `dftFun f` is a function on the dual group
`AddChar G ℂ`. The Hausdorff–Young inequality says that for
`1 < p ≤ 2` with conjugate exponent `q = p / (p - 1)`,

`(∑ ψ, ‖dftFun f ψ‖ ^ q) ^ (1 / q) ≤ (card G) ^ (1 / q) * (∑ x, ‖f x‖ ^ p) ^ (1 / p)`.

The endpoints are the triangle inequality (`p = 1`, the transform is
bounded by the `ℓ¹` norm) and Plancherel (`p = 2`), and the interior
cases follow by the Riesz–Thorin interpolation theorem in base
MathlibExt (`riesz_thorin`), applied to the Fourier transform as a
linear map, with interpolation parameter `θ = 2 - 2 / p`.

This is a companion to the Fourier-series material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(Fejér's theorem, Fourier coefficients tending to zero): Hausdorff–Young
is the `ℓ^p → ℓ^q` refinement of the `ℓ¹ → ℓ^∞` bound on Fourier
coefficients. It is not one of the 72 v1 targets. The ingredients are
in pinned Mathlib (Fourier inversion, Plancherel for finite abelian
groups) and in base MathlibExt (the discrete Fourier transform, the
finite counting-measure Riesz–Thorin theorem), but the
Hausdorff–Young inequality itself is in neither.

Sources: F. Hausdorff, "Eine Ausdehnung des Parsevalschen Satzes
über Fourierreihen", Mathematische Zeitschrift 16 (1923), 163–169;
W. H. Young, "On the determination of the summability of a function
by means of its Fourier constants", Proceedings of the London
Mathematical Society 12 (1913), 71–88; E. M. Stein and R. Shakarchi,
Functional Analysis, Princeton, 2011, Chapter 1, §5.

## Main declarations

* `hausdorffYoung_dft` : the Hausdorff–Young inequality for `1 < p ≤ 2`.
* `dftFun_sup_le` : the `p = 1` endpoint, `‖dftFun f ψ‖ ≤ ∑ x, ‖f x‖`.
* `sum_norm_sq_dftFun` : Plancherel in squared-norm form,
  `∑ ψ, ‖dftFun f ψ‖ ^ 2 = card G * ∑ x, ‖f x‖ ^ 2`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.HausdorffYoungFiniteAbelian

open MeasureTheory
open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted
open MathlibExt.Analysis.FunctionalAnalysis.RieszThorinWanted

/-- The enorm of a complex number is the `ENNReal.ofReal` of its norm. -/
private theorem enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← coe_nnnorm z, ENNReal.ofReal_coe_nnreal]

/-- Every complex-valued function on a finite measurable space is
almost-everywhere strongly measurable for counting measure. -/
private theorem aemeas_of_finite {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Finite ι] (y : ι → ℂ) :
    AEStronglyMeasurable y (Measure.count : Measure ι) :=
  (measurable_of_finite y).aestronglyMeasurable

/-- For counting measure on a finite type, the `eLpNorm` with exponent
`ENNReal.ofReal r` is the `ENNReal.ofReal` of the familiar finite-sum
`ℓ^r` norm. -/
private theorem eLpNorm_count_eq_ofReal_sum {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (y : ι → ℂ) {r : ℝ}
    (hr0 : 0 < r) :
    eLpNorm y (ENNReal.ofReal r) (Measure.count : Measure ι) =
      ENNReal.ofReal ((∑ i, ‖y i‖ ^ r) ^ (1 / r)) := by
  have hrE0 : (ENNReal.ofReal r) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hr0
  have hrEtop : (ENNReal.ofReal r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable y (Measure.count : Measure ι) :=
    aemeas_of_finite y
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrE0 hrEtop hmeas, lintegral_count,
    tsum_fintype, ENNReal.toReal_ofReal hr0.le]
  have hsum : (∑ i, ‖y i‖ₑ ^ r) = ENNReal.ofReal (∑ i, ‖y i‖ ^ r) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) r)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [enorm_complex_eq_ofReal,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  rw [hsum, ← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) r)
    (by positivity : (0:ℝ) ≤ 1 / r)]

/-- The `p = 1` endpoint of Hausdorff–Young: each Fourier coefficient is
bounded by the `ℓ¹` norm of the function. -/
theorem dftFun_sup_le {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ)
    (ψ : AddChar G ℂ) :
    ‖dftFun f ψ‖ ≤ ∑ x : G, ‖f x‖ := by
  show ‖∑ x : G, ψ x * f x‖ ≤ ∑ x : G, ‖f x‖
  calc ‖∑ x : G, ψ x * f x‖ ≤ ∑ x : G, ‖ψ x * f x‖ := norm_sum_le _ _
    _ = ∑ x : G, ‖f x‖ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul, AddChar.norm_apply, one_mul]

/-- Plancherel in squared-norm form: the sum of the squared norms of the
Fourier coefficients is `card G` times the sum of the squared norms of
the values. -/
theorem sum_norm_sq_dftFun {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ x : G, ‖f x‖ ^ 2 := by
  have h := dft_plancherel f f
  have star_mul (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    change (starRingEnd ℂ) z * z = _
    rw [mul_comm, Complex.mul_conj']
    norm_cast
  simp only [star_mul] at h
  have h_real : (∑ x : G, ‖f x‖ ^ 2) =
      ((Fintype.card G : ℝ))⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
    apply Complex.ofReal_inj.mp
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    exact h
  have hN : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmul : (Fintype.card G : ℝ) * (∑ x : G, ‖f x‖ ^ 2) =
      ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
    rw [h_real]
    field_simp
  exact hmul.symm

/-- The discrete Fourier transform as a linear map, for interpolation. -/
private def dftLinMap {G : Type*} [AddCommGroup G] [Fintype G] :
    (G → ℂ) →ₗ[ℂ] (AddChar G ℂ → ℂ) where
  toFun := dftFun
  map_add' := by
    intro f g
    funext ψ
    simp only [dftFun, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro c f
    funext ψ
    show (∑ x : G, ψ x * (c * f x)) = c * ∑ x : G, ψ x * f x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- The `ℓ¹ → ℓ^∞` endpoint bound for the Fourier transform, in
`eLpNorm` form, for interpolation. -/
private theorem eLpNorm_dft_top_le {G : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSpace (AddChar G ℂ)]
    [MeasurableSingletonClass G] [MeasurableSingletonClass (AddChar G ℂ)]
    (f : G → ℂ) :
    eLpNorm (dftFun f) ⊤ (Measure.count : Measure (AddChar G ℂ)) ≤
      eLpNorm f (ENNReal.ofReal 1) (Measure.count : Measure G) := by
  have htop : eLpNorm (dftFun f) ⊤ (Measure.count : Measure (AddChar G ℂ)) =
      ⨆ ψ, ‖dftFun f ψ‖ₑ := by
    rw [eLpNorm_exponent_top (aemeas_of_finite (dftFun f)), eLpNormEssSup_count]
  rw [htop, eLpNorm_count_eq_ofReal_sum f (by norm_num : (0:ℝ) < 1)]
  apply iSup_le
  intro ψ
  have hsum : (∑ x : G, ‖f x‖ ^ (1:ℝ)) ^ (1 / (1:ℝ)) = ∑ x : G, ‖f x‖ := by
    simp only [div_one, Real.rpow_one]
  rw [enorm_complex_eq_ofReal, hsum,
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact dftFun_sup_le f ψ

/-- The `ℓ² → ℓ²` endpoint bound for the Fourier transform, in `eLpNorm`
form, for interpolation: it is an equality up to the factor
`(card G) ^ (1 / 2)`. -/
private theorem eLpNorm_dft_two {G : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSpace (AddChar G ℂ)]
    [MeasurableSingletonClass G] [MeasurableSingletonClass (AddChar G ℂ)]
    (f : G → ℂ) :
    eLpNorm (dftFun f) (ENNReal.ofReal 2) (Measure.count : Measure (AddChar G ℂ)) =
      (Fintype.card G : ENNReal) ^ (1 / 2 : ℝ) *
        eLpNorm f (ENNReal.ofReal 2) (Measure.count : Measure G) := by
  have hsum_rpow : (∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ (2:ℝ)) =
      (Fintype.card G : ℝ) * ∑ x : G, ‖f x‖ ^ (2:ℝ) := by
    have h := sum_norm_sq_dftFun f
    simp only [← Real.rpow_two] at h
    exact h
  have hreal : ((∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ)) =
      (Fintype.card G : ℝ) ^ (1 / 2 : ℝ) *
        (∑ x : G, ‖f x‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ) := by
    rw [hsum_rpow, Real.mul_rpow (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i _ => by positivity)]
  have hcard : (Fintype.card G : ENNReal) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((Fintype.card G : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1 / 2)]
  rw [eLpNorm_count_eq_ofReal_sum _ (by norm_num : (0:ℝ) < 2),
    eLpNorm_count_eq_ofReal_sum _ (by norm_num : (0:ℝ) < 2), hcard,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _), hreal]

/-- The Hausdorff–Young inequality on a finite abelian group: for
`1 < p ≤ 2` with conjugate exponent `q = p / (p - 1)`,
the `ℓ^q` norm of the Fourier transform is bounded by
`(card G) ^ (1 / q)` times the `ℓ^p` norm of the function.

The measurability hypotheses are the ones the finite counting-measure
Riesz–Thorin theorem in base MathlibExt takes; in applications they are
discharged with the discrete (`⊤`) measurable-space instance. -/
theorem hausdorffYoung_dft {G : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSpace (AddChar G ℂ)]
    [MeasurableSingletonClass G] [MeasurableSingletonClass (AddChar G ℂ)]
    {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (f : G → ℂ) :
    (∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) ≤
      (Fintype.card G : ℝ) ^ (1 / (p / (p - 1))) *
        (∑ x : G, ‖f x‖ ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have hpm1' : p - 1 ≠ 0 := ne_of_gt hpm1
  set q := p / (p - 1) with hqdef
  set θ := 2 - 2 / p with hθdef
  have hqpos : 0 < q := by
    rw [hqdef]
    exact div_pos hp0 hpm1
  have hq1 : (1:ℝ) ≤ q := by
    rw [hqdef, le_div_iff₀ hpm1]
    linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    have h : 2 / p ≤ 2 := by
      rw [div_le_iff₀ hp0]
      linarith [hp1.le]
    linarith
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    have h : 1 ≤ 2 / p := by
      rw [le_div_iff₀ hp0]
      linarith [hp2]
    linarith
  have hp₀ : (1 : ENNReal) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]
  have hp₁ : (1 : ENNReal) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_le_ofReal_iff hp0.le).mpr hp1.le
  have hq₀ : (1 : ENNReal) ≤ (⊤ : ENNReal) := le_top
  have hq₁ : (1 : ENNReal) ≤ ENNReal.ofReal 2 := hp₁
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_le_ofReal_iff hqpos.le).mpr hq1
  have hp_eq : (ENNReal.ofReal p)⁻¹ =
      ENNReal.ofReal (1 - θ) * (ENNReal.ofReal 1)⁻¹ +
        ENNReal.ofReal θ * (ENNReal.ofReal 2)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_one, inv_one, mul_one,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
      ← ENNReal.ofReal_mul hθ0,
      ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - θ)
        (by positivity : (0:ℝ) ≤ θ * 2⁻¹)]
    congr 1
    rw [hθdef]
    field_simp
    ring
  have hq_eq : (ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal (1 - θ) * (⊤ : ENNReal)⁻¹ +
        ENNReal.ofReal θ * (ENNReal.ofReal 2)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hqpos, ENNReal.inv_top, mul_zero, zero_add,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
      ← ENNReal.ofReal_mul hθ0]
    congr 1
    rw [hqdef, hθdef]
    field_simp
  have h₀ : ∀ g : G → ℂ,
      eLpNorm (dftLinMap g) ⊤ (Measure.count : Measure (AddChar G ℂ)) ≤
        1 * eLpNorm g (ENNReal.ofReal 1) (Measure.count : Measure G) := by
    intro g
    rw [one_mul]
    exact eLpNorm_dft_top_le g
  have h₁ : ∀ g : G → ℂ,
      eLpNorm (dftLinMap g) (ENNReal.ofReal 2)
        (Measure.count : Measure (AddChar G ℂ)) ≤
        (Fintype.card G : ENNReal) ^ (1 / 2 : ℝ) *
          eLpNorm g (ENNReal.ofReal 2) (Measure.count : Measure G) := by
    intro g
    exact le_of_eq (eLpNorm_dft_two g)
  have hRT := riesz_thorin (p₀ := ENNReal.ofReal 1) (p₁ := ENNReal.ofReal 2)
    (q₀ := ⊤) (q₁ := ENNReal.ofReal 2) (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal q) (M₀ := 1)
    (M₁ := (Fintype.card G : ENNReal) ^ (1 / 2 : ℝ))
    hθ0 hθ1 hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq dftLinMap h₀ h₁ f
  have hconv1 : eLpNorm (dftLinMap f) (ENNReal.ofReal q)
      (Measure.count : Measure (AddChar G ℂ)) =
      ENNReal.ofReal ((∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ q) ^ (1 / q)) :=
    eLpNorm_count_eq_ofReal_sum (dftFun f) hqpos
  have hconv2 : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure G) =
      ENNReal.ofReal ((∑ x : G, ‖f x‖ ^ p) ^ (1 / p)) :=
    eLpNorm_count_eq_ofReal_sum f hp0
  have hfactor : (1 : ENNReal) ^ (1 - θ) *
      ((Fintype.card G : ENNReal) ^ (1 / 2 : ℝ)) ^ θ =
      ENNReal.ofReal ((Fintype.card G : ℝ) ^ (1 / q)) := by
    rw [ENNReal.one_rpow, one_mul, ← ENNReal.rpow_mul]
    have h12θ : (1 / 2 : ℝ) * θ = 1 / q := by
      rw [hθdef, hqdef]
      field_simp
    rw [h12θ, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _)
        (div_nonneg zero_le_one hqpos.le)]
  rw [hconv1, hconv2, hfactor] at hRT
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hRT
  have hRHS_nonneg : (0:ℝ) ≤ (Fintype.card G : ℝ) ^ (1 / q) *
      (∑ x : G, ‖f x‖ ^ p) ^ (1 / p) := by
    apply mul_nonneg
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact Real.rpow_nonneg
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
  exact (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).mp hRT

end MathlibExt.Analysis.Fourier.HausdorffYoungFiniteAbelian
