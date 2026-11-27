/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureSesquilinearity
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureDiagonal
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Cauchy–Schwarz bounds for normal CFC coefficient forms

For a normal operator `T` on a complete complex Hilbert space, let `μ_(g,h)` be its regular CFC
coefficient measure on `K=σ_ℂ(T)` and `ν_g` the positive diagonal measure. On a measurable set
`s`, the form `F_s(h,g)=μ_(g,h)(s)` is Hermitian and positive semidefinite.

Cauchy–Schwarz gives `|μ_(g,h)(s)|²≤ν_g.real(s) ν_h.real(s)`. Since `ν_g.real(s)≤‖g‖²`, this
yields `|F_s(h,g)|≤‖h‖‖g‖`. All norms are those of the Hilbert space and the complex scalars; no
new Hilbert norm is used.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Sesquilinear form of a CFC set coefficient.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for any set `s ⊆ K`,
`normalCFCCoefficientFormLinear T hT s (h,g)=μ_(g,h)(s)`, conjugate-linear in `h` and
linear in `g`. -/
def normalCFCCoefficientFormLinear (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun h :=
    { toFun g := (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s
      map_add' := by
        intro g₁ g₂
        rw [normalCFCCoefficientMeasure_add_left]
        rfl
      map_smul' := by
        intro c g
        rw [normalCFCCoefficientMeasure_smul_left]
        rfl }
  map_add' := by
    intro h₁ h₂
    ext g
    change (normalCFCCoefficientMeasure T hT g (h₁ + h₂) : ComplexMeasure (spectrum ℂ T)) s = _
    rw [normalCFCCoefficientMeasure_add_right]
    rfl
  map_smul' := by
    intro c h
    ext g
    change (normalCFCCoefficientMeasure T hT g (c • h) : ComplexMeasure (spectrum ℂ T)) s =
      star c • (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s
    rw [normalCFCCoefficientMeasure_smul_right]
    rfl

/-- **Value of the algebraic CFC coefficient form.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `s ⊆ K` and `g,h ∈ H`,
`normalCFCCoefficientFormLinear T hT s h g=μ_(g,h)(s)`. -/
theorem normalCFCCoefficientFormLinear_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (h g : H) :
    normalCFCCoefficientFormLinear T hT s h g =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s := rfl

private theorem coefficient_diagonal_im_zero (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (x : H) :
    (normalCFCCoefficientFormLinear T hT s x x).im = 0 := by
  rw [normalCFCCoefficientFormLinear_apply, normalCFCCoefficientMeasure_diagonal_apply T hT x s hs]
  exact Complex.ofReal_im _

private theorem coefficient_form_hermitian (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (x y : H) :
    star (normalCFCCoefficientFormLinear T hT s y x) =
      normalCFCCoefficientFormLinear T hT s x y := by
  let L := normalCFCCoefficientFormLinear T hT s
  have hx : (L x x).im = 0 := coefficient_diagonal_im_zero T hT s hs x
  have hy : (L y y).im = 0 := coefficient_diagonal_im_zero T hT s hs y
  have hadd : L (x + y) (x + y) = L x x + L x y + L y x + L y y := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have hphase : L (x + Complex.I • y) (x + Complex.I • y) =
      L x x + Complex.I * L x y - Complex.I * L y x + L y y := by
    have hleft (a b z : H) : L (a + b) z = L a z + L b z :=
      congrArg (fun f : H →ₗ[ℂ] ℂ => f z) (L.map_add a b)
    have hright (z a b : H) : L z (a + b) = L z a + L z b := (L z).map_add a b
    have hsmulLeft (c : ℂ) (a z : H) : L (c • a) z = star c * L a z := by
      have heq := congrArg (fun f : H →ₗ[ℂ] ℂ => f z) (L.map_smulₛₗ c a)
      simpa only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul] using heq
    have hsmulRight (c : ℂ) (z a : H) : L z (c • a) = c * L z a := by
      simpa only [smul_eq_mul] using (L z).map_smul c a
    rw [hleft, hright, hright, hsmulRight, hsmulLeft, hsmulRight, hsmulLeft]
    simp only [Complex.star_def, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  have him := coefficient_diagonal_im_zero T hT s hs (x + y)
  change (L (x + y) (x + y)).im = 0 at him
  rw [hadd] at him
  simp only [Complex.add_im, hx, hy, zero_add, add_zero] at him
  have hre := coefficient_diagonal_im_zero T hT s hs (x + Complex.I • y)
  change (L (x + Complex.I • y) (x + Complex.I • y)).im = 0 at hre
  rw [hphase] at hre
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, add_zero, hx, hy] at hre
  change star (L y x) = L x y
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- **Hermitian symmetry of measurable CFC coefficients.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K` and
`g,h ∈ H`, `μ_(g,h)(s)=conj(μ_(h,g)(s))`. -/
theorem normalCFCCoefficientMeasure_conj_symm (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s =
      star ((normalCFCCoefficientMeasure T hT h g : ComplexMeasure (spectrum ℂ T)) s) := by
  exact (coefficient_form_hermitian T hT s hs h g).symm

private theorem coefficient_diagonal_nonneg (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (x : H) :
    0 ≤ (normalCFCCoefficientFormLinear T hT s x x).re := by
  rw [normalCFCCoefficientFormLinear_apply, normalCFCCoefficientMeasure_diagonal_apply T hT x s hs]
  simpa only [Complex.ofReal_re] using
    (measureReal_nonneg (μ := normalCFCDiagonalMeasure T hT x) (s := s))

/-- **Cauchy–Schwarz inequality for a spectral set coefficient.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable
`s` and `g,h ∈ H`, `|μ_(g,h)(s)|²≤ν_g.real(s)*ν_h.real(s)`, where
`ν_v=normalCFCDiagonalMeasure T hT v`. -/
theorem normalCFCCoefficientMeasure_cauchySchwarz (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖(normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s‖ ^ 2 ≤
      (normalCFCDiagonalMeasure T hT g).real s * (normalCFCDiagonalMeasure T hT h).real s := by
  let L := normalCFCCoefficientFormLinear T hT s
  let core : PreInnerProductSpace.Core ℂ H :=
    { inner := fun x y => L x y
      conj_inner_symm x y := coefficient_form_hermitian T hT s hs x y
      re_inner_nonneg x := coefficient_diagonal_nonneg T hT s hs x
      add_left x y z := by
        change L (x + y) z = L x z + L y z
        rw [map_add, LinearMap.add_apply]
      smul_left x y c := by
        change L (c • x) y = star c * L x y
        rw [map_smulₛₗ, LinearMap.smul_apply]
        rfl }
  have hcs := @_root_.InnerProductSpace.Core.inner_mul_inner_self_le ℂ H _ _ _ core h g
  change ‖L h g‖ * ‖L g h‖ ≤ (L h h).re * (L g g).re at hcs
  have hnorm : ‖L g h‖ = ‖L h g‖ := by
    rw [← norm_star (L g h)]
    exact congrArg norm (coefficient_form_hermitian T hT s hs h g)
  rw [hnorm] at hcs
  simpa only [L, normalCFCCoefficientFormLinear_apply,
    normalCFCCoefficientMeasure_diagonal_apply T hT h s hs,
    normalCFCCoefficientMeasure_diagonal_apply T hT g s hs,
    Complex.ofReal_re, pow_two, mul_comm] using hcs

/-- **Diagonal spectral set mass bounded by vector norm.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g ∈ H` and any set `s ⊆ K`, `ν_g.real(s)≤‖g‖²`, where
`ν_g=normalCFCDiagonalMeasure T hT g`. -/
private theorem diagonal_mass_le_norm_sq (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (s : Set (spectrum ℂ T)) :
    (normalCFCDiagonalMeasure T hT g).real s ≤ ‖g‖ ^ 2 := by
  calc
    (normalCFCDiagonalMeasure T hT g).real s ≤
        (normalCFCDiagonalMeasure T hT g).real univ :=
      measureReal_mono (μ := normalCFCDiagonalMeasure T hT g) (subset_univ s)
        (measure_ne_top (normalCFCDiagonalMeasure T hT g) univ)
    _ = ‖g‖ ^ 2 := normalCFCDiagonalMeasure_real_univ T hT g

/-- **Hilbert norm bound for a measurable CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K` and
`g,h ∈ H`, `|μ_(g,h)(s)|≤‖g‖*‖h‖`. -/
theorem normalCFCCoefficientMeasure_norm_apply_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖(normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s‖ ≤ ‖g‖ * ‖h‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg g) (norm_nonneg h))).mp
  calc
    ‖(normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s‖ ^ 2 ≤
        (normalCFCDiagonalMeasure T hT g).real s * (normalCFCDiagonalMeasure T hT h).real s :=
      normalCFCCoefficientMeasure_cauchySchwarz T hT g h s hs
    _ ≤ ‖g‖ ^ 2 * ‖h‖ ^ 2 :=
      mul_le_mul (diagonal_mass_le_norm_sq T hT g s) (diagonal_mass_le_norm_sq T hT h s)
        (measureReal_nonneg (μ := normalCFCDiagonalMeasure T hT h) (s := s)) (sq_nonneg ‖g‖)
    _ = (‖g‖ * ‖h‖) ^ 2 := by ring

/-- **Unit bound for the CFC coefficient form.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s` and `h,g ∈ H`,
`‖normalCFCCoefficientFormLinear T hT s h g‖≤1*‖h‖*‖g‖`. -/
theorem normalCFCCoefficientFormLinear_norm_apply_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (h g : H) :
    ‖normalCFCCoefficientFormLinear T hT s h g‖ ≤ (1 : ℝ) * ‖h‖ * ‖g‖ := by
  rw [normalCFCCoefficientFormLinear_apply]
  have hbound := normalCFCCoefficientMeasure_norm_apply_le T hT g h s hs
  calc
    ‖(normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s‖ ≤
        ‖g‖ * ‖h‖ := hbound
    _ = (1 : ℝ) * ‖h‖ * ‖g‖ := by ring

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
