/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

@[expose] public section

open MeasureTheory

open scoped MatrixGroups ENNReal Topology

noncomputable section

namespace MathlibExt.NumberTheory.SelbergSpectralGap

/-!
# The Selberg congruence spectral-gap constant

For a congruence subgroup `Γ ≤ SL(2, ℤ)`, an exceptional eigenvalue is an
eigenvalue `λ ∈ (0, 1/4)` of the hyperbolic Laplacian
`Δ = -y² (∂²/∂x² + ∂²/∂y²)` on `L²(Γ \ ℍ)`, below the continuous spectrum
threshold `1/4`. The gap parameter of `Γ` measures the deepest exceptional
eigenvalue: `θ(Γ) = sup {√(1/4 - λ) | λ exceptional} ∪ {0}`, which is
`√(max (0, 1/4 - λ₁(Γ)))` for the first nonzero eigenvalue `λ₁(Γ)` whenever
the spectrum below `1/4` is discrete. The Selberg constant (catalogue
constant C61a) is `C₆₁ = sup_Γ θ(Γ)` over congruence subgroups; it is `0`
exactly when no congruence subgroup has an exceptional eigenvalue, which
is Selberg's eigenvalue conjecture. This file proves the elementary
framework `0 ≤ C₆₁ ≤ 1/2` and that equivalence. Selberg's bound
`λ₁ ≥ 3/16` (`C₆₁ ≤ 1/4`) and the Kim--Sarnak bound `λ₁ ≥ 975/4096`
(`C₆₁ ≤ 7/64`) are registered as proof requests in the wanted file.

Model scope. Eigenvalues are modelled by smooth eigenfunctions on the
upper half plane that are `Γ`-invariant and square-integrable over a
fundamental domain assembled from finitely many translates of the
standard `SL(2, ℤ)` fundamental domain, with Mathlib's hyperbolic volume
on `UpperHalfPlane`. This captures the discrete `L²` spectrum. It does
not formalize the self-adjoint extension of the Laplacian, its full
spectrum including the continuous part `[1/4, ∞)`, discreteness of the
spectrum below `1/4`, independence of the `L²` condition from the chosen
coset covering, or that every spectral value below `1/4` comes from a
smooth `L²` eigenfunction in this sense. Since `θ(Γ)` depends only on
eigenvalues below `1/4`, the constant defined here is the catalogue
constant under those recorded identifications.

Source: Optimization Problems, constants/61a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`21fddd97d037cfa94393294ab112f709d5242cdc0ca11ef3bd62073408a80a8e`.
-/

/-- A subgroup of `SL(2, ℤ)` is a congruence subgroup when it contains a
principal congruence subgroup: all matrices congruent to the identity
modulo some positive level `N`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ γ : SL(2, ℤ),
    (∀ i j, γ.1 i j ≡ (1 : Matrix (Fin 2) (Fin 2) ℤ) i j [ZMOD (N : ℤ)]) →
      γ ∈ Γ

/-- The full modular group is a congruence subgroup (level `1`). -/
theorem isCongruenceSubgroup_top : IsCongruenceSubgroup ⊤ :=
  ⟨1, one_pos, fun γ _ => Subgroup.mem_top γ⟩

/-- Zero extension of an upper-half-plane function to the complex plane,
used to read coordinate derivatives in the interior. -/
def ext (f : UpperHalfPlane → ℂ) : ℂ → ℂ :=
  fun z => if hz : 0 < z.im then f ⟨z, hz⟩ else 0

/-- The derivative of `f` in the real coordinate direction: the real
Fréchet derivative of the zero extension applied to the vector `1`.
Real (not complex) differentiability is essential here: with complex
derivatives the two second derivatives below would cancel by
Cauchy--Riemann and the Laplacian would be identically zero. -/
def partialRe (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  fderiv ℝ (ext f) z (1 : ℂ)

/-- The derivative of `f` in the imaginary coordinate direction: the real
Fréchet derivative of the zero extension applied to the vector `I`. -/
def partialIm (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  fderiv ℝ (ext f) z Complex.I

/-- The hyperbolic Laplacian `-y² (∂²/∂x² + ∂²/∂y²)`, read through the
zero extension. On smooth functions this agrees with the coordinate
formula at every interior point. -/
def hyperbolicLaplacian (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  -((z.im : ℂ) ^ 2) * (partialRe (partialRe f) z + partialIm (partialIm f) z)

private theorem ext_fderiv_const (c v : ℂ) (z : UpperHalfPlane) :
    fderiv ℝ (ext fun _ => c) z v = 0 := by
  have heq : ext (fun _ => c) =ᶠ[𝓝 (z : ℂ)] fun _ => c := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos]
      with w hw
    rw [ext, dif_pos hw]
  rw [heq.fderiv_eq]
  simp

theorem partialRe_const (c : ℂ) (z : UpperHalfPlane) :
    partialRe (fun _ => c) z = 0 :=
  ext_fderiv_const c 1 z

theorem partialIm_const (c : ℂ) (z : UpperHalfPlane) :
    partialIm (fun _ => c) z = 0 :=
  ext_fderiv_const c Complex.I z

/-- The hyperbolic Laplacian kills constant functions, as it should. -/
theorem hyperbolicLaplacian_const (c : ℂ) (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun _ => c) z = 0 := by
  have hRe : partialRe (fun _ => c) = fun _ => 0 :=
    funext (partialRe_const c)
  have hIm : partialIm (fun _ => c) = fun _ => 0 :=
    funext (partialIm_const c)
  rw [hyperbolicLaplacian, hRe, hIm, partialRe_const, partialIm_const]
  simp


/-- Near an interior point, the zero extension agrees with any extension
of `f`, so their real derivatives at that point agree. -/
private theorem ext_eventuallyEq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    ext f =ᶠ[𝓝 (z : ℂ)] F := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos]
    with w hw
  rw [ext, dif_pos hw]
  exact hF ⟨w, hw⟩

private theorem partialRe_eq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    partialRe f z = fderiv ℝ F z (1 : ℂ) := by
  rw [partialRe, (ext_eventuallyEq hF z).fderiv_eq]

private theorem partialIm_eq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    partialIm f z = fderiv ℝ F z Complex.I := by
  rw [partialIm, (ext_eventuallyEq hF z).fderiv_eq]

private theorem fderiv_im_sq_apply (w v : ℂ) :
    fderiv ℝ (fun u : ℂ => ((u.im ^ 2 : ℝ) : ℂ)) w v =
      ((2 * w.im * v.im : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w :=
    Complex.imCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun r : ℝ => r ^ 2)
      ((2 * w.im) • ContinuousLinearMap.id ℝ ℝ) w.im := by
    simpa using (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) (x := w.im) 2)
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp w h1)
  rw [show (fun u : ℂ => ((u.im ^ 2 : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun r : ℝ => r ^ 2) ∘ Complex.im from rfl,
    h4.fderiv]
  simp [mul_comm]

private theorem fderiv_two_im_apply (w v : ℂ) :
    fderiv ℝ (fun u : ℂ => ((2 * u.im : ℝ) : ℂ)) w v =
      ((2 * v.im : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w :=
    Complex.imCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun r : ℝ => 2 * r)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) w.im :=
    (hasFDerivAt_id w.im).const_mul 2
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp w h1)
  rw [show (fun u : ℂ => ((2 * u.im : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun r : ℝ => 2 * r) ∘ Complex.im from rfl,
    h4.fderiv]
  simp

/-- Non-holomorphic sanity check: for `f(z) = (im z)^2`, the hyperbolic
Laplacian is `-2 (im z)^2`, not zero. With complex derivatives this
computation would collapse by Cauchy--Riemann. -/
theorem hyperbolicLaplacian_im_sq (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) z =
      -2 * (((z : ℂ).im ^ 2 : ℝ) : ℂ) := by
  have hRe : partialRe (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) =
      fun _ => 0 := by
    funext u
    rw [partialRe_eq (F := fun w : ℂ => ((w.im ^ 2 : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_im_sq_apply]
    simp
  have hIm : partialIm (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) =
      fun u : UpperHalfPlane => ((2 * (u : ℂ).im : ℝ) : ℂ) := by
    funext u
    rw [partialIm_eq (F := fun w : ℂ => ((w.im ^ 2 : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_im_sq_apply]
    simp
  have hImIm :
      partialIm (fun u : UpperHalfPlane => ((2 * (u : ℂ).im : ℝ) : ℂ)) z = 2 := by
    rw [partialIm_eq (F := fun w : ℂ => ((2 * w.im : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_two_im_apply]
    simp
  rw [hyperbolicLaplacian, hRe, hIm, partialRe_const, hImIm]
  have hzim : ((z : ℂ).im : ℂ) = (z.im : ℂ) := rfl
  rw [← hzim]
  push_cast
  ring

/-- Smoothness of order two on the upper half plane, through a complex
extension that is twice real-differentiable at every interior point
(real, not complex, differentiability: eigenfunctions need not be
holomorphic). -/
def IsSmooth (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ContDiffOn ℝ 2 F {z | 0 < z.im} ∧ ∀ z : UpperHalfPlane, f z = F z

/-- The standard fundamental domain for `SL(2, ℤ)`, as a set in the upper
half plane. -/
def fundamentalDomain : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖(z : ℂ)‖}

/-- A finite set of coset representatives covering `SL(2, ℤ)` by left
cosets of `Γ`. -/
def IsCosetCover (Γ : Subgroup SL(2, ℤ)) (s : Finset SL(2, ℤ)) : Prop :=
  ∀ g : SL(2, ℤ), ∃ a ∈ s, ∃ γ ∈ Γ, g = γ * a

/-- Square-integrability on the quotient `Γ \ ℍ`, expressed through one
finite coset covering: the hyperbolic integral of `‖f‖²` over the
corresponding translates of the standard fundamental domain is finite.
Independence from the chosen covering is part of the recorded model
scope in the module docstring. -/
def IsL2Quotient (Γ : Subgroup SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ s : Finset SL(2, ℤ), IsCosetCover Γ s ∧
    (∫⁻ z in ⋃ a ∈ (s : Set SL(2, ℤ)), (fun z => a • z) '' fundamentalDomain,
      ‖f z‖ₑ ^ 2) < ∞

/-- `λ` is an eigenvalue of the hyperbolic Laplacian on `L²(Γ \ ℍ)`, in
the smooth eigenfunction sense of this file: some nonzero smooth
`Γ`-invariant square-integrable function satisfies `Δf = λ f`. -/
def IsEigenvalue (Γ : Subgroup SL(2, ℤ)) (lam : ℝ) : Prop :=
  ∃ f : UpperHalfPlane → ℂ, f ≠ 0 ∧ IsSmooth f ∧
    (∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ z : UpperHalfPlane, f (γ • z) = f z) ∧
    IsL2Quotient Γ f ∧
    ∀ z : UpperHalfPlane, hyperbolicLaplacian f z = (lam : ℂ) * f z

/-- The set of gap contributions of `Γ`: `0` together with
`√(1/4 - λ)` for every exceptional eigenvalue `λ ∈ (0, 1/4)`. -/
def exceptionalGaps (Γ : Subgroup SL(2, ℤ)) : Set ℝ :=
  {0} ∪ {y | ∃ lam : ℝ, IsEigenvalue Γ lam ∧ 0 < lam ∧ lam < 1 / 4 ∧
    y = Real.sqrt (1 / 4 - lam)}

/-- The gap parameter `θ(Γ)`: the supremum of the gap contributions. -/
noncomputable def exceptionalGap (Γ : Subgroup SL(2, ℤ)) : ℝ :=
  sSup (exceptionalGaps Γ)

/-- The **Selberg congruence spectral-gap constant** `C₆₁`: the supremum
of `θ(Γ)` over all congruence subgroups `Γ` of `SL(2, ℤ)`. -/
noncomputable def selbergConstant : ℝ :=
  sSup {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
    y = exceptionalGap Γ}

/-- Selberg's eigenvalue conjecture in the model of this file: no
congruence subgroup has an eigenvalue in `(0, 1/4)`. -/
def SelbergEigenvalueConjecture : Prop :=
  ∀ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ → ∀ lam : ℝ,
    IsEigenvalue Γ lam → ¬ (0 < lam ∧ lam < 1 / 4)

private theorem sqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem le_half_of_mem_exceptionalGaps {Γ : Subgroup SL(2, ℤ)} {y : ℝ}
    (hy : y ∈ exceptionalGaps Γ) : y ≤ 1 / 2 := by
  rcases hy with rfl | ⟨lam, _hlam, hpos, hlt, rfl⟩
  · norm_num
  · calc
      Real.sqrt (1 / 4 - lam) ≤ Real.sqrt (1 / 4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      _ = 1 / 2 := sqrt_quarter

theorem exceptionalGaps_bddAbove (Γ : Subgroup SL(2, ℤ)) :
    BddAbove (exceptionalGaps Γ) :=
  ⟨1 / 2, fun _y hy => le_half_of_mem_exceptionalGaps hy⟩

theorem exceptionalGaps_nonempty (Γ : Subgroup SL(2, ℤ)) :
    (exceptionalGaps Γ).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem zero_le_exceptionalGap (Γ : Subgroup SL(2, ℤ)) :
    0 ≤ exceptionalGap Γ :=
  le_csSup (exceptionalGaps_bddAbove Γ) (Or.inl rfl)

theorem exceptionalGap_le_half (Γ : Subgroup SL(2, ℤ)) :
    exceptionalGap Γ ≤ 1 / 2 := by
  apply csSup_le (exceptionalGaps_nonempty Γ)
  intro y hy
  exact le_half_of_mem_exceptionalGaps hy

/-- An exceptional eigenvalue contributes its square-root gap. -/
theorem sqrt_le_exceptionalGap {Γ : Subgroup SL(2, ℤ)} {lam : ℝ}
    (hlam : IsEigenvalue Γ lam) (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ exceptionalGap Γ :=
  le_csSup (exceptionalGaps_bddAbove Γ) (Or.inr ⟨lam, hlam, hpos, hlt, rfl⟩)

theorem selbergGaps_bddAbove :
    BddAbove {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
      y = exceptionalGap Γ} := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨Γ, _hΓ, rfl⟩
  exact exceptionalGap_le_half Γ

theorem selbergGaps_nonempty :
    {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
      y = exceptionalGap Γ}.Nonempty :=
  ⟨exceptionalGap ⊤, ⊤, isCongruenceSubgroup_top, rfl⟩

/-- The gap of any congruence subgroup is at most Selberg's constant. -/
theorem exceptionalGap_le_selbergConstant {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) : exceptionalGap Γ ≤ selbergConstant :=
  le_csSup selbergGaps_bddAbove ⟨Γ, hΓ, rfl⟩

theorem zero_le_selbergConstant : 0 ≤ selbergConstant :=
  (zero_le_exceptionalGap ⊤).trans
    (exceptionalGap_le_selbergConstant isCongruenceSubgroup_top)

/-- Elementary upper bound from the definition: `C₆₁ ≤ 1/2`. -/
theorem selbergConstant_le_half : selbergConstant ≤ 1 / 2 := by
  apply csSup_le selbergGaps_nonempty
  rintro y ⟨Γ, _hΓ, rfl⟩
  exact exceptionalGap_le_half Γ

/-- An exceptional eigenvalue for a congruence subgroup bounds Selberg's
constant from below by its square-root gap. -/
theorem sqrt_le_selbergConstant {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) {lam : ℝ} (hlam : IsEigenvalue Γ lam)
    (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ selbergConstant :=
  (sqrt_le_exceptionalGap hlam hpos hlt).trans
    (exceptionalGap_le_selbergConstant hΓ)

/-- Selberg's constant vanishes exactly when no congruence subgroup has
an exceptional eigenvalue; this is Selberg's eigenvalue conjecture in
the model of this file. -/
theorem selbergConstant_eq_zero_iff :
    selbergConstant = 0 ↔ SelbergEigenvalueConjecture := by
  constructor
  · intro hC Γ hΓ lam hlam hlt
    have h1 := sqrt_le_selbergConstant hΓ hlam hlt.1 hlt.2
    rw [hC] at h1
    have h2 : (0 : ℝ) < Real.sqrt (1 / 4 - lam) := by
      apply Real.sqrt_pos.mpr
      linarith
    linarith
  · intro hconj
    apply le_antisymm _ zero_le_selbergConstant
    apply csSup_le selbergGaps_nonempty
    rintro y ⟨Γ, hΓ, rfl⟩
    apply csSup_le (exceptionalGaps_nonempty Γ)
    intro t ht
    rcases ht with rfl | ⟨lam, hlam, hpos, hlt, rfl⟩
    · exact le_refl 0
    · exact absurd ⟨hpos, hlt⟩ (hconj Γ hΓ lam hlam)

end MathlibExt.NumberTheory.SelbergSpectralGap

end
