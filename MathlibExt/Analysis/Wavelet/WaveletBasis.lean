/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import MathlibExt.Analysis.Wavelet.ScalingFunction

/-!
# Scaling functions and wavelet bases of multiresolution approximations

The two main constructions of S. Mallat, *Multiresolution approximations and wavelet orthonormal
bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), 69–87, for a multiresolution
approximation `(V_j)` in the sense of
`MathlibExt.Analysis.Wavelet.Multiresolution.IsMultiresolutionApproximation`:

* Section 2: there is a scaling function `φ` whose integer translates form an orthonormal basis
  of `V_0` (and then, by property (3), `√(2^j) φ(2^j x - k)` is an orthonormal basis of `V_j`);
* Section 4: there is a wavelet `ψ` such that `√(2^j) ψ(2^j x - k)`, `(j, k) ∈ ℤ²`, is an
  orthonormal basis of `L²(ℝ)`.

The scaling function is supplied by `MathlibExt.Analysis.Wavelet.ScalingFunction`. The wavelet
construction using the filter `H` and the conjugate filter `G(ω) = e^{-iω} conj(H(ω + π))`
is proved here: the scaling function supplies low-pass coefficients in `ℓ²(ℤ)`, the conjugate
mirror filter supplies a high-pass sequence, and the two even-translate families form an
orthonormal basis of the scale-one space, which dilations transport to every scale.
Both statements assert existence.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace MathlibExt.Analysis.Wavelet.MultiresolutionWanted

open MathlibExt.Analysis.Wavelet.Multiresolution

noncomputable section

/-! ### The dilation unitary -/

private lemma measurePreserving_two_mul :
    MeasurePreserving (fun x : ℝ => 2 * x) volume
      (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)) :=
  ⟨measurable_const_mul 2, by
    rw [Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    norm_num⟩

private lemma measurePreserving_div_two :
    MeasurePreserving (fun x : ℝ => x / 2) volume (ENNReal.ofReal 2 • (volume : Measure ℝ)) := by
  refine ⟨measurable_id.div_const 2, ?_⟩
  rw [show (fun x : ℝ => x / 2) = (fun x : ℝ => (1 / 2 : ℝ) * x) by funext x; ring,
    Real.map_volume_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  congr 1
  norm_num

/-- Composing with `x ↦ 2x` preserves almost-everywhere equality for Lebesgue measure. -/
private lemma ae_two_mul {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (2 * x)) =ᵐ[volume] (fun x => g (2 * x)) := by
  have hμ : (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ) : Measure ℝ) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul le_rfl
  have h' : f =ᵐ[ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)] g := hμ.ae_eq h
  exact measurePreserving_two_mul.quasiMeasurePreserving.ae_eq_comp h'

/-- Composing with `x ↦ x / 2` preserves almost-everywhere equality for Lebesgue measure. -/
private lemma ae_div_two {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (x / 2)) =ᵐ[volume] (fun x => g (x / 2)) := by
  have hμ : (ENNReal.ofReal 2 • (volume : Measure ℝ) : Measure ℝ) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul le_rfl
  have h' : f =ᵐ[ENNReal.ofReal 2 • (volume : Measure ℝ)] g := hμ.ae_eq h
  exact measurePreserving_div_two.quasiMeasurePreserving.ae_eq_comp h'

/-- Composing with `x ↦ 2x` preserves almost-everywhere equality for the
half-scaled Lebesgue measure. -/
private lemma ae_two_mul_scaled {f g : ℝ → ℂ}
    (h : f =ᵐ[ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)] g) :
    (fun x => f (2 * x)) =ᵐ[volume] (fun x => g (2 * x)) :=
  measurePreserving_two_mul.quasiMeasurePreserving.ae_eq_comp h

/-- Composing with `x ↦ x / 2` preserves almost-everywhere equality for the
doubled Lebesgue measure. -/
private lemma ae_div_two_scaled {f g : ℝ → ℂ}
    (h : f =ᵐ[ENNReal.ofReal 2 • (volume : Measure ℝ)] g) :
    (fun x => f (x / 2)) =ᵐ[volume] (fun x => g (x / 2)) :=
  measurePreserving_div_two.quasiMeasurePreserving.ae_eq_comp h

/-- Composing with a translation preserves almost-everywhere equality for Lebesgue measure. -/
private lemma ae_sub (a : ℝ) {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (x - a)) =ᵐ[volume] (fun x => g (x - a)) :=
  (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae_eq_comp h

private noncomputable def toScaledHalf :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)) :=
  Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (μ := ENNReal.ofReal (1 / 2) • (volume : Measure ℝ))
    (ν := volume) (c := ENNReal.ofReal (1 / 2)) ENNReal.ofReal_ne_top le_rfl

private noncomputable def toScaledTwo :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (ENNReal.ofReal 2 • (volume : Measure ℝ)) :=
  Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (μ := ENNReal.ofReal 2 • (volume : Measure ℝ))
    (ν := volume) (c := ENNReal.ofReal 2) ENNReal.ofReal_ne_top le_rfl

private noncomputable def dilComp :
    Lp ℂ 2 (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) (μ := volume)
    (μb := ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)) ℂ (fun x : ℝ => 2 * x)
    measurePreserving_two_mul

private noncomputable def undilComp :
    Lp ℂ 2 (ENNReal.ofReal 2 • (volume : Measure ℝ)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) (μ := volume)
    (μb := ENNReal.ofReal 2 • (volume : Measure ℝ)) ℂ (fun x : ℝ => x / 2) measurePreserving_div_two

/-- The dilation `f ↦ √2 • f(2 ·)`, as a function on `L²(ℝ)`. -/
private noncomputable def dilFun (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((Real.sqrt 2 : ℝ) : ℂ) • dilComp (toScaledHalf f)

/-- The inverse dilation `f ↦ 2 ^ (-1 / 2) • f(· / 2)`, as a function on `L²(ℝ)`. -/
private noncomputable def undilFun (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • undilComp (toScaledTwo f)

private lemma dilComp_ae (f : Lp ℂ 2 (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ))) :
    ⇑(dilComp f) =ᵐ[volume] fun x => f (2 * x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_two_mul

private lemma undilComp_ae (f : Lp ℂ 2 (ENNReal.ofReal 2 • (volume : Measure ℝ))) :
    ⇑(undilComp f) =ᵐ[volume] fun x => f (x / 2) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_div_two

private lemma dilFun_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(dilFun f) =ᵐ[volume] fun x => ((Real.sqrt 2 : ℝ) : ℂ) * f (2 * x) := by
  have h3 : (fun x => ⇑(toScaledHalf f) (2 * x)) =ᵐ[volume] fun x => f (2 * x) :=
    ae_two_mul_scaled (Lp.coeFn_LpToLpOfMeasureLeSMul (μ := ENNReal.ofReal (1 / 2) •
      (volume : Measure ℝ)) (ν := volume) (c := ENNReal.ofReal (1 / 2))
      ENNReal.ofReal_ne_top le_rfl f)
  filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ) (dilComp (toScaledHalf f)),
    dilComp_ae (toScaledHalf f), h3] with x hx1 hx2 hx3
  simp only [Pi.smul_apply, smul_eq_mul] at hx1 hx2
  have hdef : ⇑(dilFun f) x = ((Real.sqrt 2 : ℝ) : ℂ) * ⇑(dilComp (toScaledHalf f)) x := hx1
  rw [hdef, hx2, hx3]

private lemma undilFun_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(undilFun f) =ᵐ[volume] fun x => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * f (x / 2) := by
  have h3 : (fun x => ⇑(toScaledTwo f) (x / 2)) =ᵐ[volume] fun x => f (x / 2) :=
    ae_div_two_scaled (Lp.coeFn_LpToLpOfMeasureLeSMul (μ := ENNReal.ofReal 2 •
      (volume : Measure ℝ)) (ν := volume) (c := ENNReal.ofReal 2)
      ENNReal.ofReal_ne_top le_rfl f)
  filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ (undilComp (toScaledTwo f)),
    undilComp_ae (toScaledTwo f), h3] with x hx1 hx2 hx3
  simp only [Pi.smul_apply, smul_eq_mul] at hx1 hx2
  have hdef : ⇑(undilFun f) x =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ⇑(undilComp (toScaledTwo f)) x := hx1
  rw [hdef, hx2, hx3]

private lemma dil_undil (f : Lp ℂ 2 (volume : Measure ℝ)) : dilFun (undilFun f) = f := by
  apply Lp.ext
  filter_upwards [dilFun_ae (undilFun f), ae_two_mul (undilFun_ae f)] with x hx1 hx2
  rw [hx1, hx2]
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  rw [show (2 * x) / 2 = x by ring, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]

private lemma undil_dil (f : Lp ℂ 2 (volume : Measure ℝ)) : undilFun (dilFun f) = f := by
  apply Lp.ext
  filter_upwards [undilFun_ae (dilFun f), ae_div_two (dilFun_ae f)] with x hx1 hx2
  rw [hx1, hx2]
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  rw [show 2 * (x / 2) = x by ring, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]

private lemma norm_toScaledHalf (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖toScaledHalf f‖ = (Real.sqrt 2)⁻¹ * ‖f‖ := by
  have hcoe : ⇑(toScaledHalf f) =ᵐ[ENNReal.ofReal (1 / 2) • (volume : Measure ℝ)] ⇑f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (μ := ENNReal.ofReal (1 / 2) • (volume : Measure ℝ))
      (ν := volume) (c := ENNReal.ofReal (1 / 2)) ENNReal.ofReal_ne_top le_rfl f
  have hexp : (1 / (2 : ℝ≥0∞)).toReal = (1 : ℝ) / 2 := by
    rw [one_div, ENNReal.toReal_inv]
    norm_num
  have hrpow : ((ENNReal.ofReal (1 / 2)) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
      (Real.sqrt 2)⁻¹ := by
    rw [hexp]
    have h1 : (ENNReal.ofReal (1 / 2 : ℝ)) ^ ((1 : ℝ) / 2) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    rw [h1, ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    simp
  calc ‖toScaledHalf f‖ = (eLpNorm ⇑(toScaledHalf f) 2
          (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ))).toReal := Lp.norm_def _
    _ = (eLpNorm ⇑f 2 (ENNReal.ofReal (1 / 2) • (volume : Measure ℝ))).toReal :=
        by rw [eLpNorm_congr_ae hcoe]
    _ = ((ENNReal.ofReal (1 / 2)) ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm ⇑f 2 volume).toReal := by
        rw [eLpNorm_smul_measure_of_ne_zero (by norm_num) ⇑f 2 volume]
        simp only [smul_eq_mul]
    _ = (Real.sqrt 2)⁻¹ * ‖f‖ := by
        rw [ENNReal.toReal_mul, hrpow, ← Lp.norm_def]

private lemma norm_dilFun (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖dilFun f‖ = ‖f‖ := by
  have h1 : ‖dilFun f‖ = Real.sqrt 2 * ‖dilComp (toScaledHalf f)‖ := by
    have hdef : dilFun f = ((Real.sqrt 2 : ℝ) : ℂ) • dilComp (toScaledHalf f) := rfl
    rw [hdef, norm_smul]
    congr 1
    simp [Real.sqrt_nonneg]
  rw [h1, dilComp.norm_map, norm_toScaledHalf]
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp

private noncomputable def dilLin : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) where
  toFun := dilFun
  map_add' f g := by
    apply Lp.ext
    filter_upwards [dilFun_ae (f + g), dilFun_ae f, dilFun_ae g,
      ae_two_mul (Lp.coeFn_add f g), Lp.coeFn_add (dilFun f) (dilFun g)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h5, h1, h2, h3, h4]
    ring
  map_smul' c f := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    filter_upwards [dilFun_ae (c • f), dilFun_ae f, ae_two_mul (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (dilFun f)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    rw [h4, h1, h2, h3]
    ring

private noncomputable def dilIsometry : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) :=
  { dilLin with norm_map' := fun f => norm_dilFun f }

/-- The dilation unitary `f ↦ √2 • f(2 ·)` on `L²(ℝ)`. -/
private noncomputable def dilEquiv : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective dilIsometry (by
    intro f
    exact ⟨undilFun f, dil_undil f⟩)

private lemma dilEquiv_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(dilEquiv f) =ᵐ[volume] fun x => ((Real.sqrt 2 : ℝ) : ℂ) * f (2 * x) :=
  dilFun_ae f

private lemma dilEquiv_symm_eq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilEquiv.symm f = undilFun f := by
  apply dilEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change f = dilFun (undilFun f)
  exact (dil_undil f).symm

private lemma dilEquiv_symm_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(dilEquiv.symm f) =ᵐ[volume] fun x => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * f (x / 2) := by
  rw [dilEquiv_symm_eq]
  exact undilFun_ae f

/-! ### The translation unitaries -/

private noncomputable def transLin (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) (μ := volume) (μb := volume) ℂ (· - a)
    (measurePreserving_sub_right volume a)

private lemma transLin_ae (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(transLin a f) =ᵐ[volume] fun x => f (x - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

private lemma transLin_inv (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    transLin a (transLin (-a) f) = f := by
  apply Lp.ext
  filter_upwards [transLin_ae a (transLin (-a) f), ae_sub a (transLin_ae (-a) f)] with x hx1 hx2
  rw [hx1, hx2]
  congr 1
  ring

/-- Translation by `a` on `L²(ℝ)`, as a unitary. -/
private noncomputable def transEquiv (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (transLin a) (by
    intro f
    exact ⟨transLin (-a) f, transLin_inv a f⟩)

private lemma transEquiv_ae (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(transEquiv a f) =ᵐ[volume] fun x => f (x - a) :=
  transLin_ae a f

private lemma transEquiv_symm_eq (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (transEquiv a).symm f = transLin (-a) f := by
  apply (transEquiv a).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change f = transLin a (transLin (-a) f)
  exact (transLin_inv a f).symm

/-! ### Restricting a unitary to submodules -/

/-- A unitary mapping a submodule `K` onto a submodule `L` restricts to a unitary `K ≃ L`. -/
private noncomputable def mapSubmoduleEquiv
    (U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    {K L : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (h : ∀ f ∈ K, U f ∈ L) (h' : ∀ f ∈ L, U.symm f ∈ K) : K ≃ₗᵢ[ℂ] L where
  toFun f := ⟨U f, h f f.2⟩
  invFun g := ⟨U.symm g, h' g g.2⟩
  left_inv f := by
    apply Subtype.ext
    simp only
    exact U.symm_apply_apply f
  right_inv g := by
    apply Subtype.ext
    simp only
    exact U.apply_symm_apply g
  map_add' f g := by
    apply Subtype.ext
    change U ((f : Lp ℂ 2 (volume : Measure ℝ)) + g) = U f + U g
    exact map_add U _ _
  map_smul' c f := by
    apply Subtype.ext
    change U (c • (f : Lp ℂ 2 (volume : Measure ℝ))) = c • U f
    exact map_smul U c _
  norm_map' f := by
    change ‖U (f : Lp ℂ 2 (volume : Measure ℝ))‖ = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖
    exact U.norm_map _

/-! ### Dilation and translation preserve the resolution spaces -/

private lemma dil_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ V j) : dilEquiv f ∈ V (j + 1) := by
  obtain ⟨_, _, _, _, hDil, _, _⟩ := hV
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  set g : Lp ℂ 2 (volume : Measure ℝ) :=
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • dilEquiv f with hg
  have hg_ae : ⇑g =ᵐ[volume] fun x => f (2 * x) := by
    filter_upwards [dilEquiv_ae f, Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ (dilEquiv f)]
      with x hx1 hx2
    simp only [Pi.smul_apply, smul_eq_mul] at hx2
    rw [hg, hx2, hx1]
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]
  have hg_mem : g ∈ V (j + 1) := (hDil j f g hg_ae).mp hf
  have hEq : dilEquiv f = ((Real.sqrt 2 : ℝ) : ℂ) • g := by
    rw [hg, smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
  rw [hEq]
  exact Submodule.smul_mem _ _ hg_mem

private lemma dil_symm_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ V (j + 1)) : dilEquiv.symm f ∈ V j := by
  obtain ⟨_, _, _, _, hDil, _, _⟩ := hV
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  set g : Lp ℂ 2 (volume : Measure ℝ) :=
    ((Real.sqrt 2 : ℝ) : ℂ) • dilEquiv.symm f with hg
  have hg_ae : ⇑f =ᵐ[volume] fun x => g (2 * x) := by
    have h2 := ae_two_mul (dilEquiv_symm_ae f)
    have h3 : (fun x => ⇑g (2 * x)) =ᵐ[volume]
        fun x => ((Real.sqrt 2 : ℝ) : ℂ) * ⇑(dilEquiv.symm f) (2 * x) := by
      have hsm : ⇑g =ᵐ[volume]
          fun x => ((Real.sqrt 2 : ℝ) : ℂ) * ⇑(dilEquiv.symm f) x := by
        rw [hg]
        filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ) (dilEquiv.symm f)] with x hx
        simp only [Pi.smul_apply, smul_eq_mul] at hx
        exact hx
      exact ae_two_mul hsm
    filter_upwards [h2, h3] with x hx1 hx2
    rw [hx2, hx1]
    rw [show (2 * x) / 2 = x by ring, ← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  have hg_mem : g ∈ V j := (hDil j g f hg_ae).mpr hf
  have hEq : dilEquiv.symm f = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • g := by
    rw [hg, smul_smul, inv_mul_cancel₀ hsqrt, one_smul]
  rw [hEq]
  exact Submodule.smul_mem _ _ hg_mem

private lemma trans_mem_V0 {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ V 0) : transEquiv (k : ℝ) f ∈ V 0 := by
  obtain ⟨_, _, _, _, _, hTr, _⟩ := hV
  apply hTr 0 k f (transEquiv (k : ℝ) f) _ hf
  filter_upwards [transEquiv_ae (k : ℝ) f] with x hx
  rw [hx]
  congr 1
  simp

private lemma trans_mem_V1 {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : f ∈ V 1) : transEquiv (k : ℝ) f ∈ V 1 := by
  obtain ⟨_, _, _, _, _, hTr, _⟩ := hV
  apply hTr 1 (2 * k) f (transEquiv (k : ℝ) f) _ hf
  filter_upwards [transEquiv_ae (k : ℝ) f] with x hx
  rw [hx]
  congr 1
  rw [zpow_neg_one]
  push_cast
  field_simp

/-! ### The shift unitary on `ℓ²(ℤ)` -/

private lemma shiftLpMem (s : ℤ) (x : lp (fun _ : ℤ => ℂ) 2) :
    Memℓp (fun m => (x : ∀ _ : ℤ, ℂ) (m - s)) 2 := by
  apply memℓp_gen
  have hx : Summable fun i => ‖(x : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (p := 2) (by simp)).mp x.prop
  exact (Equiv.subRight s).summable_iff.mpr hx

private noncomputable def shiftLpFun (s : ℤ) (x : lp (fun _ : ℤ => ℂ) 2) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun m => (x : ∀ _ : ℤ, ℂ) (m - s), shiftLpMem s x⟩

private lemma shiftLpFun_apply (s : ℤ) (x : lp (fun _ : ℤ => ℂ) 2) (m : ℤ) :
    ((shiftLpFun s x : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m =
      (x : ∀ _ : ℤ, ℂ) (m - s) :=
  rfl

private noncomputable def shiftLpLin (s : ℤ) : lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ]
    lp (fun _ : ℤ => ℂ) 2 where
  toFun := shiftLpFun s
  map_add' x y := by
    apply lp.ext
    funext m
    rfl
  map_smul' c x := by
    apply lp.ext
    funext m
    rfl

private noncomputable def shiftLpIsometry (s : ℤ) :
    lp (fun _ : ℤ => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  { shiftLpLin s with
    norm_map' := fun x => by
      change ‖shiftLpFun s x‖ = ‖x‖
      rw [lp.norm_eq_tsum_rpow (p := 2) (by simp) (shiftLpFun s x),
        lp.norm_eq_tsum_rpow (p := 2) (by simp) x]
      congr 1
      simp only [shiftLpFun_apply]
      exact (Equiv.subRight s).tsum_eq
        (fun i => ‖(x : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) }

/-- The shift by `s` on `ℓ²(ℤ)`, as a unitary. -/
private noncomputable def shiftLpEquiv (s : ℤ) :
    lp (fun _ : ℤ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearIsometryEquiv.ofSurjective (shiftLpIsometry s) (by
    intro x
    refine ⟨shiftLpFun (-s) x, ?_⟩
    apply lp.ext
    funext m
    change (x : ∀ _ : ℤ, ℂ) (m - s - -s) = (x : ∀ _ : ℤ, ℂ) m
    rw [sub_neg_eq_add, sub_add_cancel])

private lemma shiftLpEquiv_apply (s : ℤ) (x : lp (fun _ : ℤ => ℂ) 2) (m : ℤ) :
    ((shiftLpEquiv s x : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m =
      (x : ∀ _ : ℤ, ℂ) (m - s) :=
  rfl

/-! ### The scaling basis at scale one -/

/-- Dilation restricts to a unitary `V 0 ≃ V 1`. -/
private noncomputable def dilSub {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) : V 0 ≃ₗᵢ[ℂ] V 1 :=
  mapSubmoduleEquiv dilEquiv (fun _f hf => dil_mem hV 0 hf)
    (fun _f hf => dil_symm_mem hV 0 hf)

/-- The scaling basis of `V 1`, obtained by dilating the scaling basis of `V 0`. -/
private noncomputable def scaleOneBasis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0)) :
    HilbertBasis ℤ ℂ (V 1) :=
  ⟨(dilSub hV).symm.trans b0.repr⟩

private lemma scaleOneBasis_apply {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0)) (k : ℤ) :
    scaleOneBasis hV b0 k = (dilSub hV) (b0 k) := by
  have hrepr : (scaleOneBasis hV b0).repr = (dilSub hV).symm.trans b0.repr := rfl
  calc scaleOneBasis hV b0 k
      = (scaleOneBasis hV b0).repr.symm (lp.single 2 k 1) :=
        (HilbertBasis.repr_symm_single _ _).symm
    _ = (dilSub hV) (b0 k) := by
        have hsymm : ((dilSub hV).symm.trans b0.repr).symm =
            b0.repr.symm.trans (dilSub hV) := rfl
        rw [hrepr, hsymm, LinearIsometryEquiv.trans_apply, HilbertBasis.repr_symm_single]

private lemma transEquiv_apply (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    transEquiv a f = transLin a f :=
  rfl

/-! ### Translation restrictions and their action on the bases -/

/-- Integer translation restricts to a unitary of `V 1`. -/
private noncomputable def transSubV1 {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) : V 1 ≃ₗᵢ[ℂ] V 1 :=
  mapSubmoduleEquiv (transEquiv (k : ℝ)) (fun _f hf => trans_mem_V1 hV k hf)
    (fun _f hf => by
      rw [transEquiv_symm_eq]
      have hcast : (-(k : ℝ)) = ((-k : ℤ) : ℝ) := by push_cast; ring
      rw [hcast]
      exact trans_mem_V1 hV (-k) hf)

/-- Integer translation restricts to a unitary of `V 0`. -/
private noncomputable def transSubV0 {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) : V 0 ≃ₗᵢ[ℂ] V 0 :=
  mapSubmoduleEquiv (transEquiv (k : ℝ)) (fun _f hf => trans_mem_V0 hV k hf)
    (fun _f hf => by
      rw [transEquiv_symm_eq]
      have hcast : (-(k : ℝ)) = ((-k : ℤ) : ℝ) := by push_cast; ring
      rw [hcast]
      exact trans_mem_V0 hV (-k) hf)

private lemma transSubV1_val {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) (v : V 1) :
    ((transSubV1 hV k) v : Lp ℂ 2 (volume : Measure ℝ)) =
      transEquiv (k : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ)) :=
  rfl

private lemma transSubV0_val {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ) (v : V 0) :
    ((transSubV0 hV k) v : Lp ℂ 2 (volume : Measure ℝ)) =
      transEquiv (k : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ)) :=
  rfl

private lemma dilSub_val {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (v : V 0) :
    ((dilSub hV) v : Lp ℂ 2 (volume : Measure ℝ)) = dilEquiv (v : Lp ℂ 2 (volume : Measure ℝ)) :=
  rfl

private lemma transSubV1_basis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (k m : ℤ) :
    (transSubV1 hV k) (scaleOneBasis hV b0 m) = scaleOneBasis hV b0 (m + 2 * k) := by
  rw [scaleOneBasis_apply, scaleOneBasis_apply]
  apply Subtype.ext
  change transEquiv (k : ℝ) (dilEquiv (b0 m).val) = dilEquiv (b0 (m + 2 * k)).val
  apply Lp.ext
  have e1 := ae_sub (k : ℝ) (dilEquiv_ae (b0 m).val)
  have e2 := ae_sub (k : ℝ) (ae_two_mul (hb m))
  have e3 := ae_two_mul (hb (m + 2 * k))
  filter_upwards [transEquiv_ae (k : ℝ) (dilEquiv (b0 m).val), e1, e2,
    dilEquiv_ae (b0 (m + 2 * k)).val, e3] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, hx2, hx3, hx4, hx5]
  have harg : 2 * (x - (k : ℝ)) - (m : ℝ) = 2 * x - ((m + 2 * k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [harg]

private lemma transSubV0_basis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (k m : ℤ) :
    (transSubV0 hV k) (b0 m) = b0 (m + k) := by
  apply Subtype.ext
  change transEquiv (k : ℝ) (b0 m).val = (b0 (m + k)).val
  apply Lp.ext
  filter_upwards [transEquiv_ae (k : ℝ) (b0 m).val, ae_sub (k : ℝ) (hb m), hb (m + k)] with
    x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  have harg : (x - (k : ℝ)) - (m : ℝ) = x - ((m + k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [harg]

private lemma repr_transSubV1 {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (k : ℤ) (v : V 1) :
    (scaleOneBasis hV b0).repr ((transSubV1 hV k) v) =
      shiftLpEquiv (2 * k) ((scaleOneBasis hV b0).repr v) := by
  apply lp.ext
  funext m
  rw [shiftLpEquiv_apply, HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  have hinner : ⟪(scaleOneBasis hV b0 m : V 1), (transSubV1 hV k) v⟫_ℂ =
      ⟪(scaleOneBasis hV b0 (m - 2 * k) : V 1), v⟫_ℂ := by
    change ⟪((scaleOneBasis hV b0 m : V 1) : Lp ℂ 2 (volume : Measure ℝ)),
        ((transSubV1 hV k) v : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
      ⟪((scaleOneBasis hV b0 (m - 2 * k) : V 1) : Lp ℂ 2 (volume : Measure ℝ)),
        (v : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ
    rw [transSubV1_val]
    have hU : ⟪((scaleOneBasis hV b0 m : V 1) : Lp ℂ 2 (volume : Measure ℝ)),
          transEquiv (k : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
        ⟪(transEquiv (k : ℝ)).symm ((scaleOneBasis hV b0 m : V 1) :
            Lp ℂ 2 (volume : Measure ℝ)), (v : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ := by
      have h := LinearIsometryEquiv.inner_map_map (transEquiv (k : ℝ)).symm
        ((scaleOneBasis hV b0 m : V 1) : Lp ℂ 2 (volume : Measure ℝ))
        (transEquiv (k : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ)))
      rw [LinearIsometryEquiv.symm_apply_apply] at h
      exact h.symm
    rw [hU]
    have hbasis := transSubV1_basis hV b0 φ hb (-k) m
    rw [show m + 2 * -k = m - 2 * k by ring] at hbasis
    have hval : (transEquiv (k : ℝ)).symm
          ((scaleOneBasis hV b0 m : V 1) : Lp ℂ 2 (volume : Measure ℝ)) =
        ((scaleOneBasis hV b0 (m - 2 * k) : V 1) : Lp ℂ 2 (volume : Measure ℝ)) := by
      rw [transEquiv_symm_eq, ← hbasis]
      change transLin (-(k : ℝ)) ((scaleOneBasis hV b0 m : V 1) : Lp ℂ 2 (volume : Measure ℝ)) =
        transEquiv ((-k : ℤ) : ℝ) ((scaleOneBasis hV b0 m : V 1) :
          Lp ℂ 2 (volume : Measure ℝ))
      rw [transEquiv_apply]
      congr 1
      push_cast
      ring
    rw [hval]
  exact hinner

/-! ### The conjugate mirror filter on `ℓ²(ℤ)` -/

private lemma conj_neg_one_zpow (j : ℤ) : conj ((-1 : ℂ) ^ j) = (-1 : ℂ) ^ j := by simp

private lemma inner_lp_eq (x y : lp (fun _ : ℤ => ℂ) 2) :
    ⟪x, y⟫_ℂ = ∑' i, conj ((x : ∀ _ : ℤ, ℂ) i) * (y : ∀ _ : ℤ, ℂ) i := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply, mul_comm]

private lemma summable_conj_mul (u v : lp (fun _ : ℤ => ℂ) 2) :
    Summable fun i => conj ((u : ∀ _ : ℤ, ℂ) i) * (v : ∀ _ : ℤ, ℂ) i := by
  have h := lp.summable_inner (𝕜 := ℂ) u v
  have h2 : (fun i => conj ((u : ∀ _ : ℤ, ℂ) i) * (v : ∀ _ : ℤ, ℂ) i)
      = fun i => ⟪(u : ∀ _ : ℤ, ℂ) i, (v : ∀ _ : ℤ, ℂ) i⟫_ℂ := by
    funext i
    rw [RCLike.inner_apply, mul_comm]
  rw [h2]
  exact h

private lemma tsum_conj' (f : ℤ → ℂ) : conj (∑' i, f i) = ∑' i, conj (f i) := by
  rw [starRingEnd_apply, tsum_star]
  exact tsum_congr fun i => (starRingEnd_apply _).symm

/-- The mirror filter: `d[m] = (-1)^m conj(c[1 - m])`, Mallat's equation (69) in the
time domain. -/
private noncomputable def mirrorLp (c : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun m => (-1 : ℂ) ^ m * conj ((c : ∀ _ : ℤ, ℂ) (1 - m)), by
    apply memℓp_gen
    have hx : Summable fun i => ‖(c : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
      (memℓp_gen_iff (p := 2) (by simp)).mp c.prop
    have hterm : (fun m => ‖(-1 : ℂ) ^ m * conj ((c : ∀ _ : ℤ, ℂ) (1 - m))‖ ^
        (2 : ℝ≥0∞).toReal)
        = fun m => ‖(c : ∀ _ : ℤ, ℂ) (1 - m)‖ ^ (2 : ℝ≥0∞).toReal := by
      funext m
      rw [norm_mul, show ‖(-1 : ℂ) ^ m‖ = 1 by simp [norm_zpow], one_mul]
      congr 1
      simp
    change Summable fun m => ‖(-1 : ℂ) ^ m * conj ((c : ∀ _ : ℤ, ℂ) (1 - m))‖ ^
      (2 : ℝ≥0∞).toReal
    rw [hterm]
    exact (Equiv.subLeft 1).summable_iff.mpr hx⟩

private lemma mirrorLp_apply (c : lp (fun _ : ℤ => ℂ) 2) (m : ℤ) :
    ((mirrorLp c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m =
      (-1 : ℂ) ^ m * conj ((c : ∀ _ : ℤ, ℂ) (1 - m)) :=
  rfl

private lemma neg_one_zpow_mul_self (a b : ℤ) (h : Even (a + b)) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  exact h.neg_one_zpow

private lemma inner_shift_mirror_mirror (c : lp (fun _ : ℤ => ℂ) 2) (n m : ℤ) :
    ⟪shiftLpEquiv (2 * n) (mirrorLp c), shiftLpEquiv (2 * m) (mirrorLp c)⟫_ℂ =
      conj ⟪shiftLpEquiv (2 * m) c, shiftLpEquiv (2 * n) c⟫_ℂ := by
  have hT : ⟪shiftLpEquiv (2 * n) (mirrorLp c), shiftLpEquiv (2 * m) (mirrorLp c)⟫_ℂ =
      ∑' k, (c : ∀ _ : ℤ, ℂ) k * conj ((c : ∀ _ : ℤ, ℂ) (k - 2 * (n - m))) := by
    rw [inner_lp_eq]
    have hstep : (∑' k, conj (((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
          ∀ _ : ℤ, ℂ) k) * (((shiftLpEquiv (2 * m) (mirrorLp c) : lp
          (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) k))
        = ∑' k, (c : ∀ _ : ℤ, ℂ) (1 - k + 2 * n) *
            conj ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * m)) := by
      refine tsum_congr fun k => ?_
      simp only [shiftLpEquiv_apply, mirrorLp_apply, map_mul, conj_neg_one_zpow,
        Complex.conj_conj]
      have hsgn : (-1 : ℂ) ^ (k - 2 * n) * (-1 : ℂ) ^ (k - 2 * m) = 1 :=
        neg_one_zpow_mul_self _ _ ⟨k - n - m, by ring⟩
      have hidx1 : 1 - (k - 2 * n) = 1 - k + 2 * n := by ring
      have hidx2 : 1 - (k - 2 * m) = 1 - k + 2 * m := by ring
      rw [hidx1, hidx2]
      calc ((-1 : ℂ) ^ (k - 2 * n) * (c : ∀ _ : ℤ, ℂ) (1 - k + 2 * n)) *
              ((-1 : ℂ) ^ (k - 2 * m) * conj ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * m)))
          = ((-1 : ℂ) ^ (k - 2 * n) * (-1 : ℂ) ^ (k - 2 * m)) *
              ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * n) *
                conj ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * m))) := by ring
        _ = (c : ∀ _ : ℤ, ℂ) (1 - k + 2 * n) *
              conj ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * m)) := by rw [hsgn, one_mul]
    rw [hstep]
    rw [← (Equiv.subLeft (1 + 2 * n)).tsum_eq (fun j => (c : ∀ _ : ℤ, ℂ) j *
      conj ((c : ∀ _ : ℤ, ℂ) (j - 2 * (n - m))))]
    refine tsum_congr fun k => ?_
    change (c : ∀ _ : ℤ, ℂ) (1 - k + 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (1 - k + 2 * m)) =
      (c : ∀ _ : ℤ, ℂ) ((1 + 2 * n) - k) *
        conj ((c : ∀ _ : ℤ, ℂ) ((1 + 2 * n) - k - 2 * (n - m)))
    have hidx1 : (1 + 2 * n) - k = 1 - k + 2 * n := by ring
    have hidx2 : 1 - k + 2 * n - 2 * (n - m) = 1 - k + 2 * m := by ring
    rw [hidx1, hidx2]
  rw [hT, inner_lp_eq, tsum_conj']
  simp only [shiftLpEquiv_apply, map_mul, Complex.conj_conj]
  rw [← (Equiv.addRight (2 * m)).tsum_eq (fun j => (c : ∀ _ : ℤ, ℂ) (j - 2 * m) *
    conj ((c : ∀ _ : ℤ, ℂ) (j - 2 * n)))]
  refine tsum_congr fun k => ?_
  change (c : ∀ _ : ℤ, ℂ) k * conj ((c : ∀ _ : ℤ, ℂ) (k - 2 * (n - m))) =
    (c : ∀ _ : ℤ, ℂ) (k + 2 * m - 2 * m) * conj ((c : ∀ _ : ℤ, ℂ) (k + 2 * m - 2 * n))
  have hidx1 : k + 2 * m - 2 * m = k := by ring
  have hidx2 : k + 2 * m - 2 * n = k - 2 * (n - m) := by ring
  rw [hidx1, hidx2]

private lemma orthonormal_shift_mirror {c : lp (fun _ : ℤ => ℂ) 2}
    (hc : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) c)) (n m : ℤ) :
    ⟪shiftLpEquiv (2 * n) (mirrorLp c), shiftLpEquiv (2 * m) (mirrorLp c)⟫_ℂ =
      if n = m then 1 else 0 := by
  rw [inner_shift_mirror_mirror, orthonormal_iff_ite.mp hc]
  by_cases h : m = n
  · subst h
    simp
  · have h2 : n ≠ m := fun hh => h hh.symm
    simp [h, h2]

private lemma tsum_eq_zero_of_involution_neg {F : ℤ → ℂ} (hF : Summable F)
    (e : ℤ ≃ ℤ) (h : ∀ k, F (e k) = -F k) : ∑' k, F k = 0 := by
  have h1 : ∑' k, F k = ∑' k, F (e k) := (e.tsum_eq F).symm
  have h2 : (∑' k, F (e k)) = ∑' k, -F k := tsum_congr h
  have h3 : (∑' k, -F k) = -(∑' k, F k) := hF.hasSum.neg.tsum_eq
  have h4 : (2 : ℂ) * ∑' k, F k = 0 := by
    linear_combination h1.trans (h2.trans h3)
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

private lemma inner_shift_mirror_cross (c : lp (fun _ : ℤ => ℂ) 2) (n m : ℤ) :
    ⟪shiftLpEquiv (2 * n) c, shiftLpEquiv (2 * m) (mirrorLp c)⟫_ℂ = 0 := by
  have hFsumm : Summable fun k => conj ((c : ∀ _ : ℤ, ℂ) (k - 2 * n)) *
      ((-1 : ℂ) ^ (k - 2 * m) * conj ((c : ∀ _ : ℤ, ℂ) (1 - (k - 2 * m)))) := by
    have h := summable_conj_mul (shiftLpEquiv (2 * n) c)
      (shiftLpEquiv (2 * m) (mirrorLp c))
    simpa only [shiftLpEquiv_apply, mirrorLp_apply] using h
  rw [inner_lp_eq]
  simp only [shiftLpEquiv_apply, mirrorLp_apply]
  refine tsum_eq_zero_of_involution_neg hFsumm (Equiv.subLeft (1 + 2 * (n + m))) ?_
  intro k
  have hidx1 : (1 + 2 * (n + m)) - k - 2 * n = 1 - k + 2 * m := by ring
  have hidx2 : (1 + 2 * (n + m)) - k - 2 * m = 1 - k + 2 * n := by ring
  have hidx3 : 1 - ((1 + 2 * (n + m)) - k - 2 * m) = k - 2 * n := by ring
  change conj ((c : ∀ _ : ℤ, ℂ) ((1 + 2 * (n + m)) - k - 2 * n)) *
        ((-1 : ℂ) ^ ((1 + 2 * (n + m)) - k - 2 * m) *
          conj ((c : ∀ _ : ℤ, ℂ) (1 - ((1 + 2 * (n + m)) - k - 2 * m))))
      = - (conj ((c : ∀ _ : ℤ, ℂ) (k - 2 * n)) *
        ((-1 : ℂ) ^ (k - 2 * m) * conj ((c : ∀ _ : ℤ, ℂ) (1 - (k - 2 * m)))))
  rw [hidx3, hidx1, hidx2]
  have hsgn : (-1 : ℂ) ^ (1 - k + 2 * n) = -(-1 : ℂ) ^ (k - 2 * m) := by
    have hodd : Odd ((1 - k + 2 * n) - (k - 2 * m)) := ⟨n + m - k, by ring⟩
    have h1 : 1 - k + 2 * n = (k - 2 * m) + ((1 - k + 2 * n) - (k - 2 * m)) := by ring
    rw [h1, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hodd.neg_one_zpow, mul_neg, mul_one]
  have hidx4 : 1 - (k - 2 * m) = 1 - k + 2 * m := by ring
  rw [hidx4, hsgn]
  ring

/-! ### The parity-restricted autocorrelation -/

/-- The even/odd decomposition of `ℤ` is injective. -/
private theorem evenOdd_injective :
    Function.Injective (Sum.elim (fun n : ℤ => 2 * n) (fun n : ℤ => 2 * n + 1)) := by
  rintro (a | a) (b | b) h <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq] at h ⊢ <;>
    omega

/-- The even/odd decomposition of `ℤ` is surjective. -/
private theorem evenOdd_surjective :
    Function.Surjective (Sum.elim (fun n : ℤ => 2 * n) (fun n : ℤ => 2 * n + 1)) := by
  intro j
  by_cases h : j % 2 = 0
  · exact ⟨Sum.inl (j / 2), by simp only [Sum.elim_inl]; omega⟩
  · exact ⟨Sum.inr ((j - 1) / 2), by simp only [Sum.elim_inr]; omega⟩

/-- The even/odd decomposition of `ℤ`. -/
private noncomputable def evenOddEquiv : ℤ ⊕ ℤ ≃ ℤ :=
  Equiv.ofBijective _ ⟨evenOdd_injective, evenOdd_surjective⟩

private lemma tsum_split_even_odd {F : ℤ → ℂ} (hF : Summable F) :
    ∑' j, F j = (∑' n, F (2 * n)) + ∑' n, F (2 * n + 1) := by
  have heq1 : ((F ∘ evenOddEquiv) ∘ Sum.inl) = fun n => F (2 * n) := funext fun n => rfl
  have heq2 : ((F ∘ evenOddEquiv) ∘ Sum.inr) = fun n => F (2 * n + 1) := funext fun n => rfl
  have hs1 : Summable ((F ∘ evenOddEquiv) ∘ Sum.inl) := by
    rw [heq1]
    exact hF.comp_injective (fun a b h => by omega)
  have hs2 : Summable ((F ∘ evenOddEquiv) ∘ Sum.inr) := by
    rw [heq2]
    exact hF.comp_injective (fun a b h => by omega)
  calc ∑' j, F j = ∑' x : ℤ ⊕ ℤ, F (evenOddEquiv x) := (evenOddEquiv.tsum_eq F).symm
    _ = (∑' n, F (2 * n)) + ∑' n, F (2 * n + 1) := Summable.tsum_sum hs1 hs2

private lemma tsum_split_parity {F : ℤ → ℂ} (hF : Summable F) (l : ℤ) :
    ∑' j, F j = (∑' n, F (l - 2 * n)) + ∑' n, F (l + 1 - 2 * n) := by
  have hG : Summable fun j => F (l - j) := (Equiv.subLeft l).summable_iff.mpr hF
  calc ∑' j, F j = ∑' j, F (l - j) := ((Equiv.subLeft l).tsum_eq F).symm
    _ = (∑' n, F (l - 2 * n)) + ∑' n, F (l - (2 * n + 1)) := tsum_split_even_odd hG
    _ = (∑' n, F (l - 2 * n)) + ∑' n, F (l + 1 - 2 * n) := by
        congr 1
        rw [← (Equiv.addRight 1).tsum_eq (fun n => F (l + 1 - 2 * n))]
        refine tsum_congr fun n => ?_
        change F (l - (2 * n + 1)) = F (l + 1 - 2 * (n + 1))
        congr 1
        ring

/-- Downsampling a square-summable sequence along an arithmetic progression. -/
private noncomputable def downsampleLp (c : lp (fun _ : ℤ => ℂ) 2) (l : ℤ) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun n => (c : ∀ _ : ℤ, ℂ) (l - 2 * n), by
    apply memℓp_gen
    have hx : Summable fun i => ‖(c : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
      (memℓp_gen_iff (p := 2) (by simp)).mp c.prop
    have h2 : Summable fun m => ‖(c : ∀ _ : ℤ, ℂ) (l - m)‖ ^ (2 : ℝ≥0∞).toReal :=
      (Equiv.subLeft l).summable_iff.mpr hx
    exact h2.comp_injective (fun a b h => by omega)⟩

private lemma downsampleLp_apply (c : lp (fun _ : ℤ => ℂ) 2) (l n : ℤ) :
    ((downsampleLp c l : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) n =
      (c : ∀ _ : ℤ, ℂ) (l - 2 * n) :=
  rfl

/-- The parity-restricted autocorrelation `∑' n, conj(c[l - 2n]) c[l + s - 2n]`. -/
private noncomputable def parityAutocorr (c : lp (fun _ : ℤ => ℂ) 2) (s l : ℤ) : ℂ :=
  ∑' n, conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (l + s - 2 * n)

private lemma parityAutocorr_summable (c : lp (fun _ : ℤ => ℂ) 2) (s l : ℤ) :
    Summable fun n => conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
      (c : ∀ _ : ℤ, ℂ) (l + s - 2 * n) := by
  have h := summable_conj_mul (downsampleLp c l) (downsampleLp c (l + s))
  simpa only [downsampleLp_apply] using h

private lemma parityAutocorr_add (c : lp (fun _ : ℤ => ℂ) 2) (s l : ℤ) :
    parityAutocorr c s l + parityAutocorr c s (l + 1) = ⟪shiftLpEquiv s c, c⟫_ℂ := by
  have hFsumm : Summable fun j => conj ((c : ∀ _ : ℤ, ℂ) j) * (c : ∀ _ : ℤ, ℂ) (j + s) := by
    have h := summable_conj_mul c (shiftLpEquiv (-s) c)
    simpa only [shiftLpEquiv_apply, sub_neg_eq_add] using h
  have hQ : ∀ l : ℤ, parityAutocorr c s l =
      ∑' n, conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (l - 2 * n + s) := by
    intro l
    unfold parityAutocorr
    refine tsum_congr fun n => ?_
    rw [show l + s - 2 * n = l - 2 * n + s by ring]
  rw [hQ, hQ, ← tsum_split_parity hFsumm l, inner_lp_eq]
  rw [← (Equiv.subRight s).tsum_eq
    (fun j => conj ((c : ∀ _ : ℤ, ℂ) j) * (c : ∀ _ : ℤ, ℂ) (j + s))]
  refine tsum_congr fun j => ?_
  simp only [shiftLpEquiv_apply, Equiv.subRight_apply, sub_add_cancel]

private lemma parityAutocorr_conj (c : lp (fun _ : ℤ => ℂ) 2) (s l : ℤ) :
    conj (parityAutocorr c s l) = parityAutocorr c (-s) (l + s) := by
  have h1 : conj (parityAutocorr c s l) =
      ∑' n, (c : ∀ _ : ℤ, ℂ) (l - 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (l + s - 2 * n)) := by
    unfold parityAutocorr
    rw [tsum_conj']
    exact tsum_congr fun n => by rw [map_mul, Complex.conj_conj]
  have h2 : parityAutocorr c (-s) (l + s) =
      ∑' n, (c : ∀ _ : ℤ, ℂ) (l - 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (l + s - 2 * n)) := by
    unfold parityAutocorr
    refine tsum_congr fun n => ?_
    change conj ((c : ∀ _ : ℤ, ℂ) (l + s - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (l + s + -s - 2 * n) =
      (c : ∀ _ : ℤ, ℂ) (l - 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (l + s - 2 * n))
    rw [show l + s + -s - 2 * n = l - 2 * n by ring]
    exact mul_comm _ _
  rw [h1, h2]

private lemma parityAutocorr_class (c : lp (fun _ : ℤ => ℂ) 2) (s l l' : ℤ)
    (h : Even (l - l')) : parityAutocorr c s l = parityAutocorr c s l' := by
  obtain ⟨d, hd⟩ := h
  unfold parityAutocorr
  rw [← (Equiv.addRight d).tsum_eq
    (fun n => conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (l + s - 2 * n))]
  refine tsum_congr fun n => ?_
  change conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * (n + d))) * (c : ∀ _ : ℤ, ℂ) (l + s - 2 * (n + d)) =
    conj ((c : ∀ _ : ℤ, ℂ) (l' - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (l' + s - 2 * n)
  have h1 : l - 2 * (n + d) = l' - 2 * n := by omega
  have h2 : l + s - 2 * (n + d) = l' + s - 2 * n := by omega
  rw [h1, h2]

private lemma mirror_autocorr_even (c : lp (fun _ : ℤ => ℂ) 2) (t l : ℤ) :
    (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
      (mirrorLp c : ∀ _ : ℤ, ℂ) (l + 2 * t - 2 * n)) = parityAutocorr c (2 * t) (l + 1) := by
  have hexp : (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
        (mirrorLp c : ∀ _ : ℤ, ℂ) (l + 2 * t - 2 * n))
      = ∑' n, (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
          conj ((c : ∀ _ : ℤ, ℂ) (1 - l - 2 * t + 2 * n)) := by
    refine tsum_congr fun n => ?_
    simp only [mirrorLp_apply, map_mul, conj_neg_one_zpow, Complex.conj_conj]
    have hsgn : (-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + 2 * t - 2 * n) = 1 := by
      have hprod : (-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + 2 * t - 2 * n)
          = (-1 : ℂ) ^ ((l - 2 * n) + (l + 2 * t - 2 * n)) :=
        (zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) _ _).symm
      rw [hprod]
      apply Even.neg_one_zpow
      exact ⟨l + t - 2 * n, by ring⟩
    have hidx1 : 1 - (l - 2 * n) = 1 - l + 2 * n := by ring
    have hidx2 : 1 - (l + 2 * t - 2 * n) = 1 - l - 2 * t + 2 * n := by ring
    rw [hidx1, hidx2]
    calc ((-1 : ℂ) ^ (l - 2 * n) * (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n)) *
            ((-1 : ℂ) ^ (l + 2 * t - 2 * n) *
              conj ((c : ∀ _ : ℤ, ℂ) (1 - l - 2 * t + 2 * n)))
        = ((-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + 2 * t - 2 * n)) *
            ((c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
              conj ((c : ∀ _ : ℤ, ℂ) (1 - l - 2 * t + 2 * n))) := by ring
      _ = (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
            conj ((c : ∀ _ : ℤ, ℂ) (1 - l - 2 * t + 2 * n)) := by rw [hsgn, one_mul]
  have hconj : conj (parityAutocorr c (-(2 * t)) (l + 1)) =
      ∑' n, (c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * n) *
        conj ((c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * t - 2 * n)) := by
    unfold parityAutocorr
    rw [tsum_conj']
    simp only [map_mul, Complex.conj_conj]
    refine tsum_congr fun n => ?_
    rw [show l + 1 + -(2 * t) - 2 * n = l + 1 - 2 * t - 2 * n by ring]
  have hQ2 : parityAutocorr c (2 * t) (l + 1) =
      conj (parityAutocorr c (-(2 * t)) (l + 1)) := by
    have h1 : conj (parityAutocorr c (2 * t) (l + 1)) =
        parityAutocorr c (-(2 * t)) (l + 1) := by
      rw [parityAutocorr_conj c (2 * t) (l + 1)]
      exact parityAutocorr_class c (-(2 * t)) (l + 1 + 2 * t) (l + 1) ⟨t, by ring⟩
    have h2 := congrArg conj h1
    rwa [Complex.conj_conj] at h2
  rw [hexp, hQ2, hconj]
  rw [← (Equiv.subLeft l).tsum_eq
    (fun n => (c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * t - 2 * n)))]
  refine tsum_congr fun n => ?_
  change (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (1 - l - 2 * t + 2 * n)) =
    (c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * (l - n)) * conj ((c : ∀ _ : ℤ, ℂ) (l + 1 - 2 * t - 2 * (l - n)))
  rw [show l + 1 - 2 * (l - n) = 1 - l + 2 * n by ring,
    show l + 1 - 2 * t - 2 * (l - n) = 1 - l - 2 * t + 2 * n by ring]

private lemma mirror_autocorr_odd (c : lp (fun _ : ℤ => ℂ) 2) {s l : ℤ} (hs : Odd s) :
    (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
      (mirrorLp c : ∀ _ : ℤ, ℂ) (l + s - 2 * n))
      = -conj (parityAutocorr c (-s) (1 - l)) := by
  have hexp : (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
        (mirrorLp c : ∀ _ : ℤ, ℂ) (l + s - 2 * n))
      = -(∑' n, (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
          conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n))) := by
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    simp only [mirrorLp_apply, map_mul, conj_neg_one_zpow, Complex.conj_conj]
    have hsgn : (-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + s - 2 * n) = -1 := by
      have hprod : (-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + s - 2 * n)
          = (-1 : ℂ) ^ ((l - 2 * n) + (l + s - 2 * n)) :=
        (zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) _ _).symm
      rw [hprod]
      apply Odd.neg_one_zpow
      obtain ⟨t, ht⟩ := hs
      exact ⟨l - 2 * n + t, by omega⟩
    have hidx1 : 1 - (l - 2 * n) = 1 - l + 2 * n := by ring
    have hidx2 : 1 - (l + s - 2 * n) = 1 - l - s + 2 * n := by ring
    rw [hidx1, hidx2]
    calc ((-1 : ℂ) ^ (l - 2 * n) * (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n)) *
            ((-1 : ℂ) ^ (l + s - 2 * n) *
              conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n)))
        = ((-1 : ℂ) ^ (l - 2 * n) * (-1 : ℂ) ^ (l + s - 2 * n)) *
            ((c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
              conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n))) := by ring
      _ = -( (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
            conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n))) := by
        rw [hsgn, neg_one_mul]
  have hR : (∑' n, (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) *
        conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n))) =
      conj (parityAutocorr c (-s) (1 - l)) := by
    unfold parityAutocorr
    rw [tsum_conj']
    simp only [map_mul, Complex.conj_conj]
    rw [← (Equiv.neg ℤ).tsum_eq
      (fun n => (c : ∀ _ : ℤ, ℂ) (1 - l - 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (1 - l + -s - 2 * n)))]
    refine tsum_congr fun n => ?_
    change (c : ∀ _ : ℤ, ℂ) (1 - l + 2 * n) * conj ((c : ∀ _ : ℤ, ℂ) (1 - l - s + 2 * n)) =
      (c : ∀ _ : ℤ, ℂ) (1 - l - 2 * (-n)) * conj ((c : ∀ _ : ℤ, ℂ) (1 - l + -s - 2 * (-n)))
    rw [show 1 - l - 2 * (-n) = 1 - l + 2 * n by ring,
      show 1 - l + -s - 2 * (-n) = 1 - l - s + 2 * n by ring]
  rw [hexp, hR]

/-- The coefficient identity: the even translates of the low-pass and mirror filters
jointly resolve the identity on `ℓ²(ℤ)`. -/
private lemma coeff_identity {c : lp (fun _ : ℤ => ℂ) 2}
    (hc : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) c)) (l k : ℤ) :
    (∑' n, conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (k - 2 * n)) +
      (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
        (mirrorLp c : ∀ _ : ℤ, ℂ) (k - 2 * n)) = if l = k then 1 else 0 := by
  have hQ : parityAutocorr c (k - l) l =
      ∑' n, conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (k - 2 * n) := by
    unfold parityAutocorr
    refine tsum_congr fun n => ?_
    rw [show l + (k - l) - 2 * n = k - 2 * n by ring]
  have hshift0 : shiftLpEquiv (0 : ℤ) c = c := by
    apply lp.ext
    funext m
    rw [shiftLpEquiv_apply]
    simp
  have hnorm1 : ⟪c, c⟫_ℂ = 1 := by
    have h0 := orthonormal_iff_ite.mp hc 0 0
    simp only [mul_zero] at h0
    rw [hshift0] at h0
    simpa using h0
  by_cases hlk : l = k
  · have hkl : k - l = 0 := by omega
    have hB : (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
          (mirrorLp c : ∀ _ : ℤ, ℂ) (k - 2 * n)) = parityAutocorr c (2 * 0) (l + 1) := by
      rw [← mirror_autocorr_even c 0 l]
      refine tsum_congr fun n => ?_
      rw [show k - 2 * n = l + 2 * 0 - 2 * n by omega]
    rw [← hQ, hkl, hB]
    simp only [mul_zero]
    have hadd := parityAutocorr_add c (0 : ℤ) l
    rw [hshift0] at hadd
    rw [hadd, hnorm1]
    simp [hlk]
  · have hif : (if l = k then (1 : ℂ) else 0) = 0 := by simp only [hlk, ite_false]
    rw [hif]
    rcases Int.even_or_odd (k - l) with hev | hodd
    · obtain ⟨t, ht⟩ := hev
      have ht2 : k - l = 2 * t := by omega
      have hB : (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
            (mirrorLp c : ∀ _ : ℤ, ℂ) (k - 2 * n)) = parityAutocorr c (2 * t) (l + 1) := by
        rw [← mirror_autocorr_even c t l]
        refine tsum_congr fun n => ?_
        rw [show k - 2 * n = l + 2 * t - 2 * n by omega]
      rw [← hQ, ht2, hB]
      have hadd := parityAutocorr_add c (2 * t) l
      rw [hadd]
      have h0 := orthonormal_iff_ite.mp hc t 0
      simp only [mul_zero] at h0
      rw [hshift0] at h0
      have ht0 : t ≠ 0 := by omega
      simp only [ht0, ite_false] at h0
      exact h0
    · have hB : (∑' n, conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
          (mirrorLp c : ∀ _ : ℤ, ℂ) (k - 2 * n))
          = -conj (parityAutocorr c (-(k - l)) (1 - l)) := by
        rw [← mirror_autocorr_odd c hodd]
        refine tsum_congr fun n => ?_
        rw [show k - 2 * n = l + (k - l) - 2 * n by ring]
      rw [← hQ, hB]
      have hconj : conj (parityAutocorr c (-(k - l)) (1 - l)) = parityAutocorr c (k - l) l := by
        rw [parityAutocorr_conj c (-(k - l)) (1 - l), neg_neg]
        apply parityAutocorr_class
        obtain ⟨t, ht⟩ := hodd
        exact ⟨-l - t, by omega⟩
      rw [hconj]
      exact add_neg_cancel _

private lemma parseval_finite {c : lp (fun _ : ℤ => ℂ) 2}
    (hc : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) c))
    {x : lp (fun _ : ℤ => ℂ) 2} {S : Finset ℤ}
    (hx : ∀ i ∉ S, (x : ∀ _ : ℤ, ℂ) i = 0) :
    ‖x‖ ^ 2 = (∑' n, ‖⟪shiftLpEquiv (2 * n) c, x⟫_ℂ‖ ^ 2) +
      ∑' n, ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ‖ ^ 2 := by
  have hdC : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) (mirrorLp c)) :=
    orthonormal_iff_ite.mpr fun i j => orthonormal_shift_mirror hc i j
  have hnormx : ‖x‖ ^ 2 = ∑' j, ‖(x : ∀ _ : ℤ, ℂ) j‖ ^ 2 := by
    rw [lp.norm_eq_tsum_rpow (p := 2) (by simp) x]
    rw [show (2 : ℝ≥0∞).toReal = 2 by simp]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity :
      (0 : ℝ) ≤ ∑' j, ‖(x : ∀ _ : ℤ, ℂ) j‖ ^ (2 : ℝ))]
    norm_num
  have hCsumm : ∀ l m : ℤ, Summable fun n =>
      (conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) * (c : ∀ _ : ℤ, ℂ) (m - 2 * n) +
        conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
          (mirrorLp c : ∀ _ : ℤ, ℂ) (m - 2 * n)) := by
    intro l m
    exact Summable.add (summable_conj_mul (downsampleLp c l) (downsampleLp c m))
      (summable_conj_mul (downsampleLp (mirrorLp c) l) (downsampleLp (mirrorLp c) m))
  have hExpand : ∀ n : ℤ,
      (⟪shiftLpEquiv (2 * n) c, x⟫_ℂ * conj ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ +
        ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ *
          conj ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ : ℂ)
      = ∑ l ∈ S, ∑ m ∈ S,
          (conj (((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) l) *
              ((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m +
            conj (((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
              ∀ _ : ℤ, ℂ) l) *
              ((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
                ∀ _ : ℤ, ℂ) m) *
            ((x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) m)) := by
    intro n
    have hA : ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ =
        ∑ l ∈ S, conj (((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) :
          ∀ _ : ℤ, ℂ) l) * (x : ∀ _ : ℤ, ℂ) l := by
      rw [inner_lp_eq, tsum_eq_sum (fun i hi => by rw [hx i hi, mul_zero])]
    have hB : ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ =
        ∑ l ∈ S, conj (((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
          ∀ _ : ℤ, ℂ) l) * (x : ∀ _ : ℤ, ℂ) l := by
      rw [inner_lp_eq, tsum_eq_sum (fun i hi => by rw [hx i hi, mul_zero])]
    rw [hA, hB, map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  have hC : (∑' n, (⟪shiftLpEquiv (2 * n) c, x⟫_ℂ *
        conj ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ +
        ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ *
          conj ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ : ℂ)) =
      ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    calc (∑' n, (⟪shiftLpEquiv (2 * n) c, x⟫_ℂ *
          conj ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ +
          ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ *
            conj ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ : ℂ))
        = ∑' n, ∑ l ∈ S, ∑ m ∈ S,
            (conj (((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) l) *
                ((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m +
              conj (((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
                ∀ _ : ℤ, ℂ) l) *
                ((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
                  ∀ _ : ℤ, ℂ) m) *
              ((x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) m)) := tsum_congr hExpand
      _ = ∑ l ∈ S, ∑ m ∈ S, ∑' n,
            (conj (((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) l) *
                ((shiftLpEquiv (2 * n) c : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) m +
              conj (((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
                ∀ _ : ℤ, ℂ) l) *
                ((shiftLpEquiv (2 * n) (mirrorLp c) : lp (fun _ : ℤ => ℂ) 2) :
                  ∀ _ : ℤ, ℂ) m) *
              ((x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) m)) := by
          simp only [shiftLpEquiv_apply]
          rw [Summable.tsum_finsetSum (fun l _ => summable_sum fun m _ => (hCsumm l m).mul_right _)]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Summable.tsum_finsetSum (fun m _ => (hCsumm l m).mul_right _)]
      _ = ∑ l ∈ S, ∑ m ∈ S, (if l = m then (1 : ℂ) else 0) *
            ((x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) m)) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
          simp only [shiftLpEquiv_apply]
          have hA_summ : Summable fun n => conj ((c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
              (c : ∀ _ : ℤ, ℂ) (m - 2 * n) := by
            simpa only [downsampleLp_apply] using
              summable_conj_mul (downsampleLp c l) (downsampleLp c m)
          have hB_summ : Summable fun n => conj ((mirrorLp c : ∀ _ : ℤ, ℂ) (l - 2 * n)) *
              (mirrorLp c : ∀ _ : ℤ, ℂ) (m - 2 * n) := by
            simpa only [downsampleLp_apply] using
              summable_conj_mul (downsampleLp (mirrorLp c) l) (downsampleLp (mirrorLp c) m)
          rw [Summable.tsum_mul_right _ (hCsumm l m), Summable.tsum_add hA_summ hB_summ,
            coeff_identity hc l m]
      _ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
          have hsingle : ∀ l ∈ S, (∑ m ∈ S, (if l = m then (1 : ℂ) else 0) *
              ((x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) m))) =
              (x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) l) := by
            intro l hl
            rw [Finset.sum_eq_single l]
            · simp
            · intro m _ hml
              simp [Ne.symm hml]
            · intro h
              exact absurd hl h
          rw [Finset.sum_congr rfl hsingle]
          rw [show (∑ l ∈ S, (x : ∀ _ : ℤ, ℂ) l * conj ((x : ∀ _ : ℤ, ℂ) l) : ℂ) =
              ((∑ l ∈ S, ‖(x : ∀ _ : ℤ, ℂ) l‖ ^ 2 : ℝ) : ℂ) by
            push_cast
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]]
          congr 1
          rw [hnormx, tsum_eq_sum (fun i hi => by rw [hx i hi]; simp)]
  have hterm : ∀ n : ℤ, (⟪shiftLpEquiv (2 * n) c, x⟫_ℂ *
        conj ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ +
        ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ *
          conj ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ : ℂ) =
      ((‖⟪shiftLpEquiv (2 * n) c, x⟫_ℂ‖ ^ 2 +
        ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) :=
    fun n => by
      rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 : (∑' n, (⟪shiftLpEquiv (2 * n) c, x⟫_ℂ *
        conj ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ +
        ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ *
          conj ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ : ℂ)) =
      Complex.ofReal (∑' n, (‖⟪shiftLpEquiv (2 * n) c, x⟫_ℂ‖ ^ 2 +
        ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ‖ ^ 2 : ℝ)) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hC2 : (∑' n, (‖⟪shiftLpEquiv (2 * n) c, x⟫_ℂ‖ ^ 2 +
        ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ‖ ^ 2 : ℝ)) = ‖x‖ ^ 2 :=
    Complex.ofReal_inj.mp (by rw [h1] at hC; exact hC)
  exact hC2.symm.trans (Summable.tsum_add (Orthonormal.inner_products_summable x hc)
    (Orthonormal.inner_products_summable x hdC))

/-- The finitely supported sequences form a submodule of `ℓ²(ℤ)`. -/
private noncomputable def finSuppSubmodule : Submodule ℂ (lp (fun _ : ℤ => ℂ) 2) where
  carrier := {y | Set.Finite {i | (y : ∀ _ : ℤ, ℂ) i ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    apply Set.Finite.subset (hy.union hz)
    intro i hi
    by_contra hcon
    have hy0 : (y : ∀ _ : ℤ, ℂ) i = 0 := by
      by_contra h
      exact hcon (Set.mem_union_left _ h)
    have hz0 : (z : ∀ _ : ℤ, ℂ) i = 0 := by
      by_contra h
      exact hcon (Set.mem_union_right _ h)
    exact hi (by
      change ((y + z : lp (fun _ : ℤ => ℂ) 2) : ∀ _ : ℤ, ℂ) i = 0
      rw [lp.coeFn_add, Pi.add_apply, hy0, hz0, add_zero])
  smul_mem' := by
    intro c y hy
    apply Set.Finite.subset hy
    intro i hi
    simp only [Set.mem_ofPred_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact fun h => hi (by rw [h, mul_zero])

private lemma lp_total_of_orthogonal {c : lp (fun _ : ℤ => ℂ) 2}
    (hc : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) c)) (x : lp (fun _ : ℤ => ℂ) 2)
    (hx1 : ∀ n, ⟪shiftLpEquiv (2 * n) c, x⟫_ℂ = 0)
    (hx2 : ∀ n, ⟪shiftLpEquiv (2 * n) (mirrorLp c), x⟫_ℂ = 0) : x = 0 := by
  have hdC : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) (mirrorLp c)) :=
    orthonormal_iff_ite.mpr fun i j => orthonormal_shift_mirror hc i j
  let b : HilbertBasis ℤ ℂ (lp (fun _ : ℤ => ℂ) 2) :=
    ⟨LinearIsometryEquiv.refl ℂ _⟩
  have hb_apply : ∀ i : ℤ, b i = lp.single 2 i 1 := fun i =>
    (HilbertBasis.repr_symm_single b i).symm
  have hle : Submodule.span ℂ (Set.range b) ≤ finSuppSubmodule := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    rw [hb_apply]
    apply Set.Finite.subset (Set.finite_singleton i)
    intro j hj
    simp only [Set.mem_ofPred_eq, lp.single_apply, Pi.single_apply] at hj ⊢
    by_contra hji
    simp only [Set.mem_singleton_iff] at hji
    simp only [hji, ite_false] at hj
    exact hj rfl
  have hxmem : x ∈ closure ((Submodule.span ℂ (Set.range b) : Submodule ℂ _) : Set _) := by
    have hmem : x ∈ (Submodule.span ℂ (Set.range b)).topologicalClosure := by
      rw [b.dense_span]
      exact Submodule.mem_top
    exact hmem
  have hxmem2 : x ∈ closure (finSuppSubmodule : Set (lp (fun _ : ℤ => ℂ) 2)) :=
    closure_mono (fun y hy => hle hy) hxmem
  suffices h : ∀ ε : ℝ, 0 < ε → ‖x‖ ^ 2 ≤ 6 * ε ^ 2 by
    have h0 : ‖x‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖x‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have hxpos : 0 < ‖x‖ :=
        lt_of_le_of_ne (norm_nonneg _) (fun h => hne (by rw [← h]; norm_num))
      have hle := h (‖x‖ / 3) (div_pos hxpos (by norm_num))
      nlinarith [hpos, hle]
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h0
    exact h0
  intro ε hε
  obtain ⟨y, hymem, hydist⟩ := (Metric.mem_closure_iff.mp hxmem2) ε hε
  have hsupp : Set.Finite {i | (y : ∀ _ : ℤ, ℂ) i ≠ 0} := hymem
  set S := hsupp.toFinset with hS
  have hxS : ∀ i ∉ S, (y : ∀ _ : ℤ, ℂ) i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hsupp.mem_toFinset.mpr hne)
  have hdist : ‖x - y‖ < ε := by
    rw [← dist_eq_norm]
    exact hydist
  have hAy : (∑' n, ‖⟪shiftLpEquiv (2 * n) c, y⟫_ℂ‖ ^ 2) ≤ ‖x - y‖ ^ 2 := by
    have hEq : (∑' n, ‖⟪shiftLpEquiv (2 * n) c, y⟫_ℂ‖ ^ 2) =
        ∑' n, ‖⟪shiftLpEquiv (2 * n) c, y - x⟫_ℂ‖ ^ 2 := by
      refine tsum_congr fun n => ?_
      congr 1
      rw [inner_sub_right, hx1 n, sub_zero]
    rw [hEq]
    have hle := Orthonormal.tsum_inner_products_le (y - x) hc
    rwa [norm_sub_rev] at hle
  have hBy : (∑' n, ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), y⟫_ℂ‖ ^ 2) ≤ ‖x - y‖ ^ 2 := by
    have hEq : (∑' n, ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), y⟫_ℂ‖ ^ 2) =
        ∑' n, ‖⟪shiftLpEquiv (2 * n) (mirrorLp c), y - x⟫_ℂ‖ ^ 2 := by
      refine tsum_congr fun n => ?_
      congr 1
      rw [inner_sub_right, hx2 n, sub_zero]
    rw [hEq]
    have hle := Orthonormal.tsum_inner_products_le (y - x) hdC
    rwa [norm_sub_rev] at hle
  have hPars := parseval_finite hc hxS
  have hle2 : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 := by
    rw [hPars]
    linarith [hAy, hBy]
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  calc ‖x‖ ^ 2 ≤ (‖x - y‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ 2 * (‖x - y‖ ^ 2 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖x - y‖ - ‖y‖)]
    _ ≤ 2 * (‖x - y‖ ^ 2 + 2 * ‖x - y‖ ^ 2) := by linarith [hle2]
    _ = 6 * ‖x - y‖ ^ 2 := by ring
    _ ≤ 6 * ε ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (norm_nonneg _) hdist.le 2

/-! ### Dilations by integer powers -/

/-- Composing with `x ↦ a * x`, `a ≠ 0`, preserves almost-everywhere equality for
Lebesgue measure. -/
private lemma ae_const_mul {a : ℝ} (ha : a ≠ 0) {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (a * x)) =ᵐ[volume] (fun x => g (a * x)) := by
  have hμ : (ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul le_rfl
  have h' : f =ᵐ[ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)] g := hμ.ae_eq h
  have hmap : MeasurePreserving (fun x : ℝ => a * x) volume
      (ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)) :=
    ⟨measurable_const_mul a, Real.map_volume_mul_left ha⟩
  exact hmap.quasiMeasurePreserving.ae_eq_comp h'

private lemma sqrt_two_zpow (j : ℤ) :
    ((Real.sqrt ((2 : ℝ) ^ j) : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ j := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast (2 : ℝ) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (j : ℝ) * (1 / 2 : ℝ) = (1 / 2 : ℝ) * (j : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow, Real.rpow_intCast,
    Complex.ofReal_zpow]

private lemma dilIter_ae (j : ℤ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑((dilEquiv ^ j) f) =ᵐ[volume]
      fun x => ((Real.sqrt 2 : ℝ) : ℂ) ^ j * f ((2 : ℝ) ^ j * x) := by
  induction j using Int.induction_on generalizing f with
  | zero =>
      rw [show (dilEquiv ^ (0 : ℤ)) f = f by simp]
      filter_upwards [] with x
      simp
  | succ j ih =>
      have hmul : (dilEquiv ^ ((j : ℤ) + 1)) f = (dilEquiv ^ (j : ℤ)) (dilEquiv f) := by
        rw [zpow_add_one]
        rfl
      rw [hmul]
      filter_upwards [ih (dilEquiv f),
        ae_const_mul (by positivity : (2 : ℝ) ^ (j : ℤ) ≠ 0) (dilEquiv_ae f)] with x hx1 hx2
      have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ^ ((j : ℤ) + 1) =
          ((Real.sqrt 2 : ℝ) : ℂ) ^ (j : ℤ) * ((Real.sqrt 2 : ℝ) : ℂ) :=
        zpow_add_one₀ (by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)) _
      have harg : (2 : ℝ) ^ ((j : ℤ) + 1) * x = 2 * ((2 : ℝ) ^ (j : ℤ) * x) := by
        rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
      rw [hx1, hx2, hsc, harg, ← mul_assoc]
  | pred j ih =>
      have hmul : (dilEquiv ^ (-(j : ℤ) - 1)) f = (dilEquiv ^ (-(j : ℤ))) (dilEquiv.symm f) := by
        have h1 : -(j : ℤ) - 1 = -(j : ℤ) + -1 := by ring
        rw [h1, zpow_add, zpow_neg_one]
        rfl
      rw [hmul]
      filter_upwards [ih (dilEquiv.symm f),
        ae_const_mul (by positivity : (2 : ℝ) ^ (-(j : ℤ)) ≠ 0) (dilEquiv_symm_ae f)] with x hx1 hx2
      have harg : (2 : ℝ) ^ (-(j : ℤ) - 1) * x = (2 : ℝ) ^ (-(j : ℤ)) * x / 2 := by
        rw [show -(j : ℤ) - 1 = -(j : ℤ) + -1 by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          show (2 : ℝ) ^ (-1 : ℤ) = (2 : ℝ)⁻¹ by rw [zpow_neg, zpow_one], div_eq_mul_inv]
        ring
      have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ^ (-(j : ℤ) - 1) =
          ((Real.sqrt 2 : ℝ) : ℂ) ^ (-(j : ℤ)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
        rw [show -(j : ℤ) - 1 = -(j : ℤ) + -1 by ring,
          zpow_add₀ (by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)),
          show ((Real.sqrt 2 : ℝ) : ℂ) ^ (-1 : ℤ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ by
            rw [zpow_neg, zpow_one]]
      rw [hx1, hx2, harg, hsc, ← mul_assoc]

private lemma dilIter_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) (k : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ∈ V k) :
    (dilEquiv ^ j) f ∈ V (k + j) := by
  induction j using Int.induction_on generalizing k f with
  | zero => simpa using hf
  | succ j ih =>
      have hmul : (dilEquiv ^ ((j : ℤ) + 1)) f = (dilEquiv ^ (j : ℤ)) (dilEquiv f) := by
        rw [zpow_add_one]
        rfl
      rw [hmul]
      have h1 : dilEquiv f ∈ V (k + 1) := dil_mem hV k hf
      have h2 := ih (k + 1) (dilEquiv f) h1
      rwa [show k + 1 + (j : ℤ) = k + ((j : ℤ) + 1) by ring] at h2
  | pred j ih =>
      have hmul : (dilEquiv ^ (-(j : ℤ) - 1)) f = (dilEquiv ^ (-(j : ℤ))) (dilEquiv.symm f) := by
        have h1 : -(j : ℤ) - 1 = -(j : ℤ) + -1 := by ring
        rw [h1, zpow_add, zpow_neg_one]
        rfl
      rw [hmul]
      have h1 : dilEquiv.symm f ∈ V (k - 1) := by
        have hf' : f ∈ V (k - 1 + 1) := by
          rw [show k - 1 + 1 = k by ring]
          exact hf
        exact dil_symm_mem hV (k - 1) hf'
      have h2 := ih (k - 1) (dilEquiv.symm f) h1
      rwa [show k - 1 + -(j : ℤ) = k + (-(j : ℤ) - 1) by ring] at h2

private lemma dilSymmIter_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) (k : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ∈ V k) :
    (dilEquiv ^ j).symm f ∈ V (k - j) := by
  have hsymm : (dilEquiv ^ j).symm f = (dilEquiv ^ (-j)) f := by
    apply (dilEquiv ^ j).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hmul : (dilEquiv ^ j) ((dilEquiv ^ (-j)) f) = f := by
      change ((dilEquiv ^ j) * (dilEquiv ^ (-j))) f = f
      rw [← zpow_add, show j + -j = (0 : ℤ) by ring, zpow_zero]
      rfl
    exact hmul.symm
  rw [hsymm]
  have h2 := dilIter_mem hV (-j) k f hf
  rwa [show k + -j = k - j by ring] at h2

private lemma dilIter_orth_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ)
    {w : Lp ℂ 2 (volume : Measure ℝ)} (hw : w ∈ (V 0)ᗮ) :
    (dilEquiv ^ j) w ∈ (V j)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hU : ⟪y, (dilEquiv ^ j) w⟫_ℂ =
      ⟪(dilEquiv ^ j).symm y, w⟫_ℂ := by
    have h := LinearIsometryEquiv.inner_map_map (dilEquiv ^ j).symm y ((dilEquiv ^ j) w)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  rw [hU]
  exact (Submodule.mem_orthogonal (V 0) w).mp hw ((dilEquiv ^ j).symm y)
    (by simpa using dilSymmIter_mem hV j j y hy)

private lemma dilIter_symm_apply (j : ℤ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dilEquiv ^ j).symm f = (dilEquiv ^ (-j)) f := by
  apply (dilEquiv ^ j).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change f = ((dilEquiv ^ j) * (dilEquiv ^ (-j))) f
  rw [← zpow_add, show j + -j = (0 : ℤ) by ring, zpow_zero]
  rfl

/-! ### The wavelet at scale zero -/

/-- The inclusion of `V 0` in `V 1`, as a linear isometry. -/
private noncomputable def inclIsometry {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (h : V 0 ≤ V 1) : V 0 →ₗᵢ[ℂ] V 1 where
  toFun y0 := ⟨y0.val, h y0.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

private lemma incl_basis_eq {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (φ1 : V 1) (hφ1 : (φ1 : Lp ℂ 2 (volume : Measure ℝ)) = φ)
    (h01 : V 0 ≤ V 1) (k : ℤ) :
    inclIsometry h01 (b0 k) = (transSubV1 hV k) φ1 := by
  apply Subtype.ext
  change ((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =
    transEquiv (k : ℝ) ((φ1 : V 1) : Lp ℂ 2 (volume : Measure ℝ))
  rw [hφ1]
  apply Lp.ext
  filter_upwards [hb k, transEquiv_ae (k : ℝ) φ] with x hx1 hx2
  rw [hx1, hx2]

/-- Integer translation preserves the orthogonal complement of `V 0`. -/
private lemma trans_orth_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (k : ℤ)
    {w : Lp ℂ 2 (volume : Measure ℝ)} (hw : w ∈ (V 0)ᗮ) :
    transEquiv (k : ℝ) w ∈ (V 0)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hU : ⟪y, transEquiv (k : ℝ) w⟫_ℂ = ⟪(transEquiv (k : ℝ)).symm y, w⟫_ℂ := by
    have h := LinearIsometryEquiv.inner_map_map (transEquiv (k : ℝ)).symm y
      (transEquiv (k : ℝ) w)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  rw [hU]
  exact (Submodule.mem_orthogonal (V 0) w).mp hw ((transEquiv (k : ℝ)).symm y) (by
    rw [transEquiv_symm_eq]
    have hcast : (-(k : ℝ)) = ((-k : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, ← transEquiv_apply]
    exact trans_mem_V0 hV (-k) hy)

/-- The wavelet at scale zero: the mirror filter applied to the scaling function,
transported back from `ℓ²(ℤ)` to `V 1`. -/
private noncomputable def waveletOne {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0)) (φ1 : V 1) : V 1 :=
  (scaleOneBasis hV b0).repr.symm (mirrorLp ((scaleOneBasis hV b0).repr φ1))

private lemma waveletOne_repr {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0)) (φ1 : V 1) :
    (scaleOneBasis hV b0).repr (waveletOne hV b0 φ1) =
      mirrorLp ((scaleOneBasis hV b0).repr φ1) :=
  LinearIsometryEquiv.apply_symm_apply _ _

private lemma waveletOne_orth {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (φ1 : V 1) (hφ1 : (φ1 : Lp ℂ 2 (volume : Measure ℝ)) = φ)
    (h01 : V 0 ≤ V 1) (y0 : V 0) :
    ⟪waveletOne hV b0 φ1, inclIsometry h01 y0⟫_ℂ = 0 := by
  have hL : (innerSL ℂ (waveletOne hV b0 φ1)).comp
      (inclIsometry h01).toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext_on (s := Set.range b0) ?_ ?_
    · intro x
      have hmem : x ∈ (Submodule.span ℂ (Set.range b0)).topologicalClosure := by
        rw [b0.dense_span]
        exact Submodule.mem_top
      exact hmem
    · rintro y ⟨n, rfl⟩
      change ⟪waveletOne hV b0 φ1, inclIsometry h01 (b0 n)⟫_ℂ = 0
      rw [incl_basis_eq hV b0 φ hb φ1 hφ1 h01 n]
      have hinner : ⟪waveletOne hV b0 φ1, (transSubV1 hV n) φ1⟫_ℂ =
          ⟪mirrorLp ((scaleOneBasis hV b0).repr φ1),
            shiftLpEquiv (2 * n) ((scaleOneBasis hV b0).repr φ1)⟫_ℂ := by
        rw [← LinearIsometryEquiv.inner_map_map (scaleOneBasis hV b0).repr
          (waveletOne hV b0 φ1) ((transSubV1 hV n) φ1), waveletOne_repr,
          repr_transSubV1 hV b0 φ hb n φ1]
      rw [hinner, ← inner_conj_symm]
      have h0 := inner_shift_mirror_cross ((scaleOneBasis hV b0).repr φ1) n 0
      have hshift0 : shiftLpEquiv (0 : ℤ) (mirrorLp ((scaleOneBasis hV b0).repr φ1)) =
          mirrorLp ((scaleOneBasis hV b0).repr φ1) := by
        apply lp.ext
        funext m
        rw [shiftLpEquiv_apply]
        simp
      simp only [mul_zero] at h0
      rw [hshift0] at h0
      rw [h0, map_zero]
  have hcongr := DFunLike.congr_fun hL y0
  simpa [innerSL_apply_apply] using hcongr

/-- The orthogonal complement of `V j` in `V (j + 1)`. -/
private noncomputable def orthSubspace (V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (j : ℤ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) := (V j)ᗮ ⊓ V (j + 1)

private lemma orthSubspace_complete {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) : CompleteSpace (orthSubspace V j) := by
  have hclosed : IsClosed ((orthSubspace V j : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) :=
    (Submodule.isClosed_orthogonal (V j)).inter (hV.1 (j + 1))
  exact @IsClosed.completeSpace_coe _ _ _ _ hclosed

private lemma exists_wavelet_orthBasis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (b0 : HilbertBasis ℤ ℂ (V 0))
    (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hb : ∀ k : ℤ, ⇑((b0 k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun x => φ (x - (k : ℝ))) (h01 : V 0 ≤ V 1) :
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ), ∃ bO : HilbertBasis ℤ ℂ (orthSubspace V 0),
      (∀ k, ((bO k : orthSubspace V 0) : Lp ℂ 2 (volume : Measure ℝ)) =
        transEquiv (k : ℝ) ψ) ∧ ψ ∈ (V 0)ᗮ ∧ ψ ∈ V 1 ∧
      (∀ k, ⇑((bO k : orthSubspace V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
        fun x => ψ (x - (k : ℝ))) := by
  have hφ0 : φ ∈ V 0 := by
    have hφ : φ = (b0 0).val := by
      apply Lp.ext
      filter_upwards [hb 0] with x hx
      rw [hx]
      simp
    rw [hφ]
    exact (b0 0).2
  let φ1 : V 1 := ⟨φ, h01 hφ0⟩
  have hφ1 : (φ1 : Lp ℂ 2 (volume : Measure ℝ)) = φ := rfl
  let ψ1 := waveletOne hV b0 φ1
  let ψ : Lp ℂ 2 (volume : Measure ℝ) := ψ1.val
  have hc' : Orthonormal ℂ (fun n => shiftLpEquiv (2 * n) ((scaleOneBasis hV b0).repr φ1)) := by
    rw [orthonormal_iff_ite]
    intro n m
    have h1 : ⟪shiftLpEquiv (2 * n) ((scaleOneBasis hV b0).repr φ1),
        shiftLpEquiv (2 * m) ((scaleOneBasis hV b0).repr φ1)⟫_ℂ =
        ⟪(transSubV1 hV n) φ1, (transSubV1 hV m) φ1⟫_ℂ := by
      rw [← LinearIsometryEquiv.inner_map_map (scaleOneBasis hV b0).repr
        ((transSubV1 hV n) φ1) ((transSubV1 hV m) φ1),
        repr_transSubV1 hV b0 φ hb n φ1, repr_transSubV1 hV b0 φ hb m φ1]
    rw [h1, ← incl_basis_eq hV b0 φ hb φ1 hφ1 h01 n,
      ← incl_basis_eq hV b0 φ hb φ1 hφ1 h01 m]
    exact orthonormal_iff_ite.mp b0.orthonormal n m
  have hψorth : ψ ∈ (V 0)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have h0 := waveletOne_orth hV b0 φ hb φ1 hφ1 h01 ⟨y, hy⟩
    have hinner : ⟪ψ, y⟫_ℂ = ⟪ψ1, inclIsometry h01 ⟨y, hy⟩⟫_ℂ := rfl
    rw [← inner_conj_symm, hinner, h0, map_zero]
  have hψ1 : ψ ∈ V 1 := ψ1.2
  have hatom : ∀ k : ℤ, ((transSubV1 hV k) ψ1 : V 1).val ∈ orthSubspace V 0 := by
    intro k
    refine ⟨?_, ?_⟩
    · have hval : ((transSubV1 hV k) ψ1 : V 1).val = transEquiv (k : ℝ) ψ := by
        rw [transSubV1_val]
      rw [hval]
      exact trans_orth_mem hV k hψorth
    · exact ((transSubV1 hV k) ψ1).2
  let atom : ℤ → orthSubspace V 0 :=
    fun k => ⟨((transSubV1 hV k) ψ1 : V 1).val, hatom k⟩
  have hatom_val : ∀ k : ℤ, ((atom k : orthSubspace V 0) : Lp ℂ 2 (volume : Measure ℝ)) =
      transEquiv (k : ℝ) ψ := by
    intro k
    change ((transSubV1 hV k) ψ1 : V 1).val = transEquiv (k : ℝ) ψ
    rw [transSubV1_val]
  have horth : Orthonormal ℂ atom := by
    rw [orthonormal_iff_ite]
    intro k l
    have h1 : ⟪atom k, atom l⟫_ℂ =
        ⟪shiftLpEquiv (2 * k) (mirrorLp ((scaleOneBasis hV b0).repr φ1)),
          shiftLpEquiv (2 * l) (mirrorLp ((scaleOneBasis hV b0).repr φ1))⟫_ℂ := by
      have h2 : ⟪atom k, atom l⟫_ℂ =
          ⟪(transSubV1 hV k) ψ1, (transSubV1 hV l) ψ1⟫_ℂ := rfl
      have hw1 : (scaleOneBasis hV b0).repr ψ1 =
          mirrorLp ((scaleOneBasis hV b0).repr φ1) := waveletOne_repr hV b0 φ1
      rw [h2, ← LinearIsometryEquiv.inner_map_map (scaleOneBasis hV b0).repr
        ((transSubV1 hV k) ψ1) ((transSubV1 hV l) ψ1),
        repr_transSubV1 hV b0 φ hb k ψ1, repr_transSubV1 hV b0 φ hb l ψ1, hw1]
    rw [h1]
    exact orthonormal_shift_mirror hc' k l
  haveI : CompleteSpace (orthSubspace V 0) := orthSubspace_complete hV 0
  have htotal : (Submodule.span ℂ (Set.range atom))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hzorth : ∀ n : ℤ, ⟪atom n, z⟫_ℂ = 0 := by
      intro n
      exact (Submodule.mem_orthogonal _ z).mp hz (atom n)
        (Submodule.subset_span (Set.mem_range_self n))
    let z1 : V 1 := ⟨z.val, z.2.2⟩
    have hz' : (scaleOneBasis hV b0).repr z1 = 0 := by
      apply lp_total_of_orthogonal hc'
      · intro n
        have h1 : ⟪shiftLpEquiv (2 * n) ((scaleOneBasis hV b0).repr φ1),
            (scaleOneBasis hV b0).repr z1⟫_ℂ =
            ⟪(transSubV1 hV n) φ1, z1⟫_ℂ := by
          rw [← LinearIsometryEquiv.inner_map_map (scaleOneBasis hV b0).repr
            ((transSubV1 hV n) φ1) z1, repr_transSubV1 hV b0 φ hb n φ1]
        rw [h1]
        have h2 : ⟪(transSubV1 hV n) φ1, z1⟫_ℂ = ⟪(b0 n).val, z.val⟫_ℂ := by
          change ⟪((transSubV1 hV n) φ1 : V 1).val, z.val⟫_ℂ = ⟪(b0 n).val, z.val⟫_ℂ
          congr 1
          rw [← incl_basis_eq hV b0 φ hb φ1 hφ1 h01 n]
          rfl
        rw [h2]
        exact (Submodule.mem_orthogonal (V 0) z.val).mp z.2.1 (b0 n).val (b0 n).2
      · intro n
        have hw1 : (scaleOneBasis hV b0).repr ψ1 =
            mirrorLp ((scaleOneBasis hV b0).repr φ1) := waveletOne_repr hV b0 φ1
        have h1 : ⟪shiftLpEquiv (2 * n) (mirrorLp ((scaleOneBasis hV b0).repr φ1)),
            (scaleOneBasis hV b0).repr z1⟫_ℂ =
            ⟪(transSubV1 hV n) ψ1, z1⟫_ℂ := by
          rw [← LinearIsometryEquiv.inner_map_map (scaleOneBasis hV b0).repr
            ((transSubV1 hV n) ψ1) z1, repr_transSubV1 hV b0 φ hb n ψ1, hw1]
        rw [h1]
        have h2 : ⟪(transSubV1 hV n) ψ1, z1⟫_ℂ = ⟪atom n, z⟫_ℂ := rfl
        rw [h2]
        exact hzorth n
    have hz1 : z1 = 0 := by
      have hinj := (scaleOneBasis hV b0).repr.injective
      have h0 : (scaleOneBasis hV b0).repr z1 = (scaleOneBasis hV b0).repr 0 := by
        rw [hz']
        simp
      exact hinj h0
    have hval : z.val = 0 := congrArg Subtype.val hz1
    exact Subtype.ext hval
  refine ⟨ψ, HilbertBasis.mkOfOrthogonalEqBot horth htotal, ?_, hψorth, hψ1, ?_⟩
  · intro k
    rw [show (HilbertBasis.mkOfOrthogonalEqBot horth htotal : HilbertBasis ℤ ℂ _) k = atom k from
      congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot horth htotal) k]
    exact hatom_val k
  · intro k
    rw [show (HilbertBasis.mkOfOrthogonalEqBot horth htotal : HilbertBasis ℤ ℂ _) k = atom k from
      congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot horth htotal) k]
    rw [hatom_val]
    exact transEquiv_ae (k : ℝ) ψ

private lemma mra_mono {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) {a b : ℤ} (hab : a ≤ b) : V a ≤ V b := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
      rw [heq]
      exact le_trans ih (hV.2.1 _)

/-- One-step descent: a vector of `V m` orthogonal to the complement `O (m - 1)` lies
in `V (m - 1)`. -/
private lemma mem_of_orth_of_mem {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) {m : ℤ}
    {w : Lp ℂ 2 (volume : Measure ℝ)} (hw : w ∈ V m)
    (horth : ∀ u ∈ orthSubspace V (m - 1), ⟪w, u⟫_ℂ = 0) : w ∈ V (m - 1) := by
  haveI : CompleteSpace (V (m - 1)) :=
    @IsClosed.completeSpace_coe _ _ _ _ (hV.1 (m - 1))
  obtain ⟨p, hpK, hporth⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := V (m - 1)) w
  have hle : V (m - 1) ≤ V m := mra_mono hV (by omega)
  have hsub : w - p ∈ V m := sub_mem hw (hle hpK)
  have hsub' : w - p ∈ V (m - 1 + 1) := by
    rw [show m - 1 + 1 = m by ring]
    exact hsub
  have hw' : ⟪w, w - p⟫_ℂ = 0 := horth _ ⟨hporth, hsub'⟩
  have hself : ⟪w - p, w - p⟫_ℂ = 0 := by
    rw [inner_sub_left, hw',
      show ⟪p, w - p⟫_ℂ = 0 from
        (Submodule.mem_orthogonal (V (m - 1)) (w - p)).mp hporth p hpK, sub_zero]
  have hzero : w - p = 0 := inner_self_eq_zero.mp hself
  rw [sub_eq_zero.mp hzero]
  exact hpK

/-- Dilation restricts to a unitary between the orthogonal complements at different
scales. -/
private noncomputable def dilSubO {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (j : ℤ) :
    orthSubspace V 0 ≃ₗᵢ[ℂ] orthSubspace V j :=
  mapSubmoduleEquiv (dilEquiv ^ j)
    (fun _f hf => ⟨dilIter_orth_mem hV j hf.1, by
      have h2 := dilIter_mem hV j 1 _f hf.2
      rwa [show (1 : ℤ) + j = j + 1 by ring] at h2⟩)
    (fun _f hf => by
      refine ⟨?_, ?_⟩
      · refine (Submodule.mem_orthogonal (V 0) _).mpr ?_
        intro y hy
        have hU : ⟪y, (dilEquiv ^ j).symm _f⟫_ℂ = ⟪(dilEquiv ^ j) y, _f⟫_ℂ := by
          have h := LinearIsometryEquiv.inner_map_map (dilEquiv ^ j) y
            ((dilEquiv ^ j).symm _f)
          rw [LinearIsometryEquiv.apply_symm_apply] at h
          exact h.symm
        rw [hU]
        exact (Submodule.mem_orthogonal (V j) _f).mp hf.1 ((dilEquiv ^ j) y)
          (by simpa using dilIter_mem hV j 0 y hy)
      · have hsymm : (dilEquiv ^ j).symm _f = (dilEquiv ^ (-j)) _f := dilIter_symm_apply j _f
        rw [hsymm]
        have h2 := dilIter_mem hV (-j) (j + 1) _f hf.2
        rwa [show j + 1 + -j = (1 : ℤ) by ring] at h2)

/-- The wavelet basis of the orthogonal complement at scale `j`, obtained by dilating
the scale-zero basis. -/
private noncomputable def waveletBasisOj {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (bO : HilbertBasis ℤ ℂ (orthSubspace V 0))
    (j : ℤ) : HilbertBasis ℤ ℂ (orthSubspace V j) :=
  ⟨(dilSubO hV j).symm.trans bO.repr⟩

private lemma waveletBasisOj_apply {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) (bO : HilbertBasis ℤ ℂ (orthSubspace V 0))
    (j k : ℤ) : waveletBasisOj hV bO j k = (dilSubO hV j) (bO k) := by
  have hrepr : (waveletBasisOj hV bO j).repr = (dilSubO hV j).symm.trans bO.repr := rfl
  calc waveletBasisOj hV bO j k
      = (waveletBasisOj hV bO j).repr.symm (lp.single 2 k 1) :=
        (HilbertBasis.repr_symm_single _ _).symm
    _ = (dilSubO hV j) (bO k) := by
        have hsymm : ((dilSubO hV j).symm.trans bO.repr).symm =
            bO.repr.symm.trans (dilSubO hV j) := rfl
        rw [hrepr, hsymm, LinearIsometryEquiv.trans_apply, HilbertBasis.repr_symm_single]

/-- A vector orthogonal to every wavelet atom is zero: the atoms span each orthogonal
complement, the complements span the resolution spaces by the projection argument,
and the resolution spaces are dense with trivial intersection. -/
private lemma eq_zero_of_orthogonal_atoms {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V)
    (atom : ℤ × ℤ → Lp ℂ 2 (volume : Measure ℝ))
    (hbOj : ∀ j : ℤ, ∃ bOj : HilbertBasis ℤ ℂ (orthSubspace V j),
      ∀ k, ((bOj k : orthSubspace V j) : Lp ℂ 2 (volume : Measure ℝ)) = atom (j, k))
    {z : Lp ℂ 2 (volume : Measure ℝ)} (hz : ∀ jk : ℤ × ℤ, ⟪atom jk, z⟫_ℂ = 0) : z = 0 := by
  have hperpOj : ∀ (j : ℤ) (w : orthSubspace V j),
      ⟪(w : Lp ℂ 2 (volume : Measure ℝ)), z⟫_ℂ = 0 := by
    intro j w
    obtain ⟨bOj, hbOj⟩ := hbOj j
    have hexp := HilbertBasis.hasSum_repr bOj w
    let F : (orthSubspace V j) →L[ℂ] ℂ :=
      (innerSL ℂ z).comp (Submodule.subtypeL (orthSubspace V j))
    have hmap := HasSum.map hexp F F.continuous
    have hzero : (⇑F ∘ fun i => (bOj.repr w i) • bOj i) = fun _ => (0 : ℂ) := by
      funext k
      change F ((bOj.repr w k) • bOj k) = 0
      have h1 : F ((bOj.repr w k) • bOj k) =
          (bOj.repr w k) * conj
            ⟪((bOj k : orthSubspace V j) : Lp ℂ 2 (volume : Measure ℝ)), z⟫_ℂ := by
        change (innerSL ℂ z) ((bOj.repr w k) • ((bOj k : orthSubspace V j) :
            Lp ℂ 2 (volume : Measure ℝ))) = _
        rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm]
      rw [h1, hbOj k, hz (j, k), map_zero, mul_zero]
    rw [hzero] at hmap
    have hunique := HasSum.unique hmap hasSum_zero
    have hFw : ⟪z, (w : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ = 0 := hunique
    rw [← inner_conj_symm, hFw, map_zero]
  have hzV : ∀ j : ℤ, ∀ y ∈ V j, ⟪y, z⟫_ℂ = 0 := by
    intro j y hy
    haveI : CompleteSpace (V j) := @IsClosed.completeSpace_coe _ _ _ _ (hV.1 j)
    obtain ⟨p, hpK, hporth⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := V j) z
    have hpO : ∀ i : ℤ, i < j → ∀ u ∈ orthSubspace V i, ⟪p, u⟫_ℂ = 0 := by
      intro i hi u hu
      have h1 : ⟪z, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ = 0 := by
        have h2 := hperpOj i ⟨u, hu⟩
        rw [← inner_conj_symm, h2, map_zero]
      have h2 : ⟪z - p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ = 0 := by
        have h3 : (u : Lp ℂ 2 (volume : Measure ℝ)) ∈ V j :=
          mra_mono hV (by omega : i + 1 ≤ j) hu.2
        have h4 := (Submodule.mem_orthogonal (V j) (z - p)).mp hporth u h3
        rw [← inner_conj_symm, h4, map_zero]
      have h3 : ⟪z, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
          ⟪p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ +
            ⟪z - p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ := by
        conv_lhs => rw [← add_sub_cancel p z]
        exact inner_add_left _ _ _
      have h4 : ⟪p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ = 0 := by
        calc ⟪p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ
            = ⟪z, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ -
              ⟪z - p, (u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ := by
                rw [h3]; ring
          _ = 0 := by rw [h1, h2, sub_self]
      exact h4
    have hiter : ∀ N : ℕ, p ∈ V (j - N) := by
      intro N
      induction N with
      | zero => simpa using hpK
      | succ N ih =>
          have hstep := mem_of_orth_of_mem hV ih (m := j - (N : ℤ)) (by
            intro u hu
            exact hpO _ (by omega) u hu)
          have heq : j - (N : ℤ) - 1 = j - ((N + 1 : ℕ) : ℤ) := by push_cast; ring
          rwa [heq] at hstep
    have hpall : ∀ j' : ℤ, p ∈ V j' := by
      intro j'
      by_cases hj' : j' ≤ j
      · obtain ⟨N, hN⟩ : ∃ N : ℕ, j' = j - N := ⟨(j - j').toNat, by omega⟩
        rw [hN]
        exact hiter _
      · exact mra_mono hV (by omega : j ≤ j') hpK
    have hp0 : p = 0 := hV.2.2.2.1 p hpall
    have hdec : ⟪y, z⟫_ℂ = ⟪y, p⟫_ℂ + ⟪y, z - p⟫_ℂ := by
      conv_lhs => rw [← add_sub_cancel p z]
      exact inner_add_right _ _ _
    have hp0' : ⟪y, p⟫_ℂ = 0 := by
      rw [hp0]
      simp
    have h3 := (Submodule.mem_orthogonal (V j) (z - p)).mp hporth y hy
    rw [hdec, hp0', h3, add_zero]
  have hclosed : IsClosed {y : Lp ℂ 2 (volume : Measure ℝ) | ⟪y, z⟫_ℂ = 0} :=
    isClosed_singleton.preimage (continuous_id.inner continuous_const)
  have hsub : (⋃ j, (V j : Set (Lp ℂ 2 (volume : Measure ℝ)))) ⊆
      {y : Lp ℂ 2 (volume : Measure ℝ) | ⟪y, z⟫_ℂ = 0} := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy ⊢
    obtain ⟨j, hj⟩ := hy
    exact hzV j y hj
  have huniv : closure (⋃ j, (V j : Set (Lp ℂ 2 (volume : Measure ℝ)))) ⊆
      {y : Lp ℂ 2 (volume : Measure ℝ) | ⟪y, z⟫_ℂ = 0} :=
    hclosed.closure_subset_iff.mpr hsub
  rw [hV.2.2.1.closure_eq] at huniv
  have hzz : ⟪z, z⟫_ℂ = 0 := huniv (Set.mem_univ z)
  exact inner_self_eq_zero.mp hzz

/-- **Wavelet orthonormal basis of a multiresolution approximation** (S. Mallat,
*Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math.
Soc. 315 (1989), Section 4, the conclusion after (70)). If `(V_j)` is a multiresolution
approximation of `L²(ℝ)`, there is a wavelet `ψ ∈ L²(ℝ)` such that the functions
`x ↦ √(2^j) ψ(2^j x - k)`, `(j, k) ∈ ℤ²`, form an orthonormal basis of `L²(ℝ)`, and those of
scale `j` lie in the orthogonal complement `O_j` of `V_j` in `V_{j+1}` (so that, the `O_j` being
mutually orthogonal, they form an orthonormal basis of `O_j`). -/
theorem exists_wavelet_hilbertBasis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ), ∃ b : HilbertBasis (ℤ × ℤ) ℂ (Lp ℂ 2 (volume : Measure ℝ)),
      (∀ jk : ℤ × ℤ, ⇑(b jk : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
        fun x => ((Real.sqrt ((2 : ℝ) ^ jk.1) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ jk.1 * x - jk.2)) ∧
      ∀ (j k : ℤ), (b (j, k) : Lp ℂ 2 (volume : Measure ℝ)) ∈ V (j + 1) ∧
        (b (j, k) : Lp ℂ 2 (volume : Measure ℝ)) ∈ (V j)ᗮ := by
  obtain ⟨φ, b0, hb⟩ := exists_scaling_function hV
  have h01 : V 0 ≤ V 1 := hV.2.1 0
  obtain ⟨ψ, bO, hbO, hψorth, hψ1, _hbOae⟩ := exists_wavelet_orthBasis hV b0 φ hb h01
  let atom : ℤ × ℤ → Lp ℂ 2 (volume : Measure ℝ) :=
    fun jk => (dilEquiv ^ jk.1) (transEquiv (jk.2 : ℝ) ψ)
  have hatomV : ∀ j k : ℤ, atom (j, k) ∈ V (j + 1) := by
    intro j k
    have h1 : transEquiv (k : ℝ) ψ ∈ V 1 := trans_mem_V1 hV k hψ1
    have h2 := dilIter_mem hV j 1 _ h1
    rwa [show (1 : ℤ) + j = j + 1 by ring] at h2
  have hatomO : ∀ j k : ℤ, atom (j, k) ∈ (V j)ᗮ := by
    intro j k
    exact dilIter_orth_mem hV j (trans_orth_mem hV k hψorth)
  have hbOj : ∀ j : ℤ, ∃ bOj : HilbertBasis ℤ ℂ (orthSubspace V j),
      ∀ k, ((bOj k : orthSubspace V j) : Lp ℂ 2 (volume : Measure ℝ)) = atom (j, k) := by
    intro j
    refine ⟨waveletBasisOj hV bO j, fun k => ?_⟩
    rw [waveletBasisOj_apply]
    show ((dilSubO hV j) (bO k) : orthSubspace V j).val = atom (j, k)
    change (dilEquiv ^ j) ((bO k : orthSubspace V 0) : Lp ℂ 2 (volume : Measure ℝ)) = atom (j, k)
    rw [hbO k]
  have horth : Orthonormal ℂ atom := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, k⟩ ⟨j', k'⟩
    by_cases hjj : j = j'
    · subst hjj
      have h1 : ⟪atom (j, k), atom (j, k')⟫_ℂ =
          ⟪transEquiv (k : ℝ) ψ, transEquiv (k' : ℝ) ψ⟫_ℂ := by
        rw [← LinearIsometryEquiv.inner_map_map (dilEquiv ^ j) (transEquiv (k : ℝ) ψ)
          (transEquiv (k' : ℝ) ψ)]
      rw [h1, ← hbO k, ← hbO k']
      change ⟪(bO k : orthSubspace V 0), (bO k' : orthSubspace V 0)⟫_ℂ =
        if (j, k) = (j, k') then (1 : ℂ) else 0
      rw [orthonormal_iff_ite.mp bO.orthonormal k k']
      by_cases hkk : k = k'
      · subst hkk
        simp
      · simp [hkk]
    · have hlt : j < j' ∨ j' < j := lt_or_gt_of_ne hjj
      rcases hlt with hlt | hlt
      · have hmem : atom (j, k) ∈ V j' := mra_mono hV (by omega : j + 1 ≤ j') (hatomV j k)
        have horth' : atom (j', k') ∈ (V j')ᗮ := hatomO j' k'
        have hne : (j, k) ≠ (j', k') := fun h => hjj (Prod.ext_iff.mp h).1
        simp only [hne, ite_false]
        exact (Submodule.mem_orthogonal (V j') (atom (j', k'))).mp horth' (atom (j, k)) hmem
      · have hmem : atom (j', k') ∈ V j := mra_mono hV (by omega : j' + 1 ≤ j) (hatomV j' k')
        have horth' : atom (j, k) ∈ (V j)ᗮ := hatomO j k
        have h0 := (Submodule.mem_orthogonal (V j) (atom (j, k))).mp horth' (atom (j', k')) hmem
        have hne : (j, k) ≠ (j', k') := fun h => hjj (Prod.ext_iff.mp h).1
        rw [← inner_conj_symm, ite_eq_right hne, h0, map_zero]
  have htotal : (Submodule.span ℂ (Set.range atom))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hzorth : ∀ jk : ℤ × ℤ, ⟪atom jk, z⟫_ℂ = 0 := by
      intro jk
      exact (Submodule.mem_orthogonal _ z).mp hz (atom jk) (Submodule.subset_span ⟨jk, rfl⟩)
    exact eq_zero_of_orthogonal_atoms hV atom hbOj hzorth
  refine ⟨ψ, HilbertBasis.mkOfOrthogonalEqBot horth htotal, ?_, ?_⟩
  · intro jk
    rw [show (HilbertBasis.mkOfOrthogonalEqBot horth htotal : HilbertBasis (ℤ × ℤ) ℂ _)
        jk = atom jk from congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot horth htotal) jk]
    change ⇑((dilEquiv ^ jk.1) (transEquiv (jk.2 : ℝ) ψ)) =ᵐ[volume] fun x =>
      ((Real.sqrt ((2 : ℝ) ^ jk.1) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ jk.1 * x - jk.2)
    filter_upwards [dilIter_ae jk.1 (transEquiv (jk.2 : ℝ) ψ),
      ae_const_mul (by positivity : (2 : ℝ) ^ jk.1 ≠ 0) (transEquiv_ae (jk.2 : ℝ) ψ)] with x hx1 hx2
    rw [hx1, hx2, sqrt_two_zpow]
  · intro j k
    rw [show (HilbertBasis.mkOfOrthogonalEqBot horth htotal : HilbertBasis (ℤ × ℤ) ℂ _)
        (j, k) = atom (j, k) from
      congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot horth htotal) (j, k)]
    exact ⟨hatomV j k, hatomO j k⟩

end
end MathlibExt.Analysis.Wavelet.MultiresolutionWanted
