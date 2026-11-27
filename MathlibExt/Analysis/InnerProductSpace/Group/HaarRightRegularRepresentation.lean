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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRightRegularPullback
public import MathlibExt.MeasureTheory.Group.ModularCharacterContinuity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import MathlibExt.MeasureTheory.Function.CompactApproximation
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Unitary representation by normalized Haar right translation

For the normalized pullback `R_gξ(x)=Δ(g)^(-1/2) • ξ(xg)`, linearity, `R_1=I` and
`R_(gh)=R_gR_h` give a linear isometric group action on Haar L².

With complete complex Hilbert coefficients, these isometries form a strongly continuous unitary
representation. The inverse is the operator at `g⁻¹`. The modular weight and group order are
retained for nonabelian groups.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace StronglyContinuousUnitaryRepresentation

noncomputable section

universe uG uH

private theorem haarL2_norm_sq
    {X : Type uG} [MeasurableSpace X] (ν : Measure X)
    {E : Type uH} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ζ : Lp E 2 ν) :
    ‖ζ‖ ^ 2 = ∫ x : X, ‖ζ x‖ ^ 2 ∂ν := by
  calc
    ‖ζ‖ ^ 2 = (RCLike.re (inner ℂ ζ ζ) : ℝ) :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) ζ
    _ = RCLike.re (∫ x : X, inner ℂ (ζ x) (ζ x) ∂ν) := rfl
    _ = ∫ x : X, (RCLike.re (inner ℂ (ζ x) (ζ x)) : ℝ) ∂ν :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) ζ ζ)).symm
    _ = ∫ x : X, ‖ζ x‖ ^ 2 ∂ν :=
      integral_congr_ae (Eventually.of_forall fun x =>
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (ζ x)).symm)

private theorem compactIndicatorApprox
    {X : Type uG} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.Regular]
    {E : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ENNReal} (hp : p ≠ ⊤) {s : Set X} (hs : IsCompact s) (hsclosed : IsClosed s)
    (c : E) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ f : X → E, HasCompactSupport f ∧ Continuous f ∧ MemLp f p ν ∧
      eLpNorm (f - s.indicator (fun _ => c)) p ν ≤ ε := by
  exact MeasureTheory.compactIndicatorApprox ν hp hs hsclosed c hε

private theorem locallyCompactVectorApprox
    {X : Type uG} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.Regular]
    {E : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ENNReal} (hp : p ≠ ⊤) {f : X → E} (hf : MemLp f p ν)
    {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ g : X → E, HasCompactSupport g ∧ eLpNorm (f - g) p ν ≤ ε ∧
      Continuous g ∧ MemLp g p ν := by
  exact MeasureTheory.locallyCompactVectorApprox ν hp hf hε

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- **Multiplicativity of the normalized right modular weight.** For a locally compact
topological group, let `w(g)=Measure.modularCharacter(g)^(-1/2)` as a positive real
scalar. Then `w(gh)=w(g)w(h)`, independently of a chosen Haar measure or Hilbert space. -/
theorem haarRightModularWeight_mul (g h : G) :
    (Measure.modularCharacter (g * h) : ℝ) ^ (-(2 : ℝ)⁻¹) =
      (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) *
        (Measure.modularCharacter h : ℝ) ^ (-(2 : ℝ)⁻¹) := by
  rw [map_mul, NNReal.coe_mul]
  exact Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem rightQuasi (g : G) :
    QuasiMeasurePreserving (fun x : G => x * g) μ μ := by
  refine ⟨(measurable_id.mul_const g).aemeasurable, ?_⟩
  rw [Measure.map_right_mul_modular μ g]
  exact Measure.AbsolutelyContinuous.smul_left Measure.AbsolutelyContinuous.rfl _

/-- **Additivity of normalized right pullback.** Let `G` be a locally compact topological
group with its Borel structure, `μ` a regular Haar measure and `H` a complex normed
inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `ξ,η∈Lp H 2 μ`,
`R_g(ξ+η)=R_gξ+R_gη`. -/
theorem haarRightPullback_add (g : G) (ξ η : Lp H 2 μ) :
    haarRightPullback μ g (ξ + η) = haarRightPullback μ g ξ + haarRightPullback μ g η := by
  apply Lp.ext
  have hinput := (rightQuasi μ g).ae_eq_comp (Lp.coeFn_add ξ η)
  have houtput := Lp.coeFn_add (haarRightPullback μ g ξ) (haarRightPullback μ g η)
  filter_upwards [haarRightPullback_ae_eq μ g (ξ + η),
    haarRightPullback_ae_eq μ g ξ, haarRightPullback_ae_eq μ g η,
    hinput, houtput] with x h₁ h₂ h₃ h₄ h₅
  simp only [Function.comp_apply, Pi.add_apply] at h₄ h₅
  rw [h₁, h₅, h₂, h₃, h₄]
  exact smul_add _ _ _

/-- **Complex linearity of normalized right pullback.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `c∈ℂ`, `R_g(c •
ξ)=c • R_gξ`. -/
theorem haarRightPullback_smul (g : G) (c : ℂ) (ξ : Lp H 2 μ) :
    haarRightPullback μ g (c • ξ) = c • haarRightPullback μ g ξ := by
  apply Lp.ext
  have hinput := (rightQuasi μ g).ae_eq_comp (Lp.coeFn_smul c ξ)
  have houtput := Lp.coeFn_smul c (haarRightPullback μ g ξ)
  filter_upwards [haarRightPullback_ae_eq μ g (c • ξ),
    haarRightPullback_ae_eq μ g ξ, hinput, houtput] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply, Pi.smul_apply] at h₃ h₄
  rw [h₁, h₄, h₂, h₃]
  exact smul_comm _ c _

/-- **Identity element acts as the identity right pullback.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `ξ∈Lp H 2 μ`,
`R_1ξ=ξ`. -/
theorem haarRightPullback_one (ξ : Lp H 2 μ) : haarRightPullback μ (1 : G) ξ = ξ := by
  apply Lp.ext
  simpa only [map_one, NNReal.coe_one, Real.one_rpow, one_smul, mul_one] using
    haarRightPullback_ae_eq μ (1 : G) ξ

/-- **Group composition order of normalized right Haar operators.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complex normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `g,h∈G` and
`ξ∈Lp H 2 μ`, `R_(gh)ξ=R_g(R_hξ)`. -/
theorem haarRightPullback_mul (g h : G) (ξ : Lp H 2 μ) :
    haarRightPullback μ (g * h) ξ = haarRightPullback μ g (haarRightPullback μ h ξ) := by
  apply Lp.ext
  have hinner := (rightQuasi μ g).ae_eq_comp (haarRightPullback_ae_eq μ h ξ)
  filter_upwards [haarRightPullback_ae_eq μ (g * h) ξ,
    haarRightPullback_ae_eq μ g (haarRightPullback μ h ξ), hinner] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃]
  calc
    _ = ((Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) *
          (Measure.modularCharacter h : ℝ) ^ (-(2 : ℝ)⁻¹)) • ξ (x * (g * h)) := by
      rw [haarRightModularWeight_mul]
    _ = (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) •
          ((Measure.modularCharacter h : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * (g * h))) :=
      mul_smul _ _ _
    _ = _ := by rw [mul_assoc]

/-- **Normalized right translation as a linear isometric equivalence.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complex normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`.
`haarRightRegularIsometry μ g` has forward function `R_g` and inverse `R_(g⁻¹)`;
completeness of `H` is not required. -/
def haarRightRegularIsometry (g : G) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := haarRightPullback μ g
  invFun := haarRightPullback μ g⁻¹
  left_inv ξ := by
    calc
      _ = haarRightPullback μ (g⁻¹ * g) ξ := (haarRightPullback_mul μ g⁻¹ g ξ).symm
      _ = ξ := by rw [inv_mul_cancel, haarRightPullback_one]
  right_inv ξ := by
    calc
      _ = haarRightPullback μ (g * g⁻¹) ξ := (haarRightPullback_mul μ g g⁻¹ ξ).symm
      _ = ξ := by rw [mul_inv_cancel, haarRightPullback_one]
  map_add' := haarRightPullback_add μ g
  map_smul' := haarRightPullback_smul μ g
  norm_map' := norm_haarRightPullback μ g

variable [CompleteSpace H]

/-- **Unitary group homomorphism of normalized right Haar translations.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complex normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. Assume `H` is
complete. `haarRightRegularUnitaryHom μ : G → U(B(Lp H 2 μ))` sends `g` to `R_g`. -/
def haarRightRegularUnitaryHom : G →* unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun g := Unitary.linearIsometryEquiv.symm (haarRightRegularIsometry (H := H) μ g)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    exact haarRightPullback_one μ ξ
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    exact haarRightPullback_mul μ g h ξ

/-- **Representative of a normalized right unitary group value.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. Assume `H` is
complete. for `g∈G`, `ξ∈Lp H 2 μ`, the unitary at `g` has almost-everywhere value
`Δ(g)^(-1/2) • ξ(xg)`. -/
theorem haarRightRegularUnitaryHom_ae_eq (g : G) (ξ : Lp H 2 μ) :
    (haarRightRegularUnitaryHom (H := H) μ g).val ξ =ᵐ[μ]
      fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g) :=
  haarRightPullback_ae_eq μ g ξ

private theorem haarRight_on_toLp_ae (g : G) (f : G → H) (hf : MemLp f 2 μ) :
    (haarRightRegularUnitaryHom (H := H) μ g).val (hf.toLp f) =ᵐ[μ]
      fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • f (x * g) := by
  have hinput := (rightQuasi μ g).ae_eq_comp (MemLp.coeFn_toLp hf)
  filter_upwards [haarRightRegularUnitaryHom_ae_eq μ g (hf.toLp f), hinput]
    with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂]

private theorem continuous_haarRight_on_compact
    (f : G → H) (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf : MemLp f 2 μ) :
    Continuous (fun g : G =>
      (haarRightRegularUnitaryHom (H := H) μ g).val (hf.toLp f)) := by
  have hd : Continuous (fun g : G => (Measure.modularCharacter g : ℝ)) :=
    continuous_subtype_val.comp Measure.continuous_modularCharacter
  have hw : Continuous (fun g : G =>
      (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹)) :=
    hd.rpow_const fun g => Or.inl (ne_of_gt
      (show (0 : ℝ) < (Measure.modularCharacter g : ℝ) from
        Measure.modularCharacterFun_pos g))
  let F : G → G → H := fun g x =>
    (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • f (x * g)
  have hFcont : Continuous F.uncurry :=
    (hw.comp continuous_fst).smul
      (hfcont.comp (continuous_snd.mul continuous_fst))
  let η : Lp H 2 μ := hf.toLp f
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨U, hUcompact, hUneigh⟩ := exists_compact_mem_nhds g₀
  have hg₀ : g₀ ∈ U := mem_of_mem_nhds hUneigh
  let K : Set G := (fun p : G × G => p.1 * p.2⁻¹) '' (tsupport f ×ˢ U)
  have hfK : IsCompact (tsupport f) := hfcomp
  have hK : IsCompact K :=
    (hfK.prod hUcompact).image (continuous_fst.mul continuous_snd.inv)
  have hFzero : ∀ g x : G, g ∈ U → x ∉ K → F g x = 0 := by
    intro g x hg hx
    have hfx : f (x * g) = 0 := by
      by_contra hne
      apply hx
      refine ⟨(x * g, g), ⟨subset_closure hne, hg⟩, ?_⟩
      change (x * g) * g⁻¹ = x
      rw [mul_assoc, mul_inv_cancel, mul_one]
    simp only [F, hfx, smul_zero]
  let I : G → ℝ := fun g => ∫ x : G, ‖F g x - F g₀ x‖ ^ 2 ∂μ
  have hI : ContinuousAt I g₀ := by
    have hjoint : Continuous (fun p : G × G => ‖F p.1 p.2 - F g₀ p.2‖ ^ 2) :=
      (hFcont.sub (hFcont.comp (continuous_const.prodMk continuous_snd))).norm.pow 2
    have hsupp : ∀ g x : G, g ∈ U → x ∉ K → ‖F g x - F g₀ x‖ ^ 2 = 0 := by
      intro g x hg hx
      simp only [hFzero g x hg hx, hFzero g₀ x hg₀ hx, sub_self, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact (continuousOn_integral_of_compact_support (μ := μ) hK
      hjoint.continuousOn hsupp).continuousAt hUneigh
  have hN (g : G) :
      dist ((haarRightRegularUnitaryHom (H := H) μ g).val η)
        ((haarRightRegularUnitaryHom (H := H) μ g₀).val η) ^ 2 = I g := by
    rw [dist_eq_norm, haarL2_norm_sq μ]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
        ((haarRightRegularUnitaryHom (H := H) μ g).val η)
        ((haarRightRegularUnitaryHom (H := H) μ g₀).val η),
      haarRight_on_toLp_ae μ g f hf, haarRight_on_toLp_ae μ g₀ f hf]
        with x hs h₁ h₂
    simp only [Pi.sub_apply] at hs
    change ((haarRightRegularUnitaryHom (H := H) μ g).val η) x = F g x at h₁
    change ((haarRightRegularUnitaryHom (H := H) μ g₀).val η) x = F g₀ x at h₂
    rw [hs, h₁, h₂]
  have hIzero : I g₀ = 0 := by simp only [I, sub_self, norm_zero, zero_pow (by decide :
    (2 : ℕ) ≠ 0), integral_zero]
  have hItendsto : Tendsto I (𝓝 g₀) (𝓝 0) := by
    simpa only [ContinuousAt, hIzero] using hI
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hevent := (Metric.tendsto_nhds.mp hItendsto) (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [hevent] with g hg
  have hsq :
      dist ((haarRightRegularUnitaryHom (H := H) μ g).val η)
        ((haarRightRegularUnitaryHom (H := H) μ g₀).val η) ^ 2 < ε ^ 2 := by
    rw [hN]
    exact (le_abs_self (I g)).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hg)
  exact (sq_lt_sq₀ dist_nonneg hε.le).mp hsq

private theorem continuous_haarRight_orbit (ξ : Lp H 2 μ) :
    Continuous (fun g : G => (haarRightRegularUnitaryHom (H := H) μ g).val ξ) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨f, hfcomp, happrox, hfcont, hf⟩ :=
    locallyCompactVectorApprox μ ENNReal.ofNat_ne_top (Lp.memLp ξ)
      (ENNReal.ofReal_pos.mpr hquarter).ne'
  let η : Lp H 2 μ := hf.toLp f
  have hed : edist ξ η = eLpNorm ((ξ : G → H) - f) 2 μ := by
    simpa only [Lp.toLp_coeFn] using
      (Lp.edist_toLp_toLp (ξ : G → H) f (Lp.memLp ξ) hf)
  have hdist : dist ξ η ≤ ε / 4 := by
    have h : ENNReal.ofReal (dist ξ η) ≤ ENNReal.ofReal (ε / 4) := by
      rw [← edist_dist, hed]
      exact happrox
    exact (ENNReal.ofReal_le_ofReal_iff hquarter.le).mp h
  have hηcont : ContinuousAt (fun g : G =>
      (haarRightRegularUnitaryHom (H := H) μ g).val η) g₀ :=
    (continuous_haarRight_on_compact μ f hfcont hfcomp hf).continuousAt
  have hevent := (Metric.tendsto_nhds.mp hηcont) (ε / 2) (half_pos hε)
  have hisometry (g : G) (x y : Lp H 2 μ) :
      dist ((haarRightRegularUnitaryHom (H := H) μ g).val x)
        ((haarRightRegularUnitaryHom (H := H) μ g).val y) = dist x y :=
    (Unitary.linearIsometryEquiv (haarRightRegularUnitaryHom (H := H) μ g)).isometry.dist_eq x y
  filter_upwards [hevent] with g hg
  calc
    _ ≤ dist ((haarRightRegularUnitaryHom (H := H) μ g).val ξ)
          ((haarRightRegularUnitaryHom (H := H) μ g).val η) +
        dist ((haarRightRegularUnitaryHom (H := H) μ g).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val ξ) := dist_triangle _ _ _
    _ ≤ dist ((haarRightRegularUnitaryHom (H := H) μ g).val ξ)
          ((haarRightRegularUnitaryHom (H := H) μ g).val η) +
        (dist ((haarRightRegularUnitaryHom (H := H) μ g).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val η) +
        dist ((haarRightRegularUnitaryHom (H := H) μ g₀).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val ξ)) :=
      add_le_add
        (le_refl (dist ((haarRightRegularUnitaryHom (H := H) μ g).val ξ)
          ((haarRightRegularUnitaryHom (H := H) μ g).val η)))
        (dist_triangle
          ((haarRightRegularUnitaryHom (H := H) μ g).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val ξ))
    _ = dist ξ η +
        (dist ((haarRightRegularUnitaryHom (H := H) μ g).val η)
          ((haarRightRegularUnitaryHom (H := H) μ g₀).val η) + dist η ξ) := by
      rw [hisometry, hisometry]
    _ < ε := by rw [dist_comm η ξ]; linarith

variable (G H)

/-- **Strongly continuous normalized right Haar representation.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. Assume `H` is
complete. `haarRightRegular G μ H` is the strongly continuous unitary representation with
operator value `g ↦ R_g`. -/
def haarRightRegular : StronglyContinuousUnitaryRepresentation G (Lp H 2 μ) where
  toMonoidHom := haarRightRegularUnitaryHom (H := H) μ
  continuous_orbit := by
    intro ξ
    exact continuous_haarRight_orbit μ ξ

/-- **Almost-everywhere formula of the right regular representation.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complex normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. Assume `H` is
complete. for `g∈G` and `ξ∈Lp H 2 μ`, `(haarRightRegular G μ H g)ξ(x)=Δ(g)^(-1/2) • ξ(xg)`
almost everywhere. -/
theorem haarRightRegular_ae_eq (g : G) (ξ : Lp H 2 μ) :
    (haarRightRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ =ᵐ[μ]
      fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g) :=
  haarRightRegularUnitaryHom_ae_eq μ g ξ

end

end StronglyContinuousUnitaryRepresentation
