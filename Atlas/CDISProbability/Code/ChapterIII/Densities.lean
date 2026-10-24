/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Code.ChapterIII.ConditionalLaws
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.HasLaw

/-!
# CDIS Probabilités II-III: marginal and conditional densities

Densities are taken with values in `ℝ≥0∞` (the course's densities are nonnegative reals; a
real density `f` corresponds to `ENNReal.ofReal ∘ f`). The pair `(X, Y)` has density `f` when
its law is `volume.withDensity f` on `ℝ × ℝ`.

* id 38: `X` and `Y` have the marginal densities `f_X(x) = ∫ f(x, y) dy`, `f_Y(y) = ∫ f(x, y) dx`.
* id 51: for `0 < f_X(x) < ∞`, `f_{Y|X=x}(y) = f(x, y) / f_X(x)` is a density, and
  `P_{Y|X=x} = f_{Y|X=x} ℓ` for `P_X`-almost every `x`.
* id 52: `E(g(X, Y)) = ∫ (∫ g(x, y) f_{Y|X=x}(y) dy) f_X(x) dx` (nonnegative `g`), and
  `P(X ∈ B₁, Y ∈ B₂) = ∫_{B₁} (∫_{B₂} f_{Y|X=x}(y) dy) f_X(x) dx`.
* id 54 (density case): `f_Y(y) = ∫ f_{Y|X=x}(y) f_X(x) dx` for almost every `y`, and Bayes'
  formula for densities.
* id 55 (2): `X` and `Y` are independent iff `f_{Y|X=x} ℓ = f_Y ℓ` for `P_X`-almost every `x`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CDIS

section Marginals

variable {f : ℝ × ℝ → ℝ≥0∞}

/-- First marginal density `f_X(x) = ∫ f(x, y) dy`. -/
noncomputable def marginalFst (f : ℝ × ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := ∫⁻ y, f (x, y)

/-- Second marginal density `f_Y(y) = ∫ f(x, y) dx`. -/
noncomputable def marginalSnd (f : ℝ × ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ := ∫⁻ x, f (x, y)

lemma measurable_marginalFst (hf : Measurable f) : Measurable (marginalFst f) :=
  hf.lintegral_prod_right'

lemma measurable_marginalSnd (hf : Measurable f) : Measurable (marginalSnd f) :=
  hf.lintegral_prod_left'

/-- CDIS P.II, id 38 (first marginal). -/
theorem map_fst_withDensity (hf : Measurable f) :
    (volume.withDensity f).map Prod.fst = volume.withDensity (marginalFst f) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs, show Prod.fst ⁻¹' s = s ×ˢ (univ : Set ℝ) from prod_univ.symm,
    Measure.volume_eq_prod, setLIntegral_prod f hf.aemeasurable]
  simp only [Measure.restrict_univ, marginalFst]

/-- CDIS P.II, id 38 (second marginal). -/
theorem map_snd_withDensity (hf : Measurable f) :
    (volume.withDensity f).map Prod.snd = volume.withDensity (marginalSnd f) := by
  ext t ht
  rw [Measure.map_apply measurable_snd ht, withDensity_apply _ (measurable_snd ht),
    withDensity_apply _ ht, show Prod.snd ⁻¹' t = (univ : Set ℝ) ×ˢ t from univ_prod.symm,
    Measure.volume_eq_prod, setLIntegral_prod f hf.aemeasurable, Measure.restrict_univ,
    lintegral_lintegral_swap
      (show AEMeasurable (Function.uncurry fun x y ↦ f (x, y)) _ from hf.aemeasurable)]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}

/-- CDIS P.II, id 38: if `(X, Y)` has density `f`, then `X` has density `f_X`. -/
theorem hasLaw_fst_of_hasLaw_prod (hf : Measurable f)
    (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    HasLaw X (volume.withDensity (marginalFst f)) P :=
  (show HasLaw Prod.fst (volume.withDensity (marginalFst f)) (volume.withDensity f) from
    ⟨measurable_fst.aemeasurable, map_fst_withDensity hf⟩).fun_comp hXY

/-- CDIS P.II, id 38: if `(X, Y)` has density `f`, then `Y` has density `f_Y`. -/
theorem hasLaw_snd_of_hasLaw_prod (hf : Measurable f)
    (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    HasLaw Y (volume.withDensity (marginalSnd f)) P :=
  (show HasLaw Prod.snd (volume.withDensity (marginalSnd f)) (volume.withDensity f) from
    ⟨measurable_snd.aemeasurable, map_snd_withDensity hf⟩).fun_comp hXY

end Marginals

section ConditionalDensity

variable {f : ℝ × ℝ → ℝ≥0∞}

/-- The points where the conditional density is defined: `0 < f_X(x) < ∞`. -/
def goodSet (f : ℝ × ℝ → ℝ≥0∞) : Set ℝ := {x | marginalFst f x ≠ 0 ∧ marginalFst f x ≠ ⊤}

lemma measurableSet_goodSet (hf : Measurable f) : MeasurableSet (goodSet f) :=
  ((measurable_marginalFst hf) (measurableSet_singleton 0).compl).inter
    ((measurable_marginalFst hf) (measurableSet_singleton ⊤).compl)

/-- CDIS P.III, id 51: the conditional density `f_{Y|X=x}(y) = f(x, y) / f_X(x)`. -/
noncomputable def condDensity (f : ℝ × ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ := f (x, y) / marginalFst f x

/-- CDIS P.III, id 51: for `0 < f_X(x) < ∞`, `f_{Y|X=x}` is a probability density. -/
theorem lintegral_condDensity {x : ℝ} (hx : x ∈ goodSet f) :
    ∫⁻ y, condDensity f x y = 1 := by
  simp only [condDensity, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hx.1)]
  exact ENNReal.mul_inv_cancel hx.1 hx.2

lemma condDensity_mul_marginalFst {x : ℝ} (hx : x ∈ goodSet f) (y : ℝ) :
    condDensity f x y * marginalFst f x = f (x, y) :=
  ENNReal.div_mul_cancel hx.1 hx.2

open scoped Classical in
/-- The density used for the conditional-law kernel: `f_{Y|X=x}` on the good set, and the
uniform density on `[0,1]` elsewhere (a `P_X`-null set), so that every fiber is a probability. -/
noncomputable def kernelDensity (f : ℝ × ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ :=
  if x ∈ goodSet f then condDensity f x y else (Icc (0 : ℝ) 1).indicator 1 y

lemma measurable_kernelDensity (hf : Measurable f) :
    Measurable (Function.uncurry (kernelDensity f)) := by
  unfold Function.uncurry kernelDensity
  refine Measurable.ite ((measurableSet_goodSet hf).preimage measurable_fst) ?_ ?_
  · exact hf.div ((measurable_marginalFst hf).comp measurable_fst)
  · exact (measurable_one.indicator measurableSet_Icc).comp measurable_snd

/-- The kernel `x ↦ f_{Y|X=x} ℓ`. -/
noncomputable def condDensityKernel (f : ℝ × ℝ → ℝ≥0∞) : Kernel ℝ ℝ :=
  Kernel.withDensity (Kernel.const ℝ volume) (kernelDensity f)

lemma condDensityKernel_apply (hf : Measurable f) (x : ℝ) :
    condDensityKernel f x = volume.withDensity (kernelDensity f x) := by
  rw [condDensityKernel, Kernel.withDensity_apply _ (measurable_kernelDensity hf),
    Kernel.const_apply]

lemma isMarkovKernel_condDensityKernel (hf : Measurable f) :
    IsMarkovKernel (condDensityKernel f) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [condDensityKernel_apply hf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  by_cases hx : x ∈ goodSet f
  · simp only [kernelDensity, hx, ite_true]
    exact lintegral_condDensity hx
  · simp only [kernelDensity, hx, ite_false]
    rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
    simp

/-- Almost every `x` (for Lebesgue measure) has `f_X(x) < ∞` when `f` is a probability density. -/
lemma ae_marginalFst_ne_top (hf : Measurable f) (h1 : ∫⁻ p, f p = 1) :
    ∀ᵐ x, marginalFst f x ≠ ⊤ := by
  have hint : ∫⁻ x, marginalFst f x ≠ ⊤ := by
    change ∫⁻ x, ∫⁻ y, f (x, y) ≠ ⊤
    rw [← lintegral_prod f hf.aemeasurable, ← Measure.volume_eq_prod, h1]
    exact ENNReal.one_ne_top
  filter_upwards [ae_lt_top (measurable_marginalFst hf) hint] with x hx using hx.ne

/-- The rectangle formula for the kernel: `∫_{B₁} f_X(x) (∫_{B₂} f_{Y|X=x}) dx = ∫∫_{B₁×B₂} f`. -/
lemma withDensity_eq_compProd_condDensityKernel (hf : Measurable f) (h1 : ∫⁻ p, f p = 1) :
    volume.withDensity f = volume.withDensity (marginalFst f) ⊗ₘ condDensityKernel f := by
  have := isMarkovKernel_condDensityKernel hf
  have : IsFiniteMeasure (volume.withDensity f) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1]; simp⟩
  refine Measure.ext_prod fun {s t} hs ht ↦ ?_
  rw [Measure.compProd_apply_prod hs ht, withDensity_apply _ (hs.prod ht), Measure.volume_eq_prod,
    setLIntegral_prod f hf.aemeasurable,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_marginalFst hf)
      ((condDensityKernel f).measurable_coe ht) hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [ae_marginalFst_ne_top hf h1] with x hxtop _
  simp only [Pi.mul_apply]
  rw [condDensityKernel_apply hf, withDensity_apply _ ht]
  by_cases hx0 : marginalFst f x = 0
  · rw [hx0, zero_mul]
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in t, f (x, y) ≤ ∫⁻ y, f (x, y) := setLIntegral_le_lintegral _ _
      _ = 0 := hx0
  · have hx : x ∈ goodSet f := ⟨hx0, hxtop⟩
    simp only [kernelDensity, hx, ite_true, condDensity, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hx0), mul_comm (marginalFst f x),
      mul_assoc, ENNReal.inv_mul_cancel hx0 hxtop, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}

lemma lintegral_eq_one_of_hasLaw (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    ∫⁻ p, f p = 1 := by
  have := hXY.map_eq ▸ isProbabilityMeasure_map hXY.aemeasurable
  have h := this.measure_univ
  rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h

/-- CDIS P.III, id 51: the conditional law of `Y` given `X` is the kernel with density
`f_{Y|X=x}`, `P_X`-almost everywhere. -/
theorem condDistrib_ae_eq_condDensityKernel (hf : Measurable f) (hX : Measurable X)
    (hY : Measurable Y) (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    condDistrib Y X P =ᵐ[P.map X] condDensityKernel f := by
  have := isMarkovKernel_condDensityKernel hf
  refine condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable hY.aemeasurable ?_
  rw [hXY.map_eq, (hasLaw_fst_of_hasLaw_prod hf hXY).map_eq]
  exact withDensity_eq_compProd_condDensityKernel hf (lintegral_eq_one_of_hasLaw hXY)

/-- `P_X`-almost every `x` has `0 < f_X(x) < ∞`. -/
lemma ae_mem_goodSet (hf : Measurable f)
    (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    ∀ᵐ x ∂(P.map X), x ∈ goodSet f := by
  rw [(hasLaw_fst_of_hasLaw_prod hf hXY).map_eq,
    ae_withDensity_iff' (measurable_marginalFst hf).aemeasurable]
  filter_upwards [ae_marginalFst_ne_top hf (lintegral_eq_one_of_hasLaw hXY)] with x hx h0
  exact ⟨h0, hx⟩

/-- CDIS P.III, id 51, in the course's form: for `P_X`-almost every `x`,
`P_{Y|X=x} = f_{Y|X=x} ℓ`, with `f_{Y|X=x}(y) = f(x, y) / f_X(x)`. -/
theorem condDistrib_ae_eq_withDensity_condDensity (hf : Measurable f) (hX : Measurable X)
    (hY : Measurable Y) (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    ∀ᵐ x ∂(P.map X), condDistrib Y X P x = volume.withDensity (condDensity f x) := by
  filter_upwards [condDistrib_ae_eq_condDensityKernel hf hX hY hXY, ae_mem_goodSet hf hXY]
    with x hx hgood
  rw [hx, condDensityKernel_apply hf]
  congr 1
  funext y
  simp only [kernelDensity, hgood, ite_true]

/-- CDIS P.III, id 52: `E(g(X, Y)) = ∫ (∫ g(x, y) f_{Y|X=x}(y) dy) f_X(x) dx` for nonnegative
measurable `g`. -/
theorem lintegral_comp_eq_lintegral_condDensity (hf : Measurable f) (hX : Measurable X)
    (hY : Measurable Y) (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P)
    {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (X ω, Y ω) ∂P =
      ∫⁻ x, (∫⁻ y, g (x, y) * condDensity f x y) * marginalFst f x := by
  have h1 := lintegral_eq_one_of_hasLaw hXY
  have := isMarkovKernel_condDensityKernel hf
  rw [← lintegral_map hg (hX.prodMk hY), hXY.map_eq,
    withDensity_eq_compProd_condDensityKernel hf h1, Measure.lintegral_compProd hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_marginalFst hf)
      hg.lintegral_kernel_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_marginalFst_ne_top hf h1] with x hxtop
  simp only [Pi.mul_apply]
  by_cases hx0 : marginalFst f x = 0
  · simp [hx0]
  · have hx : x ∈ goodSet f := ⟨hx0, hxtop⟩
    rw [condDensityKernel_apply hf, lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (kernelDensity f x) from
        (measurable_kernelDensity hf).comp measurable_prodMk_left)
      (show Measurable fun y ↦ g (x, y) from hg.comp measurable_prodMk_left), mul_comm]
    congr 1
    refine lintegral_congr fun y ↦ ?_
    simp only [Pi.mul_apply, kernelDensity, hx, ite_true, mul_comm]

/-- CDIS P.III, id 52 (rectangles):
`P(X ∈ B₁, Y ∈ B₂) = ∫_{B₁} (∫_{B₂} f_{Y|X=x}(y) dy) f_X(x) dx`. -/
theorem measure_mem_prod_eq (hf : Measurable f) (hX : Measurable X) (hY : Measurable Y)
    (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) {B₁ B₂ : Set ℝ}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    P {ω | X ω ∈ B₁ ∧ Y ω ∈ B₂} =
      ∫⁻ x in B₁, (∫⁻ y in B₂, condDensity f x y) * marginalFst f x := by
  have h := lintegral_comp_eq_lintegral_condDensity hf hX hY hXY
    (measurable_one.indicator (hB₁.prod hB₂) : Measurable ((B₁ ×ˢ B₂).indicator (1 : ℝ × ℝ → ℝ≥0∞)))
  rw [show {ω | X ω ∈ B₁ ∧ Y ω ∈ B₂} = (fun ω ↦ (X ω, Y ω)) ⁻¹' (B₁ ×ˢ B₂) from rfl,
    ← lintegral_indicator_one ((hX.prodMk hY) (hB₁.prod hB₂))]
  convert h using 1
  · exact lintegral_congr fun ω ↦ rfl
  · rw [← lintegral_indicator hB₁]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ B₁
    · rw [indicator_of_mem hx, ← lintegral_indicator hB₂]
      congr 1
      refine lintegral_congr fun y ↦ ?_
      by_cases hy : y ∈ B₂ <;> simp [hx, hy]
    · simp [hx]

/-- CDIS P.III, id 54 (density case): `f_Y(y) = ∫ f_{Y|X=x}(y) f_X(x) dx` for almost every `y`.
Densities are only defined up to null sets, so "for every `y`" in the course becomes "almost
every `y`" here. -/
theorem ae_marginalSnd_eq_lintegral_condDensity (hf : Measurable f) (h1 : ∫⁻ p, f p = 1) :
    ∀ᵐ y, marginalSnd f y = ∫⁻ x, condDensity f x y * marginalFst f x := by
  have key : ∀ᵐ x, ∀ᵐ y, f (x, y) = condDensity f x y * marginalFst f x := by
    filter_upwards [ae_marginalFst_ne_top hf h1] with x hxtop
    by_cases hx0 : marginalFst f x = 0
    · have hzero : (fun y ↦ f (x, y)) =ᵐ[volume] 0 :=
        (lintegral_eq_zero_iff (hf.comp measurable_prodMk_left)).1 hx0
      filter_upwards [hzero] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy, hx0]
    · exact Filter.Eventually.of_forall fun y ↦
        (condDensity_mul_marginalFst ⟨hx0, hxtop⟩ y).symm
  have hmeas : MeasurableSet
      {p : ℝ × ℝ | f (p.1, p.2) = condDensity f p.1 p.2 * marginalFst f p.1} := by
    refine measurableSet_eq_fun hf ?_
    exact (hf.div ((measurable_marginalFst hf).comp measurable_fst)).mul
      ((measurable_marginalFst hf).comp measurable_fst)
  filter_upwards [(Measure.ae_ae_comm hmeas).1 key] with y hy
  exact lintegral_congr_ae hy

/-- The conditional density of `X` given `Y = y`: `f_{X|Y=y}(x) = f(x, y) / f_Y(y)`. -/
noncomputable def condDensitySnd (f : ℝ × ℝ → ℝ≥0∞) (y x : ℝ) : ℝ≥0∞ := f (x, y) / marginalSnd f y

/-- CDIS P.III, id 54 (Bayes formula for densities):
`f_{X|Y=y}(x) = f_{Y|X=x}(y) f_X(x) / f_Y(y)` when `0 < f_X(x) < ∞`. -/
theorem condDensitySnd_eq {x : ℝ} (hx : x ∈ goodSet f) (y : ℝ) :
    condDensitySnd f y x = condDensity f x y * marginalFst f x / marginalSnd f y := by
  rw [condDensity_mul_marginalFst hx]
  rfl

/-- CDIS P.III, id 55 (2): when `(X, Y)` has a density, `X` and `Y` are independent iff the
conditional density of `Y` given `X = x` does not depend on `x`: `f_{Y|X=x} ℓ = f_Y ℓ` for
`P_X`-almost every `x`. -/
theorem indepFun_iff_ae_withDensity_condDensity_eq (hf : Measurable f) (hX : Measurable X)
    (hY : Measurable Y) (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (volume.withDensity f) P) :
    IndepFun X Y P ↔ ∀ᵐ x ∂(P.map X),
      volume.withDensity (condDensity f x) = volume.withDensity (marginalSnd f) := by
  have hYlaw := (hasLaw_snd_of_hasLaw_prod hf hXY).map_eq
  have hcd := condDistrib_ae_eq_withDensity_condDensity hf hX hY hXY
  rw [indepFun_iff_condDistrib_ae_eq_const hX hY]
  constructor
  · intro h
    filter_upwards [h, hcd] with x h1 h2
    rw [← h2, h1, Kernel.const_apply, hYlaw]
  · intro h
    filter_upwards [h, hcd] with x h1 h2
    rw [h2, h1, Kernel.const_apply, hYlaw]

end ConditionalDensity

end CDIS
