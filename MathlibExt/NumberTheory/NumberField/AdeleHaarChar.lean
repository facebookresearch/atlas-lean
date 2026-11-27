/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean`
and
`P2M/Sol/S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import MathlibExt.NumberTheory.NumberField.AdelicBox

/-!
# The Haar character of ideles with trivial finite part

For a number field `F`, an idele `a` whose finite component is `1` scales an additive Haar
measure on the adele ring by `∏_w ‖a_w‖ ^ mult w`, the product running over the infinite
places. We also record the countability and second-countability facts for the adele ring that
the measure-theoretic arguments need.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal

namespace NumberField.AdelicCountability

scoped instance instCountableNumberField (K : Type*) [Field K] [NumberField K] :
    Countable K := by
  obtain ⟨_, s, h⟩ := Module.Finite.exists_fin (R := ℚ) (M := K)
  have hspan : Countable (Submodule.span ℚ (Set.range s)) := inferInstance
  rw [h] at hspan
  exact (Submodule.topEquiv.symm.toEquiv.countable_iff).mpr hspan

scoped instance instCountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hsurj.countable

scoped instance instCountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Countable R] : Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hinj.countable

scoped instance instCountableValueGroup₀ {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] [Countable Γ₀] (v : R →*₀ Γ₀) :
    Countable (MonoidWithZeroHom.ValueGroup₀ v) :=
  MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.countable

scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

scoped instance instCountableWithZero {α : Type*} [Countable α] : Countable (WithZero α) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
  refine ⟨⟨fun x => if h : x = 0 then 0 else f (WithZero.unzero h) + 1, fun a b hab => ?_⟩⟩
  dsimp only [] at hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [dite_eq_left ha, dite_eq_right hb] at hab
    exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_left hb] at hab
    exact absurd hab (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_right hb] at hab
    rw [← WithZero.coe_unzero ha, ← WithZero.coe_unzero hb, hf (Nat.add_right_cancel hab)]

private theorem isCountablyGenerated_uniformity_of_valued (R : Type*) (Γ₀ : Type*) [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Countable Γ₀] [vR : Valued R Γ₀] :
    (uniformity R).IsCountablyGenerated :=
  (Valued.hasBasis_uniformity R Γ₀).isCountablyGenerated

scoped instance instSecondCountableAdicCompletion (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable K] (v : HeightOneSpectrum R) :
    SecondCountableTopology (v.adicCompletion K) := by
  have hcg : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    isCountablyGenerated_uniformity_of_valued _ (WithZero (Multiplicative ℤ))
  have hsep : SeparableSpace (v.adicCompletion K) :=
    ⟨_, Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := K)
        (v := v)⟩
  exact UniformSpace.secondCountable_of_separable _

open RestrictedProduct Topology in
private theorem secondCountableTopology_restrictedProduct {ι : Type*} [Countable ι]
    {R : ι → Type*} {B : ∀ i, Set (R i)}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    (hBo : ∀ i, IsOpen (B i)) :
    SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.cofinite]) := by
  have hprin : ∀ t : Finset ι, Filter.cofinite ≤ Filter.principal ((↑t : Set ι)ᶜ) := fun t =>
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by simp))
  have hpiece : ∀ t : Finset ι,
      SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.principal ((↑t : Set ι)ᶜ)]) := fun t =>
    (isEmbedding_coe_of_principal).secondCountableTopology
  set U : Finset ι → Set (Πʳ i, [R i, B i]_[Filter.cofinite]) :=
    fun t => Set.range (inclusion R B (hprin t)) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun t =>
    (isOpenEmbedding_inclusion_principal hBo (hprin t)).isOpen_range
  have hUsc : ∀ t, SecondCountableTopology (U t) := by
    intro t
    have := hpiece t
    exact (((isOpenEmbedding_inclusion_principal hBo (hprin
        t)).isEmbedding.toHomeomorph).symm).isEmbedding.secondCountableTopology
  have hcover : ⋃ t : Finset ι, U t = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hfin : {i | x.1 i ∉ B i}.Finite := Filter.eventually_cofinite.mp x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    rw [Filter.eventually_principal]
    intro i hi
    by_contra hmem
    exact hi (by simpa using hfin.mem_toFinset.mpr hmem)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUopen hcover

open IsDedekindDomain in
open scoped RestrictedProduct in
scoped instance instSecondCountableFiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable R] [Countable K] :
    SecondCountableTopology (FiniteAdeleRing R K) := by
  have : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    secondCountableTopology_restrictedProduct fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

scoped instance instSecondCountableCompletion {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) : SecondCountableTopology v.Completion := by
  have : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
  have : SeparableSpace v.Completion :=
    ⟨_, Set.countable_range _, AbsoluteValue.Completion.denseRange_coe (v := v.1)⟩
  have : (uniformity v.Completion).IsCountablyGenerated :=
    EMetric.instIsCountablyGeneratedUniformity
  exact UniformSpace.secondCountable_of_separable _

scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

scoped instance instSecondCountableAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K] [Countable R] :
    SecondCountableTopology (AdeleRing R K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing R K)

scoped instance instCountableRingOfIntegers (K : Type*) [Field K] [NumberField K] :
    Countable (NumberField.RingOfIntegers K) :=
  Subtype.countable

end NumberField.AdelicCountability
open scoped NumberField.AdelicCountability

namespace NumberField.AdeleHaarChar

private theorem map_mul_left_volume_real {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun x => c * x) = ‖c‖ₑ⁻¹ • volume := by
  have h := Real.map_volume_mul_left hc
  rw [show ((c * ·) : ℝ → ℝ) = fun x => c * x from rfl] at h
  rw [h, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc), Real.eNorm_eq_ofReal_abs]

private theorem det_restrictScalars_mulLeft_complex (c : ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) = normSq c := by
  rw [← LinearMap.det_toMatrix basisOneI]
  have hM : (LinearMap.toMatrix basisOneI basisOneI ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))
      = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hM, Matrix.det_fin_two_of]
  simp [normSq_apply]

private theorem map_mul_left_volume_complex {c : ℂ} (hc : c ≠ 0) :
    (volume : Measure ℂ).map (fun x => c * x) = (‖c‖ₑ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_mulLeft_complex]
    exact (normSq_pos.mpr hc).ne'
  have hfun : (fun x => c * x) = ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by
    ext x; simp [LinearMap.mulLeft_apply]
  have habs : |LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ)| = ‖c‖ ^ 2 := by
    rw [det_restrictScalars_mulLeft_complex, abs_of_nonneg (normSq_nonneg c), normSq_eq_norm_sq]
  calc (volume : Measure ℂ).map (fun x => c * x)
      = volume.map ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by rw [← hfun]
    _ = ENNReal.ofReal |(LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet
    _ = (‖c‖ₑ ^ 2)⁻¹ • volume := by
        rw [abs_inv, habs, ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.mpr hc) 2),
          ENNReal.ofReal_pow (norm_nonneg c), ofReal_norm]

private theorem volume_image_mul_left_real {c : ℝ} (hc : c ≠ 0) {S : Set ℝ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_real (inv_ne_zero hc)]
  simp [_root_.smul_apply, smul_eq_mul, eNorm_inv, hc]

private theorem volume_image_mul_left_complex {c : ℂ} (hc : c ≠ 0) {S : Set ℂ}
    (hS : MeasurableSet S) : volume ((fun x => c * x) '' S) = ‖c‖ₑ ^ 2 * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_complex (inv_ne_zero hc)]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [eNorm_inv hc, ENNReal.inv_pow, inv_inv]

variable (F : Type*) [Field F] [NumberField F]

/-- **Borel σ-algebra at an infinite place.** The Borel σ-algebra on the completion at an
infinite place. -/
@[reducible] def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

/-- **Lebesgue measure at a real place.** Lebesgue measure on `ℝ`, transported to the completion
at a real place. -/
def placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) : Measure (w.Completion) :=
  (volume : Measure ℝ).map (Completion.ringEquivRealOfIsReal hw).symm

/-- **Lebesgue measure at a complex place.** Lebesgue measure on `ℂ`, transported to the
completion at a complex place. -/
def placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) : Measure (w.Completion) :=
  (volume : Measure ℂ).map (Completion.ringEquivComplexOfIsComplex hw).symm

variable (F) in
open Classical in
/-- **Haar measure at an infinite place.** The standard additive Haar measure on the completion
at an infinite place: transported Lebesgue measure on `ℝ` or on `ℂ`. -/
def placeMeasure (w : InfinitePlace F) : Measure (w.Completion) :=
  if hw : w.IsReal then placeMeasureReal hw
  else placeMeasureComplex (not_isReal_iff_isComplex.mp hw)

scoped instance isAddHaarMeasure_placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) :
    (placeMeasureReal hw).IsAddHaarMeasure := by
  unfold placeMeasureReal
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous
    (Completion.isometryEquivRealOfIsReal hw).continuous

scoped instance isAddHaarMeasure_placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    (placeMeasureComplex hw).IsAddHaarMeasure := by
  unfold placeMeasureComplex
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivComplexOfIsComplex hw).symm : ℂ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
    (Completion.isometryEquivComplexOfIsComplex hw).continuous

omit [NumberField F] in
private theorem placeMeasureReal_image_mul {w : InfinitePlace F} (hw : w.IsReal)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureReal hw ((fun x => a * x) '' S) = ‖a‖ₑ * placeMeasureReal hw S := by
  set e := Completion.ringEquivRealOfIsReal hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureReal
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_real hea (hmeas_symm hS), henorm]

omit [NumberField F] in
private theorem placeMeasureComplex_image_mul {w : InfinitePlace F} (hw : w.IsComplex)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureComplex hw ((fun x => a * x) '' S) = ‖a‖ₑ ^ 2 * placeMeasureComplex hw S := by
  set e := Completion.ringEquivComplexOfIsComplex hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbedding w).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureComplex
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_complex hea (hmeas_symm hS), henorm]

omit [NumberField F] in
private theorem placeMeasure_image_mul (w : InfinitePlace F) {a : w.Completion} (ha : a ≠ 0)
    {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasure F w ((fun x => a * x) '' S) = ‖a‖ₑ ^ w.mult * placeMeasure F w S := by
  unfold placeMeasure
  split
  · next hw =>
    rw [placeMeasureReal_image_mul hw ha hS,
      show w.mult = 1 from by simp [mult, hw], pow_one]
  · next hw =>
    rw [placeMeasureComplex_image_mul (not_isReal_iff_isComplex.mp hw) ha hS,
      show w.mult = 2 from by simp [mult, hw]]

scoped instance isAddHaarMeasure_placeMeasure (w : InfinitePlace F) :
    (placeMeasure F w).IsAddHaarMeasure := by
  unfold placeMeasure
  split
  · exact isAddHaarMeasure_placeMeasureReal _
  · exact isAddHaarMeasure_placeMeasureComplex _

variable (F) in
/-- **Product Haar measure over the infinite places.** The product of the standard Haar measures
on the completions at the infinite places. -/
def archMeasure : Measure ((w : InfinitePlace F) → w.Completion) :=
  Measure.pi (fun w => placeMeasure F w)

scoped instance isFiniteMeasureOnCompacts_archMeasure :
    IsFiniteMeasureOnCompacts (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isOpenPosMeasure_archMeasure : (archMeasure F).IsOpenPosMeasure := by
  unfold archMeasure; infer_instance

scoped instance sigmaFinite_archMeasure : SigmaFinite (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isAddLeftInvariant_archMeasure : (archMeasure F).IsAddLeftInvariant := by
  constructor
  intro a
  have hmeas : Measurable (fun x : (w : InfinitePlace F) → w.Completion => a + x) :=
    measurable_const.add measurable_id
  refine Eq.symm (Measure.pi_eq fun B hB => ?_)
  have hpre : (fun x : (w : InfinitePlace F) → w.Completion => a + x) ⁻¹' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w + t) ⁻¹' B w) := by
    ext x
    simp [Set.mem_pi, Pi.add_apply]
  unfold archMeasure
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact measure_preimage_add (placeMeasure F w) (a w) (B w)

scoped instance isAddHaarMeasure_archMeasure : (archMeasure F).IsAddHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

omit [NumberField F] in
private theorem image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (B : (w : InfinitePlace F) → Set (w.Completion)) :
    (fun x => a * x) '' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w * t) '' B w) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro w _
    exact ⟨y w, hy w (Set.mem_univ w), rfl⟩
  · intro hx
    choose b hb hab using fun w => hx w (Set.mem_univ w)
    refine ⟨fun w => b w, fun w _ => hb w, ?_⟩
    funext w
    exact hab w

private theorem archMeasure_image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (ha : ∀ w, a w ≠ 0) (B : (w : InfinitePlace F) → Set (w.Completion))
    (hB : ∀ w, MeasurableSet (B w)) :
    archMeasure F ((fun x => a * x) '' Set.pi Set.univ B)
      = (∏ w, ‖a w‖ₑ ^ w.mult) * archMeasure F (Set.pi Set.univ B) := by
  rw [image_mul_pi a B]
  unfold archMeasure
  rw [Measure.pi_pi, Measure.pi_pi]
  calc ∏ w, placeMeasure F w ((fun t => a w * t) '' B w)
      = ∏ w, (‖a w‖ₑ ^ w.mult * placeMeasure F w (B w)) := by
        refine Finset.prod_congr rfl fun w _ => ?_
        exact placeMeasure_image_mul w (ha w) (hB w)
    _ = (∏ w, ‖a w‖ₑ ^ w.mult) * ∏ w, placeMeasure F w (B w) := Finset.prod_mul_distrib

attribute [scoped instance] AdelicBox.properSpace_completion

omit [NumberField F] in
private theorem placeMeasure_pos_closedBall (w : InfinitePlace F) :
    0 < placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) :=
  ((Metric.isOpen_ball (x := (0 : w.Completion)) (ε := 1)).measure_pos (placeMeasure F w)
    (Metric.nonempty_ball.mpr one_pos)).trans_le
    (measure_mono Metric.ball_subset_closedBall)

omit [NumberField F] in
private theorem placeMeasure_closedBall_lt_top (w : InfinitePlace F) :
    placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) < ⊤ :=
  (isCompact_closedBall (0 : w.Completion) 1).measure_lt_top

variable (F) in
/-- **Borel σ-algebra on the infinite adeles.** The product σ-algebra on the infinite adeles,
which is their Borel σ-algebra. -/
@[reducible] def infMS : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

attribute [local instance] infMS

scoped instance infBorelSpace : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

variable (F) in
/-- The Borel σ-algebra on the finite adeles. -/
@[reducible] private def finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

attribute [local instance] finBorel

private local instance finBorelSpace : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

variable (F) in
/-- The product σ-algebra on the adeles, viewed as infinite times finite adeles. -/
@[reducible] private def adeleMS : MeasurableSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

attribute [local instance] adeleMS

private local instance adeleBorelSpaceProd : BorelSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

variable (F) in
/-- The integral finite adeles, as a compact set with nonempty interior. -/
private def zhatCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 F) F) where
  carrier := AdelicBox.integralFiniteAdeles (𝓞 F) F
  isCompact' := AdelicBox.isCompact_integralFiniteAdeles F
  interior_nonempty' := by
    rw [(AdelicBox.isOpen_integralFiniteAdeles F).interior_eq]
    exact ⟨0, fun v => zero_mem _⟩

variable (F) in
/-- The additive Haar measure on the finite adeles normalized on the integral adeles. -/
private def finMeasure : Measure (FiniteAdeleRing (𝓞 F) F) :=
  Measure.addHaarMeasure (zhatCompacts F)

private local instance isAddHaarMeasure_finMeasure : (finMeasure F).IsAddHaarMeasure := by
  unfold finMeasure; infer_instance

private local instance sigmaFinite_finMeasure : SigmaFinite (finMeasure F) := by
  unfold finMeasure; infer_instance

variable (F) in
/-- **Haar measure on the infinite adeles.** The product of the standard Haar measures on the
completions at the infinite places, as a measure on the infinite adeles. -/
def infMeasure : Measure (InfiniteAdeleRing F) := archMeasure F

scoped instance isAddHaarMeasure_infMeasure : (infMeasure F).IsAddHaarMeasure :=
  inferInstanceAs ((archMeasure F).IsAddHaarMeasure)

scoped instance sigmaFinite_infMeasure : SigmaFinite (infMeasure F) :=
  inferInstanceAs (SigmaFinite (archMeasure F))

variable (F) in
/-- The product of the infinite and finite Haar measures on the adeles. -/
private def adelicMeasure : Measure (AdeleRing (𝓞 F) F) :=
  (infMeasure F).prod (finMeasure F)

private local instance isAddHaarMeasure_adelicMeasure : (adelicMeasure F).IsAddHaarMeasure :=
  inferInstanceAs
    ((((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).IsAddHaarMeasure)

private local instance sigmaFinite_adelicMeasure : SigmaFinite (adelicMeasure F) :=
  inferInstanceAs (SigmaFinite
    (((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))

variable (F) in
/-- A compact reference set with nonempty interior: closed unit balls times integral adeles. -/
private def refSet : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
  (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
    (AdelicBox.integralFiniteAdeles (𝓞 F) F)

variable (F) in
private theorem isCompact_refSet : IsCompact (refSet F) :=
  (isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1).prod
    (AdelicBox.isCompact_integralFiniteAdeles F)

variable (F) in
private theorem interior_refSet_nonempty : (interior (refSet F)).Nonempty := by
  have hopen : IsOpen ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) :=
    (isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball).prod
      (AdelicBox.isOpen_integralFiniteAdeles F)
  have hsub : ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) ⊆ refSet F :=
    Set.prod_mono (Set.pi_mono fun w _ => Metric.ball_subset_closedBall) le_rfl
  have hmem : ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) ∈
      ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
        ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) := by
    refine Set.mem_prod.mpr ⟨fun w _ => ?_, fun v => zero_mem _⟩
    exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
  exact ⟨_, interior_maximal hsub hopen hmem⟩

variable (F) in
private theorem adelicMeasure_refSet_ne_top :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ ⊤ := by
  unfold refSet
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top
    (by
      show archMeasure F _ ≠ ⊤
      unfold archMeasure
      rw [Measure.pi_pi]
      exact (ENNReal.prod_lt_top fun w _ => placeMeasure_closedBall_lt_top w).ne)
    ((AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top).ne

private local instance regular_adelicMeasure : (adelicMeasure F).Regular :=
  Measure.regular_of_isAddLeftInvariant (μ := adelicMeasure F)
    (K := refSet F) (isCompact_refSet F) (interior_refSet_nonempty F)
    (adelicMeasure_refSet_ne_top F)

variable (F) in
private theorem finMeasure_zhat : finMeasure F (AdelicBox.integralFiniteAdeles (𝓞 F) F) = 1 :=
  Measure.addHaarMeasure_self (K₀ := zhatCompacts F)

variable (F) in
private theorem adelicMeasure_refSet_ne_zero :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ 0 := by
  unfold refSet
  rw [Measure.prod_prod]
  refine mul_ne_zero ?_ ?_
  · show archMeasure F _ ≠ 0
    unfold archMeasure
    rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun w _ => (placeMeasure_pos_closedBall w).ne'
  · rw [finMeasure_zhat]
    exact one_ne_zero

private theorem arch_component_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (a : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  rw [show ((a : AdeleRing (𝓞 F) F) * (↑a⁻¹ : AdeleRing (𝓞 F) F)).1 w
      = (a : AdeleRing (𝓞 F) F).1 w * (↑a⁻¹ : AdeleRing (𝓞 F) F).1 w from rfl, h0, zero_mul] at h
  exact zero_ne_one h

private theorem distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    (distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ)
      = ∏ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  classical
  set aArch : (w : InfinitePlace F) → w.Completion :=
    (show (w : InfinitePlace F) → w.Completion from (a : AdeleRing (𝓞 F) F).1) with haArch
  have haw : ∀ w, aArch w ≠ 0 := fun w => arch_component_ne_zero a w
  have hs₀ : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ 0 :=
    adelicMeasure_refSet_ne_zero F
  have hsfin : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ ⊤ :=
    adelicMeasure_refSet_ne_top F
  have hsplit : (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (show Set (AdeleRing (𝓞 F) F) from
          (((fun x => aArch * x) ''
            (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)) ×ˢ
            (AdelicBox.integralFiniteAdeles (𝓞 F) F))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(show InfiniteAdeleRing F from y.1), hy.1, rfl⟩, ?_⟩
      change ((a : AdeleRing (𝓞 F) F) * y).2 ∈ _
      rw [show ((a : AdeleRing (𝓞 F) F) * y).2 = (a : AdeleRing (𝓞 F) F).2 * y.2 from rfl, ha,
        one_mul]
      exact hy.2
    · rintro ⟨⟨y1, hy1, hxy1⟩, hx2⟩
      refine ⟨(show AdeleRing (𝓞 F) F from ((show InfiniteAdeleRing F from y1), x.2)),
        ⟨hy1, hx2⟩, Prod.ext ?_ ?_⟩
      · change (show InfiniteAdeleRing F from aArch * y1) = x.1
        exact hxy1
      · change (a : AdeleRing (𝓞 F) F).2 * x.2 = x.2
        rw [ha, one_mul]
  have harch : archMeasure F ((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))
      = (∏ w, ‖aArch w‖ₑ ^ w.mult) * archMeasure F
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) :=
    archMeasure_image_mul_pi aArch haw
      (fun w => Metric.closedBall (0 : w.Completion) 1) (fun w => measurableSet_closedBall)
  have hcompute : (archMeasure F).prod (finMeasure F)
      ((((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)) ×ˢ
        (AdelicBox.integralFiniteAdeles (𝓞 F) F)))
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞)
        * (archMeasure F).prod (finMeasure F) (refSet F) := by
    unfold refSet
    rw [Measure.prod_prod, Measure.prod_prod, harch, mul_assoc]
    congr 1
    rw [ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, eNorm_eq_nnNorm]
  have hμgs : adelicMeasure F (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞)
        * adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) := by
    rw [hsplit]
    exact hcompute
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicMeasure F)
    (s := (show Set (AdeleRing (𝓞 F) F) from refSet F)) (g := a) hs₀ hsfin hμgs
  rw [key]
  push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnNorm]
  rfl

end NumberField.AdeleHaarChar

namespace NumberField.AdeleRing

/-- **Haar modulus of an idele with trivial finite part.** Let `F` be a number field and `a` an
idele of `F` whose finite component is `1`. Multiplication by `a` scales every additive Haar
measure on the adele ring by `∏_w ‖a_w‖ ^ mult w`, the product over the infinite places `w` of
`F`; that is, the distributive Haar character of the adele ring takes this value at `a`. -/
theorem distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (F : Type*) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (ha : (a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 = 1) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = ∏ w : NumberField.InfinitePlace F,
          ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult :=
  NumberField.AdeleHaarChar.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one a ha

end NumberField.AdeleRing
