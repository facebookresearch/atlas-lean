/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Code.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Exponential

/-!
# CDIS Probabilités V: the inversion method

* id 93: the generalized inverse `F⁻(u) = inf {x | F(x) ≥ u}` of a distribution function.
* id 101: its properties (monotone, `F⁻ ∘ F ≤ id`, `F ∘ F⁻ ≥ id` with equality on the range,
  and the equivalence `F(x) ≥ u ↔ x ≥ F⁻(u)`).
* id 94: the inversion method: if `U` is uniform on `]0,1[` then `F⁻(U)` has distribution
  function `F`.
* id 92: the bijective case: `F⁻¹(U) ~ X` and `F(X) ~ U`.

The course defines `F⁻` on `]0,1[` only. In Lean `genInv F` is total. For `u ≤ 0` the infimum is
over `ℝ` and for `u > 1` over `∅`, and both return the junk value `0` (`genInv_of_nonpos`,
`genInv_of_one_lt`). At `u = 1` the set `{x | F(x) ≥ 1}` can be nonempty and bounded below, and
then `genInv F 1` is its genuine infimum: for the Dirac mass at `5` it is `5`
(`genInv_cdf_dirac_one`). Every statement below carries the hypothesis `u ∈ ]0,1[` where the
course has it implicitly, and the value at `1` does not matter since `U ∈ ]0,1[` almost surely.

Prior art: the same object is `Measure.quantile` in TauCeti (`TauCeti/Probability/Quantile.lean`)
and `lowerQuantile` in the open Mathlib PR #42461. Neither is in Mathlib yet.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace CDIS

/-- CDIS P.V, id 93: generalized inverse of a distribution function. -/
noncomputable def genInv (F : ℝ → ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ F x}

section Generalized

variable {F : StieltjesFunction ℝ} {u x : ℝ}

lemma nonempty_setOf_le (hF : Tendsto F atTop (𝓝 1)) (hu : u < 1) : {x | u ≤ F x}.Nonempty :=
  ((hF.eventually (eventually_gt_nhds hu)).exists).imp fun _ h ↦ h.le

lemma bddBelow_setOf_le (hF : Tendsto F atBot (𝓝 0)) (hu : 0 < u) : BddBelow {x | u ≤ F x} := by
  obtain ⟨a, ha⟩ := eventually_atBot.1 (hF.eventually (eventually_lt_nhds hu))
  refine ⟨a, fun x hx ↦ le_of_not_gt fun hxa ↦ ?_⟩
  exact (ha x hxa.le).not_ge hx

/-- CDIS P.V, id 101, item 3: `F(F⁻(u)) ≥ u`, for every `u < 1` and so on `]0,1[`, since
`F⁻(u)` belongs to `{x | u ≤ F x}`: this is where right continuity is used. -/
theorem le_apply_genInv (hF1 : Tendsto F atTop (𝓝 1)) (hu1 : u < 1) : u ≤ F (genInv F u) := by
  have hne := nonempty_setOf_le hF1 hu1
  have h : Tendsto F (𝓝[>] (genInv F u)) (𝓝 (F (genInv F u))) :=
    (F.right_continuous _).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  refine ge_of_tendsto h (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
  obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
  exact hz.trans (F.mono hzy.le)

/-- CDIS P.V, id 101, item 4 (first half): `F(x) ≥ u ↔ x ≥ F⁻(u)` for `u ∈ ]0,1[`. -/
theorem genInv_le_iff (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1))
    (hu : u ∈ Ioo (0 : ℝ) 1) : genInv F u ≤ x ↔ u ≤ F x :=
  ⟨fun h ↦ (le_apply_genInv hF1 hu.2).trans (F.mono h),
    fun h ↦ csInf_le (bddBelow_setOf_le hF0 hu.1) h⟩

/-- CDIS P.V, id 101, item 4 (second half), in the stronger strict form. -/
theorem lt_genInv_of_apply_lt (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1))
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : F x < u) : x < genInv F u :=
  lt_of_not_ge fun h ↦ hx.not_ge ((genInv_le_iff hF0 hF1 hu).1 h)

/-- CDIS P.V, id 101, item 4 (second half), as stated in the course. -/
theorem le_genInv_of_apply_lt (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1))
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : F x < u) : x ≤ genInv F u :=
  (lt_genInv_of_apply_lt hF0 hF1 hu hx).le

/-- CDIS P.V, id 101, item 1: `F⁻` is nondecreasing on `]0,1[`. -/
theorem monotoneOn_genInv (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1)) :
    MonotoneOn (genInv F) (Ioo 0 1) := fun _ hu _ hv huv ↦
  (genInv_le_iff hF0 hF1 hu).2 (huv.trans (le_apply_genInv hF1 hv.2))

/-- CDIS P.V, id 101, item 2: `F⁻(F(x)) ≤ x`. The course writes it for all `x`, but `F⁻` is only
defined on `]0,1[`, so `F(x) > 0` is required (with `F(x) = 0` the infimum is over `ℝ`). -/
theorem genInv_apply_le (hF0 : Tendsto F atBot (𝓝 0)) (hx : 0 < F x) : genInv F (F x) ≤ x :=
  csInf_le (bddBelow_setOf_le hF0 hx) (le_refl (F x) : F x ≤ F x)

/-- CDIS P.V, id 101, item 3 (equality case): `F(F⁻(u)) = u` when `u ∈ F(ℝ)`. -/
theorem apply_genInv_of_mem_range (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1))
    (hu : u ∈ Ioo (0 : ℝ) 1) (hrange : u ∈ range F) : F (genInv F u) = u := by
  obtain ⟨y, rfl⟩ := hrange
  exact le_antisymm (F.mono ((genInv_le_iff hF0 hF1 hu).2 le_rfl)) (le_apply_genInv hF1 hu.2)

lemma genInv_of_nonpos (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x) (hu : u ≤ 0) : genInv F u = 0 := by
  rw [genInv, show {x | u ≤ F x} = univ from eq_univ_of_forall fun x ↦ hu.trans (hF x),
    Real.sInf_univ]

lemma genInv_of_one_lt (F : ℝ → ℝ) (hF : ∀ x, F x ≤ 1) (hu : 1 < u) : genInv F u = 0 := by
  rw [genInv, show {x | u ≤ F x} = ∅ from
    eq_empty_of_forall_notMem fun x hx ↦ (hx.trans (hF x)).not_gt hu, Real.sInf_empty]

/-- At `u = 1` the value of `genInv` is not the junk `0` in general: for the Dirac mass at `5`,
`F⁻(1) = 5`. -/
theorem genInv_cdf_dirac_one : genInv (cdf (Measure.dirac (5 : ℝ))) 1 = 5 := by
  have hset : {x | (1 : ℝ) ≤ cdf (Measure.dirac (5 : ℝ)) x} = Ici 5 := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici, cdf_eq_real]
    by_cases h : (5 : ℝ) ≤ x <;> simp [h, measureReal_def]
  rw [genInv, hset, csInf_Ici]

/-- The generalized inverse of a distribution function is measurable. -/
theorem measurable_genInv (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1))
    (hnn : ∀ x, 0 ≤ F x) (hle : ∀ x, F x ≤ 1) : Measurable (genInv F) := by
  refine measurable_of_Iic fun x ↦ ?_
  -- Off `]0,1[` the function is `0` except possibly at `1`, so the sublevel set is, up to the
  -- point `1`, either `(]0,1[)ᶜ` or empty there.
  have hsplit : genInv F ⁻¹' Iic x =
      (Ioo 0 1 ∩ Iic (F x)) ∪ ((Iic 0 ∪ Ioi 1) ∩ {_u | (0 : ℝ) ≤ x}) ∪
        ({1} ∩ genInv F ⁻¹' Iic x) := by
    ext v
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_Ioo, mem_Ioi,
      mem_ofPred_eq, mem_singleton_iff]
    rcases lt_trichotomy v 1 with hv1 | rfl | hv1
    · rcases le_or_gt v 0 with hv0 | hv0
      · simp [genInv_of_nonpos _ hnn hv0, hv0, not_lt.2 hv0, hv1.ne]
      · simp [genInv_le_iff hF0 hF1 ⟨hv0, hv1⟩, hv0, hv1, hv1.not_gt, hv0.not_ge]
    · simp
    · simp [genInv_of_one_lt _ hle hv1, hv1, hv1.ne', not_lt.2 hv1.le]
  rw [hsplit]
  refine ((measurableSet_Ioo.inter measurableSet_Iic).union
    ((measurableSet_Iic.union measurableSet_Ioi).inter ?_)).union
    (subsingleton_singleton.anti inter_subset_left).measurableSet
  by_cases hx : (0 : ℝ) ≤ x <;> simp [hx]

end Generalized

section Inversion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma measurable_genInv_cdf (μ : Measure ℝ) : Measurable (genInv (cdf μ)) :=
  measurable_genInv (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) (cdf_nonneg μ) (cdf_le_one μ)

/-- Lebesgue measure of `]0,1[ ∩ ]-∞, c]` for `c ∈ [0,1]`. -/
lemma volume_Ioo_inter_Iic {c : ℝ} (h1 : c ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  refine le_antisymm ?_ ?_
  · calc volume (Ioo (0 : ℝ) 1 ∩ Iic c) ≤ volume (Icc 0 c) :=
          measure_mono fun v hv ↦ ⟨hv.1.1.le, hv.2⟩
      _ = ENNReal.ofReal c := by simp [Real.volume_Icc]
  · calc ENNReal.ofReal c = volume (Ioo 0 c) := by simp [Real.volume_Ioo]
      _ ≤ volume (Ioo (0 : ℝ) 1 ∩ Iic c) :=
          measure_mono fun v hv ↦ ⟨⟨hv.1, hv.2.trans_le h1⟩, hv.2.le⟩

/-- CDIS P.V, id 94 (inversion method), measure form: `F⁻` pushes the uniform law on `]0,1[`
forward to the law whose distribution function is `F`. -/
theorem map_genInv_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (genInv (cdf μ)) = μ := by
  have hm := measurable_genInv_cdf μ
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map (genInv (cdf μ))) :=
    isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply (hm measurableSet_Iic),
    ← ofReal_cdf μ x]
  have hset : genInv (cdf μ) ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext v
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    exact ⟨fun h ↦ ⟨h.2, (genInv_le_iff (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) h.2).1 h.1⟩,
      fun h ↦ ⟨(genInv_le_iff (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) h.1).2 h.2, h.1⟩⟩
  rw [hset, volume_Ioo_inter_Iic (cdf_le_one μ x)]

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 94 (inversion method): if `U` is uniform on `]0,1[`, then `F⁻(U)` has law `μ`,
where `F` is the distribution function of `μ`. -/
theorem hasLaw_genInv_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) :
    HasLaw (fun ω ↦ genInv (cdf μ) (U ω)) μ P where
  aemeasurable := (measurable_genInv_cdf μ).comp_aemeasurable hU.aemeasurable
  map_eq := by
    rw [show (fun ω ↦ genInv (cdf μ) (U ω)) = genInv (cdf μ) ∘ U from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_genInv_cdf μ).aemeasurable
        hU.aemeasurable, hU.map_eq, map_genInv_cdf]

/-- CDIS P.V, id 94, in the course's form: `F_X⁻(U)` has the same law as `X`. -/
theorem hasLaw_genInv_cdf_map {X U : Ω → ℝ} (hX : AEMeasurable X P)
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) :
    HasLaw (fun ω ↦ genInv (cdf (P.map X)) (U ω)) (P.map X) P :=
  have : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map hX
  hasLaw_genInv_cdf (P.map X) hU

end Inversion

section Bijective

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure ℝ} [IsProbabilityMeasure μ] {I : Set ℝ} {G : ℝ → ℝ}

/-- Hypotheses of id 92: `F` maps the open set `I` bijectively onto `]0,1[`, with inverse `G`.
The course takes `I = ]a,b[` with `-∞ ≤ a < b ≤ +∞`; every such interval is open, so this covers
the bounded case as well as `]0,+∞[` (exponential law) and `ℝ` (Cauchy, Laplace, logistic). -/
structure IsCdfBijection (F : ℝ → ℝ) (I : Set ℝ) (G : ℝ → ℝ) : Prop where
  isOpen : IsOpen I
  mapsTo : MapsTo F I (Ioo 0 1)
  mapsTo_inv : MapsTo G (Ioo 0 1) I
  left_inv : ∀ x ∈ I, G (F x) = x
  right_inv : ∀ u ∈ Ioo (0 : ℝ) 1, F (G u) = u

/-- An open set contains an interval `]x - ε, x + ε[` around each of its points. -/
lemma exists_Ioo_subset_of_isOpen (hI : IsOpen I) {x : ℝ} (hx : x ∈ I) :
    ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ I := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI x hx
  exact ⟨ε, hε, Real.ball_eq_Ioo x ε ▸ hball⟩

omit [IsProbabilityMeasure μ] in
/-- Under the hypotheses of id 92, `G` agrees with `F⁻` on `]0,1[`. -/
lemma IsCdfBijection.genInv_eq (h : IsCdfBijection (cdf μ) I G) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : genInv (cdf μ) u = G u := by
  have h0 := tendsto_cdf_atBot μ
  have h1 := tendsto_cdf_atTop μ
  refine le_antisymm ((genInv_le_iff h0 h1 hu).2 (h.right_inv u hu).ge) (le_of_not_gt fun hlt ↦ ?_)
  obtain ⟨ε, hε, hsub⟩ := exists_Ioo_subset_of_isOpen h.isOpen (h.mapsTo_inv hu)
  -- `z` sits strictly between `max(F⁻ u, G u - ε)` and `G u`, yet `F z = u = F (G u)`.
  set z := max (genInv (cdf μ) u) (G u - ε / 2) with hz
  have hzG : z < G u := max_lt hlt (by linarith)
  have hzI : z ∈ I := hsub ⟨by linarith [le_max_right (genInv (cdf μ) u) (G u - ε / 2)],
    by linarith⟩
  have hFz : cdf μ z = u := le_antisymm
    ((monotone_cdf μ hzG.le).trans (h.right_inv u hu).le)
    ((le_apply_genInv h1 hu.2).trans (monotone_cdf μ (le_max_left _ _)))
  have := h.left_inv z hzI
  rw [hFz] at this
  exact hzG.ne this.symm

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 92, first claim: `F⁻¹(U)` has the same law as `X`. -/
theorem IsCdfBijection.hasLaw_comp {U : Ω → ℝ} (h : IsCdfBijection (cdf μ) I G)
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) : HasLaw (fun ω ↦ G (U ω)) μ P := by
  refine (hasLaw_genInv_cdf μ hU).congr ?_
  have hmem : ∀ᵐ ω ∂P, U ω ∈ Ioo (0 : ℝ) 1 := by
    have := hU.map_eq ▸ (ae_restrict_mem (μ := volume) measurableSet_Ioo)
    exact ae_of_ae_map hU.aemeasurable this
  filter_upwards [hmem] with ω hω
  exact (h.genInv_eq hω).symm

/-- CDIS P.V, id 92, second claim: `F(X)` is uniform on `]0,1[`, in measure form. -/
theorem IsCdfBijection.map_cdf (h : IsCdfBijection (cdf μ) I G) :
    μ.map (cdf μ) = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hm : Measurable (cdf μ) := (monotone_cdf μ).measurable
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have : IsProbabilityMeasure (μ.map (cdf μ)) := isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun c ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    inter_comm]
  rcases le_or_gt c 0 with hc0 | hc0
  · -- both sides vanish: `{F ≤ c}` lies below every `G v`, and `μ(]-∞, G v]) = v` for `v ∈ ]0,1[`
    have hsub : ∀ v ∈ Ioo (0 : ℝ) 1, cdf μ ⁻¹' Iic c ⊆ Iic (G v) := fun v hv x hx ↦
      le_of_not_gt fun hlt ↦ (h.mapsTo (h.mapsTo_inv hv)).1.not_ge
        ((monotone_cdf μ hlt.le).trans ((mem_Iic.1 hx).trans hc0))
    have hS : μ.real (cdf μ ⁻¹' Iic c) ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      set v := min (ε / 2) (1 / 2) with hv
      have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith [min_le_right (ε / 2) (1 / 2)]⟩
      calc μ.real (cdf μ ⁻¹' Iic c) ≤ μ.real (Iic (G v)) := measureReal_mono (hsub v hv01)
        _ = v := by
          rw [measureReal_def, ← ofReal_cdf, h.right_inv v hv01, ENNReal.toReal_ofReal hv01.1.le]
        _ ≤ 0 + ε := by linarith [min_le_left (ε / 2) (1 / 2)]
    have hμ : μ (cdf μ ⁻¹' Iic c) = 0 := (measureReal_eq_zero_iff (by finiteness)).1
      (le_antisymm hS measureReal_nonneg)
    have hvol : volume (Ioo (0 : ℝ) 1 ∩ Iic c) = 0 :=
      measure_mono_null (fun v hv ↦ (hv.1.1.not_ge (hv.2.trans hc0)).elim) measure_empty
    rw [hvol, hμ]
  rcases lt_or_ge c 1 with hc1 | hc1
  · -- `{F ≤ c} = ]-∞, G c]`
    have hGc := h.mapsTo_inv ⟨hc0, hc1⟩
    have hFG := h.right_inv c ⟨hc0, hc1⟩
    obtain ⟨ε, hε, hIoo⟩ := exists_Ioo_subset_of_isOpen h.isOpen hGc
    have hset : cdf μ ⁻¹' Iic c = Iic (G c) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      refine ⟨fun hx ↦ le_of_not_gt fun hlt ↦ ?_, fun hx ↦ hFG ▸ monotone_cdf μ hx⟩
      -- some `y ∈ ]G c, x]` close to `G c` lies in `I` and has `F y = c`, against injectivity
      set y := min ((G c + x) / 2) (G c + ε / 2)
      have hyG : G c < y := by simp only [y, lt_min_iff]; constructor <;> linarith
      have hy : y ∈ I := hIoo ⟨by linarith, by
        have : y ≤ G c + ε / 2 := min_le_right _ _
        linarith⟩
      have hyx : y ≤ x := by simp only [y, min_le_iff]; left; linarith
      have hFy : cdf μ y = c := le_antisymm ((monotone_cdf μ hyx).trans hx)
        (hFG ▸ monotone_cdf μ hyG.le)
      have := h.left_inv y hy
      rw [hFy] at this
      exact hyG.ne this
    rw [hset, ← ofReal_cdf, hFG, volume_Ioo_inter_Iic hc1.le]
  · -- `{F ≤ c} = ℝ`
    have hset : cdf μ ⁻¹' Iic c = univ :=
      eq_univ_of_forall fun x ↦ (cdf_le_one μ x).trans hc1
    have hIoo : Ioo (0 : ℝ) 1 ∩ Iic c = Ioo 0 1 := inter_eq_left.2 fun v hv ↦ hv.2.le.trans hc1
    rw [hset, hIoo, measure_univ]
    simp [Real.volume_Ioo]

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 92, second claim: `F_X(X)` is uniform on `]0,1[`. -/
theorem IsCdfBijection.hasLaw_cdf_comp {X : Ω → ℝ} (hX : HasLaw X μ P)
    (h : IsCdfBijection (cdf μ) I G) :
    HasLaw (fun ω ↦ cdf μ (X ω)) (volume.restrict (Ioo (0 : ℝ) 1)) P where
  aemeasurable := (monotone_cdf μ).measurable.comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [show (fun ω ↦ cdf μ (X ω)) = cdf μ ∘ X from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (monotone_cdf μ).measurable.aemeasurable
        hX.aemeasurable, hX.map_eq, h.map_cdf]

/-- Id 92 applies to the exponential law of rate `r` on `I = ]0,+∞[`, where
`F(x) = 1 - e^{-r x}` and `F⁻¹(u) = -log(1 - u) / r`. -/
theorem isCdfBijection_expMeasure {r : ℝ} (hr : 0 < r) :
    IsCdfBijection (cdf (expMeasure r)) (Ioi 0) (fun u ↦ -Real.log (1 - u) / r) where
  isOpen := isOpen_Ioi
  mapsTo x hx := by
    have hx : 0 < x := hx
    have hexp : Real.exp (-(r * x)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    rw [cdf_expMeasure_eq hr, ite_eq_left_of_eq_true _ _ (eq_true hx.le)]
    exact ⟨by linarith, by linarith [Real.exp_pos (-(r * x))]⟩
  mapsTo_inv u hu := by
    have hlog : Real.log (1 - u) < 0 := Real.log_neg (by linarith [hu.2]) (by linarith [hu.1])
    exact div_pos (neg_pos.2 hlog) hr
  left_inv x hx := by
    have hx : 0 < x := hx
    rw [cdf_expMeasure_eq hr, ite_eq_left_of_eq_true _ _ (eq_true hx.le), sub_sub_cancel,
      Real.log_exp]
    field_simp
  right_inv u hu := by
    have hlog : Real.log (1 - u) < 0 := Real.log_neg (by linarith [hu.2]) (by linarith [hu.1])
    have hG : 0 ≤ -Real.log (1 - u) / r := (div_pos (neg_pos.2 hlog) hr).le
    rw [cdf_expMeasure_eq hr, ite_eq_left_of_eq_true _ _ (eq_true hG), mul_div_cancel₀ _ hr.ne',
      neg_neg, Real.exp_log (by linarith [hu.2])]
    ring

end Bijective

end CDIS
