/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw

/-!
# CDIS Probabilités V: the inversion method

* id 93: the generalized inverse `F⁻(u) = inf {x | F(x) ≥ u}` of a distribution function.
* id 101: its properties (monotone, `F⁻ ∘ F ≤ id`, `F ∘ F⁻ ≥ id` with equality on the range,
  and the equivalence `F(x) ≥ u ↔ x ≥ F⁻(u)`).
* id 94: the inversion method: if `U` is uniform on `]0,1[` then `F⁻(U)` has distribution
  function `F`.
* id 92: the bijective case: `F⁻¹(U) ~ X` and `F(X) ~ U`.

The course defines `F⁻` on `]0,1[` only. In Lean `genInv F` is total; outside `]0,1[` the infimum
is taken over `ℝ` or over `∅` and returns the junk value `0`. Every statement below carries the
hypothesis `u ∈ ]0,1[` where the course has it implicitly.

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

/-- `F⁻(u)` belongs to `{x | u ≤ F x}`: this is where right continuity is used. -/
lemma le_apply_genInv (hF1 : Tendsto F atTop (𝓝 1)) (hu1 : u < 1) : u ≤ F (genInv F u) := by
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

/-- CDIS P.V, id 101, item 3: `F(F⁻(u)) ≥ u` for `u ∈ ]0,1[`. -/
theorem le_apply_genInv' (hF1 : Tendsto F atTop (𝓝 1)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ≤ F (genInv F u) :=
  le_apply_genInv hF1 hu.2

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
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 ‹_›
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
  have : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX).2 ‹_›
  hasLaw_genInv_cdf (P.map X) hU

end Inversion

section Bijective

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ} {G : ℝ → ℝ}

/-- Hypotheses of id 92: `F` maps `]a,b[` bijectively onto `]0,1[`, with inverse `G`. -/
structure IsCdfBijection (F : ℝ → ℝ) (a b : ℝ) (G : ℝ → ℝ) : Prop where
  lt : a < b
  mapsTo : MapsTo F (Ioo a b) (Ioo 0 1)
  mapsTo_inv : MapsTo G (Ioo 0 1) (Ioo a b)
  left_inv : ∀ x ∈ Ioo a b, G (F x) = x
  right_inv : ∀ u ∈ Ioo (0 : ℝ) 1, F (G u) = u

omit [IsProbabilityMeasure μ] in
/-- Under the hypotheses of id 92, `G` agrees with `F⁻` on `]0,1[`. -/
lemma IsCdfBijection.genInv_eq (h : IsCdfBijection (cdf μ) a b G) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : genInv (cdf μ) u = G u := by
  have h0 := tendsto_cdf_atBot μ
  have h1 := tendsto_cdf_atTop μ
  have hGu := h.mapsTo_inv hu
  refine le_antisymm ((genInv_le_iff h0 h1 hu).2 (h.right_inv u hu).ge) (le_of_not_gt fun hlt ↦ ?_)
  -- `z` sits strictly between `max(F⁻ u, a)` and `G u`, yet `F z = u = F (G u)`.
  set z := max (genInv (cdf μ) u) ((a + G u) / 2) with hz
  have hza : a < z := lt_max_of_lt_right (by linarith [hGu.1])
  have hzG : z < G u := max_lt hlt (by linarith [hGu.1])
  have hzab : z ∈ Ioo a b := ⟨hza, hzG.trans hGu.2⟩
  have hFz : cdf μ z = u := le_antisymm
    ((monotone_cdf μ hzG.le).trans (h.right_inv u hu).le)
    ((le_apply_genInv h1 hu.2).trans (monotone_cdf μ (le_max_left _ _)))
  have := h.left_inv z hzab
  rw [hFz] at this
  exact hzG.ne this.symm

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 92, first claim: `F⁻¹(U)` has the same law as `X`. -/
theorem IsCdfBijection.hasLaw_comp {U : Ω → ℝ} (h : IsCdfBijection (cdf μ) a b G)
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) : HasLaw (fun ω ↦ G (U ω)) μ P := by
  refine (hasLaw_genInv_cdf μ hU).congr ?_
  have hmem : ∀ᵐ ω ∂P, U ω ∈ Ioo (0 : ℝ) 1 := by
    have := hU.map_eq ▸ (ae_restrict_mem (μ := volume) measurableSet_Ioo)
    exact ae_of_ae_map hU.aemeasurable this
  filter_upwards [hmem] with ω hω
  exact (h.genInv_eq hω).symm

/-- CDIS P.V, id 92, second claim: `F(X)` is uniform on `]0,1[`, in measure form. -/
theorem IsCdfBijection.map_cdf (h : IsCdfBijection (cdf μ) a b G) :
    μ.map (cdf μ) = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hm : Measurable (cdf μ) := (monotone_cdf μ).measurable
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have : IsProbabilityMeasure (μ.map (cdf μ)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 ‹_›
  -- `F(a) = 0`: `F` takes every value of `]0,1[` on `]a,b[`, so it is `≤ ε` just right of `a`.
  have hFa : cdf μ a ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    set v := min (ε / 2) (1 / 2) with hv
    have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith [min_le_right (ε / 2) (1 / 2)]⟩
    have hGv := h.mapsTo_inv hv01
    calc cdf μ a ≤ cdf μ (G v) := monotone_cdf μ hGv.1.le
      _ = v := h.right_inv v hv01
      _ ≤ 0 + ε := by linarith [min_le_left (ε / 2) (1 / 2)]
  refine Measure.ext_of_Iic _ _ fun c ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    inter_comm]
  rcases le_or_gt c 0 with hc0 | hc0
  · -- both sides vanish: `{F ≤ c} ⊆ ]-∞, a]` and `μ(]-∞, a]) = F(a) = 0`
    have hsub : cdf μ ⁻¹' Iic c ⊆ Iic a := fun x hx ↦ le_of_not_gt fun hxa ↦ by
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Ioo a b, y ≤ x :=
        ⟨min x ((a + b) / 2), ⟨lt_min hxa (by linarith [h.lt]), by
          linarith [min_le_right x ((a + b) / 2), h.lt]⟩, min_le_left _ _⟩
      exact (h.mapsTo hy).1.not_ge ((monotone_cdf μ hyx).trans (mem_Iic.1 hx |>.trans hc0))
    have hμa : μ (Iic a) = 0 := by
      rw [← ofReal_cdf μ a, ENNReal.ofReal_eq_zero]
      exact hFa
    have hvol : volume (Ioo (0 : ℝ) 1 ∩ Iic c) = 0 :=
      measure_mono_null (fun v hv ↦ (hv.1.1.not_ge (hv.2.trans hc0)).elim) measure_empty
    rw [hvol]
    exact measure_mono_null hsub hμa
  rcases lt_or_ge c 1 with hc1 | hc1
  · -- `{F ≤ c} = ]-∞, G c]`
    have hGc := h.mapsTo_inv ⟨hc0, hc1⟩
    have hFG := h.right_inv c ⟨hc0, hc1⟩
    have hset : cdf μ ⁻¹' Iic c = Iic (G c) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      refine ⟨fun hx ↦ le_of_not_gt fun hlt ↦ ?_, fun hx ↦ hFG ▸ monotone_cdf μ hx⟩
      -- some `y ∈ ]G c, min x b[` has `F y > c` by injectivity on `]a,b[`
      set y := min ((G c + x) / 2) ((G c + b) / 2)
      have hy : y ∈ Ioo a b := ⟨by
        have := hGc.1; have := hGc.2; simp only [y, lt_min_iff]; constructor <;> linarith,
        by have := hGc.2; simp only [y, min_lt_iff]; right; linarith⟩
      have hyG : G c < y := by simp only [y, lt_min_iff]; constructor <;> linarith [hGc.2]
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
    (h : IsCdfBijection (cdf μ) a b G) :
    HasLaw (fun ω ↦ cdf μ (X ω)) (volume.restrict (Ioo (0 : ℝ) 1)) P where
  aemeasurable := (monotone_cdf μ).measurable.comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [show (fun ω ↦ cdf μ (X ω)) = cdf μ ∘ X from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (monotone_cdf μ).measurable.aemeasurable
        hX.aemeasurable, hX.map_eq, h.map_cdf]

end Bijective

end CDIS
