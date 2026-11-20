/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


abbrev PiFiberFreeConfig (K : Set E) :=
  ∀ i : {e : E // e ∉ K}, S i

noncomputable local instance piFiberFreeFintype (K : Set E) :
    Fintype {e : E // e ∉ K} := by
  classical
  infer_instance


noncomputable def piFiberSplit (K : Set E) :
    (∀ e, S e) ≃ᵐ
      ((∀ i : {e : E // e ∈ K}, S i) × PiFiberFreeConfig (S := S) K) := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd S (fun e => e ∈ K)



noncomputable def piFiberAssemble (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) : ∀ e, S e := by
  classical
  intro e
  by_cases he : e ∈ K
  · exact x e
  · exact z ⟨e, he⟩

@[simp] theorem piFiberAssemble_apply_mem (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) {e : E} (he : e ∈ K) :
    piFiberAssemble K x z e = x e := by
  simp [piFiberAssemble, he]

@[simp] theorem piFiberAssemble_apply_notMem (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) {e : E} (he : e ∉ K) :
    piFiberAssemble K x z e = z ⟨e, he⟩ := by
  simp [piFiberAssemble, he]

theorem measurable_piFiberAssemble_right (K : Set E) (x : ∀ e, S e) :
    Measurable (piFiberAssemble K x) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [piFiberAssemble, he] using
      (measurable_const : Measurable
        (fun _ : PiFiberFreeConfig (S := S) K => x e))
  · let i : {e : E // e ∉ K} := ⟨e, he⟩
    simpa [piFiberAssemble, he, i] using
      (measurable_pi_apply i : Measurable
        (fun z : PiFiberFreeConfig (S := S) K => z i))

theorem measurable_piFiberAssemble_uncurry (K : Set E) :
    Measurable (Function.uncurry (piFiberAssemble (S := S) K)) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [Function.uncurry, piFiberAssemble, he] using
      (measurable_pi_apply e).comp measurable_fst
  · let i : {e : E // e ∉ K} := ⟨e, he⟩
    simpa [Function.uncurry, piFiberAssemble, he, i] using
      (measurable_pi_apply i).comp measurable_snd

theorem piFiberAssemble_piEquiv_symm
    (K : Set E)
    (u : ∀ i : {e : E // e ∈ K}, S i)
    (v w : PiFiberFreeConfig (S := S) K) :
    piFiberAssemble K
        ((piFiberSplit (S := S) K).symm (u, v)) w =
      (piFiberSplit (S := S) K).symm (u, w) := by
  classical
  funext e
  by_cases he : e ∈ K
  · simp [piFiberAssemble, piFiberSplit, he]
  · simp [piFiberAssemble, piFiberSplit, he]






noncomputable def piAgreementFiberMeasure
    (μ : ∀ e, Measure (S e)) (K : Set E) (x : ∀ e, S e) :
    Measure (∀ e, S e) :=
  Measure.map (piFiberAssemble K x)
    (Measure.pi fun i : {e : E // e ∉ K} => μ i)

instance piAgreementFiberMeasure.instIsProbabilityMeasure
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (K : Set E) (x : ∀ e, S e) :
    IsProbabilityMeasure (piAgreementFiberMeasure μ K x) := by
  unfold piAgreementFiberMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_piFiberAssemble_right K x).aemeasurable




theorem ae_isCoboundedUnder_ge_real {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) :
    Filter.IsCoboundedUnder (fun a b : ℝ => a ≥ b) (ae ν) f := by
  have hexists : ∃ n : ℕ, ν {x | f x ≤ (n : ℝ)} ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ν (⋃ n : ℕ, {x | f x ≤ (n : ℝ)}) = 0 :=
      measure_iUnion_null h
    have hunion : (⋃ n : ℕ, {x | f x ≤ (n : ℝ)}) = Set.univ := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
      exact exists_nat_ge (f x)
    rw [hunion, measure_univ] at hzero
    exact one_ne_zero hzero
  obtain ⟨n, hn⟩ := hexists
  exact Filter.IsCoboundedUnder.of_frequently_le (a := (n : ℝ))
    (frequently_ae_iff.mpr hn)


noncomputable def piCylinderEssInf
    (μ : ∀ e, Measure (S e)) (f : (∀ e, S e) → ℝ)
    (K : Set E) (x : ∀ e, S e) : ℝ :=
  essInf (fun z : PiFiberFreeConfig (S := S) K =>
    f (piFiberAssemble K x z))
    (Measure.pi fun i : {e : E // e ∉ K} => μ i)


theorem piCylinderEssInf_eq_of_piAgreeOn
    (μ : ∀ e, Measure (S e)) (f : (∀ e, S e) → ℝ)
    (K : Set E) {x y : ∀ e, S e} (hxy : piAgreeOn K x y) :
    piCylinderEssInf μ f K x = piCylinderEssInf μ f K y := by
  have hassemble : piFiberAssemble K x = piFiberAssemble K y := by
    funext z e
    by_cases he : e ∈ K
    · simp [piFiberAssemble, he, hxy e he]
    · simp [piFiberAssemble, he]
  simp only [piCylinderEssInf, hassemble]


theorem piCylinderEssInf_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (K : Set E) (x : ∀ e, S e) :
    0 ≤ piCylinderEssInf μ f K x := by
  refine le_essInf_of_ae_le 0 (Filter.Eventually.of_forall fun z => ?_)
    (ae_isCoboundedUnder_ge_real
      (Measure.pi fun i : {e : E // e ∉ K} => μ i)
      (fun z => f (piFiberAssemble K x z)))
  exact hf0 _




noncomputable def piCylinderSublevelMeasure
    (μ : ∀ e, Measure (S e)) (f : (∀ e, S e) → ℝ)
    (K : Set E) (r : ℝ) (x : ∀ e, S e) : ℝ≥0∞ :=
  Measure.pi (fun i : {e : E // e ∉ K} => μ i)
    {z | f (piFiberAssemble K x z) ≤ r}

theorem measurable_piCylinderSublevelMeasure
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (K : Set E) (r : ℝ) :
    Measurable (piCylinderSublevelMeasure μ f K r) := by
  let A : Set ((∀ e, S e) × PiFiberFreeConfig (S := S) K) :=
    {p | f (piFiberAssemble K p.1 p.2) ≤ r}
  have hA : MeasurableSet A := by
    exact measurableSet_le
      (hf.comp (measurable_piFiberAssemble_uncurry K)) measurable_const
  have hm := measurable_measure_prodMk_left
    (ν := Measure.pi fun i : {e : E // e ∉ K} => μ i) hA
  simpa only [piCylinderSublevelMeasure, A] using hm

theorem lt_piCylinderEssInf_iff
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (K : Set E) (x : ∀ e, S e) (a : ℝ) :
    a < piCylinderEssInf μ f K x ↔
      ∃ n : ℕ, piCylinderSublevelMeasure μ f K
        (a + 1 / (n + 1 : ℝ)) x = 0 := by
  let h : PiFiberFreeConfig (S := S) K → ℝ :=
    fun z => f (piFiberAssemble K x z)
  let ν : Measure (PiFiberFreeConfig (S := S) K) :=
    Measure.pi fun i : {e : E // e ∉ K} => μ i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hh0 : ∀ z, 0 ≤ h z := fun z => hf0 _
  have hbounded : Filter.IsBoundedUnder (fun p q : ℝ => p ≥ q)
      (ae ν) h := by
    change ∃ b : ℝ, ∀ᵐ z ∂ν, h z ≥ b
    exact ⟨0, Filter.Eventually.of_forall hh0⟩
  constructor
  · intro ha
    have ha' : a < essInf h ν := by
      simpa only [piCylinderEssInf, h, ν] using ha
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ha')
    have hr : a + 1 / (n + 1 : ℝ) < essInf h ν := by
      linarith
    have hae : ∀ᵐ z ∂ν, a + 1 / (n + 1 : ℝ) < h z :=
      ae_lt_of_lt_essInf hr hbounded
    refine ⟨n, ?_⟩
    rw [piCylinderSublevelMeasure, measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with z hz
    exact not_le_of_gt hz
  · rintro ⟨n, hn⟩
    have hae : ∀ᵐ z ∂ν,
        a + 1 / (n + 1 : ℝ) ≤ h z := by
      rw [piCylinderSublevelMeasure,
        measure_eq_zero_iff_ae_notMem] at hn
      filter_upwards [hn] with z hz
      exact le_of_lt (lt_of_not_ge hz)
    have hrle : a + 1 / (n + 1 : ℝ) ≤ essInf h ν :=
      le_essInf_of_ae_le _ hae
        (ae_isCoboundedUnder_ge_real ν h)
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    exact lt_of_lt_of_le (lt_add_of_pos_right a hpos) hrle




theorem measurable_piCylinderEssInf
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (K : Set E) :
    Measurable (piCylinderEssInf μ f K) := by
  apply measurable_of_Ioi
  intro a
  have hpre : piCylinderEssInf μ f K ⁻¹' Ioi a =
      ⋃ n : ℕ, {x | piCylinderSublevelMeasure μ f K
        (a + 1 / (n + 1 : ℝ)) x = 0} := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_setOf_eq]
    exact lt_piCylinderEssInf_iff μ f hf0 K x a
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_singleton 0 |>.preimage
    (measurable_piCylinderSublevelMeasure μ f hf K _)




theorem piCylinderEssInf_le_ae
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (K : Set E) :
    ∀ᵐ x ∂Measure.pi μ, piCylinderEssInf μ f K x ≤ f x := by
  classical
  let split := piFiberSplit (S := S) K
  let μK : Measure (∀ i : {e : E // e ∈ K}, S i) :=
    Measure.pi fun i : {e : E // e ∈ K} => μ i
  let μC : Measure (PiFiberFreeConfig (S := S) K) :=
    Measure.pi fun i : {e : E // e ∉ K} => μ i
  let P : ((∀ i : {e : E // e ∈ K}, S i) ×
      PiFiberFreeConfig (S := S) K) → Prop := fun p =>
    piCylinderEssInf μ f K (split.symm p) ≤ f (split.symm p)
  have hP : MeasurableSet {p | P p} := by
    exact measurableSet_le
      ((measurable_piCylinderEssInf μ f hf hf0 K).comp split.symm.measurable)
      (hf.comp split.symm.measurable)
  have hprod : ∀ᵐ p ∂μK.prod μC, P p := by
    rw [Measure.ae_prod_iff_ae_ae hP]
    refine Filter.Eventually.of_forall fun u => ?_
    let h : PiFiberFreeConfig (S := S) K → ℝ :=
      fun w => f (split.symm (u, w))
    have hbounded : Filter.IsBoundedUnder (fun a b : ℝ => a ≥ b)
        (ae μC) h := by
      change ∃ b : ℝ, ∀ᵐ w ∂μC, h w ≥ b
      exact ⟨0, Filter.Eventually.of_forall fun w => hf0 _⟩
    have hae : ∀ᵐ v ∂μC, essInf h μC ≤ h v :=
      ae_essInf_le hbounded
    filter_upwards [hae] with v hv
    simpa only [P, piCylinderEssInf, h, μC, split,
      piFiberAssemble_piEquiv_symm] using hv
  have hmp : MeasurePreserving split (Measure.pi μ) (μK.prod μC) := by
    simpa only [split, piFiberSplit, μK, μC] using
      (measurePreserving_piEquivPiSubtypeProd μ (fun e => e ∈ K))
  rw [← hmp.map_eq] at hprod
  have hpull := (ae_map_iff hmp.measurable.aemeasurable hP).mp hprod
  filter_upwards [hpull] with x hx
  have hs : split.symm (split x) = x := split.symm_apply_apply x
  simpa only [P, hs] using hx



noncomputable def piFunctionalDisjointEssMaxAt
    (μ : ∀ e, Measure (S e)) (f g : (∀ e, S e) → ℝ)
    (x y : ∀ e, S e) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => piCylinderEssInf μ f pair.1 x *
      piCylinderEssInf μ g pair.2 y


noncomputable def piFunctionalDisjointEssMax
    (μ : ∀ e, Measure (S e)) (f g : (∀ e, S e) → ℝ)
    (x : ∀ e, S e) : ℝ :=
  piFunctionalDisjointEssMaxAt μ f g x x

theorem piFunctionalDisjointEssMaxAt_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (x y : ∀ e, S e) :
    0 ≤ piFunctionalDisjointEssMaxAt μ f g x y := by
  unfold piFunctionalDisjointEssMaxAt
  let pair : Set E × Set E := (∅, ∅)
  have hpair : pair ∈ disjointCoordinatePairs E := by
    exact mem_disjointCoordinatePairs.mpr (Set.empty_disjoint ∅)
  calc
    0 ≤ piCylinderEssInf μ f pair.1 x *
        piCylinderEssInf μ g pair.2 y :=
      mul_nonneg (piCylinderEssInf_nonneg μ f hf0 pair.1 x)
        (piCylinderEssInf_nonneg μ g hg0 pair.2 y)
    _ ≤ (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun p => piCylinderEssInf μ f p.1 x *
          piCylinderEssInf μ g p.2 y) :=
      Finset.le_sup'
        (fun p : Set E × Set E => piCylinderEssInf μ f p.1 x *
          piCylinderEssInf μ g p.2 y) hpair

theorem measurable_piFunctionalDisjointEssMaxAt
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Measurable (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalDisjointEssMaxAt μ f g p.1 p.2) := by
  have hrw : (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalDisjointEssMaxAt μ f g p.1 p.2) =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair p => piCylinderEssInf μ f pair.1 p.1 *
          piCylinderEssInf μ g pair.2 p.2) := by
    funext p
    rw [piFunctionalDisjointEssMaxAt, Finset.sup'_apply]
  rw [hrw]
  apply Finset.measurable_sup'
  intro pair _
  exact ((measurable_piCylinderEssInf μ f hf hf0 pair.1).comp measurable_fst).mul
    ((measurable_piCylinderEssInf μ g hg hg0 pair.2).comp measurable_snd)

theorem measurable_piFunctionalDisjointEssMax
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Measurable (piFunctionalDisjointEssMax μ f g) := by
  have hrw : piFunctionalDisjointEssMax μ f g =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair x => piCylinderEssInf μ f pair.1 x *
          piCylinderEssInf μ g pair.2 x) := by
    funext x
    rw [piFunctionalDisjointEssMax, piFunctionalDisjointEssMaxAt,
      Finset.sup'_apply]
  rw [hrw]
  apply Finset.measurable_sup'
  intro pair _
  exact (measurable_piCylinderEssInf μ f hf hf0 pair.1).mul
    (measurable_piCylinderEssInf μ g hg hg0 pair.2)



def PiDependsOn (K : Set E) (h : (∀ e, S e) → ℝ) : Prop :=
  ∀ ⦃x y⦄, piAgreeOn K x y → h x = h y


noncomputable def piFunctionalFamilyMax
    (F : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  (Finset.univ : Finset (Set E)).sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
    fun K => F K x


noncomputable def piFunctionalFamilyDisjointMaxAt
    (F G : Set E → (∀ e, S e) → ℝ) (x y : ∀ e, S e) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => F pair.1 x * G pair.2 y

noncomputable def piFunctionalFamilyDisjointMax
    (F G : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  piFunctionalFamilyDisjointMaxAt F G x x




def HasMeasurableFunctionalBKR (μ : ∀ e, Measure (S e)) : Prop :=
  ∀ (F G : Set E → (∀ e, S e) → ℝ),
    (∀ K, Measurable (F K)) → (∀ K, Measurable (G K)) →
    (∀ K x, 0 ≤ F K x) → (∀ K x, 0 ≤ G K x) →
    (∀ K, PiDependsOn K (F K)) → (∀ K, PiDependsOn K (G K)) →
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi μ) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi μ



def HasMeasurableDualFunctionalBKR (μ : ∀ e, Measure (S e)) : Prop :=
  ∀ (F G : Set E → (∀ e, S e) → ℝ),
    (∀ K, Measurable (F K)) → (∀ K, Measurable (G K)) →
    (∀ K x, 0 ≤ F K x) → (∀ K x, 0 ≤ G K x) →
    (∀ K, PiDependsOn K (F K)) → (∀ K, PiDependsOn K (G K)) →
    (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) ≤
      ∫⁻ x, ENNReal.ofReal
        (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
        ∂Measure.pi μ

theorem piFunctionalFamilyMax_cylinder_le_ae
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∀ᵐ x ∂Measure.pi μ,
      piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x ≤ f x := by
  have hall : ∀ K : Set E, ∀ᵐ x ∂Measure.pi μ,
      piCylinderEssInf μ f K x ≤ f x :=
    fun K => piCylinderEssInf_le_ae μ f hf hf0 K
  filter_upwards [ae_all_iff.mpr hall] with x hx
  unfold piFunctionalFamilyMax
  apply Finset.sup'_le
  intro K _
  exact hx K

theorem piFunctionalFamilyMax_cylinder_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (x : ∀ e, S e) :
    0 ≤ piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x := by
  unfold piFunctionalFamilyMax
  let K : Set E := ∅
  calc
    0 ≤ piCylinderEssInf μ f K x :=
      piCylinderEssInf_nonneg μ f hf0 K x
    _ ≤ (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
        (fun L => piCylinderEssInf μ f L x) :=
      Finset.le_sup' (fun L : Set E => piCylinderEssInf μ f L x)
        (Finset.mem_univ K)



theorem functionalBKR_generalProduct_of_familyBKR
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (hBKR : HasMeasurableFunctionalBKR μ)
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax μ f g x)
        ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ) *
        ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ := by
  let F : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ f K
  let G : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ g K
  have hcore := hBKR F G
    (fun K => measurable_piCylinderEssInf μ f hf hf0 K)
    (fun K => measurable_piCylinderEssInf μ g hg hg0 K)
    (fun K x => piCylinderEssInf_nonneg μ f hf0 K x)
    (fun K x => piCylinderEssInf_nonneg μ g hg0 K x)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ f K hxy)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ g K hxy)
  have hF := piFunctionalFamilyMax_cylinder_le_ae μ f hf hf0
  have hG := piFunctionalFamilyMax_cylinder_le_ae μ g hg hg0
  have hFint : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x)
      ∂Measure.pi μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ := by
    apply lintegral_mono_ae
    filter_upwards [hF] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hGint : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x)
      ∂Measure.pi μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ := by
    apply lintegral_mono_ae
    filter_upwards [hG] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  calc
    (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax μ f g x)
        ∂Measure.pi μ) =
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
          ∂Measure.pi μ := by rfl
    _ ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi μ) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi μ := hcore
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ) *
          ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ :=
      mul_le_mul hFint hGint (by positivity) (by positivity)



theorem dualFunctionalBKR_generalProduct_of_familyBKR
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (hBKR : HasMeasurableDualFunctionalBKR μ)
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ p, ENNReal.ofReal
        (piFunctionalDisjointEssMaxAt μ f g p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi μ := by
  let F : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ f K
  let G : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ g K
  have hcore := hBKR F G
    (fun K => measurable_piCylinderEssInf μ f hf hf0 K)
    (fun K => measurable_piCylinderEssInf μ g hg hg0 K)
    (fun K x => piCylinderEssInf_nonneg μ f hf0 K x)
    (fun K x => piCylinderEssInf_nonneg μ g hg0 K x)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ f K hxy)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ g K hxy)
  have hF := piFunctionalFamilyMax_cylinder_le_ae μ f hf hf0
  have hG := piFunctionalFamilyMax_cylinder_le_ae μ g hg hg0
  calc
    (∫⁻ p, ENNReal.ofReal
        (piFunctionalDisjointEssMaxAt μ f g p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) =
        ∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi μ).prod (Measure.pi μ) := by rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi μ := hcore
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi μ := by
      apply lintegral_mono_ae
      filter_upwards [hF, hG] with x hxF hxG
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul hxF hxG
        (piFunctionalFamilyMax_cylinder_nonneg μ g hg0 x)
        (hf0 x)



theorem piFunctionalFamilyMax_nonneg
    (F : Set E → (∀ e, S e) → ℝ) (hF0 : ∀ K x, 0 ≤ F K x)
    (x : ∀ e, S e) :
    0 ≤ piFunctionalFamilyMax F x := by
  unfold piFunctionalFamilyMax
  let K : Set E := ∅
  calc
    0 ≤ F K x := hF0 K x
    _ ≤ (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
        (fun L => F L x) :=
      Finset.le_sup' (fun L : Set E => F L x) (Finset.mem_univ K)

theorem familyMember_le_cylinderMin_familyMax
    (F : Set E → StatMech.ConfigSpace E → ℝ)
    (hF : ∀ K, PiDependsOn K (F K))
    (K : Set E) (omega : StatMech.ConfigSpace E) :
    F K omega ≤ cylinderMin (piFunctionalFamilyMax F) K omega := by
  unfold cylinderMin
  apply Finset.le_inf'
  intro eta heta
  have hagree : piAgreeOn K omega eta := by
    intro e he
    exact (mem_agreementFiber.mp heta e he).symm
  calc
    F K omega = F K eta := hF K hagree
    _ ≤ piFunctionalFamilyMax F eta := by
      unfold piFunctionalFamilyMax
      exact Finset.le_sup' (fun L : Set E => F L eta) (Finset.mem_univ K)

theorem piFunctionalFamilyDisjointMaxAt_le
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K))
    (omega eta : StatMech.ConfigSpace E) :
    piFunctionalFamilyDisjointMaxAt F G omega eta ≤
      functionalDisjointMaxAt (piFunctionalFamilyMax F)
        (piFunctionalFamilyMax G) omega eta := by
  unfold piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  have hleft : F pair.1 omega ≤
      cylinderMin (piFunctionalFamilyMax F) pair.1 omega :=
    familyMember_le_cylinderMin_familyMax F hF pair.1 omega
  have hright : G pair.2 eta ≤
      cylinderMin (piFunctionalFamilyMax G) pair.2 eta :=
    familyMember_le_cylinderMin_familyMax G hG pair.2 eta
  calc
    F pair.1 omega * G pair.2 eta ≤
        cylinderMin (piFunctionalFamilyMax F) pair.1 omega *
          cylinderMin (piFunctionalFamilyMax G) pair.2 eta :=
      mul_le_mul hleft hright (hG0 pair.2 eta)
        (cylinderMin_nonneg (piFunctionalFamilyMax_nonneg F hF0) pair.1 omega)
    _ ≤ functionalDisjointMaxAt (piFunctionalFamilyMax F)
          (piFunctionalFamilyMax G) omega eta := by
      unfold functionalDisjointMaxAt
      exact Finset.le_sup'
        (fun p : Set E × Set E =>
          cylinderMin (piFunctionalFamilyMax F) p.1 omega *
            cylinderMin (piFunctionalFamilyMax G) p.2 eta) hpair

theorem functionalFamilyBKR_real
    (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    productExpectation phi (piFunctionalFamilyDisjointMax F G) ≤
      productExpectation phi (piFunctionalFamilyMax F) *
        productExpectation phi (piFunctionalFamilyMax G) := by
  calc
    productExpectation phi (piFunctionalFamilyDisjointMax F G) ≤
        productExpectation phi
          (functionalDisjointMax (piFunctionalFamilyMax F)
            (piFunctionalFamilyMax G)) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalFamilyDisjointMaxAt_le F G hF0 hG0 hF hG omega omega)
        (pweight_nonneg hphi0 omega)
    _ ≤ productExpectation phi (piFunctionalFamilyMax F) *
          productExpectation phi (piFunctionalFamilyMax G) :=
      functionalBKR_real phi hphi0 hphi1 _ _
        (piFunctionalFamilyMax_nonneg F hF0)
        (piFunctionalFamilyMax_nonneg G hG0)

theorem dualFunctionalFamilyBKR_real
    (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    dualProductExpectation phi (fun p =>
        piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ≤
      productExpectation phi (fun x =>
        piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
  calc
    dualProductExpectation phi (fun p =>
        piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ≤
        dualProductExpectation phi (fun p =>
          functionalDisjointMaxAt (piFunctionalFamilyMax F)
            (piFunctionalFamilyMax G) p.1 p.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalFamilyDisjointMaxAt_le F G hF0 hG0 hF hG omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ ≤ productExpectation phi (fun x =>
          piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) :=
      dualFunctionalBKR_real phi hphi0 hphi1 _ _
        (piFunctionalFamilyMax_nonneg F hF0)
        (piFunctionalFamilyMax_nonneg G hG0)

theorem productExpectation_fin_cons {n : ℕ}
    (phi : Fin (n + 1) → Bool → ℝ)
    (H : (Fin (n + 1) → Bool) → ℝ) :
    productExpectation phi H =
      ∑ b : Bool, phi 0 b *
        productExpectation (fun i b => phi i.succ b)
          (fun eta => H (Fin.cons b eta)) := by
  unfold productExpectation pweight
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  have hcons :
      (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) (b, eta) =
        Fin.cons b eta := by
    rfl
  rw [hcons]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring




def HasBernoulliBlockRepresentation {T : Type*} [Fintype T]
    (w : T → ℝ) : Prop :=
  ∃ (n : ℕ) (phi : Fin n → Bool → ℝ)
      (decode : (Fin n → Bool) → T),
    (∀ i b, 0 ≤ phi i b) ∧
    (∀ i, phi i false + phi i true = 1) ∧
    Function.Surjective decode ∧
    ∀ H : T → ℝ,
      productExpectation phi (H ∘ decode) = ∑ t, w t * H t

theorem HasBernoulliBlockRepresentation.equiv
    {T U : Type*} [Fintype T] [Fintype U]
    (e : T ≃ U) (w : U → ℝ)
    (h : HasBernoulliBlockRepresentation (fun t => w (e t))) :
    HasBernoulliBlockRepresentation w := by
  classical
  obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := h
  refine ⟨n, phi, e ∘ decode, hphi0, hphi1, e.surjective.comp hdecode, ?_⟩
  intro H
  rw [← e.sum_comp]
  simpa only [Function.comp_apply, Function.comp_def] using
    hexpect (H ∘ e)

theorem productExpectation_const {I : Type*} [Fintype I] [DecidableEq I]
    (phi : I → Bool → ℝ)
    (hphi1 : ∀ i, phi i false + phi i true = 1) (c : ℝ) :
    productExpectation phi (fun _ => c) = c := by
  classical
  unfold productExpectation
  rw [← Finset.sum_mul, sum_pweight_eq_one hphi1, one_mul]

theorem hasBernoulliBlockRepresentation_option
    {T : Type*} [Fintype T] [Nonempty T]
    (ih : ∀ (v : T → ℝ), (∀ t, 0 ≤ v t) → (∑ t, v t) = 1 →
      HasBernoulliBlockRepresentation v)
    (w : Option T → ℝ) (hw0 : ∀ t, 0 ≤ w t)
    (hw1 : (∑ t, w t) = 1) :
    HasBernoulliBlockRepresentation w := by
  classical
  let q : ℝ := w none
  let r : ℝ := ∑ t : T, w (some t)
  have hqr : q + r = 1 := by
    simpa only [q, r, Fintype.sum_option] using hw1
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun t _ => hw0 (some t)
  have hq0 : 0 ≤ q := hw0 none
  by_cases hr : r = 0
  · let a : T := Classical.choice inferInstance
    let v : T → ℝ := fun t => if t = a then 1 else 0
    have hv0 : ∀ t, 0 ≤ v t := by
      intro t
      simp only [v]
      split <;> positivity
    have hv1 : (∑ t, v t) = 1 := by
      simp [v]
    obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := ih v hv0 hv1
    let psi : Fin (n + 1) → Bool → ℝ := fun i =>
      Fin.cases (fun b => if b then q else r) phi i
    let decode' : (Fin (n + 1) → Bool) → Option T := fun omega =>
      if omega 0 then none else some (decode (Fin.tail omega))
    refine ⟨n + 1, psi, decode', ?_, ?_, ?_, ?_⟩
    · intro i b
      refine Fin.cases ?_ (fun j => ?_) i
      · cases b <;> simp [psi, hr0, hq0]
      · simpa [psi] using hphi0 j b
    · intro i
      refine Fin.cases ?_ (fun j => hphi1 j) i
      simpa [psi, add_comm] using hqr
    · intro t
      cases t with
      | none =>
          refine ⟨Fin.cons true (fun _ => false), ?_⟩
          simp [decode']
      | some t =>
          obtain ⟨eta, heta⟩ := hdecode t
          refine ⟨Fin.cons false eta, ?_⟩
          simp [decode', heta]
    · intro H
      rw [productExpectation_fin_cons]
      rw [Fintype.sum_bool]
      simp only [psi, Fin.cases_zero, decode', Fin.cons_zero, Bool.false_eq_true,
        if_false, Bool.true_eq, if_true, Fin.tail_cons, Function.comp_apply]
      change q * productExpectation phi (fun _ => H none) +
          r * productExpectation phi ((fun t => H (some t)) ∘ decode) = _
      rw [productExpectation_const phi hphi1, hexpect]
      have hsome : ∀ t : T, w (some t) = 0 := by
        intro t
        have hle : w (some t) ≤ r := Finset.single_le_sum
          (fun u _ => hw0 (some u)) (Finset.mem_univ t)
        linarith [hw0 (some t)]
      rw [Fintype.sum_option]
      simp only [hsome, zero_mul, Finset.sum_const_zero, add_zero, hr, zero_mul]
      rfl
  · let v : T → ℝ := fun t => w (some t) / r
    have hv0 : ∀ t, 0 ≤ v t := fun t => div_nonneg (hw0 (some t)) hr0
    have hv1 : (∑ t, v t) = 1 := by
      simp only [v, ← Finset.sum_div, r]
      exact div_self hr
    obtain ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩ := ih v hv0 hv1
    let psi : Fin (n + 1) → Bool → ℝ := fun i =>
      Fin.cases (fun b => if b then q else r) phi i
    let decode' : (Fin (n + 1) → Bool) → Option T := fun omega =>
      if omega 0 then none else some (decode (Fin.tail omega))
    refine ⟨n + 1, psi, decode', ?_, ?_, ?_, ?_⟩
    · intro i b
      refine Fin.cases ?_ (fun j => ?_) i
      · cases b <;> simp [psi, hr0, hq0]
      · simpa [psi] using hphi0 j b
    · intro i
      refine Fin.cases ?_ (fun j => hphi1 j) i
      simpa [psi, add_comm] using hqr
    · intro t
      cases t with
      | none =>
          refine ⟨Fin.cons true (fun _ => false), ?_⟩
          simp [decode']
      | some t =>
          obtain ⟨eta, heta⟩ := hdecode t
          refine ⟨Fin.cons false eta, ?_⟩
          simp [decode', heta]
    · intro H
      rw [productExpectation_fin_cons]
      rw [Fintype.sum_bool]
      simp only [psi, Fin.cases_zero, decode', Fin.cons_zero, Bool.false_eq_true,
        if_false, Bool.true_eq, if_true, Fin.tail_cons, Function.comp_apply]
      change q * productExpectation phi (fun _ => H none) +
          r * productExpectation phi ((fun t => H (some t)) ∘ decode) = _
      rw [productExpectation_const phi hphi1, hexpect]
      rw [Fintype.sum_option]
      simp only [v]
      calc
        q * H none + r * ∑ t, w (some t) / r * H (some t) =
            w none * H none + ∑ t, w (some t) * H (some t) := by
          rw [show q = w none from rfl]
          rw [Finset.mul_sum]
          apply congrArg (fun z => w none * H none + z)
          apply Finset.sum_congr rfl
          intro t _
          field_simp

theorem exists_bernoulliBlockRepresentation
    {T : Type u} [Fintype T] (w : T → ℝ)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : (∑ t, w t) = 1) :
    HasBernoulliBlockRepresentation w := by
  classical
  let P := fun (T : Type u) [Fintype T] =>
    ∀ (w : T → ℝ), (∀ t, 0 ≤ w t) → (∑ t, w t) = 1 →
      HasBernoulliBlockRepresentation w
  suffices h : P T by exact h w hw0 hw1
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ T
  · intro A B _ e hA w hw0 hw1
    letI : Fintype A := Fintype.ofEquiv B e.symm
    apply HasBernoulliBlockRepresentation.equiv e w
    apply hA (fun a => w (e a)) (fun a => hw0 (e a))
    simpa only [← e.sum_comp] using hw1
  · intro w _ hw1
    simp at hw1
  · intro A _ hA w hw0 hw1
    by_cases hne : Nonempty A
    · letI : Nonempty A := hne
      exact hasBernoulliBlockRepresentation_option hA w hw0 hw1
    · letI : IsEmpty A := not_nonempty_iff.mp hne
      let phi : Fin 0 → Bool → ℝ := fun i => Fin.elim0 i
      let decode : (Fin 0 → Bool) → Option A := fun _ => none
      refine ⟨0, phi, decode, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro t
        cases t with
        | none => exact ⟨fun i => Fin.elim0 i, rfl⟩
        | some a => exact isEmptyElim a
      · intro H
        change productExpectation phi (fun _ => H none) = _
        rw [productExpectation_const phi (fun i => Fin.elim0 i)]
        rw [Fintype.sum_option]
        have hwnone : w none = 1 := by simpa using hw1
        simp [hwnone]



section DependentBlocks

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)]

theorem familyMember_le_piCylinderMin_familyMax
    (F : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, PiDependsOn K (F K))
    (K : Set E) (x : ∀ e, S e) :
    F K x ≤ piCylinderMin (piFunctionalFamilyMax F) K x := by
  unfold piCylinderMin
  apply Finset.le_inf'
  intro y hy
  have hagree : piAgreeOn K x y := mem_piAgreementFiber.mp hy
  calc
    F K x = F K y := hF K hagree
    _ ≤ piFunctionalFamilyMax F y := by
      unfold piFunctionalFamilyMax
      exact Finset.le_sup' (fun L : Set E ↦ F L y) (Finset.mem_univ K)

theorem piFunctionalFamilyDisjointMaxAt_le_pi
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K))
    (x y : ∀ e, S e) :
    piFunctionalFamilyDisjointMaxAt F G x y ≤
      piFunctionalDisjointMaxAt
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) x y := by
  unfold piFunctionalFamilyDisjointMaxAt piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  have hleft : F pair.1 x ≤
      piCylinderMin (piFunctionalFamilyMax F) pair.1 x :=
    familyMember_le_piCylinderMin_familyMax F hF pair.1 x
  have hright : G pair.2 y ≤
      piCylinderMin (piFunctionalFamilyMax G) pair.2 y :=
    familyMember_le_piCylinderMin_familyMax G hG pair.2 y
  have hminF0 : 0 ≤ piCylinderMin (piFunctionalFamilyMax F) pair.1 x := by
    unfold piCylinderMin
    apply Finset.le_inf'
    intro z _
    exact piFunctionalFamilyMax_nonneg F hF0 z
  calc
    F pair.1 x * G pair.2 y ≤
        piCylinderMin (piFunctionalFamilyMax F) pair.1 x *
          piCylinderMin (piFunctionalFamilyMax G) pair.2 y :=
      mul_le_mul hleft hright (hG0 pair.2 y) hminF0
    _ ≤ (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun p ↦ piCylinderMin (piFunctionalFamilyMax F) p.1 x *
          piCylinderMin (piFunctionalFamilyMax G) p.2 y) :=
      Finset.le_sup' (fun p : Set E × Set E ↦
        piCylinderMin (piFunctionalFamilyMax F) p.1 x *
          piCylinderMin (piFunctionalFamilyMax G) p.2 y) hpair



def decodeDependentBlockConfig
    (decode : ∀ e, (D e → Bool) → S e)
    (omega : StatMech.ConfigSpace (Sigma D)) : ∀ e, S e :=
  fun e => decode e (fun d => omega ⟨e, d⟩)


def dependentWholeBlocks (K : Set E) : Set (Sigma D) :=
  {z | z.1 ∈ K}

theorem dependentWholeBlocks_disjoint {K L : Set E} (hKL : Disjoint K L) :
    Disjoint (dependentWholeBlocks (D := D) K)
      (dependentWholeBlocks (D := D) L) := by
  rw [Set.disjoint_left]
  intro z hzK hzL
  exact Set.disjoint_left.1 hKL hzK hzL

noncomputable def encodeDependentBlockConfig
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e)) (x : ∀ e, S e) :
    StatMech.ConfigSpace (Sigma D) :=
  fun z => Classical.choose (hdecode z.1 (x z.1)) z.2

@[simp] theorem decodeDependentBlockConfig_encode
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e)) (x : ∀ e, S e) :
    decodeDependentBlockConfig decode
      (encodeDependentBlockConfig decode hdecode x) = x := by
  funext e
  exact Classical.choose_spec (hdecode e (x e))

noncomputable def liftDependentPiCylinder
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : StatMech.ConfigSpace (Sigma D)) (x : ∀ e, S e) :
    StatMech.ConfigSpace (Sigma D) := by
  classical
  exact fun z => if z.1 ∈ K then omega z else
      encodeDependentBlockConfig decode hdecode x z

theorem liftDependentPiCylinder_agreeOn
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : StatMech.ConfigSpace (Sigma D)) (x : ∀ e, S e) :
    agreeOn (dependentWholeBlocks (D := D) K) omega
      (liftDependentPiCylinder decode hdecode K omega x) := by
  intro z hz
  simp only [dependentWholeBlocks, Set.mem_setOf_eq] at hz
  simp [liftDependentPiCylinder, hz]

theorem decodeDependentBlockConfig_lift
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : StatMech.ConfigSpace (Sigma D)) (x : ∀ e, S e)
    (hx : piAgreeOn K (decodeDependentBlockConfig decode omega) x) :
    decodeDependentBlockConfig decode
      (liftDependentPiCylinder decode hdecode K omega x) = x := by
  funext e
  by_cases he : e ∈ K
  · simpa [decodeDependentBlockConfig, liftDependentPiCylinder, he] using hx e he
  · simpa [decodeDependentBlockConfig, liftDependentPiCylinder, he] using
      congrFun (decodeDependentBlockConfig_encode decode hdecode x) e

theorem piAgreeOn_decodeDependent_of_agreeOn
    (decode : ∀ e, (D e → Bool) → S e) (K : Set E)
    {omega eta : StatMech.ConfigSpace (Sigma D)}
    (h : agreeOn (dependentWholeBlocks (D := D) K)
      omega eta) :
    piAgreeOn K (decodeDependentBlockConfig decode omega)
      (decodeDependentBlockConfig decode eta) := by
  intro e he
  apply congrArg (decode e)
  funext d
  exact (h ⟨e, d⟩ he).symm

theorem piCylinderMin_decodeDependentBlockConfig
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f : (∀ e, S e) → ℝ) (K : Set E)
    (omega : StatMech.ConfigSpace (Sigma D)) :
    piCylinderMin f K (decodeDependentBlockConfig decode omega) =
      cylinderMin
        (f ∘ decodeDependentBlockConfig decode)
        (dependentWholeBlocks (D := D) K) omega := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro eta heta
    exact Finset.inf'_le _ (mem_piAgreementFiber.mpr
      (piAgreeOn_decodeDependent_of_agreeOn decode K
        (mem_agreementFiber.mp heta)))
  · apply Finset.le_inf'
    intro x hx
    let eta := liftDependentPiCylinder decode hdecode K omega x
    have heta : eta ∈ agreementFiber
        (dependentWholeBlocks (D := D) K) omega :=
      mem_agreementFiber.mpr
        (liftDependentPiCylinder_agreeOn decode hdecode K omega x)
    calc
      cylinderMin
          (f ∘ decodeDependentBlockConfig decode)
          (dependentWholeBlocks (D := D) K) omega ≤
          (f ∘ decodeDependentBlockConfig decode) eta :=
        Finset.inf'_le _ heta
      _ = f x := by
        rw [Function.comp_apply,
          decodeDependentBlockConfig_lift decode hdecode K omega x
            (mem_piAgreementFiber.mp hx)]

theorem piFunctionalDisjointMaxAt_decodeDependent_le
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (omega eta : StatMech.ConfigSpace (Sigma D)) :
    piFunctionalDisjointMaxAt f g (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode eta) ≤
      functionalDisjointMaxAt
        (f ∘ decodeDependentBlockConfig decode)
        (g ∘ decodeDependentBlockConfig decode) omega eta := by
  classical
  unfold piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [piCylinderMin_decodeDependentBlockConfig decode hdecode,
    piCylinderMin_decodeDependentBlockConfig decode hdecode]
  unfold functionalDisjointMaxAt
  have hbit :
      (dependentWholeBlocks (D := D) pair.1,
        dependentWholeBlocks (D := D) pair.2) ∈
        disjointCoordinatePairs (Sigma D) :=
    mem_disjointCoordinatePairs.mpr
      (dependentWholeBlocks_disjoint (D := D)
        (mem_disjointCoordinatePairs.mp hpair))
  exact Finset.le_sup'
    (fun bitPair : Set (Sigma D) × Set (Sigma D) =>
      cylinderMin (f ∘ decodeDependentBlockConfig decode) bitPair.1 omega *
        cylinderMin (g ∘ decodeDependentBlockConfig decode) bitPair.2 eta)
    hbit

theorem piFunctionalDisjointMax_decodeDependent_le
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega : StatMech.ConfigSpace (Sigma D)) :
    piFunctionalDisjointMax f g (decodeDependentBlockConfig decode omega) ≤
      functionalDisjointMax
        (f ∘ decodeDependentBlockConfig decode)
        (g ∘ decodeDependentBlockConfig decode) omega :=
  piFunctionalDisjointMaxAt_decodeDependent_le decode hdecode f g omega omega

set_option maxHeartbeats 20000 in
theorem functionalFamilyBKR_dependentBlocks
    (phi : Sigma D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    productExpectation phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
      productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
  let fmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode
  let gmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode
  have hfmax0 : ∀ omega, 0 ≤ fmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg F hF0 _
  have hgmax0 : ∀ omega, 0 ≤ gmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg G hG0 _
  have hbkr : productExpectation phi (functionalDisjointMax fmax gmax) ≤
      productExpectation phi fmax * productExpectation phi gmax :=
    functionalBKR_real phi hphi0 hphi1 fmax gmax hfmax0 hgmax0
  calc
    productExpectation phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
        productExpectation phi (functionalDisjointMax fmax gmax) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_left _ (pweight_nonneg hphi0 omega)
      have hfamily := piFunctionalFamilyDisjointMaxAt_le_pi F G hF0 hG0 hF hG
        (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode omega)
      have hlift := piFunctionalDisjointMax_decodeDependent_le decode hdecode
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) omega
      change piFunctionalDisjointMax
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G)
          (decodeDependentBlockConfig decode omega) ≤
        functionalDisjointMax fmax gmax omega at hlift
      exact hfamily.trans hlift
    _ ≤ productExpectation phi fmax * productExpectation phi gmax := hbkr
    _ = productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := rfl

set_option maxHeartbeats 20000 in
theorem dualFunctionalFamilyBKR_dependentBlocks
    (phi : Sigma D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D e → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    dualProductExpectation phi (fun pair =>
        piFunctionalFamilyDisjointMaxAt F G
          (decodeDependentBlockConfig decode pair.1)
          (decodeDependentBlockConfig decode pair.2)) ≤
      productExpectation phi (fun omega =>
        piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
  let fmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode
  let gmax : StatMech.ConfigSpace (Sigma D) → ℝ :=
    piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode
  have hfmax0 : ∀ omega, 0 ≤ fmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg F hF0 _
  have hgmax0 : ∀ omega, 0 ≤ gmax omega := fun omega =>
    piFunctionalFamilyMax_nonneg G hG0 _
  have hbkr : dualProductExpectation phi (fun pair =>
        functionalDisjointMaxAt fmax gmax pair.1 pair.2) ≤
      productExpectation phi (fun omega => fmax omega * gmax omega) :=
    dualFunctionalBKR_real phi hphi0 hphi1 fmax gmax hfmax0 hgmax0
  calc
    dualProductExpectation phi (fun pair =>
        piFunctionalFamilyDisjointMaxAt F G
          (decodeDependentBlockConfig decode pair.1)
          (decodeDependentBlockConfig decode pair.2)) ≤
        dualProductExpectation phi (fun pair =>
          functionalDisjointMaxAt fmax gmax pair.1 pair.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
      have hfamily := piFunctionalFamilyDisjointMaxAt_le_pi F G hF0 hG0 hF hG
        (decodeDependentBlockConfig decode omega)
        (decodeDependentBlockConfig decode eta)
      have hlift := piFunctionalDisjointMaxAt_decodeDependent_le decode hdecode
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) omega eta
      change piFunctionalDisjointMaxAt
        (piFunctionalFamilyMax F) (piFunctionalFamilyMax G)
          (decodeDependentBlockConfig decode omega)
          (decodeDependentBlockConfig decode eta) ≤
        functionalDisjointMaxAt fmax gmax omega eta at hlift
      exact hfamily.trans hlift
    _ ≤ productExpectation phi (fun omega => fmax omega * gmax omega) := hbkr
    _ = productExpectation phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
            piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := rfl

end DependentBlocks

end StatMech.FrontierA
