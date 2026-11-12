/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.FunctionalBKRGeneralProductFinite

open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]





def IsFiniteCoordinateSet (A : Set (∀ e, S e)) : Prop :=
  ∃ (n : E → ℕ) (q : ∀ e, S e → Fin (n e))
      (B : Set (∀ e, Fin (n e))),
    (∀ e, Measurable (q e)) ∧
      A = (fun x e => q e (x e)) ⁻¹' B

theorem IsFiniteCoordinateSet.measurableSet {A : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) : MeasurableSet A := by
  obtain ⟨n, q, B, hq, rfl⟩ := hA
  exact (Set.toFinite B).measurableSet.preimage
    (measurable_pi_lambda _ fun e => (hq e).comp (measurable_pi_apply e))

theorem isFiniteCoordinateSet_empty :
    IsFiniteCoordinateSet (∅ : Set (∀ e, S e)) := by
  let n : E → ℕ := fun _ => 1
  let q : ∀ e, S e → Fin (n e) := fun _ _ => 0
  refine ⟨n, q, ∅, fun _ => measurable_const, ?_⟩
  simp

theorem IsFiniteCoordinateSet.union {A B : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) (hB : IsFiniteCoordinateSet B) :
    IsFiniteCoordinateSet (A ∪ B) := by
  classical
  obtain ⟨n, q, C, hq, rfl⟩ := hA
  obtain ⟨m, r, D, hr, rfl⟩ := hB
  let k : E → ℕ := fun e => n e * m e
  let qr : ∀ e, S e → Fin (k e) := fun e x =>
    finProdFinEquiv (q e x, r e x)
  let unpair : (∀ e, Fin (k e)) → ∀ e, Fin (n e) × Fin (m e) :=
    fun y e => finProdFinEquiv.symm (y e)
  let U : Set (∀ e, Fin (k e)) :=
    {y | (fun e => (unpair y e).1) ∈ C ∨ (fun e => (unpair y e).2) ∈ D}
  refine ⟨k, qr, U, ?_, ?_⟩
  · intro e
    exact (measurable_of_finite finProdFinEquiv).comp
      (Measurable.prod (hq e) (hr e))
  · ext x
    simpa only [Set.mem_union, Set.mem_preimage, U, Set.mem_setOf_eq,
      unpair, qr, Equiv.symm_apply_apply]

theorem IsFiniteCoordinateSet.diff {A B : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) (hB : IsFiniteCoordinateSet B) :
    IsFiniteCoordinateSet (A \ B) := by
  classical
  obtain ⟨n, q, C, hq, rfl⟩ := hA
  obtain ⟨m, r, D, hr, rfl⟩ := hB
  let k : E → ℕ := fun e => n e * m e
  let qr : ∀ e, S e → Fin (k e) := fun e x =>
    finProdFinEquiv (q e x, r e x)
  let unpair : (∀ e, Fin (k e)) → ∀ e, Fin (n e) × Fin (m e) :=
    fun y e => finProdFinEquiv.symm (y e)
  let V : Set (∀ e, Fin (k e)) :=
    {y | (fun e => (unpair y e).1) ∈ C ∧ (fun e => (unpair y e).2) ∉ D}
  refine ⟨k, qr, V, ?_, ?_⟩
  · intro e
    exact (measurable_of_finite finProdFinEquiv).comp
      (Measurable.prod (hq e) (hr e))
  · ext x
    simpa only [Set.mem_diff, Set.mem_preimage, V, Set.mem_setOf_eq,
      unpair, qr, Equiv.symm_apply_apply]

theorem isSetRing_isFiniteCoordinateSet :
    IsSetRing {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} where
  empty_mem := isFiniteCoordinateSet_empty
  union_mem := by
    intro s t hs ht
    exact hs.union ht
  diff_mem := by
    intro s t hs ht
    exact hs.diff ht

theorem rectangle_isFiniteCoordinateSet
    (s : ∀ e, Set (S e)) (hs : ∀ e, MeasurableSet (s e)) :
    IsFiniteCoordinateSet (Set.pi Set.univ s) := by
  classical
  let n : E → ℕ := fun _ => 2
  let q : ∀ e, S e → Fin (n e) := fun e x =>
    if x ∈ s e then 1 else 0
  let B : Set (∀ e, Fin (n e)) := {y | ∀ e, y e = 1}
  refine ⟨n, q, B, ?_, ?_⟩
  · intro e
    exact measurable_const.ite (hs e) measurable_const
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, B,
      Set.mem_setOf_eq, q]
    constructor
    · intro hx e
      simp [hx e]
    · intro hx e
      by_contra hnot
      have hv := congrArg Fin.val (hx e)
      simp [hnot, n] at hv

theorem generateFrom_isFiniteCoordinateSet :
    (inferInstance : MeasurableSpace (∀ e, S e)) =
      MeasurableSpace.generateFrom
        {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} := by
  apply le_antisymm
  · rw [← generateFrom_pi]
    apply MeasurableSpace.generateFrom_mono
    intro A hA
    obtain ⟨s, hs, rfl⟩ := hA
    apply rectangle_isFiniteCoordinateSet s
    intro e
    exact hs e (Set.mem_univ e)
  · apply MeasurableSpace.generateFrom_le
    intro A hA
    exact hA.measurableSet

theorem exists_finiteCoordinateSet_symmDiff_lt
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    {A : Set (∀ e, S e)} (hA : MeasurableSet A)
    {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ B, IsFiniteCoordinateSet B ∧
      Measure.pi mu (B ∆ A) < eps := by
  have huniv : IsFiniteCoordinateSet (Set.univ : Set (∀ e, S e)) :=
    by simpa only [Set.pi_univ] using
      (rectangle_isFiniteCoordinateSet (S := S)
        (fun _ => Set.univ) (fun _ => MeasurableSet.univ))
  have hcover : ∃ D : Set (Set (∀ e, S e)), D.Countable ∧
      D ⊆ {B | IsFiniteCoordinateSet B} ∧
      Measure.pi mu (Set.sUnion D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · simpa using huniv
    · simp
  exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_isFiniteCoordinateSet hcover
      generateFrom_isFiniteCoordinateSet hA heps


def piRestrict (K : Set E) (x : ∀ e, S e) : ∀ i : {e : E // e ∈ K}, S i :=
  fun i => x i


noncomputable def piExtendOn (K : Set E) (base : ∀ e, S e)
    (y : ∀ i : {e : E // e ∈ K}, S i) : ∀ e, S e := by
  classical
  intro e
  by_cases he : e ∈ K
  · exact y ⟨e, he⟩
  · exact base e

theorem measurable_piExtendOn (K : Set E) (base : ∀ e, S e) :
    Measurable (piExtendOn K base) := by
  classical
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ K
  · simpa [piExtendOn, he] using
      (@measurable_pi_apply {e : E // e ∈ K} (fun i => S i.1) _ ⟨e, he⟩)
  · simpa [piExtendOn, he] using
      (measurable_const : Measurable
        (fun _ : (∀ i : {e : E // e ∈ K}, S i) => base e))

theorem piExtendOn_agreeOn (K : Set E) (base : ∀ e, S e)
    (x : ∀ e, S e) :
    piAgreeOn K x (piExtendOn K base (piRestrict K x)) := by
  intro e he
  simp [piExtendOn, piRestrict, he]

noncomputable local instance piRestrictSubtypeFintype (K : Set E) :
    Fintype {e : E // e ∈ K} := by
  classical
  infer_instance

noncomputable local instance piRestrictComplementFintype (K : Set E) :
    Fintype {e : E // e ∉ K} := by
  classical
  infer_instance

theorem measurePreserving_piRestrict
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) :
    MeasurePreserving (piRestrict (S := S) K) (Measure.pi mu)
      (Measure.pi fun i : {e : E // e ∈ K} => mu i) := by
  classical
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    mu (fun e => e ∈ K)
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi fun i : {e : E // e ∈ K} => mu i).prod
        (Measure.pi fun i : {e : E // e ∉ K} => mu i))
      (Measure.pi fun i : {e : E // e ∈ K} => mu i) :=
    measurePreserving_fst
  simpa only [Function.comp_apply, piRestrict, piFiberSplit] using hfst.comp hsplit



theorem IsFiniteCoordinateSet.preimage_piRestrict
    (K : Set E) {A : Set (∀ i : {e : E // e ∈ K}, S i)}
    (hA : IsFiniteCoordinateSet A) :
    IsFiniteCoordinateSet ((piRestrict (S := S) K) ⁻¹' A) := by
  classical
  obtain ⟨n, q, B, hq, rfl⟩ := hA
  let nf : E → ℕ := fun e => if he : e ∈ K then n ⟨e, he⟩ else 1
  let qf : ∀ e, S e → Fin (nf e) := fun e =>
    if he : e ∈ K then
      fun x => Fin.cast (by simp [nf, he]) (q ⟨e, he⟩ x)
    else fun _ => Fin.cast (by simp [nf, he]) (0 : Fin 1)
  let restrictFinite : (∀ e, Fin (nf e)) →
      ∀ i : {e : E // e ∈ K}, Fin (n i) := fun y i =>
    Fin.cast (by simp [nf, i.property]) (y i)
  let Bf : Set (∀ e, Fin (nf e)) := restrictFinite ⁻¹' B
  refine ⟨nf, qf, Bf, ?_, ?_⟩
  · intro e
    by_cases he : e ∈ K
    · simpa [qf, he] using
        (measurable_of_finite (Fin.cast (by simp [nf, he]))).comp (hq ⟨e, he⟩)
    · simp [qf, he]
  · ext x
    simp only [Set.mem_preimage, Bf]
    have heq : (fun i => q i (piRestrict K x i)) =
        restrictFinite (fun e => qf e (x e)) := by
      funext i
      simp [restrictFinite, qf, piRestrict, i.property]
    rw [heq]


def PiSetDependsOn (K : Set E) (A : Set (∀ e, S e)) : Prop :=
  ∀ ⦃x y⦄, piAgreeOn K x y → (x ∈ A ↔ y ∈ A)

theorem exists_finiteCoordinateSet_dependsOn_symmDiff_lt
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) {A : Set (∀ e, S e)} (hA : MeasurableSet A)
    (hdep : PiSetDependsOn K A) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ B, IsFiniteCoordinateSet B ∧ PiSetDependsOn K B ∧
      Measure.pi mu (B ∆ A) < eps := by
  classical
  letI : ∀ e, Nonempty (S e) := fun e => nonempty_of_isProbabilityMeasure (mu e)
  let base : ∀ e, S e := fun e => Classical.choice inferInstance
  let AK : Set (∀ i : {e : E // e ∈ K}, S i) :=
    piExtendOn K base ⁻¹' A
  have hAK : MeasurableSet AK := hA.preimage (measurable_piExtendOn K base)
  let muK : ∀ i : {e : E // e ∈ K}, Measure (S i) := fun i => mu i
  obtain ⟨BK, hBKfin, hBKerr⟩ :=
    exists_finiteCoordinateSet_symmDiff_lt muK hAK heps
  let B : Set (∀ e, S e) := piRestrict K ⁻¹' BK
  refine ⟨B, hBKfin.preimage_piRestrict K, ?_, ?_⟩
  · intro x y hxy
    have hr : piRestrict K x = piRestrict K y := by
      funext i
      exact hxy i i.property
    simp [B, hr]
  · have hAeq : A = piRestrict K ⁻¹' AK := by
      ext x
      simp only [AK, Set.mem_preimage]
      exact hdep (piExtendOn_agreeOn K base x)
    rw [hAeq, ← Set.preimage_symmDiff]
    exact (measurePreserving_piRestrict mu K).measure_preimage
      (hBKfin.measurableSet.symmDiff hAK).nullMeasurableSet |>.trans_lt hBKerr



theorem measurable_piFunctionalFamilyMax
    (F : Set E → (∀ e, S e) → ℝ) (hF : ∀ K, Measurable (F K)) :
    Measurable (piFunctionalFamilyMax F) := by
  have hrw : piFunctionalFamilyMax F =
      (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty) F := by
    funext x
    rw [piFunctionalFamilyMax, Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun K _ => hF K

theorem measurable_piFunctionalFamilyDisjointMax
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, Measurable (F K)) (hG : ∀ K, Measurable (G K)) :
    Measurable (piFunctionalFamilyDisjointMax F G) := by
  have hrw : piFunctionalFamilyDisjointMax F G =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair x => F pair.1 x * G pair.2 x) := by
    funext x
    rw [piFunctionalFamilyDisjointMax, piFunctionalFamilyDisjointMaxAt,
      Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun pair _ => (hF pair.1).mul (hG pair.2)

theorem measurable_piFunctionalFamilyDisjointMaxAt
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, Measurable (F K)) (hG : ∀ K, Measurable (G K)) :
    Measurable (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalFamilyDisjointMaxAt F G p.1 p.2) := by
  have hrw : (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalFamilyDisjointMaxAt F G p.1 p.2) =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair p => F pair.1 p.1 * G pair.2 p.2) := by
    funext p
    rw [piFunctionalFamilyDisjointMaxAt, Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun pair _ =>
    ((hF pair.1).comp measurable_fst).mul ((hG pair.2).comp measurable_snd)

theorem piFunctionalFamilyMax_le
    (F : Set E → (∀ e, S e) → ℝ) {C : ℝ}
    (hF : ∀ K x, F K x ≤ C) (x : ∀ e, S e) :
    piFunctionalFamilyMax F x ≤ C := by
  unfold piFunctionalFamilyMax
  apply Finset.sup'_le
  intro K _
  exact hF K x

theorem piFunctionalFamilyDisjointMax_le
    (F G : Set E → (∀ e, S e) → ℝ) {C D : ℝ}
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K x, F K x ≤ C) (hG : ∀ K x, G K x ≤ D)
    (x : ∀ e, S e) :
    piFunctionalFamilyDisjointMax F G x ≤ C * D := by
  unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair _
  exact mul_le_mul (hF pair.1 x) (hG pair.2 x) (hG0 pair.2 x)
    (le_trans (hF0 pair.1 x) (hF pair.1 x))

theorem piFunctionalFamilyDisjointMaxAt_le_bound
    (F G : Set E → (∀ e, S e) → ℝ) {C D : ℝ}
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K x, F K x ≤ C) (hG : ∀ K x, G K x ≤ D)
    (x y : ∀ e, S e) :
    piFunctionalFamilyDisjointMaxAt F G x y ≤ C * D := by
  unfold piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair _
  exact mul_le_mul (hF pair.1 x) (hG pair.2 y) (hG0 pair.2 y)
    (le_trans (hF0 pair.1 x) (hF pair.1 x))

theorem tendsto_piFunctionalFamilyMax
    (F : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e)
    (h : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x))) :
    Tendsto (fun n => piFunctionalFamilyMax (F n) x) atTop
      (𝓝 (piFunctionalFamilyMax Flim x)) := by
  unfold piFunctionalFamilyMax
  exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun K _ => h K)

theorem tendsto_piFunctionalFamilyDisjointMax
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e)
    (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hG : ∀ K, Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x))) :
    Tendsto (fun n => piFunctionalFamilyDisjointMax (F n) (G n) x) atTop
      (𝓝 (piFunctionalFamilyDisjointMax Flim Glim x)) := by
  unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
  exact Tendsto.finset_sup'_nhds_apply (disjointCoordinatePairs_nonempty (E := E))
    (fun pair _ => (hF pair.1).mul (hG pair.2))

theorem tendsto_piFunctionalFamilyDisjointMaxAt
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ) (x y : ∀ e, S e)
    (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hG : ∀ K, Tendsto (fun n => G n K y) atTop (𝓝 (Glim K y))) :
    Tendsto (fun n => piFunctionalFamilyDisjointMaxAt (F n) (G n) x y) atTop
      (𝓝 (piFunctionalFamilyDisjointMaxAt Flim Glim x y)) := by
  unfold piFunctionalFamilyDisjointMaxAt
  exact Tendsto.finset_sup'_nhds_apply (disjointCoordinatePairs_nonempty (E := E))
    (fun pair _ => (hF pair.1).mul (hG pair.2))

theorem measurableFamilyBKR_of_bounded_ae_limit
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ)
    (C D : ℝ) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hFm : ∀ n K, Measurable (F n K))
    (hGm : ∀ n K, Measurable (G n K))
    (hFlimm : ∀ K, Measurable (Flim K))
    (hGlimm : ∀ K, Measurable (Glim K))
    (hF0 : ∀ n K x, 0 ≤ F n K x)
    (hG0 : ∀ n K x, 0 ≤ G n K x)
    (hFlim0 : ∀ K x, 0 ≤ Flim K x)
    (hGlim0 : ∀ K x, 0 ≤ Glim K x)
    (hFC : ∀ n K x, F n K x ≤ C)
    (hGD : ∀ n K x, G n K x ≤ D)
    (hFlimC : ∀ K x, Flim K x ≤ C)
    (hGlimD : ∀ K x, Glim K x ≤ D)
    (hconvF : ∀ K, ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hconvG : ∀ K, ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x)))
    (hineq : ∀ n,
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax (F n) (G n) x)
          ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (F n) x)
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (G n) x)
            ∂Measure.pi mu ∧
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt (F n) (G n) p.1 p.2)
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax (F n) x * piFunctionalFamilyMax (G n) x)
            ∂Measure.pi mu) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax Flim Glim x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x)
          ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x)
          ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt Flim Glim p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax Flim x * piFunctionalFamilyMax Glim x)
          ∂Measure.pi mu := by
  have hconvFall : ∀ᵐ x ∂Measure.pi mu, ∀ K,
      Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)) :=
    ae_all_iff.mpr hconvF
  have hconvGall : ∀ᵐ x ∂Measure.pi mu, ∀ K,
      Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x)) :=
    ae_all_iff.mpr hconvG
  have hlimMaxF : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal (piFunctionalFamilyMax (F n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyMax Flim x))) := by
    filter_upwards [hconvFall] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyMax F Flim x hx)
  have hlimMaxG : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal (piFunctionalFamilyMax (G n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyMax Glim x))) := by
    filter_upwards [hconvGall] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyMax G Glim x hx)
  have hlimDisjoint : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyDisjointMax (F n) (G n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyDisjointMax Flim Glim x))) := by
    filter_upwards [hconvFall, hconvGall] with x hxF hxG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyDisjointMax F G Flim Glim x hxF hxG)
  have hlimSameProduct : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyMax (F n) x * piFunctionalFamilyMax (G n) x)) atTop
        (𝓝 (ENNReal.ofReal
          (piFunctionalFamilyMax Flim x * piFunctionalFamilyMax Glim x))) := by
    filter_upwards [hconvFall, hconvGall] with x hxF hxG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_piFunctionalFamilyMax F Flim x hxF).mul
        (tendsto_piFunctionalFamilyMax G Glim x hxG))
  have hconvFfst : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu), ∀ K,
      Tendsto (fun n => F n K p.1) atTop (𝓝 (Flim K p.1)) :=
    Measure.quasiMeasurePreserving_fst.ae hconvFall
  have hconvGsnd : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu), ∀ K,
      Tendsto (fun n => G n K p.2) atTop (𝓝 (Glim K p.2)) :=
    Measure.quasiMeasurePreserving_snd.ae hconvGall
  have hlimDual : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu),
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyDisjointMaxAt (F n) (G n) p.1 p.2)) atTop
        (𝓝 (ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt Flim Glim p.1 p.2))) := by
    filter_upwards [hconvFfst, hconvGsnd] with p hpF hpG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyDisjointMaxAt F G Flim Glim p.1 p.2 hpF hpG)
  have hfinC : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal C ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinD : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal D ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinCD : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal (C * D)
      ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinCDprod : (∫⁻ _ : (∀ e, S e) × (∀ e, S e),
      ENNReal.ofReal (C * D) ∂(Measure.pi mu).prod (Measure.pi mu)) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have tMaxF := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal C)
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (F n) (hFm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyMax_le (F n) (hFC n) x)) hfinC hlimMaxF
  have tMaxG := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal D)
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (G n) (hGm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyMax_le (G n) (hGD n) x)) hfinD hlimMaxG
  have tDisjoint := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMax (F n) (G n) (hFm n) (hGm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyDisjointMax_le (F n) (G n)
        (hF0 n) (hG0 n) (hFC n) (hGD n) x)) hfinCD hlimDisjoint
  have tSameProduct := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      ((measurable_piFunctionalFamilyMax (F n) (hFm n)).mul
        (measurable_piFunctionalFamilyMax (G n) (hGm n))))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul (piFunctionalFamilyMax_le (F n) (hFC n) x)
        (piFunctionalFamilyMax_le (G n) (hGD n) x)
        (piFunctionalFamilyMax_nonneg (G n) (hG0 n) x)
        hC0))
    hfinCD hlimSameProduct
  have tDual := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) × (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMaxAt (F n) (G n)
        (hFm n) (hGm n)))
    (fun n => ae_of_all _ fun p => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyDisjointMaxAt_le_bound (F n) (G n)
        (hF0 n) (hG0 n) (hFC n) (hGD n) p.1 p.2)) hfinCDprod hlimDual
  constructor
  · have hMaxFtop : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x)
        ∂Measure.pi mu) ≠ ∞ := by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      calc
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x) ∂Measure.pi mu) ≤
            ∫⁻ _ : (∀ e, S e), ENNReal.ofReal C ∂Measure.pi mu :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (piFunctionalFamilyMax_le Flim hFlimC x)
        _ = ENNReal.ofReal C := by simp
    have hMaxGtop : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x)
        ∂Measure.pi mu) ≠ ∞ := by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      calc
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x) ∂Measure.pi mu) ≤
            ∫⁻ _ : (∀ e, S e), ENNReal.ofReal D ∂Measure.pi mu :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (piFunctionalFamilyMax_le Glim hGlimD x)
        _ = ENNReal.ofReal D := by simp
    exact le_of_tendsto_of_tendsto tDisjoint
      (ENNReal.Tendsto.mul tMaxF (Or.inr hMaxGtop)
        tMaxG (Or.inr hMaxFtop))
      (Eventually.of_forall fun n => (hineq n).1)
  · exact le_of_tendsto_of_tendsto tDual tSameProduct
      (Eventually.of_forall fun n => (hineq n).2)

universe w



structure FiniteCoordinateFactorOn (K : Set E) (h : (∀ e, S e) → ℝ) where
  T : E → Type w
  fintype_T : ∀ e, Fintype (T e)
  measurableSpace_T : ∀ e, MeasurableSpace (T e)
  measurableSingleton_T : ∀ e, MeasurableSingletonClass (T e)
  q : ∀ e, S e → T e
  measurable_q : ∀ e, Measurable (q e)
  H : (∀ e, T e) → ℝ
  nonneg_H : ∀ y, 0 ≤ H y
  dependsOn_H : ∀ ⦃x y⦄, piAgreeOn K x y → H x = H y
  eq_comp : h = fun x => H (fun e => q e (x e))

structure FiniteCoordinateSetData (A : Set (∀ e, S e)) where
  n : E → ℕ
  q : ∀ e, S e → Fin (n e)
  B : Set (∀ e, Fin (n e))
  measurable_q : ∀ e, Measurable (q e)
  eq_preimage : A = (fun x e => q e (x e)) ⁻¹' B

noncomputable def finiteCoordinateSetData {A : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) : FiniteCoordinateSetData A :=
  Classical.choice <| by
    rcases hA with ⟨n, q, B, hq, hAeq⟩
    exact ⟨
      { n := n
        q := q
        B := B
        measurable_q := hq
        eq_preimage := hAeq }⟩

noncomputable def finiteQuotientRepresentative
    [∀ e, Nonempty (S e)] {n : E → ℕ} (q : ∀ e, S e → Fin (n e))
    (e : E) (t : Fin (n e)) : S e := by
  classical
  exact if h : ∃ x, q e x = t then Classical.choose h else Classical.choice inferInstance

theorem finiteQuotientRepresentative_rightInverse
    [∀ e, Nonempty (S e)] {n : E → ℕ} (q : ∀ e, S e → Fin (n e))
    (e : E) (x : S e) :
    q e (finiteQuotientRepresentative q e (q e x)) = q e x := by
  classical
  let hex : ∃ y, q e y = q e x := ⟨x, rfl⟩
  rw [finiteQuotientRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

noncomputable def finiteCoordinateFactorOn_piece
    [∀ e, Nonempty (S e)] (K : Set E) {A : Set (∀ e, S e)}
    (hAfin : IsFiniteCoordinateSet A) (hAdep : PiSetDependsOn K A)
    (c : ℝ) (hc : 0 ≤ c) :
    FiniteCoordinateFactorOn.{u, v, 0} K (A.indicator fun _ => c) := by
  classical
  let data := finiteCoordinateSetData hAfin
  let n := data.n
  let q := data.q
  let B := data.B
  have hq : ∀ e, Measurable (q e) := data.measurable_q
  have hAeq : A = (fun x e => q e (x e)) ⁻¹' B := data.eq_preimage
  let base : ∀ e, S e := fun e => Classical.choice inferInstance
  let decode : (∀ e, Fin (n e)) → (∀ e, S e) := fun y e =>
    finiteQuotientRepresentative q e (y e)
  let decodeK : (∀ e, Fin (n e)) → (∀ e, S e) := fun y e =>
    if he : e ∈ K then decode y e else base e
  let H : (∀ e, Fin (n e)) → ℝ := fun y =>
    if decodeK y ∈ A then c else 0
  refine
    { T := fun e => Fin (n e)
      fintype_T := fun _ => inferInstance
      measurableSpace_T := fun _ => inferInstance
      measurableSingleton_T := fun _ => inferInstance
      q := q
      measurable_q := hq
      H := H
      nonneg_H := fun y => by dsimp [H]; split <;> positivity
      dependsOn_H := ?_
      eq_comp := ?_ }
  · intro y z hyz
    have hdecode : decodeK y = decodeK z := by
      funext e
      by_cases he : e ∈ K
      · simp [decodeK, decode, he, hyz e he]
      · simp [decodeK, he]
    unfold H
    rw [hdecode]
  · funext x
    have hqdecode : (fun e => q e (decode (fun e => q e (x e)) e)) =
        (fun e => q e (x e)) := by
      funext e
      exact finiteQuotientRepresentative_rightInverse q e (x e)
    have hfull : decode (fun e => q e (x e)) ∈ A ↔ x ∈ A := by
      rw [hAeq]
      simp only [Set.mem_preimage]
      rw [hqdecode]
    have hagree : piAgreeOn K (decode (fun e => q e (x e)))
        (decodeK (fun e => q e (x e))) := by
      intro e he
      simp [decodeK, he]
    have hK : decodeK (fun e => q e (x e)) ∈ A ↔ x ∈ A :=
      (hAdep hagree).symm.trans hfull
    by_cases hx : x ∈ A
    · have hdecodeMem : decodeK (fun e => q e (x e)) ∈ A := hK.mpr hx
      simp [Set.indicator_apply, H, hx, hdecodeMem]
    · have hdecodeNotMem : decodeK (fun e => q e (x e)) ∉ A :=
        fun h => hx (hK.mp h)
      simp [Set.indicator_apply, H, hx, hdecodeNotMem]

universe z wF wG

noncomputable def finiteCoordinateFactorOn_sup'
    {I : Type z} [Fintype I] [DecidableEq I]
    (hI : (Finset.univ : Finset I).Nonempty) (K : Set E)
    (a : I → (∀ e, S e) → ℝ)
    (ha : ∀ i, FiniteCoordinateFactorOn.{u, v, w} K (a i)) :
    FiniteCoordinateFactorOn.{u, v, max w z} K
      (fun x => (Finset.univ : Finset I).sup' hI (fun i => a i x)) := by
  classical
  letI componentFintype : ∀ i e, Fintype ((ha i).T e) :=
    fun i e => (ha i).fintype_T e
  letI componentMeasurableSpace : ∀ i e, MeasurableSpace ((ha i).T e) :=
    fun i e => (ha i).measurableSpace_T e
  letI componentMeasurableSingleton :
      ∀ i e, MeasurableSingletonClass ((ha i).T e) :=
    fun i e => (ha i).measurableSingleton_T e
  let T : E → Type (max w z) := fun e => ∀ i, (ha i).T e
  let instF : ∀ e, Fintype (T e) := fun _ => inferInstance
  let instM : ∀ e, MeasurableSpace (T e) := fun _ => inferInstance
  let instS : ∀ e, MeasurableSingletonClass (T e) := fun _ => inferInstance
  let q : ∀ e, S e → T e := fun e x i => (ha i).q e x
  let H : (∀ e, T e) → ℝ := fun y =>
    (Finset.univ : Finset I).sup' hI fun i =>
      (ha i).H (fun e => y e i)
  refine
    { T := T
      fintype_T := instF
      measurableSpace_T := instM
      measurableSingleton_T := instS
      q := q
      measurable_q := ?_
      H := H
      nonneg_H := ?_
      dependsOn_H := ?_
      eq_comp := ?_ }
  · intro e
    apply measurable_pi_lambda
    intro i
    exact (ha i).measurable_q e
  · intro y
    unfold H
    let i := Classical.choose hI
    calc
      0 ≤ (ha i).H (fun e => y e i) := (ha i).nonneg_H _
      _ ≤ (Finset.univ : Finset I).sup' hI
          (fun j => (ha j).H (fun e => y e j)) :=
        Finset.le_sup' (fun j : I => (ha j).H (fun e => y e j))
          (Finset.mem_univ i)
  · intro y z hyz
    unfold H
    apply congrArg ((Finset.univ : Finset I).sup' hI)
    funext i
    apply (ha i).dependsOn_H
    intro e he
    exact congrFun (hyz e he) i
  · funext x
    unfold H q
    apply congrArg ((Finset.univ : Finset I).sup' hI)
    funext i
    exact congrFun (ha i).eq_comp x

theorem functionalFamilyBKR_of_finiteCoordinateFactors_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : Set E → (∀ e, S e) → ℝ)
    (fF : ∀ K, FiniteCoordinateFactorOn.{u, v, wF} K (F K))
    (fG : ∀ K, FiniteCoordinateFactorOn.{u, v, wG} K (G K))
    (hF0 : ∀ K y, 0 ≤ (fF K).H y) (hG0 : ∀ K y, 0 ≤ (fG K).H y) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi mu := by
  classical
  letI fFComponentFintype : ∀ K e, Fintype ((fF K).T e) :=
    fun K e => (fF K).fintype_T e
  letI fGComponentFintype : ∀ K e, Fintype ((fG K).T e) :=
    fun K e => (fG K).fintype_T e
  letI fFComponentMeasurableSpace : ∀ K e, MeasurableSpace ((fF K).T e) :=
    fun K e => (fF K).measurableSpace_T e
  letI fGComponentMeasurableSpace : ∀ K e, MeasurableSpace ((fG K).T e) :=
    fun K e => (fG K).measurableSpace_T e
  letI fFComponentMeasurableSingleton :
      ∀ K e, MeasurableSingletonClass ((fF K).T e) :=
    fun K e => (fF K).measurableSingleton_T e
  letI fGComponentMeasurableSingleton :
      ∀ K e, MeasurableSingletonClass ((fG K).T e) :=
    fun K e => (fG K).measurableSingleton_T e
  let T : E → Type (max u wF wG) := fun e =>
    ((K : Set E) → (fF K).T e) × ((K : Set E) → (fG K).T e)
  letI instF : ∀ e, Fintype (T e) := fun _ => inferInstance
  letI instM : ∀ e, MeasurableSpace (T e) := fun _ => inferInstance
  letI instS : ∀ e, MeasurableSingletonClass (T e) := fun _ => inferInstance
  let q : ∀ e, S e → T e := fun e x =>
    (fun K => (fF K).q e x, fun K => (fG K).q e x)
  let Fbar : Set E → (∀ e, T e) → ℝ := fun K y =>
    (fF K).H (fun e => (y e).1 K)
  let Gbar : Set E → (∀ e, T e) → ℝ := fun K y =>
    (fG K).H (fun e => (y e).2 K)
  have hq : ∀ e, Measurable (q e) := by
    intro e
    apply Measurable.prod
    · apply measurable_pi_lambda
      intro K
      exact (fF K).measurable_q e
    · apply measurable_pi_lambda
      intro K
      exact (fG K).measurable_q e
  have hFbar0 : ∀ K y, 0 ≤ Fbar K y := fun K y => hF0 K _
  have hGbar0 : ∀ K y, 0 ≤ Gbar K y := fun K y => hG0 K _
  have hFbarDep : ∀ K, PiDependsOn K (Fbar K) := by
    intro K y z hyz
    apply (fF K).dependsOn_H
    intro e he
    exact congrArg (fun z => z.1 K) (hyz e he)
  have hGbarDep : ∀ K, PiDependsOn K (Gbar K) := by
    intro K y z hyz
    apply (fG K).dependsOn_H
    intro e he
    exact congrArg (fun z => z.2 K) (hyz e he)
  have hcore := @functionalFamilyBKR_finiteFactor_and_dual
    E _ _ S _ T instM instF instS mu _ q hq Fbar Gbar
      hFbar0 hGbar0 hFbarDep hGbarDep
  have hFcomp : ∀ K x, Fbar K (fun e => q e (x e)) = F K x := by
    intro K x
    exact (congrFun (fF K).eq_comp x).symm
  have hGcomp : ∀ K x, Gbar K (fun e => q e (x e)) = G K x := by
    intro K x
    exact (congrFun (fG K).eq_comp x).symm
  simpa only [piFunctionalFamilyDisjointMax,
    piFunctionalFamilyDisjointMaxAt, piFunctionalFamilyMax,
    hFcomp, hGcomp] using hcore

theorem FiniteCoordinateFactorOn.measurable
    {K : Set E} {h : (∀ e, S e) → ℝ} (f : FiniteCoordinateFactorOn K h) :
    Measurable h := by
  letI : ∀ e, Fintype (f.T e) := f.fintype_T
  letI : ∀ e, MeasurableSpace (f.T e) := f.measurableSpace_T
  letI : ∀ e, MeasurableSingletonClass (f.T e) := f.measurableSingleton_T
  rw [f.eq_comp]
  exact (measurable_of_finite f.H).comp
    (measurable_pi_lambda _ fun e =>
      (f.measurable_q e).comp (measurable_pi_apply e))

theorem FiniteCoordinateFactorOn.nonneg
    {K : Set E} {h : (∀ e, S e) → ℝ} (f : FiniteCoordinateFactorOn K h) :
    ∀ x, 0 ≤ h x := by
  intro x
  rw [f.eq_comp]
  exact f.nonneg_H _

theorem exists_finiteFactor_approx_simple
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) (s : SimpleFunc (∀ e, S e) ℝ)
    (hs0 : ∀ x, 0 ≤ s x) {C : ℝ} (hsC : ∀ x, s x ≤ C)
    (hsdep : PiDependsOn K s) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ (t : (∀ e, S e) → ℝ)
      (f : FiniteCoordinateFactorOn.{u, v, 0} K t),
      (∀ x, t x ≤ C) ∧
      Measure.pi mu {x | t x ≠ s x} < eps := by
  classical
  letI : ∀ e, Nonempty (S e) := fun e => nonempty_of_isProbabilityMeasure (mu e)
  let values : Finset ℝ := insert 0 s.range
  let I := {v : ℝ // v ∈ values}
  letI : Fintype I := values.fintypeCoeSort
  have hI : (Finset.univ : Finset I).Nonempty :=
    ⟨⟨0, Finset.mem_insert_self 0 s.range⟩, Finset.mem_univ _⟩
  have hvalue0 : ∀ v : I, 0 ≤ v.1 := by
    intro v
    rcases Finset.mem_insert.mp v.2 with hv | hv
    · simpa [hv]
    · obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hv
      simpa [← hx] using hs0 x
  have hvalueC : ∀ v : I, v.1 ≤ C := by
    intro v
    rcases Finset.mem_insert.mp v.2 with hv | hv
    · simpa [hv] using le_trans (hs0 (Classical.choice
          (nonempty_of_isProbabilityMeasure (Measure.pi mu)))) (hsC _)
    · obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hv
      simpa [← hx] using hsC x
  obtain ⟨delta, hdelta0, hdeltasum⟩ :=
    ENNReal.exists_pos_sum_of_countable' heps.ne' I
  let A : I → Set (∀ e, S e) := fun v => {x | s x = v.1}
  have hAmeas : ∀ v, MeasurableSet (A v) := fun v => by
    change MeasurableSet (s ⁻¹' ({v.1} : Set ℝ))
    exact s.measurableSet_fiber v.1
  have hAdep : ∀ v, PiSetDependsOn K (A v) := by
    intro v x y hxy
    have hsxy := hsdep hxy
    simp only [A, Set.mem_setOf_eq]
    rw [hsxy]
  have happ : ∀ v : I, ∃ B,
      IsFiniteCoordinateSet B ∧ PiSetDependsOn K B ∧
        Measure.pi mu (B ∆ A v) < delta v := fun v =>
    exists_finiteCoordinateSet_dependsOn_symmDiff_lt
      mu K (hAmeas v) (hAdep v) (hdelta0 v)
  choose B hBfin hBdep hBerr using happ
  let a : I → (∀ e, S e) → ℝ := fun v =>
    (B v).indicator (fun _ => v.1)
  let fa : ∀ v, FiniteCoordinateFactorOn.{u, v, 0} K (a v) := fun v =>
    finiteCoordinateFactorOn_piece K (hBfin v) (hBdep v) v.1 (hvalue0 v)
  let t : (∀ e, S e) → ℝ := fun x =>
    (Finset.univ : Finset I).sup' hI (fun v => a v x)
  let f : FiniteCoordinateFactorOn.{u, v, 0} K t :=
    finiteCoordinateFactorOn_sup' hI K a fa
  refine ⟨t, f, ?_, ?_⟩
  · intro x
    unfold t
    apply Finset.sup'_le
    intro v _
    by_cases hv : x ∈ B v
    · simpa [a, hv] using hvalueC v
    · simpa [a, hv] using le_trans (hvalue0 v) (hvalueC v)
  · let Bad : Set (∀ e, S e) := ⋃ v ∈ (Finset.univ : Finset I), B v ∆ A v
    have hsubset : {x | t x ≠ s x} ⊆ Bad := by
      intro x hx
      by_contra hxBad
      have hmatch : ∀ v : I, (x ∈ B v ↔ s x = v.1) := by
        intro v
        have hn : x ∉ B v ∆ A v := by
          intro hv
          apply hxBad
          exact Set.mem_iUnion₂.mpr ⟨v, Finset.mem_univ v, hv⟩
        rw [Set.mem_symmDiff] at hn
        simp only [A, Set.mem_setOf_eq] at hn
        tauto
      have ht : t x = s x := by
        apply le_antisymm
        · unfold t
          apply Finset.sup'_le
          intro v _
          by_cases hv : x ∈ B v
          · simpa [a, hv, (hmatch v).mp hv]
          · simpa [a, hv] using hs0 x
        · let v : I := ⟨s x, Finset.mem_insert_of_mem
              (SimpleFunc.mem_range.mpr ⟨x, rfl⟩)⟩
          calc
            s x = (v : ℝ) := rfl
            _ = a v x := by
              have hv : x ∈ B v := (hmatch v).mpr rfl
              exact (Set.indicator_of_mem hv (fun _ => (v : ℝ))).symm
            _ ≤ t x := Finset.le_sup' (fun z : I => a z x) (Finset.mem_univ v)
      exact hx ht
    calc
      Measure.pi mu {x | t x ≠ s x} ≤ Measure.pi mu Bad := measure_mono hsubset
      _ ≤ ∑ v ∈ (Finset.univ : Finset I), Measure.pi mu (B v ∆ A v) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ (Finset.univ : Finset I), delta v :=
        Finset.sum_le_sum fun v _ => (hBerr v).le
      _ ≤ ∑' v : I, delta v := ENNReal.sum_le_tsum _
      _ < eps := hdeltasum

theorem exists_finiteFactor_approx_bounded
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) (h : (∀ e, S e) → ℝ) (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) {C : ℝ} (hhC : ∀ x, h x ≤ C)
    (hhdep : PiDependsOn K h) :
    ∃ (t : ℕ → (∀ e, S e) → ℝ)
        (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ C) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (h x)) := by
  classical
  let simple : ℕ → SimpleFunc (∀ e, S e) ℝ := fun n =>
    SimpleFunc.approxOn h hh (Set.range h ∪ {0}) 0 (by simp) n
  have hs0 : ∀ n x, 0 ≤ simple n x := by
    intro n x
    exact SimpleFunc.approxOn_range_nonneg hh0 n x
  have hsC : ∀ n x, simple n x ≤ C := by
    intro n x
    have hx := SimpleFunc.approxOn_mem hh (s := Set.range h ∪ {0})
      (y₀ := 0) (by simp) n x
    rcases hx with hx | hx
    · obtain ⟨y, hy⟩ := hx
      rw [← hy]
      exact hhC y
    · rw [Set.mem_singleton_iff.mp hx]
      exact le_trans (hh0 x) (hhC x)
  have hsdep : ∀ n, PiDependsOn K (simple n) := by
    intro n x y hxy
    have hhy := hhdep hxy
    simp only [simple, SimpleFunc.approxOn, SimpleFunc.coe_comp, Function.comp_apply]
    rw [hhy]
  obtain ⟨eps, heps0, hepssum⟩ :=
    ENNReal.exists_pos_sum_of_countable' (by norm_num : (1 : ℝ≥0∞) ≠ 0) ℕ
  have happ : ∀ n, ∃ (t : (∀ e, S e) → ℝ)
      (f : FiniteCoordinateFactorOn.{u, v, 0} K t),
      (∀ x, t x ≤ C) ∧ Measure.pi mu {x | t x ≠ simple n x} < eps n :=
    fun n => exists_finiteFactor_approx_simple mu K (simple n)
      (hs0 n) (hsC n) (hsdep n) (heps0 n)
  choose t f htC herr using happ
  refine ⟨t, f, htC, ?_⟩
  have herrsum : (∑' n, Measure.pi mu {x | t n x ≠ simple n x}) ≠ ∞ := by
    apply ne_top_of_lt
    exact (ENNReal.tsum_le_tsum fun n => (herr n).le).trans_lt hepssum
  have heventually := ae_eventually_notMem herrsum
  filter_upwards [heventually] with x hx
  have hsconv : Tendsto (fun n => simple n x) atTop (𝓝 (h x)) :=
    SimpleFunc.tendsto_approxOn hh (s := Set.range h ∪ {0})
      (y₀ := 0) (by simp)
        (subset_closure (Set.mem_union_left {0} ⟨x, rfl⟩))
  apply hsconv.congr'
  filter_upwards [hx] with n hn
  exact (not_not.mp hn).symm

theorem measurableFamilyBKR_bounded_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : Set E → (∀ e, S e) → ℝ)
    (hFm : ∀ K, Measurable (F K)) (hGm : ∀ K, Measurable (G K))
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hFdep : ∀ K, PiDependsOn K (F K))
    (hGdep : ∀ K, PiDependsOn K (G K))
    (C D : ℝ) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hFC : ∀ K x, F K x ≤ C) (hGD : ∀ K x, G K x ≤ D) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi mu := by
  classical
  have happF : ∀ K, ∃ (t : ℕ → (∀ e, S e) → ℝ)
      (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ C) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (F K x)) :=
    fun K => exists_finiteFactor_approx_bounded mu K (F K) (hFm K)
      (hF0 K) (hFC K) (hFdep K)
  have happG : ∀ K, ∃ (t : ℕ → (∀ e, S e) → ℝ)
      (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ D) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (G K x)) :=
    fun K => exists_finiteFactor_approx_bounded mu K (G K) (hGm K)
      (hG0 K) (hGD K) (hGdep K)
  choose Fn fFn hFnC hconvF using happF
  choose Gn fGn hGnD hconvG using happG
  let Fapp : ℕ → Set E → (∀ e, S e) → ℝ := fun n K => Fn K n
  let Gapp : ℕ → Set E → (∀ e, S e) → ℝ := fun n K => Gn K n
  have hineq : ∀ n,
      (∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyDisjointMax (Fapp n) (Gapp n) x)
          ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Fapp n) x)
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Gapp n) x)
            ∂Measure.pi mu ∧
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt (Fapp n) (Gapp n) p.1 p.2)
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax (Fapp n) x *
              piFunctionalFamilyMax (Gapp n) x)
            ∂Measure.pi mu := by
    intro n
    exact functionalFamilyBKR_of_finiteCoordinateFactors_and_dual
      mu (Fapp n) (Gapp n) (fun K => fFn K n) (fun K => fGn K n)
        (fun K => (fFn K n).nonneg_H) (fun K => (fGn K n).nonneg_H)
  apply measurableFamilyBKR_of_bounded_ae_limit mu Fapp Gapp F G
    C D hC0 hD0
  · intro n K
    exact (fFn K n).measurable
  · intro n K
    exact (fGn K n).measurable
  · exact hFm
  · exact hGm
  · intro n K
    exact (fFn K n).nonneg
  · intro n K
    exact (fGn K n).nonneg
  · exact hF0
  · exact hG0
  · intro n K
    exact hFnC K n
  · intro n K
    exact hGnD K n
  · exact hFC
  · exact hGD
  · intro K
    exact hconvF K
  · intro K
    exact hconvG K
  · exact hineq

end StatMech.FrontierA
