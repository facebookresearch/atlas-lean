/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Code.BeffaraDC.LongRectangleTorusCover
import Code.FK.FKG

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.Onsager
open StatMech.Universality




noncomputable def torusAmbientPMF (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (TorusAmbientConfig L) :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal (torusAmbientProbability L p q omega)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [torusAmbientProbability_sum_one L hp hp1 hq,
          ENNReal.ofReal_one]
      · intro omega _
        exact (div_pos (torusAmbientFKWeight_pos L omega hp hp1 hq)
          (torusAmbientPartition_pos L hp hp1 hq)).le

@[simp] theorem torusAmbientPMF_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    torusAmbientPMF L hp hp1 hq omega =
      ENNReal.ofReal (torusAmbientProbability L p q omega) :=
  PMF.ofFintype_apply _ _


noncomputable def torusAmbientMeasure (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Measure (TorusAmbientConfig L) :=
  (torusAmbientPMF L hp hp1 hq).toMeasure

instance torusAmbientMeasure_isProbabilityMeasure
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    IsProbabilityMeasure (torusAmbientMeasure L hp hp1 hq) := by
  unfold torusAmbientMeasure
  infer_instance


theorem torusAmbientMeasure_singleton (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    torusAmbientMeasure L hp hp1 hq {omega} =
      ENNReal.ofReal (torusAmbientProbability L p q omega) := by
  unfold torusAmbientMeasure
  rw [PMF.toMeasure_apply_singleton _ omega (measurableSet_singleton omega),
    torusAmbientPMF_apply]


theorem torusAmbientProbability_nonneg (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    0 ≤ torusAmbientProbability L p q omega :=
  (div_pos (torusAmbientFKWeight_pos L omega hp hp1 hq)
    (torusAmbientPartition_pos L hp hp1 hq)).le


theorem torusAmbientMeasure_real_eq_indicator_sum
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusAmbientMeasure L hp hp1 hq).real A =
      ∑ omega : TorusAmbientConfig L,
        torusAmbientProbability L p q omega *
          A.indicator (fun _ => (1 : ℝ)) omega := by
  rw [Measure.real, torusAmbientMeasure, PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro omega _homega
    by_cases hmem : omega ∈ A
    · simp only [Set.indicator_of_mem hmem, torusAmbientPMF_apply]
      rw [ENNReal.toReal_ofReal
        (torusAmbientProbability_nonneg L hp hp1 hq omega)]
      simp
    · simp [Set.indicator, hmem]
  · intro omega _homega
    by_cases hmem : omega ∈ A <;>
      simp [Set.indicator, hmem, torusAmbientPMF_apply]


theorem torusAmbientConfigExtend_sup
    (L : ℕ) [Fact (2 < L)] (omega eta : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (omega ⊔ eta) =
      torusAmbientConfigExtend L omega ⊔
        torusAmbientConfigExtend L eta := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset <;>
    simp [torusAmbientConfigExtend, he]


theorem torusAmbientConfigExtend_inf
    (L : ℕ) [Fact (2 < L)] (omega eta : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (omega ⊓ eta) =
      torusAmbientConfigExtend L omega ⊓
        torusAmbientConfigExtend L eta := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset <;>
    simp [torusAmbientConfigExtend, he]



theorem torusAmbientFKWeight_logSupermodular
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega eta : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q omega *
        torusAmbientFKWeight L p q eta ≤
      torusAmbientFKWeight L p q (omega ⊔ eta) *
        torusAmbientFKWeight L p q (omega ⊓ eta) := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_sup, torusAmbientConfigExtend_inf]
  exact FK.fkWeight_logSupermodular (onsTorusGraph L) hp hp1 hq _ _



theorem torusAmbientProbability_FKGLatticeCondition
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FKGLatticeCondition (torusAmbientProbability L p q) := by
  have hZpos : 0 < torusAmbientPartition L p q :=
    torusAmbientPartition_pos L hp hp1
      (lt_of_lt_of_le zero_lt_one hq)
  intro omega eta
  simp only [torusAmbientProbability]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr
    (torusAmbientFKWeight_logSupermodular L hp hp1 hq omega eta)


theorem torusAmbientMeasure_positivelyAssociated
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q) :
    PositivelyAssociated (torusAmbientMeasure L hp hp1 hq0) := by
  intro A B hA hB
  rw [torusAmbientMeasure_real_eq_indicator_sum,
    torusAmbientMeasure_real_eq_indicator_sum,
    torusAmbientMeasure_real_eq_indicator_sum]
  exact fkg_inequality_events
    (torusAmbientProbability_nonneg L hp hp1 hq0)
    (torusAmbientProbability_sum_one L hp hp1 hq0)
    (torusAmbientProbability_FKGLatticeCondition L hp hp1 hq)
    hA hB





noncomputable def torusPlanarPushforward (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Measure (ConfigSpace (Sym2 (Site 2))) :=
  Measure.map (torusPlanarPullback L) (torusAmbientMeasure L hp hp1 hq)



theorem measurable_torusPlanarPullback (L : ℕ) [Fact (2 < L)] :
    Measurable (torusPlanarPullback L) :=
  measurable_of_finite _




theorem measurableEmbedding_torusPlanarPullback
    (L : ℕ) [Fact (2 < L)] :
    MeasurableEmbedding (torusPlanarPullback L) := by
  refine MeasurableEmbedding.mk (torusPlanarPullback_injective L)
    (measurable_torusPlanarPullback L) ?_
  intro A _hA
  exact (Set.toFinite A).image (torusPlanarPullback L) |>.measurableSet

instance torusPlanarPushforward_isProbabilityMeasure
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    IsProbabilityMeasure (torusPlanarPushforward L hp hp1 hq) := by
  unfold torusPlanarPushforward
  exact Measure.isProbabilityMeasure_map
    (measurable_torusPlanarPullback L).aemeasurable



theorem torusPlanarPushforward_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (Site 2)))) :
    torusPlanarPushforward L hp hp1 hq B =
      torusAmbientMeasure L hp hp1 hq
        (torusPlanarPullback L ⁻¹' B) := by
  exact (measurableEmbedding_torusPlanarPullback L).map_apply
    (torusAmbientMeasure L hp hp1 hq) B


theorem torusPlanarPushforward_real_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (Site 2)))) :
    (torusPlanarPushforward L hp hp1 hq).real B =
      (torusAmbientMeasure L hp hp1 hq).real
        (torusPlanarPullback L ⁻¹' B) := by
  simp only [Measure.real, torusPlanarPushforward_apply]



theorem torusPlanarPushforward_image_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    torusPlanarPushforward L hp hp1 hq
        (torusPlanarPullback L '' A) =
      torusAmbientMeasure L hp hp1 hq A := by
  rw [torusPlanarPushforward_apply]
  rw [Set.preimage_image_eq A (torusPlanarPullback_injective L)]


theorem torusPlanarPushforward_real_image_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusPlanarPushforward L hp hp1 hq).real
        (torusPlanarPullback L '' A) =
      (torusAmbientMeasure L hp hp1 hq).real A := by
  simp only [Measure.real, torusPlanarPushforward_image_apply]


theorem torusPlanarPushforward_planarLiftEvent_apply
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    torusPlanarPushforward L hp hp1 hq
        (bdcTorusPlanarLiftEvent L A) =
      torusAmbientMeasure L hp hp1 hq A := by
  exact torusPlanarPushforward_image_apply L hp hp1 hq A


theorem torusPlanarPushforward_real_planarLiftEvent_apply
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusPlanarPushforward L hp hp1 hq).real
        (bdcTorusPlanarLiftEvent L A) =
      (torusAmbientMeasure L hp hp1 hq).real A := by
  exact torusPlanarPushforward_real_image_apply L hp hp1 hq A




theorem monotone_torusPlanarPullback (L : ℕ) [Fact (2 < L)] :
    Monotone (torusPlanarPullback L) := by
  intro omega eta homega e
  unfold torusPlanarPullback torusAmbientConfigExtend
  split_ifs with he
  · exact homega ⟨Sym2.map (torusReduceSite L) e, he⟩
  · exact le_rfl


theorem torusPlanarPullback_preimage_isIncreasing
    (L : ℕ) [Fact (2 < L)]
    {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A) :
    IsIncreasing (torusPlanarPullback L ⁻¹' A) := by
  intro omega eta homegaeta homega
  exact hA (monotone_torusPlanarPullback L homegaeta) homega



theorem torusPlanarPushforward_positivelyAssociated
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hpa : PositivelyAssociated (torusAmbientMeasure L hp hp1 hq)) :
    PositivelyAssociated (torusPlanarPushforward L hp hp1 hq) := by
  intro A B hA hB
  rw [torusPlanarPushforward_real_apply,
    torusPlanarPushforward_real_apply,
    torusPlanarPushforward_real_apply]
  rw [preimage_inter]
  exact hpa _ _
    (torusPlanarPullback_preimage_isIncreasing L hA)
    (torusPlanarPullback_preimage_isIncreasing L hB)



theorem torusPlanarPushforward_positivelyAssociated_of_one_le
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q) :
    PositivelyAssociated (torusPlanarPushforward L hp hp1 hq0) :=
  torusPlanarPushforward_positivelyAssociated L hp hp1 hq0
    (torusAmbientMeasure_positivelyAssociated L hp hp1 hq0 hq)




def torusSiteTranslateEquiv (L : ℕ) (t : Site 2) :
    (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun z := (z.1 + (t 0 : ZMod L), z.2 + (t 1 : ZMod L))
  invFun z := (z.1 - (t 0 : ZMod L), z.2 - (t 1 : ZMod L))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

@[simp] theorem torusSiteTranslateEquiv_apply
    (L : ℕ) (t : Site 2) (z : ZMod L × ZMod L) :
    torusSiteTranslateEquiv L t z =
      (z.1 + (t 0 : ZMod L), z.2 + (t 1 : ZMod L)) :=
  rfl


theorem torusReduceSite_add (L : ℕ) (z t : Site 2) :
    torusReduceSite L (z + t) = torusSiteTranslateEquiv L t (torusReduceSite L z) := by
  apply Prod.ext <;> simp [torusReduceSite, torusSiteTranslateEquiv]


theorem onsTorusGraph_adj_translate (L : ℕ) [Fact (2 < L)]
    (t : Site 2) (x y : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusSiteTranslateEquiv L t x)
        (torusSiteTranslateEquiv L t y) ↔
      (onsTorusGraph L).Adj x y := by
  change onsTorusAdj L
      (x.1 + (t 0 : ZMod L), x.2 + (t 1 : ZMod L))
      (y.1 + (t 0 : ZMod L), y.2 + (t 1 : ZMod L)) ↔
    onsTorusAdj L x y
  unfold onsTorusAdj
  constructor
  · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
    · exact Or.inl ⟨by linear_combination h0, Or.inl (by linear_combination h1)⟩
    · exact Or.inl ⟨by linear_combination h0, Or.inr (by linear_combination h1)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inl (by linear_combination h0)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inr (by linear_combination h0)⟩
  · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
    · exact Or.inl ⟨by linear_combination h0, Or.inl (by linear_combination h1)⟩
    · exact Or.inl ⟨by linear_combination h0, Or.inr (by linear_combination h1)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inl (by linear_combination h0)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inr (by linear_combination h0)⟩


theorem torusSiteTranslate_mem_edgeFinset_iff
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (e : Sym2 (ZMod L × ZMod L)) :
    Sym2.map (torusSiteTranslateEquiv L t) e ∈
        (onsTorusGraph L).edgeFinset ↔
      e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact onsTorusGraph_adj_translate L t x y


noncomputable def torusAmbientTranslateEdgeEquiv
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    TorusAmbientEdge L ≃ TorusAmbientEdge L where
  toFun e := ⟨Sym2.map (torusSiteTranslateEquiv L t) e.1,
    (torusSiteTranslate_mem_edgeFinset_iff L t e.1).2 e.2⟩
  invFun e := ⟨Sym2.map (torusSiteTranslateEquiv L t).symm e.1, by
    apply (torusSiteTranslate_mem_edgeFinset_iff L t
      (Sym2.map (torusSiteTranslateEquiv L t).symm e.1)).1
    simpa only [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id', id_eq]
      using e.2⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map (torusSiteTranslateEquiv L t).symm
        (Sym2.map (torusSiteTranslateEquiv L t) e.1) = e.1
    rw [Sym2.map_map]
    calc
      Sym2.map ((torusSiteTranslateEquiv L t).symm ∘
          torusSiteTranslateEquiv L t) e.1 =
          Sym2.map (fun x => x) e.1 := by
        apply Sym2.map_congr
        intro x _hx
        exact (torusSiteTranslateEquiv L t).symm_apply_apply x
      _ = e.1 := congrFun Sym2.map_id' e.1
  right_inv e := by
    apply Subtype.ext
    change Sym2.map (torusSiteTranslateEquiv L t)
        (Sym2.map (torusSiteTranslateEquiv L t).symm e.1) = e.1
    rw [Sym2.map_map]
    calc
      Sym2.map (torusSiteTranslateEquiv L t ∘
          (torusSiteTranslateEquiv L t).symm) e.1 =
          Sym2.map (fun x => x) e.1 := by
        apply Sym2.map_congr
        intro x _hx
        exact (torusSiteTranslateEquiv L t).apply_symm_apply x
      _ = e.1 := congrFun Sym2.map_id' e.1


noncomputable def torusAmbientTranslateConfig
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => omega (torusAmbientTranslateEdgeEquiv L t e)


noncomputable def torusAmbientTranslateConfigEquiv
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusAmbientTranslateConfig L t
  invFun eta := fun e => eta ((torusAmbientTranslateEdgeEquiv L t).symm e)
  left_inv omega := by
    funext e
    simp [torusAmbientTranslateConfig]
  right_inv eta := by
    funext e
    simp [torusAmbientTranslateConfig]


theorem torusAmbientConfigExtend_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusAmbientTranslateConfig L t omega) =
      FK.reCfgIso (torusSiteTranslateEquiv L t)
        (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hte : Sym2.map (torusSiteTranslateEquiv L t) e ∈
        (onsTorusGraph L).edgeFinset :=
      (torusSiteTranslate_mem_edgeFinset_iff L t e).2 he
    rw [torusAmbientConfigExtend, dif_pos he, torusAmbientTranslateConfig,
      FK.fvs_reCfgIso_apply, torusAmbientConfigExtend, dif_pos hte]
    rfl
  · have hte : Sym2.map (torusSiteTranslateEquiv L t) e ∉
        (onsTorusGraph L).edgeFinset := by
      intro h
      exact he ((torusSiteTranslate_mem_edgeFinset_iff L t e).1 h)
    rw [torusAmbientConfigExtend, dif_neg he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_neg hte]



theorem torusPlanarPullback_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusPlanarPullback L (torusAmbientTranslateConfig L t omega) =
      translateConfig t (torusPlanarPullback L omega) := by
  funext e
  unfold torusPlanarPullback translateConfig
  rw [torusAmbientConfigExtend_translate, FK.fvs_reCfgIso_apply,
    Sym2.map_map]
  change torusAmbientConfigExtend L omega
      (Sym2.map (torusSiteTranslateEquiv L t ∘ torusReduceSite L) e) =
    torusAmbientConfigExtend L omega
      (Sym2.map (torusReduceSite L)
        (Sym2.map (fun x => x + t) e))
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _hz
  exact (torusReduceSite_add L z t).symm



theorem measurable_torusAmbientTranslateConfig
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    Measurable (torusAmbientTranslateConfig L t) :=
  measurable_of_finite _


theorem torusAmbientFKWeight_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q
        (torusAmbientTranslateConfig L t omega) =
      torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_translate]
  exact FK.fvs_fkWeight_reCfgIso (onsTorusGraph L) (onsTorusGraph L)
    (torusSiteTranslateEquiv L t)
    (fun x y => (onsTorusGraph_adj_translate L t x y).symm)
    p q (torusAmbientConfigExtend L omega)



theorem torusAmbientProbability_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientProbability L p q
        (torusAmbientTranslateConfig L t omega) =
      torusAmbientProbability L p q omega := by
  unfold torusAmbientProbability
  rw [torusAmbientFKWeight_translate]




theorem torusAmbientTranslateConfig_measurePreserving
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Site 2) :
    MeasurePreserving (torusAmbientTranslateConfig L t)
      (torusAmbientMeasure L hp hp1 hq)
      (torusAmbientMeasure L hp hp1 hq) := by
  refine ⟨measurable_torusAmbientTranslateConfig L t, ?_⟩
  apply Measure.ext_of_singleton
  intro omega
  rw [Measure.map_apply (measurable_torusAmbientTranslateConfig L t)
    (measurableSet_singleton omega)]
  have hpre : torusAmbientTranslateConfig L t ⁻¹' {omega} =
      {(torusAmbientTranslateConfigEquiv L t).symm omega} := by
    ext eta
    simp only [mem_preimage, mem_singleton_iff]
    change (torusAmbientTranslateConfigEquiv L t) eta = omega ↔ _
    constructor
    · intro h
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      rw [h, Equiv.apply_symm_apply]
  rw [hpre, torusAmbientMeasure_singleton,
    torusAmbientMeasure_singleton]
  congr 1
  calc
    torusAmbientProbability L p q
        ((torusAmbientTranslateConfigEquiv L t).symm omega) =
      torusAmbientProbability L p q
        (torusAmbientTranslateConfig L t
          ((torusAmbientTranslateConfigEquiv L t).symm omega)) :=
        (torusAmbientProbability_translate L t p q _).symm
    _ = torusAmbientProbability L p q omega := by
      change torusAmbientProbability L p q
        ((torusAmbientTranslateConfigEquiv L t)
          ((torusAmbientTranslateConfigEquiv L t).symm omega)) = _
      rw [Equiv.apply_symm_apply]



theorem torusPlanarPushforward_shiftInvariant_of_torus
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Site 2)
    (hshift : MeasurePreserving (torusAmbientTranslateConfig L t)
      (torusAmbientMeasure L hp hp1 hq)
      (torusAmbientMeasure L hp hp1 hq)) :
    MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  refine ⟨cti_measurable_translateConfig t, ?_⟩
  unfold torusPlanarPushforward
  rw [Measure.map_map (cti_measurable_translateConfig t)
    (measurable_torusPlanarPullback L)]
  have hcomp : translateConfig t ∘ torusPlanarPullback L =
      torusPlanarPullback L ∘ torusAmbientTranslateConfig L t := by
    funext omega
    exact (torusPlanarPullback_translate L t omega).symm
  rw [hcomp]
  rw [← Measure.map_map (measurable_torusPlanarPullback L)
    (measurable_torusAmbientTranslateConfig L t)]
  rw [hshift.map_eq]


theorem torusPlanarPushforward_allShiftInvariant_of_torus
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ t : Site 2,
      MeasurePreserving (torusAmbientTranslateConfig L t)
        (torusAmbientMeasure L hp hp1 hq)
        (torusAmbientMeasure L hp hp1 hq)) :
    ∀ t : Site 2, MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  intro t
  exact torusPlanarPushforward_shiftInvariant_of_torus
    L hp hp1 hq t (hshift t)



theorem torusPlanarPushforward_allShiftInvariant
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ t : Site 2, MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  exact torusPlanarPushforward_allShiftInvariant_of_torus L hp hp1 hq
    (torusAmbientTranslateConfig_measurePreserving L hp hp1 hq)








theorem bdcLongRectangle_polynomial_deficit_of_torusCover
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    (W : Set (TorusAmbientConfig L))
    (hcover : BdcTorusWindingToThinCover L alpha n W)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hW : 1 - (torusAmbientMeasure L hp hp1 hq0).real W ≤
      c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      (torusPlanarPushforward L hp hp1 hq0).real
        (bdcLongRectangleBaseEvent alpha n) := by
  apply bdcLongRectangle_polynomial_deficit_of_cover
    (torusPlanarPushforward L hp hp1 hq0)
    (torusPlanarPushforward_positivelyAssociated_of_one_le
      L hp hp1 hq0 hq)
    (torusPlanarPushforward_allShiftInvariant L hp hp1 hq0)
    ha hn (bdcTorusPlanarLiftEvent L W)
    hcover.planarLift_subset_longRectangleUnion hc
  simpa only [torusPlanarPushforward_real_planarLiftEvent_apply]
    using hW

end StatMech.BeffaraDC
