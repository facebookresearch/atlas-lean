/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient.lean` and
`P2M/Sol/S_AutomorphicForm_hasSum_whittakerCoefficient.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.WhittakerCoefficient
public import MathlibExt.NumberTheory.NumberField.AdelicBox
public import MathlibExt.NumberTheory.NumberField.AdelicCharacter
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.LinearAlgebra.Countable

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicBox NumberField.AdelicHaar

noncomputable section

namespace D2Brick7

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

theorem exists_pos_forall_norm_lt_subset
    {U₁ : Set (InfiniteAdeleRing F)} (hU₁ : U₁ ∈ nhds (0 : InfiniteAdeleRing F)) :
    ∃ δ : ℝ, 0 < δ ∧ {y : InfiniteAdeleRing F | ∀ v, ‖y v‖ < δ} ⊆ U₁ := by
  have hU' : U₁ ∈ nhds (0 : (v : InfinitePlace F) → v.Completion) := hU₁
  rw [nhds_pi] at hU'
  obtain ⟨I, hIfin, t, htmem, hsub⟩ := Filter.mem_pi.mp hU'
  have hball : ∀ v : InfinitePlace F, ∃ δv : ℝ, 0 < δv ∧
      ∀ y : v.Completion, ‖y‖ < δv → y ∈ t v := by
    intro v
    rcases Metric.mem_nhds_iff.mp (htmem v) with ⟨δv, hδv, hbb⟩
    refine ⟨δv, hδv, fun y hy => hbb ?_⟩
    rwa [Metric.mem_ball, Pi.zero_apply, dist_zero_right]
  choose δv hδvpos hδvsub using hball
  have hne : (Finset.univ : Finset (InfinitePlace F)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne δv, (Finset.lt_inf'_iff hne).mpr fun v _ => hδvpos v, ?_⟩
  intro y hy
  exact hsub (Set.mem_pi.mpr fun v _ =>
    hδvsub v (y v) (lt_of_lt_of_le (hy v) (Finset.inf'_le δv (Finset.mem_univ v))))

open scoped Classical in

theorem adelicAddHaar_nhds_zero_inter_adelicBox_pos
    {U : Set (AdeleRing (𝓞 F) F)} (hU : U ∈ nhds (0 : AdeleRing (𝓞 F) F)) :
    0 < adelicAddHaar (𝓞 F) F (U ∩ adelicBox F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set μ := adelicAddHaar (𝓞 F) F with hμdef
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with hedef
  set b := mixedEmbedding.latticeBasis F with hbdef

  have hU' : U ∈ nhds ((0, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := hU
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := mem_nhds_prod_iff.mp hU'

  obtain ⟨δ, hδpos, hball⟩ := exists_pos_forall_norm_lt_subset F hU₁

  set L := LinearMap.toContinuousLinearMap b.equivFun.symm.toLinearMap with hLdef
  have hL0 : (0 : ℝ) < ‖L‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos
  set ε := min (δ / (‖L‖ + 1)) 1 with hεdef
  have hεpos : 0 < ε := lt_min (div_pos hδpos hL0) one_pos
  have hεle1 : ε ≤ 1 := min_le_right _ _
  have hCδ : ‖L‖ * ε < δ := by
    have h1 : ‖L‖ * ε ≤ ‖L‖ * (δ / (‖L‖ + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
    have h2 : ‖L‖ * (δ / (‖L‖ + 1)) < δ := by
      rw [← mul_div_assoc, div_lt_iff₀ hL0]
      calc ‖L‖ * δ = δ * ‖L‖ := mul_comm _ _
        _ < δ * ‖L‖ + δ := lt_add_of_pos_right _ hδpos
        _ = δ * (‖L‖ + 1) := by rw [mul_add, mul_one]
    exact lt_of_le_of_lt h1 h2

  have hcoordcont : ∀ i, Continuous fun y : InfiniteAdeleRing F => b.repr (e y) i := by
    intro i
    have h1 : Continuous (b.coord i) := (b.coord i).continuous_of_finiteDimensional
    have h2 : (fun y : InfiniteAdeleRing F => b.repr (e y) i)
        = fun y => b.coord i (e y) := by
      funext y; rw [Module.Basis.coord_apply]
    rw [h2]
    exact h1.comp (continuous_ringEquiv_mixedSpace F)

  have hsmall : ∀ y : InfiniteAdeleRing F, (∀ i, |b.repr (e y) i| < ε) → y ∈ U₁ := by
    intro y hy
    refine hball ?_
    intro v
    have hbound : ‖y v‖ ≤ ‖e y‖ := by
      rcases v.isReal_or_isComplex with hv | hv
      · exact norm_apply_le_of_isReal F y hv
      · exact norm_apply_le_of_isComplex F y hv
    have hcoords : ‖b.equivFun (e y)‖ ≤ ε := by
      rw [pi_norm_le_iff_of_nonneg hεpos.le]
      intro i
      have hbr : b.equivFun (e y) i = b.repr (e y) i :=
        congrFun (Module.Basis.equivFun_apply b (e y)) i
      rw [Real.norm_eq_abs, hbr]
      exact (hy i).le
    have hLm : L (b.equivFun (e y)) = e y := by
      rw [hLdef]
      rw [LinearMap.coe_toContinuousLinearMap']
      exact b.equivFun.symm_apply_apply (e y)
    have hnorm : ‖e y‖ ≤ ‖L‖ * ε := by
      rw [← hLm]
      exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hcoords (norm_nonneg _))
    exact lt_of_le_of_lt (hbound.trans hnorm) hCδ

  obtain ⟨W₂, hW₂sub, hW₂open, hW₂mem⟩ := mem_nhds_iff.mp hU₂
  have hc1 : Continuous fun x : AdeleRing (𝓞 F) F => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 F) F => x.2 := continuous_snd
  set Kf : Set (FiniteAdeleRing (𝓞 F) F) := W₂ ∩ integralFiniteAdeles (𝓞 F) F with hKfdef
  have hKfopen : IsOpen Kf := hW₂open.inter (isOpen_integralFiniteAdeles F)
  have hKf0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Kf := ⟨hW₂mem, fun v => zero_mem _⟩

  set CubA : Set (AdeleRing (𝓞 F) F) :=
    (⋂ i, (fun x : AdeleRing (𝓞 F) F => b.repr (e x.1) i) ⁻¹' Set.Ioo (-ε) ε)
      ∩ {x : AdeleRing (𝓞 F) F | x.2 ∈ Kf} with hCubdef
  set CorA : Set (AdeleRing (𝓞 F) F) :=
    (⋂ i, (fun x : AdeleRing (𝓞 F) F => b.repr (e x.1) i) ⁻¹' Set.Ico 0 ε)
      ∩ {x : AdeleRing (𝓞 F) F | x.2 ∈ Kf} with hCordef
  have hCubopen : IsOpen CubA := by
    rw [hCubdef]
    exact (isOpen_iInter_of_finite fun i =>
        isOpen_Ioo.preimage ((hcoordcont i).comp hc1)).inter
      (hKfopen.preimage hc2)
  have h0Cub : (0 : AdeleRing (𝓞 F) F) ∈ CubA := by
    rw [hCubdef]
    refine ⟨Set.mem_iInter.mpr fun i => ?_, hKf0⟩
    have h0 : b.repr (e (0 : AdeleRing (𝓞 F) F).1) i = 0 := by
      have hz : e (0 : AdeleRing (𝓞 F) F).1 = 0 := map_zero e
      rw [hz, map_zero, Finsupp.zero_apply]
    rw [Set.mem_preimage, h0]
    exact ⟨neg_lt_zero.mpr hεpos, hεpos⟩
  have hCorMeas : MeasurableSet CorA := by
    rw [hCordef]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.iInter fun i =>
        ((hcoordcont i).comp hc1).measurable measurableSet_Ico
    · exact (hKfopen.preimage hc2).measurableSet

  have hCorSub : CorA ⊆ U ∩ adelicBox F := by
    rw [hCordef]
    rintro x ⟨hx1, hx2⟩
    have hcoords := Set.mem_iInter.mp hx1
    have hxU₁ : x.1 ∈ U₁ := by
      refine hsmall x.1 fun i => ?_
      have h := hcoords i
      rw [Set.mem_preimage] at h
      rw [abs_of_nonneg h.1]
      exact h.2
    have hxbox : x ∈ adelicBox F := by
      refine ⟨?_, hx2.2⟩
      show e x.1 ∈ ZSpan.fundamentalDomain b
      rw [ZSpan.mem_fundamentalDomain]
      intro i
      have h := hcoords i
      rw [Set.mem_preimage] at h
      exact ⟨h.1, lt_of_lt_of_le h.2 hεle1⟩
    refine ⟨hprod ⟨hxU₁, hW₂sub hx2.1⟩, hxbox⟩

  set sft : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → AdeleRing (𝓞 F) F :=
    fun T => (e.symm (b.equivFun.symm fun i => if i ∈ T then -ε else 0), 0) with hsftdef
  have hcover : CubA ⊆ ⋃ T, (fun y => sft T + y) '' CorA := by
    rw [hCubdef]
    rintro x ⟨hx1, hx2⟩
    have hcoords := Set.mem_iInter.mp hx1
    set T := Finset.univ.filter
      (fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 F) => b.repr (e x.1) i < 0) with hTdef
    refine Set.mem_iUnion.mpr ⟨T, x - sft T, ?_, by
      show sft T + (x - sft T) = x
      ring⟩
    rw [hCordef]
    have hreprs : ∀ i, b.repr (e (x - sft T).1) i
        = b.repr (e x.1) i - (if i ∈ T then -ε else 0) := by
      intro i
      have h1 : (x - sft T).1 = x.1 - (sft T).1 := rfl
      rw [h1, map_sub, map_sub, Finsupp.sub_apply]
      congr 1
      show b.repr (e (e.symm (b.equivFun.symm fun j => if j ∈ T then -ε else 0))) i
          = (if i ∈ T then -ε else 0)
      rw [RingEquiv.apply_symm_apply]
      have hbr := congrFun (Module.Basis.equivFun_apply b
        (b.equivFun.symm fun j => if j ∈ T then -ε else 0)) i
      rw [← hbr, LinearEquiv.apply_symm_apply]
    constructor
    · refine Set.mem_iInter.mpr fun i => ?_
      rw [Set.mem_preimage, hreprs i]
      have hxi := hcoords i
      rw [Set.mem_preimage] at hxi
      by_cases hiT : i ∈ T
      · rw [ite_eq_left hiT]
        have hneg : b.repr (e x.1) i < 0 := (Finset.mem_filter.mp hiT).2
        refine ⟨sub_nonneg.mpr hxi.1.le, ?_⟩
        rw [sub_neg_eq_add]
        have h := add_lt_add_right hneg ε
        rwa [add_zero, add_comm] at h
      · rw [ite_eq_right hiT, sub_zero]
        have hnonneg : 0 ≤ b.repr (e x.1) i := not_lt.mp fun hc =>
          hiT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        exact ⟨hnonneg, hxi.2⟩
    · show (x - sft T).2 ∈ Kf
      have h2 : (x - sft T).2 = x.2 - 0 := rfl
      rw [h2, sub_zero]
      exact hx2

  have hμtrans : ∀ T, μ ((fun y => sft T + y) '' CorA) = μ CorA := by
    intro T
    have him : (fun y => sft T + y) '' CorA = (fun y => -sft T + y) ⁻¹' CorA := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hzz : -sft T + (sft T + y) = y := by ring
        show -sft T + (sft T + y) ∈ CorA
        rw [hzz]
        exact hy
      · intro hz
        refine ⟨-sft T + z, hz, ?_⟩
        show sft T + (-sft T + z) = z
        ring
    rw [him]
    exact (measurePreserving_add_left μ (-sft T)).measure_preimage
      hCorMeas.nullMeasurableSet

  have hCorpos : 0 < μ CorA := by
    by_contra hc
    have hz : μ CorA = 0 := le_zero_iff.mp (not_lt.mp hc)
    have hOpos : 0 < μ CubA := hCubopen.measure_pos μ ⟨0, h0Cub⟩
    have hbound : μ CubA ≤ ∑' T, μ ((fun y => sft T + y) '' CorA) :=
      le_trans (measure_mono hcover) (measure_iUnion_le _)
    rw [show (fun T => μ ((fun y => sft T + y) '' CorA)) = fun _ => (0 : ENNReal) from
      funext fun T => (hμtrans T).trans hz] at hbound
    rw [tsum_zero] at hbound
    exact (hOpos.ne' (le_zero_iff.mp hbound)).elim
  exact lt_of_lt_of_le hCorpos (measure_mono hCorSub)

theorem eq_at_zero_of_ae_eq_cond_adelicBox
    {f g : AdeleRing (𝓞 F) F → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hae : f =ᵐ[@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)] g) :
    f 0 = g 0 := by
  by_contra hne
  have hopen : IsOpen {x | f x ≠ g x} := isOpen_ne_fun hf hg
  have h0mem : (0 : AdeleRing (𝓞 F) F) ∈ {x | f x ≠ g x} := hne
  have hU : {x | f x ≠ g x} ∈ nhds (0 : AdeleRing (𝓞 F) F) := hopen.mem_nhds h0mem
  have hpos := adelicAddHaar_nhds_zero_inter_adelicBox_pos F hU
  have hcondz : (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)) {x | f x ≠ g x} = 0 := hae
  rw [ProbabilityTheory.cond_apply (measurableSet_adelicBox F)] at hcondz
  have hBne : (adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (adelicAddHaar_adelicBox_lt_top F).ne
  have hz : adelicAddHaar (𝓞 F) F (adelicBox F ∩ {x | f x ≠ g x}) = 0 := by
    rcases mul_eq_zero.mp hcondz with h | h
    · exact absurd h hBne
    · exact h
  rw [Set.inter_comm] at hz
  exact hpos.ne' hz

end D2Brick7

end



open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

noncomputable section

namespace D2Bricks

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

abbrev AQuot := AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F

scoped instance instCompactSpaceAQuot : CompactSpace (AQuot F) :=
  NumberField.AdeleRing.compactSpace_quotient_principalSubgroup F

theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 F) F : Set (AdeleRing (𝓞 F) F)) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨K, hKcomp, hKx⟩ := exists_compact_mem_nhds x
  have hfin : (K ∩ (AdeleRing.principalSubgroup (𝓞 F) F : Set _)).Finite := by
    refine ((NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F
      hKcomp).image (algebraMap F (AdeleRing (𝓞 F) F))).subset ?_
    rintro y ⟨hyK, ξ, rfl⟩
    exact ⟨ξ, hyK, rfl⟩
  have hxnot : x ∉ K ∩ (AdeleRing.principalSubgroup (𝓞 F) F : Set _) := fun h => hx h.2
  refine Filter.mem_of_superset
    (Filter.inter_mem hKx (hfin.isClosed.compl_mem_nhds hxnot)) ?_
  rintro y ⟨hyK, hyncl⟩ hyS
  exact hyncl ⟨hyK, hyS⟩

scoped instance instT2SpaceAQuot : T2Space (AQuot F) := by
  haveI : IsClosed (AdeleRing.principalSubgroup (𝓞 F) F : Set (AdeleRing (𝓞 F) F)) :=
    isClosed_principalSubgroup F
  infer_instance

section Char
variable (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)

def quotChar (α : F) : C(AQuot F, ℂ) where
  toFun := Quotient.lift (fun x => ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) (by
    intro a b hab
    obtain ⟨β, hβ⟩ := QuotientAddGroup.leftRel_apply.mp hab

    have hb : b = a + algebraMap F (AdeleRing (𝓞 F) F) β := by
      rw [hβ]; ring
    show ψ (algebraMap F (AdeleRing (𝓞 F) F) α * a) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * b)
    rw [hb, mul_add, ψ.map_add_eq_mul]
    have : ψ (algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) β) = 1 := by
      rw [← (algebraMap F _).map_mul]
      exact hψ.principalInvariant (α * β)
    rw [this, mul_one])
  continuous_toFun := by
    refine continuous_quot_lift _ ?_
    exact hψ.continuous.comp (continuous_const.mul continuous_id)

@[scoped simp]
theorem quotChar_apply_mk (α : F) (x : AdeleRing (𝓞 F) F) :
    quotChar F ψ hψ α (QuotientAddGroup.mk x) =
    ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) := rfl

theorem quotChar_zero : quotChar F ψ hψ 0 = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [quotChar_apply_mk, map_zero, zero_mul, AddChar.map_zero_eq_one,
    ContinuousMap.one_apply]

theorem quotChar_add (α β : F) :
    quotChar F ψ hψ (α + β) = quotChar F ψ hψ α * quotChar F ψ hψ β := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [quotChar_apply_mk, ContinuousMap.mul_apply, map_add, add_mul, ψ.map_add_eq_mul]

theorem star_quotChar (α : F) :
    star (quotChar F ψ hψ α) = quotChar F ψ hψ (-α) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.star_apply, quotChar_apply_mk, RCLike.star_def, map_neg, neg_mul]
  have h1 : ‖ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)‖ = 1 :=
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _
  rw [← Complex.inv_eq_conj h1, ← ψ.map_neg_eq_inv]

theorem quotChar_separatesPoints (q₁ q₂ : AQuot F) (hne : q₁ ≠ q₂) :
    ∃ α : F, quotChar F ψ hψ α q₁ ≠ quotChar F ψ hψ α q₂ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q₁
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q₂
  have hxy : x - y ∉ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by
    intro ⟨β, hβ⟩
    apply hne
    rw [QuotientAddGroup.eq]
    exact ⟨-β, by rw [map_neg, hβ]; ring⟩
  have hR2 : ¬ (∀ ξ : F, ψ ((x - y) * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) := fun h =>
    hxy (NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one F hψ (x - y) h)
  push Not at hR2
  obtain ⟨α, hα⟩ := hR2
  refine ⟨α, ?_⟩
  simp only [quotChar_apply_mk]
  intro heq
  apply hα
  have hne0 : ψ (algebraMap F (AdeleRing (𝓞 F) F) α * y) ≠ 0 := by
    have := NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
      (algebraMap F (AdeleRing (𝓞 F) F) α * y)
    intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this
  rw [sub_mul, mul_comm x, mul_comm y, ψ.map_sub_eq_div, heq, div_self hne0]

def quotCharSubalgebra : StarSubalgebra ℂ C(AQuot F, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (quotChar F ψ hψ))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (quotChar F ψ hψ)) ≤
      star (Algebra.adjoin ℂ (Set.range (quotChar F ψ hψ)))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨α, rfl⟩
    exact Algebra.subset_adjoin ⟨-α, (star_quotChar F ψ hψ α).symm⟩

theorem quotCharSubalgebra_separatesPoints :
    (quotCharSubalgebra F ψ hψ).SeparatesPoints := by
  intro q₁ q₂ hne
  obtain ⟨α, hα⟩ := quotChar_separatesPoints F ψ hψ q₁ q₂ hne
  exact ⟨quotChar F ψ hψ α, ⟨_, Algebra.subset_adjoin ⟨α, rfl⟩, rfl⟩, hα⟩

theorem quotCharSubalgebra_closure_eq_top :
    (quotCharSubalgebra F ψ hψ).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (quotCharSubalgebra_separatesPoints F ψ hψ)

theorem quotCharSubalgebra_coe :
    Subalgebra.toSubmodule (quotCharSubalgebra F ψ hψ).toSubalgebra =
    Submodule.span ℂ (Set.range (quotChar F ψ hψ)) := by
  change Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (quotChar F ψ hψ))) = _
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro g hg
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hg
  · exact quotChar_zero F ψ hψ
  · rintro _ _ _ _ ⟨α, rfl⟩ ⟨β, rfl⟩
    exact ⟨α + β, quotChar_add F ψ hψ α β⟩

theorem span_quotChar_closure_eq_top :
    (Submodule.span ℂ (Set.range (quotChar F ψ hψ))).topologicalClosure = ⊤ := by
  rw [← quotCharSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (quotCharSubalgebra_closure_eq_top F ψ hψ)

end Char

section Topology

scoped instance instCountableNumberField : Countable F := by
  obtain ⟨_, s, h⟩ := Module.Finite.exists_fin (R := ℚ) (M := F)
  have hspan : Countable (Submodule.span ℚ (Set.range s)) := inferInstance
  rw [h] at hspan
  exact (Submodule.topEquiv.symm.toEquiv.countable_iff).mpr hspan

scoped instance instCountableRingOfIntegers : Countable (𝓞 F) := Subtype.countable

scoped instance instCountableHeightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  rw [← Set.countable_univ_iff]
  have hcov : (Set.univ : Set (HeightOneSpectrum (𝓞 F))) ⊆
      ⋃ a : {x : 𝓞 F // x ≠ 0}, {p | (a : 𝓞 F) ∈ p.asIdeal} := by
    intro p _
    obtain ⟨a, hamem, hane⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (p.ne_bot)
    exact Set.mem_iUnion.mpr ⟨⟨a, hane⟩, hamem⟩
  refine Set.Countable.mono hcov (Set.countable_iUnion fun ⟨a, ha⟩ => ?_)
  have hspan : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 F)) := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  exact ((Ideal.finite_factors hspan).subset
    (fun p hp => Ideal.dvd_span_singleton.mpr hp)).countable

scoped instance instSecondCountableFiniteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  haveI : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      SecondCountableTopology
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T →
          (x v : v.adicCompletion F) ∈
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := by
    intro T
    haveI hdom : SecondCountableTopology (RestrictedProduct
        (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v : HeightOneSpectrum (𝓞 F) =>
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        (Filter.principal (↑T)ᶜ)) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    have hrw : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T →
        (x v : v.adicCompletion F) ∈
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))}
        = Set.range (RestrictedProduct.inclusion
        (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v : HeightOneSpectrum (𝓞 F) =>
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        (Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by rw [compl_compl]; exact T.finite_toSet)))) := by
      rw [RestrictedProduct.range_inclusion]
      ext x
      simp only [Set.mem_setOf_eq, Filter.eventually_principal, Set.mem_range,
        RestrictedProduct.inclusion_apply]
      constructor
      · intro hx v hv
        exact hx v (by simpa using hv)
      · intro hx v hv
        exact hx v (by simpa using hv)
    rw [hrw]
    exact ((RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen
      (Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by
        rw [compl_compl]; exact T.finite_toSet)))).isEmbedding.toHomeomorph.symm.isEmbedding
      ).secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T →
        (x v : v.adicCompletion F) ∈
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))})
    (fun T => (RestrictedProduct.isOpen_forall_imp_mem hAopen
      (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ T))) ?_
  rw [Set.iUnion_eq_univ_iff]
  intro x
  have hx : {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp x.2
  refine ⟨hx.toFinset, fun v hv => ?_⟩
  by_contra hvA
  exact hv (by simpa using hvA)

scoped instance instSecondCountableInfinitePlaceCompletion (w : InfinitePlace F) :
    SecondCountableTopology w.Completion := by
  have hiso : Isometry (InfinitePlace.Completion.extensionEmbedding w) :=
    InfinitePlace.Completion.isometry_extensionEmbedding w
  exact hiso.isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing :
    SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

scoped instance instSecondCountableAdeleRing :
    SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

scoped instance instSecondCountableAQuot : SecondCountableTopology (AQuot F) :=
  QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap

-- Local to this section: an erased attribute is not exported, and Lean restores Mathlib's
-- quotient instance at `end Topology`, so importers keep it. `section Bridge` below is nested
-- here so that it uses the same Borel structure on `AQuot F`.
attribute [-instance] Quotient.instMeasurableSpace

scoped instance instMeasurableSpaceAQuot : MeasurableSpace (AQuot F) := borel _
scoped instance instBorelSpaceAQuot : BorelSpace (AQuot F) := ⟨rfl⟩

scoped instance instHasOuterApproxClosedAQuot : HasOuterApproxClosed (AQuot F) := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (AQuot F) := inferInstance
  infer_instance

theorem polishSpace_of_compact_t2_secondCountable
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] :
    PolishSpace X := by
  haveI : TopologicalSpace.MetrizableSpace X := inferInstance
  letI := TopologicalSpace.metrizableSpaceMetric X
  haveI : CompleteSpace X := complete_of_compact
  infer_instance

section Bridge
variable (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)

attribute [local instance] NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox

theorem integrable_cond_adelicBox (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f) :
    Integrable f (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.bddAbove_image hf.norm.continuousOn
  have hae : ∀ᵐ x ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F)
      (adelicAddHaar (𝓞 F) F) (adelicBox F)), ‖f x‖ ≤ M := by
    refine (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)).mono fun x hx => ?_
    exact hM ⟨x, hsub hx, rfl⟩
  exact .of_bound hf.aestronglyMeasurable M hae

theorem integrable_mul_comp_mk_cond (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f)
    (g : C(AQuot F, ℂ)) :
    Integrable (fun x => f x * g (QuotientAddGroup.mk x))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  refine ((integrable_cond_adelicBox F f hf).norm.const_mul ‖g‖).mono'
    ((hf.mul (g.continuous.comp continuous_quotient_mk')).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)

include hψ in

theorem integral_mul_comp_mk_eq_zero (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f)
    (hcoef : ∀ α : F,
      ∫ x, f x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
          (adelicBox F)) = 0)
    (g : C(AQuot F, ℂ)) :
    ∫ x, f x * g (QuotientAddGroup.mk x)
      ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
        (adelicBox F)) = 0 := by
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)
  have hint := integrable_mul_comp_mk_cond F f hf

  have hIlin : ∀ g₁ g₂ : C(AQuot F, ℂ),
      ∫ x, f x * (g₁ + g₂) (QuotientAddGroup.mk x) ∂ν =
      ∫ x, f x * g₁ (QuotientAddGroup.mk x) ∂ν + ∫ x, f x * g₂ (QuotientAddGroup.mk x) ∂ν := by
    intro g₁ g₂
    rw [← integral_add (hint g₁) (hint g₂)]
    exact integral_congr_ae (.of_forall fun x => by
      simp only [ContinuousMap.add_apply]; ring)
  have hIsmul : ∀ (c : ℂ) (g : C(AQuot F, ℂ)),
      ∫ x, f x * (c • g) (QuotientAddGroup.mk x) ∂ν =
      c * ∫ x, f x * g (QuotientAddGroup.mk x) ∂ν := by
    intro c g
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring)
  let I : C(AQuot F, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ x, f x * g (QuotientAddGroup.mk x) ∂ν
      map_add' := hIlin
      map_smul' := fun c g => by rw [RingHom.id_apply, hIsmul]; ring }
  have hIcont : Continuous I := by
    have hM : ∀ g : C(AQuot F, ℂ), ‖I g‖ ≤ (∫ x, ‖f x‖ ∂ν) * ‖g‖ := by
      intro g
      rw [show I g = ∫ x, f x * g (QuotientAddGroup.mk x) ∂ν from rfl, mul_comm,
        ← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (.of_forall fun x => norm_nonneg _)
        ((integrable_cond_adelicBox F f hf).norm.const_mul ‖g‖) (.of_forall fun x => ?_)
      show ‖f x * g (QuotientAddGroup.mk x)‖ ≤ ‖g‖ * ‖f x‖
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
    exact (I.mkContinuous _ hM).continuous

  have hIrange : ∀ α : F, I (quotChar F ψ hψ α) = 0 := by
    intro α
    show ∫ x, f x * (quotChar F ψ hψ α) (QuotientAddGroup.mk x) ∂ν = 0
    simp only [quotChar_apply_mk]
    have := hcoef (-α)
    simpa only [map_neg, neg_mul, neg_neg] using this

  have hIspan : Submodule.span ℂ (Set.range (quotChar F ψ hψ)) ≤
      LinearMap.ker I := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact hIrange α
  have hItop : ∀ g : C(AQuot F, ℂ), I g = 0 := by
    intro g
    have hclosed : IsClosed {g : C(AQuot F, ℂ) | I g = 0} :=
      isClosed_eq hIcont continuous_const
    have hsub : (Submodule.span ℂ (Set.range (quotChar F ψ hψ)) :
        Set C(AQuot F, ℂ)) ⊆ {g | I g = 0} := fun g hg => hIspan hg
    have : (⊤ : Set C(AQuot F, ℂ)) ⊆ {g | I g = 0} := by
      rw [show (⊤ : Set C(AQuot F, ℂ)) =
        ((Submodule.span ℂ (Set.range (quotChar F ψ hψ))).topologicalClosure :
          Set C(AQuot F, ℂ)) from
        by rw [span_quotChar_closure_eq_top]; rfl]
      exact (hclosed.closure_subset_iff.mpr hsub)
    exact this (Set.mem_univ g)
  exact hItop g

include hψ in

theorem setIntegral_preimage_quotientAddGroup_mk_eq_zero
    (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f)
    (hcoef : ∀ α : F,
      ∫ x, f x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
          (adelicBox F)) = 0)
    (E : Set (AQuot F)) (hE : MeasurableSet E) :
    ∫ x in (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) ⁻¹' E, f x
      ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
        (adelicBox F)) = 0 := by
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)

  have hcont_mk : Continuous (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) :=
    continuous_quotient_mk'
  have hmeas : Measurable (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) :=
    hcont_mk.measurable
  have hπE : MeasurableSet ((QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E) := hmeas hE
  have hint_f : Integrable f ν := integrable_cond_adelicBox F f hf

  suffices h : ∀ (r : ℂ → ℝ), (r = Complex.re ∨ r = Complex.im) →
      ∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, r (f x) ∂ν = 0 by
    have hintE : Integrable f (ν.restrict ((QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E)) :=
      hint_f.integrableOn
    have hre : (∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, f x ∂ν).re =
        ∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, (f x).re ∂ν := by
      have := integral_re hintE; simpa only [RCLike.re_eq_complex_re] using this.symm
    have him : (∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, f x ∂ν).im =
        ∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, (f x).im ∂ν := by
      have := integral_im hintE; simpa only [RCLike.im_eq_complex_im] using this.symm
    exact Complex.ext (hre.trans (h _ (.inl rfl))) (him.trans (h _ (.inr rfl)))
  intro r hr
  have hrc : Continuous r := hr.elim (· ▸ Complex.continuous_re) (· ▸ Complex.continuous_im)
  have hrf : Integrable (fun x => r (f x)) ν := by
    refine Integrable.mono' hint_f.norm (hrc.comp hf).aestronglyMeasurable (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hr.elim (· ▸ Complex.abs_re_le_norm _) (· ▸ Complex.abs_im_le_norm _)

  set μp := (ν.withDensity (fun x => .ofReal (r (f x)))).map
    (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) with hμp
  set μn := (ν.withDensity (fun x => .ofReal (-r (f x)))).map
    (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) with hμn
  haveI : IsFiniteMeasure (ν.withDensity (fun x => .ofReal (r (f x)))) :=
    isFiniteMeasure_withDensity_ofReal hrf.2
  haveI : IsFiniteMeasure (ν.withDensity (fun x => .ofReal (-r (f x)))) :=
    isFiniteMeasure_withDensity_ofReal hrf.neg.2
  haveI : IsFiniteMeasure μp := by rw [hμp]; infer_instance
  haveI : IsFiniteMeasure μn := by rw [hμn]; infer_instance

  have hw : ∀ h : AdeleRing (𝓞 F) F → ℝ, Continuous h →
      ∀ g : BoundedContinuousFunction (AQuot F) ℝ,
      ∫ q, g q ∂((ν.withDensity (fun x => .ofReal (h x))).map
        (QuotientAddGroup.mk : _ → AQuot F)) =
      ∫ x, max (h x) 0 • g (QuotientAddGroup.mk x) ∂ν := by
    intro h hh g
    rw [integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hh.measurable.ennreal_ofReal.aemeasurable
        (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    exact integral_congr_ae (.of_forall fun x => by simp only [ENNReal.toReal_ofReal'])

  have hrfc : Continuous fun x => r (f x) := hrc.comp hf
  have hext : ∀ g : BoundedContinuousFunction (AQuot F) ℝ, ∫ q, g q ∂μp = ∫ q, g q ∂μn := by
    intro g
    rw [hμp, hw (fun x => r (f x)) hrfc g, hμn, hw (fun x => -r (f x)) hrfc.neg g, ← sub_eq_zero]
    have hgint : ∀ h : AdeleRing (𝓞 F) F → ℝ, Continuous h → Integrable h ν →
        Integrable (fun x => max (h x) 0 • g (QuotientAddGroup.mk x)) ν := by
      intro h hh hint
      refine (hint.norm.const_mul ‖g‖).mono'
        (((hh.max continuous_const).smul
          (g.continuous.comp hcont_mk)).aestronglyMeasurable)
        (.of_forall fun x => ?_)
      rw [norm_smul, mul_comm]
      refine mul_le_mul (g.norm_coe_le_norm _) ?_ (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact abs_max_le_max_abs_abs.trans (by simp)
    rw [← integral_sub (hgint (fun x => r (f x)) hrfc hrf)
      (hgint (fun x => -r (f x)) hrfc.neg hrf.neg)]
    have hpn : ∀ y : ℝ, max y 0 - max (-y) 0 = y := max_zero_sub_max_neg_zero_eq_self

    have hB4a_g := integral_mul_comp_mk_eq_zero F ψ hψ f hf hcoef
      ⟨fun q => (g q : ℂ), (Complex.continuous_ofReal).comp g.continuous⟩
    have hintg : Integrable (fun x => f x * (g (QuotientAddGroup.mk x) : ℂ)) ν :=
      integrable_mul_comp_mk_cond F f hf ⟨_, (Complex.continuous_ofReal).comp g.continuous⟩
    calc ∫ x, (max (r (f x)) 0 • g (↑x) - max (-r (f x)) 0 • g (↑x)) ∂ν
        = ∫ x, r (f x) • g (QuotientAddGroup.mk x) ∂ν :=
          integral_congr_ae (.of_forall fun x => by simp only [← sub_smul, hpn])
      _ = ∫ x, r (f x * (g (QuotientAddGroup.mk x) : ℂ)) ∂ν := by
          refine integral_congr_ae (.of_forall fun x => ?_)
          rcases hr with rfl | rfl <;> simp [Complex.mul_re, Complex.mul_im]
      _ = r (∫ x, f x * (g (QuotientAddGroup.mk x) : ℂ) ∂ν) := by
          rcases hr with rfl | rfl
          · simpa only [RCLike.re_eq_complex_re] using integral_re hintg
          · simpa only [RCLike.im_eq_complex_im] using integral_im hintg
      _ = r 0 := by rw [show (∫ x, f x * (g (↑x) : ℂ) ∂ν) = 0 from hB4a_g]
      _ = 0 := by rcases hr with rfl | rfl <;> simp
  have hμeq : μp = μn := ext_of_forall_integral_eq_of_IsFiniteMeasure hext

  have hμpE : ∫⁻ a in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, .ofReal (r (f a)) ∂ν = μp E := by
    rw [hμp, Measure.map_apply hmeas hE, withDensity_apply _ hπE]
  have hμnE : ∫⁻ a in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, .ofReal (-r (f a)) ∂ν = μn E := by
    rw [hμn, Measure.map_apply hmeas hE, withDensity_apply _ hπE]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hrf.integrableOn, hμpE, hμnE, hμeq,
    sub_self]

theorem quotientAddGroup_mk_injOn_adelicBox :
    Set.InjOn (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) (adelicBox F) := by
  intro x hx y hy hxy
  rw [QuotientAddGroup.eq] at hxy
  obtain ⟨β, hβ⟩ := hxy
  have huniq := existsUnique_algebraMap_add_mem_adelicBox F x
  have h0 : algebraMap F (AdeleRing (𝓞 F) F) 0 + x ∈ adelicBox F := by
    rw [map_zero, zero_add]; exact hx
  have hβ' : algebraMap F (AdeleRing (𝓞 F) F) β + x ∈ adelicBox F := by
    rw [hβ]; rw [show (-x + y) + x = y from by ring]; exact hy
  have hβ0 : β = 0 := huniq.unique hβ' h0
  rw [hβ0, map_zero] at hβ
  exact neg_add_eq_zero.mp hβ.symm

include hψ in

theorem ae_eq_zero_cond_of_forall_integral_eq_zero
    (f : AdeleRing (𝓞 F) F → ℂ) (_hf : Continuous f)
    (_hcoef : ∀ α : F,
      ∫ x, f x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
          (adelicBox F)) = 0) :
    f =ᵐ[@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)]
      0 := by
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)

  have hB4a := integral_mul_comp_mk_eq_zero F ψ hψ f _hf _hcoef

  obtain ⟨C, hC, hCsub⟩ := exists_isCompact_adelicBox_subset F
  haveI : CompactSpace ↥C := isCompact_iff_compactSpace.mp hC
  haveI : PolishSpace ↥C := polishSpace_of_compact_t2_secondCountable _
  have hembC : MeasurableEmbedding ((Subtype.val ⁻¹' adelicBox F : Set ↥C).restrict
      ((QuotientAddGroup.mk : _ → AQuot F) ∘ (Subtype.val : ↥C → AdeleRing (𝓞 F) F))) := by
    refine ContinuousOn.measurableEmbedding (β := AQuot F)
      (measurable_subtype_coe (measurableSet_adelicBox F))
      ((continuous_quotient_mk').comp continuous_subtype_val).continuousOn ?_
    intro x hx y hy hxy
    exact Subtype.ext (quotientAddGroup_mk_injOn_adelicBox F hx hy hxy)

  have himage : ∀ B : Set (AdeleRing (𝓞 F) F), MeasurableSet B → B ⊆ adelicBox F →
      MeasurableSet ((QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) '' B) := by
    intro B hB hBsub
    have heq : (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) '' B =
        (Subtype.val ⁻¹' adelicBox F : Set ↥C).restrict
          ((QuotientAddGroup.mk : _ → AQuot F) ∘ (Subtype.val : ↥C → _)) ''
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' B : Set ↥C)) := by
      rw [show (Subtype.val ⁻¹' adelicBox F : Set ↥C).restrict
          ((QuotientAddGroup.mk : _ → AQuot F) ∘ (Subtype.val : ↥C → _)) =
        (QuotientAddGroup.mk : _ → AQuot F) ∘ Subtype.val ∘ Subtype.val from rfl,
        Set.image_comp, Set.image_comp, Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr (Set.preimage_mono hBsub), Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr (hBsub.trans hCsub)]
    rw [heq]
    exact hembC.measurableSet_image.mpr (measurable_subtype_coe (measurable_subtype_coe hB))

  refine (integrable_cond_adelicBox F f _hf).ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun s hs _ => ?_)

  have hae_box : ∀ᵐ x ∂ν, x ∈ adelicBox F :=
    ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
  have hcap : (∫ x in s, f x ∂ν) = ∫ x in s ∩ adelicBox F, f x ∂ν := by
    refine setIntegral_congr_set ?_
    filter_upwards [hae_box] with x hx
    exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  rw [hcap]

  set E := (QuotientAddGroup.mk : AdeleRing (𝓞 F) F → AQuot F) '' (s ∩ adelicBox F) with hE
  have hEmeas : MeasurableSet E :=
    himage _ (hs.inter (measurableSet_adelicBox F)) Set.inter_subset_right
  have hRiesz := setIntegral_preimage_quotientAddGroup_mk_eq_zero F ψ hψ f _hf _hcoef E hEmeas

  have hpre : (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E ∩ adelicBox F = s ∩ adelicBox F := by
    ext x; constructor
    · rintro ⟨⟨y, ⟨hys, hybox⟩, hxy⟩, hxbox⟩
      exact ⟨(quotientAddGroup_mk_injOn_adelicBox F hybox hxbox hxy) ▸ hys, hxbox⟩
    · rintro ⟨hxs, hxbox⟩
      exact ⟨⟨x, ⟨hxs, hxbox⟩, rfl⟩, hxbox⟩
  calc ∫ x in s ∩ adelicBox F, f x ∂ν
      = ∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E ∩ adelicBox F, f x ∂ν := by rw [hpre]
    _ = ∫ x in (QuotientAddGroup.mk : _ → AQuot F) ⁻¹' E, f x ∂ν := by
        refine (setIntegral_congr_set ?_).symm
        filter_upwards [hae_box] with x hx
        exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
    _ = 0 := hRiesz

end Bridge

end Topology

end D2Bricks

end



open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

noncomputable section

namespace D2Proof

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

scoped instance instCountableNumberFieldProof : Countable F := by
  obtain ⟨_, s, h⟩ := Module.Finite.exists_fin (R := ℚ) (M := F)
  have hspan : Countable (Submodule.span ℚ (Set.range s)) := inferInstance
  rw [h] at hspan
  exact (Submodule.topEquiv.symm.toEquiv.countable_iff).mpr hspan

theorem addChar_neg_algebraMap_mul_ne_one
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) {α : F} (hα : α ≠ 0) :
    ∃ y : AdeleRing (𝓞 F) F, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y)) ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ.nontrivial (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  refine ⟨algebraMap F (AdeleRing (𝓞 F) F) (-α⁻¹) * x₀, ?_⟩
  have key : -(algebraMap F (AdeleRing (𝓞 F) F) α *
      (algebraMap F (AdeleRing (𝓞 F) F) (-α⁻¹) * x₀)) = x₀ := by
    rw [← mul_assoc, ← map_mul, mul_neg, mul_inv_cancel₀ hα, map_neg, map_one, neg_one_mul,
      neg_neg]
  rw [key]; exact hx₀

scoped instance : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

theorem addChar_neg_algebraMap_mul_vadd_invariant
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (α : F) :
    ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (x : AdeleRing (𝓞 F) F),
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * (γ +ᵥ x))) =
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  rintro ⟨_, β, rfl⟩ x
  have hv : ((⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F) +ᵥ x)
      = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl
  rw [hv, mul_add, neg_add, ψ.map_add_eq_mul]
  have h1 : ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α *
      algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
    rw [← map_mul, ← map_neg]
    exact hψ.principalInvariant (-(α * β))
  rw [h1, one_mul]

theorem setIntegral_adelicBox_addChar_neg_algebraMap_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) {α : F} (hα : α ≠ 0) :
    ∫ x in adelicBox F, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set μ := adelicAddHaar (𝓞 F) F with hμ
  set α𝔸 := algebraMap F (AdeleRing (𝓞 F) F) α
  set f : AdeleRing (𝓞 F) F → ℂ := fun x => ψ (-(α𝔸 * x)) with hf
  obtain ⟨y₀, hy₀⟩ := addChar_neg_algebraMap_mul_ne_one F ψ hψ hα
  set c : ℂ := ψ (-(α𝔸 * y₀)) with hc
  have hFD_B : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox_adelicAddHaar F
  have hFD_shift :
      IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
        ((Equiv.addLeft y₀) '' adelicBox F) μ := by
    refine hFD_B.image_of_equiv (Equiv.addLeft y₀)
      (measurePreserving_add_left μ (-y₀)).quasiMeasurePreserving (Equiv.refl _) ?_
    intro γ x
    simp only [Equiv.coe_addLeft, Equiv.refl_apply, AddSubgroup.vadd_def]
    exact (add_left_comm _ _ _).symm
  have hf_periodic := addChar_neg_algebraMap_mul_vadd_invariant F ψ hψ α
  have step1 : ∫ x in adelicBox F, f x ∂μ =
      ∫ x in (Equiv.addLeft y₀) '' adelicBox F, f x ∂μ :=
    hFD_B.setIntegral_eq hFD_shift hf_periodic
  have step2 : ∫ x in (Equiv.addLeft y₀) '' adelicBox F, f x ∂μ
      = c * ∫ x in adelicBox F, f x ∂μ := by
    have hmp : MeasurePreserving (fun x => y₀ + x) μ μ := measurePreserving_add_left μ y₀
    have hemb : MeasurableEmbedding (fun x : AdeleRing (𝓞 F) F => y₀ + x) :=
      (Homeomorph.addLeft y₀).measurableEmbedding
    have heq : (Equiv.addLeft y₀) '' adelicBox F = (fun x => y₀ + x) '' adelicBox F := rfl
    rw [heq, hmp.setIntegral_image_emb hemb f (adelicBox F)]
    have hsplit : ∀ x, f (y₀ + x) = c * f x := fun x => by
      simp only [hf, hc, α𝔸, mul_add, neg_add, ψ.map_add_eq_mul]
    simp_rw [hsplit]
    exact integral_const_mul c _
  have hI := step1.trans step2
  have h1c : (1 - c) * ∫ x in adelicBox F, f x ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hI
  exact (mul_eq_zero.mp h1c).resolve_left (sub_ne_zero.mpr hy₀.symm)

open scoped Classical in

theorem zero_mem_adelicBox : (0 : AdeleRing (𝓞 F) F) ∈ adelicBox F := by
  refine ⟨?_, ?_⟩
  ·
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [map_zero, ZSpan.mem_fundamentalDomain]
    intro i
    rw [map_zero, Finsupp.zero_apply]
    exact ⟨le_refl 0, zero_lt_one⟩
  ·
    intro v; exact zero_mem _

scoped instance : IsProbabilityMeasure
    (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
  isProbabilityMeasure_cond_adelicBox F

theorem ae_cond_mem_adelicBox :
    ∀ᵐ x ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)), x ∈ adelicBox F := by
  have h : (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)) (adelicBox F)ᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply (measurableSet_adelicBox F),
      Set.inter_compl_self, measure_empty, mul_zero]
  exact h

theorem integrable_cond_of_continuous {f : AdeleRing (𝓞 F) F → ℂ} (hf : Continuous f) :
    Integrable f (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
      (adelicBox F)) := by
  obtain ⟨C, hC_compact, hC_sub⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC_compact.exists_bound_of_continuousOn (f := f) hf.continuousOn
  refine Integrable.of_bound (hf.aestronglyMeasurable) M ?_
  filter_upwards [ae_cond_mem_adelicBox F] with x hx
  exact hM x (hC_sub hx)

theorem d2_completeness_hole
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f)
    (hcoef : ∀ α : F,
      ∫ x, f x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
          (adelicBox F)) = 0) :
    f 0 = 0 := by
  exact D2Brick7.eq_at_zero_of_ae_eq_cond_adelicBox F hf continuous_const
    (D2Bricks.ae_eq_zero_cond_of_forall_integral_eq_zero F ψ hψ f hf hcoef)

theorem continuous_addChar_algebraMap_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (α : F) :
    Continuous (fun x => ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) :=
  hψ.continuous.comp (continuous_const.mul continuous_id)

theorem hasSum_G
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (W : F → ℂ) (hsum : Summable W) (x : AdeleRing (𝓞 F) F) :
    HasSum (fun α : F => W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x))
      (∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  refine Summable.hasSum (.of_norm_bounded hsum.norm ?_)
  intro α
  rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]

theorem summable_G_shifted
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (W : F → ℂ) (hsum : Summable W) (β : F) (x : AdeleRing (𝓞 F) F) :
    Summable (fun α : F => W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x)) := by
  refine .of_norm_bounded hsum.norm ?_
  intro α
  rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]

open scoped Classical in
theorem integral_cond_addChar_algebraMap_sub
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (α β : F) :
    ∫ x, ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x)
      ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
        (adelicBox F)) = if α = β then 1 else 0 := by
  split_ifs with hαβ
  · rw [hαβ, sub_self, map_zero]
    simp only [zero_mul, AddChar.map_zero_eq_one, integral_const]
    rw [probReal_univ, one_smul]
  · have hne : α - β ≠ 0 := sub_ne_zero.mpr hαβ
    have harg : ∀ x : AdeleRing (𝓞 F) F,
        algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x
          = -(algebraMap F (AdeleRing (𝓞 F) F) (-(α - β)) * x) := fun x => by
      rw [map_neg, neg_mul, neg_neg]
    simp_rw [harg]
    rw [ProbabilityTheory.cond, integral_smul_measure]
    rw [show (∫ x, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (-(α - β)) * x))
        ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F))) =
      ∫ x in adelicBox F, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (-(α - β)) * x))
        ∂(adelicAddHaar (𝓞 F) F) from rfl]
    rw [setIntegral_adelicBox_addChar_neg_algebraMap_mul F ψ hψ (neg_ne_zero.mpr hne), smul_zero]

open scoped Classical in
theorem integral_G_mul_addChar
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (W : F → ℂ) (hsum : Summable W) (β : F) :
    ∫ x, (∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x))
      ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
        (adelicBox F)) = W β := by
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)
  have hrew : ∀ x, (∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) *
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x))
        = ∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x) := by
    intro x
    rw [← (hasSum_G F ψ hψ W hsum x).summable.tsum_mul_right]
    congr 1 with α
    rw [mul_assoc, ← ψ.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, ← map_sub]
  simp_rw [hrew]
  have hswap : HasSum (fun α : F => ∫ x, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x) ∂ν)
      (∫ x, ∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x) ∂ν) := by
    refine hasSum_integral_of_dominated_convergence (fun α _ => ‖W α‖)
      (fun α => ?_) (fun α => ?_) ?_ ?_ ?_
    · exact ((hψ.continuous.comp (continuous_const.mul continuous_id)).const_mul
        (W α)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]
    · filter_upwards with x; exact hsum.norm
    · exact integrable_const _
    · filter_upwards with x
      exact (summable_G_shifted F ψ hψ W hsum β x).hasSum
  have heval : ∀ α : F, ∫ x, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x) ∂ν
      = W α * (if α = β then 1 else 0) := by
    intro α
    rw [integral_const_mul, integral_cond_addChar_algebraMap_sub F ψ hψ α β]
  have hswap' : HasSum (fun α : F => W α * (if α = β then 1 else 0))
      (∫ x, ∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) (α - β) * x) ∂ν) := by
    refine hswap.congr_fun ?_
    intro α; rw [heval α]
  have hval : HasSum (fun α : F => W α * (if α = β then 1 else 0)) (W β) := by
    have : (fun α : F => W α * (if α = β then 1 else 0))
        = (fun α : F => if α = β then W β else 0) := by
      funext α; split_ifs with hα
      · rw [hα, mul_one]
      · rw [mul_zero]
    rw [this]
    exact hasSum_ite_eq β (W β)
  exact hswap'.unique hval

theorem continuous_G
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (W : F → ℂ) (hsum : Summable W) :
    Continuous (fun x => ∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  refine continuous_tsum (fun α => ?_) hsum.norm ?_
  · exact (hψ.continuous.comp (continuous_const.mul continuous_id)).const_mul (W α)
  · intro α x
    rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]

theorem innerSolution
    (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)) :
    HasSum (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)
      (φ g) := by
  set h : AdeleRing (𝓞 F) F → ℂ := fun x => φ (unipotentGL2 x * g) with hh_def
  set W : F → ℂ :=
    fun α => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g with hW_def
  set ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
    (adelicBox F) with hν_def
  set G : AdeleRing (𝓞 F) F → ℂ :=
    fun x => ∑' α : F, W α * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) with hG_def
  have hW_int : ∀ α : F, W α =
      ∫ x, h x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂ν := by
    intro α; exact whittakerCoefficient_eq_integral F _ ψ φ α g
  have hG_coef : ∀ β : F,
      ∫ x, G x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x)) ∂ν = W β :=
    fun β => integral_G_mul_addChar F ψ hψ W hsum β
  have hdiff_coef : ∀ β : F,
      ∫ x, (h x - G x) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x)) ∂ν = 0 := by
    intro β
    have hψβ : Continuous (fun x => ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x))) :=
      hψ.continuous.comp ((continuous_const.mul continuous_id).neg)
    have hint_h : Integrable
        (fun x => h x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x))) ν :=
      integrable_cond_of_continuous F (hcont.mul hψβ)
    have hint_G : Integrable
        (fun x => G x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) β * x))) ν :=
      integrable_cond_of_continuous F ((continuous_G F ψ hψ W hsum).mul hψβ)
    simp_rw [sub_mul]
    rw [integral_sub hint_h hint_G, ← hW_int β, hG_coef β, sub_self]
  have hG_cont : Continuous G := continuous_G F ψ hψ W hsum
  have hdiff_cont : Continuous (fun x => h x - G x) := hcont.sub hG_cont
  have hzero : h 0 - G 0 = 0 :=
    d2_completeness_hole F ψ hψ (fun x => h x - G x) hdiff_cont hdiff_coef
  have h0 : h 0 = G 0 := sub_eq_zero.mp hzero
  have hh0 : h 0 = φ g := by simp only [hh_def, unipotentGL2_zero, one_mul]
  have hG_at0 : HasSum (fun α : F => W α) (G 0) := by
    have hG0_eq : G 0 = ∑' α : F, W α := by
      simp only [hG_def, mul_zero, AddChar.map_zero_eq_one, mul_one]
    rw [hG0_eq]
    have := hasSum_G F ψ hψ W hsum 0
    simpa only [mul_zero, AddChar.map_zero_eq_one, mul_one] using this
  rw [← hh0, h0]
  exact hG_at0

end D2Proof

end


/-- Whittaker/Fourier expansion along the adelic unipotent subgroup: for a
global additive character `ψ`, a function `φ` whose unipotent translate is
continuous, and summable Whittaker coefficients, the coefficients sum to
`φ g`. -/
public theorem AutomorphicForm.hasSum_whittakerCoefficient
    (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)) :
    HasSum (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)
      (φ g) :=
  D2Proof.innerSolution F D U gen ψ hψ φ g hcont hsum
