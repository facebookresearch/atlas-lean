/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.OSSS.GrandCouplingAssembly

open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace StatMech
namespace OSSS
namespace AdaptiveCodingLaw

open Coding GrandCoupling GrandCouplingAssembly Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]



def PredictableOrder {n : ℕ} (σ : ConfigSpace E → (Fin n ≃ E)) : Prop :=
  ∀ (x y : ConfigSpace E) (t : Fin n),
    Agree (prefixSet (σ x : Fin n → E) (t : ℕ)) x y →
      (σ y : Fin n → E) t = (σ x : Fin n → E) t



lemma order_eq_on_prefix {n : ℕ} {σ : ConfigSpace E → (Fin n ≃ E)}
    (hσ : PredictableOrder σ) {x y : ConfigSpace E} {m : ℕ} (hm : m ≤ n)
    (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
    ∀ (i : ℕ) (hi : i < m),
      (σ y : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ =
        (σ x : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ := by
  intro i hi
  apply hσ x y
  intro e he
  apply hxy e
  obtain ⟨j, hj, rfl⟩ := (mem_prefixSet_iff (σ x : Fin n → E) i e).mp he
  rw [mem_prefixSet_iff]
  exact ⟨j, lt_trans hj hi, rfl⟩


lemma prefixSet_eq_of_predictable {n : ℕ} {σ : ConfigSpace E → (Fin n ≃ E)}
    (hσ : PredictableOrder σ) {x y : ConfigSpace E} {m : ℕ} (hm : m ≤ n)
    (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
    prefixSet (σ y : Fin n → E) m = prefixSet (σ x : Fin n → E) m := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, hie⟩ := (mem_prefixSet_iff (σ y : Fin n → E) m e).mp he
    rw [mem_prefixSet_iff]
    refine ⟨i, hi, ?_⟩
    rw [← hie]
    exact (order_eq_on_prefix hσ hm hxy (i : ℕ) hi).symm
  · intro he
    obtain ⟨i, hi, hie⟩ := (mem_prefixSet_iff (σ x : Fin n → E) m e).mp he
    rw [mem_prefixSet_iff]
    refine ⟨i, hi, ?_⟩
    rw [← hie]
    exact order_eq_on_prefix hσ hm hxy (i : ℕ) hi




theorem codeMap_eq_unique_of_predictable (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (u : Fin n → ℝ) {x y : ConfigSpace E}
    (hx : codeMap μ (σ x : Fin n → E) u = x)
    (hy : codeMap μ (σ y : Fin n → E) u = y) :
    x = y := by
  have hbitsX := (codeMap_eq_iff μ (σ x) x u).mp hx
  have hbitsY := (codeMap_eq_iff μ (σ y) y u).mp hy
  have hagree : ∀ m : ℕ, m ≤ n →
      Agree (prefixSet (σ x : Fin n → E) m) x y := by
    intro m hm
    induction m with
    | zero =>
        intro e he
        simp [prefixSet, prefixIdx] at he
    | succ m ih =>
        have hmn : m < n := by omega
        have hmle : m ≤ n := Nat.le_of_lt hmn
        have hprev := ih hmle
        have hsel : (σ y : Fin n → E) ⟨m, hmn⟩ =
            (σ x : Fin n → E) ⟨m, hmn⟩ := hσ x y ⟨m, hmn⟩ hprev
        have hpref : prefixSet (σ y : Fin n → E) m =
            prefixSet (σ x : Fin n → E) m :=
          prefixSet_eq_of_predictable hσ hmle hprev
        have hthr : thr μ (σ y : Fin n → E) y ⟨m, hmn⟩ =
            thr μ (σ x : Fin n → E) x ⟨m, hmn⟩ := by
          unfold thr
          rw [hpref, hsel]
          apply condProbClosed_congr
          intro e he
          exact hprev e he
        have hnew : y ((σ x : Fin n → E) ⟨m, hmn⟩) =
            x ((σ x : Fin n → E) ⟨m, hmn⟩) := by
          have hxbit := hbitsX ⟨m, hmn⟩
          have hybit := hbitsY ⟨m, hmn⟩
          rw [hsel, hthr] at hybit
          exact hybit.trans hxbit.symm
        rw [prefixSet_succ_lt (σ x : Fin n → E) m hmn]
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hnew
        · exact hprev e he
  have hfull := hagree n le_rfl
  rw [prefixSet_card (σ x)] at hfull
  funext e
  exact (hfull e (Finset.mem_univ e)).symm


theorem predictable_fibres_disjoint (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    {x y : ConfigSpace E} (hxy : x ≠ y) :
    Disjoint {u | codeMap μ (σ x : Fin n → E) u = x}
      {u | codeMap μ (σ y : Fin n → E) u = y} := by
  rw [Set.disjoint_left]
  intro u hux huy
  exact hxy (codeMap_eq_unique_of_predictable μ σ hσ u hux huy)


def adaptiveFibre (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (x : ConfigSpace E) : Set (Fin n → ℝ) :=
  {u | codeMap μ (σ x : Fin n → E) u = x}

lemma measurableSet_adaptiveFibre (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (x : ConfigSpace E) :
    MeasurableSet (adaptiveFibre μ σ x) := by
  exact (measurable_codeMap μ (σ x)) (measurableSet_singleton x)



lemma vcube_adaptiveFibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : ConfigSpace E → (Fin n ≃ E))
    (x : ConfigSpace E) :
    ((Vcube n) (adaptiveFibre μ σ x)).toReal = μ x := by
  exact vcube_fibre μ hpos hμ1 (σ x) x





theorem predictable_adaptive_fibres_full_measure (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ((Vcube n) (⋃ x, adaptiveFibre μ σ x)).toReal = 1 := by
  have hdisj : ∀ x ∈ (Finset.univ : Finset (ConfigSpace E)),
      ∀ y ∈ (Finset.univ : Finset (ConfigSpace E)), x ≠ y →
        Disjoint (adaptiveFibre μ σ x) (adaptiveFibre μ σ y) := by
    intro x _ y _ hxy
    exact predictable_fibres_disjoint μ σ hσ hxy
  have hmeas : ∀ x ∈ (Finset.univ : Finset (ConfigSpace E)),
      MeasurableSet (adaptiveFibre μ σ x) := by
    intro x _
    exact measurableSet_adaptiveFibre μ σ x
  have hmeasure : (Vcube n) (⋃ x, adaptiveFibre μ σ x) =
      ∑ x : ConfigSpace E, (Vcube n) (adaptiveFibre μ σ x) := by
    rw [← measure_biUnion_finset hdisj hmeas]
    congr 1
    ext u
    simp
  rw [hmeasure, ENNReal.toReal_sum (fun x _ => measure_ne_top (Vcube n) _)]
  simp_rw [vcube_adaptiveFibre μ hpos hμ1 σ]
  exact hμ1



noncomputable def adaptiveCode (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (u : Fin n → ℝ) : ConfigSpace E := by
  classical
  exact if h : ∃ x, u ∈ adaptiveFibre μ σ x then Classical.choose h else fun _ => false

lemma adaptiveCode_eq_of_mem (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (u : Fin n → ℝ) (x : ConfigSpace E) (hx : u ∈ adaptiveFibre μ σ x) :
    adaptiveCode μ σ u = x := by
  unfold adaptiveCode
  rw [dif_pos ⟨x, hx⟩]
  let y := Classical.choose (show ∃ y, u ∈ adaptiveFibre μ σ y from ⟨x, hx⟩)
  have hy : u ∈ adaptiveFibre μ σ y :=
    Classical.choose_spec (show ∃ y, u ∈ adaptiveFibre μ σ y from ⟨x, hx⟩)
  exact codeMap_eq_unique_of_predictable μ σ hσ u hy hx

lemma measurableSet_adaptiveFibre_union (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) :
    MeasurableSet (⋃ x, adaptiveFibre μ σ x) := by
  exact MeasurableSet.iUnion (fun x => measurableSet_adaptiveFibre μ σ x)


theorem ae_mem_adaptiveFibre_union (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ∀ᵐ u ∂(Vcube n), u ∈ ⋃ x, adaptiveFibre μ σ x := by
  refine (ae_iff_measure_eq
    (measurableSet_adaptiveFibre_union μ σ).nullMeasurableSet).2 ?_
  have hreal := predictable_adaptive_fibres_full_measure μ hpos hμ1 σ hσ
  have hmass : (Vcube n) (⋃ x, adaptiveFibre μ σ x) = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp hreal
  simpa using hmass



theorem adaptiveCode_eq_iff_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (x : ConfigSpace E) :
    ∀ᵐ u ∂(Vcube n), adaptiveCode μ σ u = x ↔ u ∈ adaptiveFibre μ σ x := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  constructor
  · intro hcode
    simp only [Set.mem_iUnion] at hu
    obtain ⟨y, hy⟩ := hu
    have hcy := adaptiveCode_eq_of_mem μ σ hσ u y hy
    have hyx : y = x := hcy.symm.trans hcode
    simpa [hyx] using hy
  · exact adaptiveCode_eq_of_mem μ σ hσ u x




theorem codeMap_selectedOrder_eq_adaptiveCode_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ∀ᵐ u ∂(Vcube n),
      codeMap μ (σ (adaptiveCode μ σ u) : Fin n → E) u = adaptiveCode μ σ u := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨x, hx⟩ := hu
  have hcode := adaptiveCode_eq_of_mem μ σ hσ u x hx
  rw [hcode]
  exact hx




theorem adaptiveCode_fibre_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (x : ConfigSpace E) :
    ((Vcube n) {u | adaptiveCode μ σ u = x}).toReal = μ x := by
  have hset : {u | adaptiveCode μ σ u = x} =ᵐ[Vcube n] adaptiveFibre μ σ x := by
    filter_upwards [adaptiveCode_eq_iff_ae μ hpos hμ1 σ hσ x] with u hu
    exact propext hu
  rw [measure_congr hset]
  exact vcube_adaptiveFibre μ hpos hμ1 σ x



lemma observable_adaptiveCode_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    (fun u => g (adaptiveCode μ σ u)) =ᵐ[Vcube n]
      (fun u => ∑ x, g x *
        Set.indicator (adaptiveFibre μ σ x) (fun _ => (1 : ℝ)) u) := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨y, hy⟩ := hu
  rw [adaptiveCode_eq_of_mem μ σ hσ u y hy, Finset.sum_eq_single y]
  · rw [Set.indicator_of_mem hy]
    ring
  · intro x _ hxy
    rw [Set.indicator_of_notMem]
    · ring
    · intro hx
      exact hxy (codeMap_eq_unique_of_predictable μ σ hσ u hx hy)
  · intro hyu
    exact absurd (Finset.mem_univ y) hyu




lemma aestronglyMeasurable_observable_adaptiveCode (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    AEStronglyMeasurable (fun u => g (adaptiveCode μ σ u)) (Vcube n) := by
  apply AEStronglyMeasurable.congr _
    (observable_adaptiveCode_ae μ hpos hμ1 σ hσ g).symm
  apply Measurable.aestronglyMeasurable
  apply Finset.measurable_sum
  intro x _
  exact measurable_const.mul
    (measurable_const.indicator (measurableSet_adaptiveFibre μ σ x))




theorem integral_g_adaptiveCode (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    ∫ u, g (adaptiveCode μ σ u) ∂(Vcube n) = ∑ x, g x * μ x := by
  rw [integral_congr_ae (observable_adaptiveCode_ae μ hpos hμ1 σ hσ g), integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul,
      integral_indicator_const (1 : ℝ) (measurableSet_adaptiveFibre μ σ x), smul_eq_mul,
      mul_one]
    show g x * ((Vcube n) (adaptiveFibre μ σ x)).toReal = g x * μ x
    rw [vcube_adaptiveFibre μ hpos hμ1 σ x]
  · intro x _
    exact Integrable.const_mul
      (Integrable.indicator (integrable_const 1) (measurableSet_adaptiveFibre μ σ x)) _









theorem integral_g_adaptiveCode_Wt (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) (s : ℕ) :
    ∫ p, g (adaptiveCode μ σ (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n)) =
      ∑ x, g x * μ x := by
  have hmp := selMap_measurePreserving n s
  have hcomp :
      ∫ p, (fun w => g (adaptiveCode μ σ w)) (selMap n s p)
          ∂((Vcube n).prod (Vcube n)) =
        ∫ w, g (adaptiveCode μ σ w) ∂(Vcube n) := by
    have hae := aestronglyMeasurable_observable_adaptiveCode μ hpos hμ1 σ hσ g
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable, hmp.map_eq]
    rwa [hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun w => g (adaptiveCode μ σ w)) (selMap n s p)) =
      (fun p => g (adaptiveCode μ σ (Wt p.1 p.2 s))) := by
    funext p
    rw [show p = (p.1, p.2) from rfl, selMap_eq_Wt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_adaptiveCode μ hpos hμ1 σ hσ g]





theorem integral_g_independent_randomOrder (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (order : (Fin n → ℝ) → (Fin n ≃ E)) (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (order U : Fin n → E) V) ∂(Vcube n)) ∂(Vcube n) =
      ∑ x, g x * μ x := by
  have hinner : ∀ U : Fin n → ℝ,
      (∫ V, g (codeMap μ (order U : Fin n → E) V) ∂(Vcube n)) =
        ∑ x, g x * μ x := by
    intro U
    exact integral_g_codeMap μ hpos hμ1 (order U) g
  simp_rw [hinner]
  rw [integral_const]
  simp





theorem integral_g_frozenOrder_Wt_zero (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V 0)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
  calc
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V 0)) ∂(Vcube n)) ∂(Vcube n)
        = ∫ U, g (adaptiveCode μ σ U) ∂(Vcube n) := by
          apply integral_congr_ae
          filter_upwards
            [codeMap_selectedOrder_eq_adaptiveCode_ae μ hpos hμ1 σ hσ] with U hU
          simp only [Wt_zero, hU]
          rw [integral_const]
          simp
    _ = ∑ x, g x * μ x := integral_g_adaptiveCode μ hpos hμ1 σ hσ g





theorem integral_g_frozenOrder_Wt_card (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V n)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
  simpa only [Wt_card] using
    integral_g_independent_randomOrder μ hpos hμ1
      (fun U => σ (adaptiveCode μ σ U)) g

end AdaptiveCodingLaw
end OSSS
end StatMech
