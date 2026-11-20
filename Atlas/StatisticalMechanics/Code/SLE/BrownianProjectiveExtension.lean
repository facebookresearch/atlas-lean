/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianCompactCylinderIntersection
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent









open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.SLE




theorem brownianProjectiveContent_tendsto_zero
    (A : Nat -> Set (Real -> Real))
    (hA : forall n, A n ∈ measurableCylinders fun _ : Real => Real)
    (hanti : Antitone A) (hinter : iInter A = ∅) :
    Tendsto (fun n => brownianProjectiveContent (A n)) atTop (nhds 0) := by
  have hcontentAnti : Antitone (fun n => brownianProjectiveContent (A n)) := by
    intro a b hab
    exact brownianProjectiveContent_mono (hA b) (hA a) (hanti hab)
  rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hcontentAnti]
  intro epsilon hepsilon
  by_cases hepsilonTop : epsilon = ∞
  · refine ⟨0, (lt_top_iff_ne_top.mpr ?_).trans_eq hepsilonTop.symm⟩
    exact brownianProjectiveContent_ne_top (A 0)
  let I : Nat -> Finset Real := fun n => measurableCylinders.finset (hA n)
  let S : forall n, Set (I n -> Real) :=
    fun n => measurableCylinders.set (hA n)
  have hS (n : Nat) : MeasurableSet (S n) :=
    measurableCylinders.measurableSet (hA n)
  have hAeq (n : Nat) : A n = cylinder (I n) (S n) :=
    measurableCylinders.eq_cylinder (hA n)
  let error : Nat -> ENNReal := fun n =>
    (epsilon / 4) * (2⁻¹ : ENNReal) ^ n
  have herror (n : Nat) : error n ≠ 0 := by
    dsimp only [error]
    exact mul_ne_zero
      (ENNReal.div_ne_zero.2 ⟨hepsilon.ne', by norm_num⟩)
      (pow_ne_zero _ (by norm_num))
  have happrox (n : Nat) :
      exists L : Set (I n -> Real), L ⊆ S n ∧ IsCompact L ∧
        brownianFiniteDimensionalPiLaw (I n) (S n \ L) < error n := by
    obtain ⟨L, hLS, hLcompact, hLdiff⟩ :=
      (hS n).exists_isCompact_diff_lt
        (μ := brownianFiniteDimensionalPiLaw (I n))
        (measure_ne_top _ _) (herror n)
    exact ⟨L, hLS, hLcompact, hLdiff⟩
  choose L hLsubset hLcompact hLdiff using happrox
  have hprefixEmpty : exists N, cylinderPrefixBase I L N = ∅ := by
    by_contra hnone
    push Not at hnone
    have hprefixNonempty (n : Nat) :
        (cylinderPrefixBase I L n).Nonempty := hnone n
    have hprefixAnti : Antitone (fun n =>
        (cylinder (cylinderPrefixSupport I n) (cylinderPrefixBase I L n) :
          Set (Real -> Real))) := by
      intro a b hab x hx
      change x ∈ (cylinder (cylinderPrefixSupport I b)
        (cylinderPrefixBase I L b) : Set (Real -> Real)) at hx
      change x ∈ (cylinder (cylinderPrefixSupport I a)
        (cylinderPrefixBase I L a) : Set (Real -> Real))
      rw [cylinder_cylinderPrefixBase] at hx ⊢
      simp only [Set.mem_iInter] at hx ⊢
      intro k hka
      exact hx k (hka.trans hab)
    obtain ⟨x, hx⟩ := nonempty_iInter_cylinder_of_compact
      (cylinderPrefixSupport I) (cylinderPrefixBase I L)
      (cylinderPrefixBase_isCompact I L hLcompact) hprefixNonempty
      hprefixAnti
    have hxA : x ∈ iInter A := by
      rw [Set.mem_iInter]
      intro k
      have hxPrefix := Set.mem_iInter.1 hx k
      rw [cylinder_cylinderPrefixBase] at hxPrefix
      have hxL : x ∈ (cylinder (I k) (L k) : Set (Real -> Real)) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hxPrefix k) le_rfl
      rw [hAeq k]
      rw [mem_cylinder] at hxL ⊢
      exact hLsubset k hxL
    rw [hinter] at hxA
    exact hxA
  obtain ⟨N, hNempty⟩ := hprefixEmpty
  let U : Set (Real -> Real) :=
    iUnion fun k => iUnion fun _hk : k ∈ Finset.range (N + 1) =>
      (cylinder (I k) (S k \ L k) : Set (Real -> Real))
  have hdiffMeasurable (k : Nat) : MeasurableSet (S k \ L k) :=
    (hS k).diff (hLcompact k).isClosed.measurableSet
  have hdiffCylinder (k : Nat) :
      (cylinder (I k) (S k \ L k) : Set (Real -> Real)) ∈
        measurableCylinders fun _ : Real => Real :=
    cylinder_mem_measurableCylinders _ _ (hdiffMeasurable k)
  have hUmem : U ∈ measurableCylinders fun _ : Real => Real := by
    dsimp only [U]
    exact isSetRing_measurableCylinders.biUnion_mem (Finset.range (N + 1))
      (fun k _hk => hdiffCylinder k)
  have hANU : A N ⊆ U := by
    intro x hxAN
    by_contra hxU
    have hxPrefix : x ∈
        (cylinder (cylinderPrefixSupport I N) (cylinderPrefixBase I L N) :
          Set (Real -> Real)) := by
      rw [cylinder_cylinderPrefixBase]
      simp only [Set.mem_iInter]
      intro k hkN
      have hxAk : x ∈ A k := hanti hkN hxAN
      rw [hAeq k, mem_cylinder] at hxAk
      have hxNotDiff :
          x ∉ (cylinder (I k) (S k \ L k) : Set (Real -> Real)) := by
        intro hxDiff
        apply hxU
        exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2
          ⟨Finset.mem_range.2 (by omega), hxDiff⟩⟩
      rw [mem_cylinder] at hxNotDiff ⊢
      by_contra hxNotL
      exact hxNotDiff ⟨hxAk, hxNotL⟩
    rw [hNempty, cylinder_empty] at hxPrefix
    exact hxPrefix
  have hcontentU :
      brownianProjectiveContent U <=
        ∑ k ∈ Finset.range (N + 1),
          brownianProjectiveContent (cylinder (I k) (S k \ L k)) := by
    dsimp only [U]
    exact addContent_biUnion_le isSetRing_measurableCylinders
      (fun k _hk => hdiffCylinder k)
  have hsumError : (∑' n : Nat, error n) = epsilon / 2 := by
    simp only [error, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    congr 1
    change (((4 : NNReal) : ENNReal))⁻¹ * ((2 : NNReal) : ENNReal) =
      (((2 : NNReal) : ENNReal))⁻¹
    rw [← ENNReal.coe_inv (show (4 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_inv (show (2 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_mul]
    norm_num
  refine ⟨N, ?_⟩
  calc
    brownianProjectiveContent (A N) <= brownianProjectiveContent U :=
      brownianProjectiveContent_mono (hA N) hUmem hANU
    _ <= ∑ k ∈ Finset.range (N + 1),
        brownianProjectiveContent (cylinder (I k) (S k \ L k)) := hcontentU
    _ <= ∑ k ∈ Finset.range (N + 1), error k := by
      exact Finset.sum_le_sum fun k _hk => by
        rw [brownianProjectiveContent_cylinder]
        · exact (hLdiff k).le
        · exact hdiffMeasurable k
    _ <= ∑' k : Nat, error k := ENNReal.sum_le_tsum _
    _ = epsilon / 2 := hsumError
    _ < epsilon := ENNReal.half_lt_self hepsilon.ne' hepsilonTop



theorem brownianProjectiveContent_isSigmaSubadditive :
    brownianProjectiveContent.IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hfUnion hfDisjoint => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero
    isSetRing_measurableCylinders brownianProjectiveContent
    (fun _ _ => brownianProjectiveContent_ne_top _) ?_ hf hfUnion hfDisjoint
  exact fun A hA hanti hinter =>
    brownianProjectiveContent_tendsto_zero A hA hanti hinter



noncomputable def brownianProductLaw : Measure (Real -> Real) :=
  brownianProjectiveContent.measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    brownianProjectiveContent_isSigmaSubadditive

instance brownianProductLaw.isProbabilityMeasure :
    IsProbabilityMeasure brownianProductLaw where
  measure_univ := by
    rw [brownianProductLaw, AddContent.measure_eq]
    · exact brownianProjectiveContent_univ
    · exact generateFrom_measurableCylinders.symm
    · exact univ_mem_measurableCylinders fun _ : Real => Real



theorem brownianProductLaw_isProjectiveLimit :
    IsProjectiveLimit brownianProductLaw brownianFiniteDimensionalPiLaw := by
  intro I
  ext S hS
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]
  change brownianProductLaw (cylinder I S) =
    brownianFiniteDimensionalPiLaw I S
  rw [brownianProductLaw, AddContent.measure_eq,
    brownianProjectiveContent_cylinder I S hS]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hS

end StatMech.SLE
