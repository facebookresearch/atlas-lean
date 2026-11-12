/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.Ising.PlusStateTI
import Code.Ising.GibbsSimplexUncond

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}













noncomputable def pstc_decayFun (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) : ℝ :=
  (∫ x, f x ∂(μ n : Measure _)) - (∫ x, f (shift g x) ∂(μ n : Measure _))






theorem pstc_decayFun_sub_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) :
    |pstc_decayFun μ g f n - pstc_decayFun μ g f' n| ≤ 2 * ‖f - f'‖ := by
  set T : C(ConfigSpace (Site d), ConfigSpace (Site d)) :=
    ⟨shift g, continuous_shift g⟩ with hT
  let μn : Measure (ConfigSpace (Site d)) := (μ n : Measure _)
  have hsub1 : (∫ x, f x ∂μn) - (∫ x, f' x ∂μn) = ∫ x, (f - f') x ∂μn := by
    rw [← integral_sub (f.integrable _) (f'.integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  have hsub2 : (∫ x, f (shift g x) ∂μn) - (∫ x, f' (shift g x) ∂μn)
      = ∫ x, ((f - f').compContinuous T) x ∂μn := by
    rw [show (fun x => f (shift g x)) = (fun x => (f.compContinuous T) x) from rfl,
      show (fun x => f' (shift g x)) = (fun x => (f'.compContinuous T) x) from rfl,
      ← integral_sub ((f.compContinuous T).integrable _) ((f'.compContinuous T).integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.compContinuous_apply, BoundedContinuousFunction.coe_sub,
      Pi.sub_apply]
  have hlin : pstc_decayFun μ g f n - pstc_decayFun μ g f' n
      = (∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn) := by
    simp only [pstc_decayFun]
    rw [← hsub1, ← hsub2]; ring
  rw [hlin]
  calc |(∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn)|
      ≤ |∫ x, (f - f') x ∂μn| + |∫ x, ((f - f').compContinuous T) x ∂μn| := abs_sub _ _
    _ ≤ ‖f - f'‖ + ‖f - f'‖ := by
        gcongr
        · have := (f - f').norm_integral_le_norm μn
          rwa [Real.norm_eq_abs] at this
        · have h1 := ((f - f').compContinuous T).norm_integral_le_norm μn
          have h2 := (f - f').norm_compContinuous_le T
          rw [Real.norm_eq_abs] at h1
          exact h1.trans h2
    _ = 2 * ‖f - f'‖ := by ring


theorem pstc_abs_decay_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) :
    |pstc_decayFun μ g f n| ≤ 2 * ‖f - f'‖ + |pstc_decayFun μ g f' n| := by
  have h := pstc_decayFun_sub_le μ g f f' n
  have hsplit : |pstc_decayFun μ g f n|
      ≤ |pstc_decayFun μ g f n - pstc_decayFun μ g f' n| + |pstc_decayFun μ g f' n| := by
    calc |pstc_decayFun μ g f n|
        = |(pstc_decayFun μ g f n - pstc_decayFun μ g f' n) + pstc_decayFun μ g f' n| := by
          ring_nf
      _ ≤ |pstc_decayFun μ g f n - pstc_decayFun μ g f' n| + |pstc_decayFun μ g f' n| :=
          abs_add_le _ _
  linarith [hsplit, h]










theorem pstc_tendsto_decay_of_dense (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) {D : Set ((ConfigSpace (Site d)) →ᵇ ℝ)}
    (hD : Dense D)
    (hdecay : ∀ f' ∈ D, Tendsto (pstc_decayFun μ g f') atTop (𝓝 0))
    (f : (ConfigSpace (Site d)) →ᵇ ℝ) :
    Tendsto (pstc_decayFun μ g f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨f', hf'D, hf'close⟩ := hD.exists_dist_lt f (by positivity : (0:ℝ) < ε / 4)
  have hnorm : ‖f - f'‖ < ε / 4 := by
    rwa [dist_eq_norm] at hf'close
  have hf' := hdecay f' hf'D
  rw [Metric.tendsto_atTop] at hf'
  obtain ⟨N, hN⟩ := hf' (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := pstc_abs_decay_le μ g f f' n
  have hf'n : |pstc_decayFun μ g f' n| < ε / 2 := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero] at this
  rw [Real.dist_eq, sub_zero]
  calc |pstc_decayFun μ g f n|
      ≤ 2 * ‖f - f'‖ + |pstc_decayFun μ g f' n| := hbound
    _ < 2 * (ε / 4) + ε / 2 := by gcongr
    _ = ε := by ring












noncomputable def pstc_coordCM (x : Site d) : C(ConfigSpace (Site d), ℝ) :=
  ⟨fun ω => if ω x then (1 : ℝ) else 0,
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (ConfigSpace.continuous_eval x)⟩

@[simp] theorem pstc_coordCM_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    pstc_coordCM x ω = if ω x then (1 : ℝ) else 0 := rfl



noncomputable def pstc_coordBcf (x : Site d) : ConfigSpace (Site d) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (pstc_coordCM x)

@[simp] theorem pstc_coordBcf_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    pstc_coordBcf x ω = if ω x then (1 : ℝ) else 0 := rfl



noncomputable def pstc_cylinderAlg (d : ℕ) : Subalgebra ℝ C(ConfigSpace (Site d), ℝ) :=
  Algebra.adjoin ℝ (Set.range (pstc_coordCM (d := d)))




theorem pstc_cylinderAlg_separatesPoints (d : ℕ) :
    (pstc_cylinderAlg d).SeparatesPoints := by
  rintro ω₁ ω₂ hne
  obtain ⟨x, hx⟩ : ∃ x, ω₁ x ≠ ω₂ x := by
    by_contra hc
    exact hne (funext fun x => not_not.mp (fun h => hc ⟨x, h⟩))
  refine ⟨(pstc_coordCM x : ConfigSpace (Site d) → ℝ),
    ⟨pstc_coordCM x, Algebra.subset_adjoin ⟨x, rfl⟩, rfl⟩, ?_⟩
  simp only [pstc_coordCM_apply]
  intro hcontra
  apply hx
  by_cases h1 : ω₁ x <;> by_cases h2 : ω₂ x <;> simp_all



noncomputable def pstc_cylinderBcfSet (d : ℕ) : Set (ConfigSpace (Site d) →ᵇ ℝ) :=
  BoundedContinuousFunction.mkOfCompact ''
    (pstc_cylinderAlg d : Set C(ConfigSpace (Site d), ℝ))





theorem pstc_cylinderBcfSet_dense (d : ℕ) : Dense (pstc_cylinderBcfSet d) := by
  rw [Metric.dense_iff]
  intro g ε hε
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (pstc_cylinderAlg d) (pstc_cylinderAlg_separatesPoints d) g.toContinuousMap ε hε
  refine ⟨BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)), ?_, ⟨(f : C(_, ℝ)), f.2, rfl⟩⟩
  rw [Metric.mem_ball]
  have hg : BoundedContinuousFunction.mkOfCompact g.toContinuousMap = g :=
    BoundedContinuousFunction.ext (congrFun rfl)
  calc dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ))) g
      = dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)))
          (BoundedContinuousFunction.mkOfCompact g.toContinuousMap) := by rw [hg]
    _ = dist (f : C(_, ℝ)) g.toContinuousMap := BoundedContinuousFunction.dist_mkOfCompact _ _
    _ = ‖(f : C(_, ℝ)) - g.toContinuousMap‖ := dist_eq_norm _ _
    _ < ε := hf








theorem pstc_decayFun_plus_eq (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f
      = fun n =>
        (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := rfl


theorem pstc_decayFun_minus_eq (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f
      = fun n =>
        (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := rfl















def pstc_PlusCylinderDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d,
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f) atTop (𝓝 0)


def pstc_MinusCylinderDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d,
    Tendsto (pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f) atTop (𝓝 0)









theorem pstc_plusIntegralShiftDecay_of_cylinderDecay (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hcyl : pstc_PlusCylinderDecay β h g φ) :
    pst_PlusIntegralShiftDecay β h g φ := by
  intro f
  have h := pstc_tendsto_decay_of_dense (fun n => plusMeasure d (φ n) β h) g
    (pstc_cylinderBcfSet_dense d) hcyl f
  rw [pstc_decayFun_plus_eq] at h
  exact h


theorem pstc_minusIntegralShiftDecay_of_cylinderDecay (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hcyl : pstc_MinusCylinderDecay β h g φ) :
    pst_MinusIntegralShiftDecay β h g φ := by
  intro f
  have h := pstc_tendsto_decay_of_dense (fun n => minusMeasure d (φ n) β h) g
    (pstc_cylinderBcfSet_dense d) hcyl f
  rw [pstc_decayFun_minus_eq] at h
  exact h









theorem pstc_decayFun_one (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (f : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
  simp only [pstc_decayFun, shift_one, id_eq, sub_self]


theorem pstc_plusCylinderDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : pstc_decayFun (fun n => plusMeasure d (φ n) β h)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact pstc_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds


theorem pstc_minusCylinderDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pstc_MinusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : pstc_decayFun (fun n => minusMeasure d (φ n) β h)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact pstc_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds












theorem pstc_plusState_isTranslationInvariant_of_cylinderDecay (β h : ℝ)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pstc_PlusCylinderDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pst_plusState_isTranslationInvariant_of_decay β h
    (fun g φ hφ hconv => pstc_plusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))


theorem pstc_minusState_isTranslationInvariant_of_cylinderDecay (β h : ℝ)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pstc_MinusCylinderDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) :=
  pst_minusState_isTranslationInvariant_of_decay β h
    (fun g φ hφ hconv => pstc_minusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))







theorem pstc_plusState_ergodic_extreme_of_cylinderDecay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pstc_PlusCylinderDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  gsu_plusState_ergodic_extreme_of_decay β h hd hβ hh
    (fun g φ hφ hconv => pstc_plusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))



theorem pstc_minusState_ergodic_extreme_of_cylinderDecay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pstc_MinusCylinderDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  gsu_minusState_ergodic_extreme_of_decay β h hd hβ hh hdlr
    (fun g φ hφ hconv => pstc_minusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))

end Ising

end StatMech
