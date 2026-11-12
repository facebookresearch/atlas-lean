/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.FunctionalBKRGeneralDual
import Code.FrontierA.FunctionalBKRGeneralFinite
import Code.Probability.InhomogeneousProduct
import Mathlib.MeasureTheory.Function.EssSup

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


abbrev AgreementFiberPoint (K : Set E) (omega : ConfigSpace E) :=
  {eta : ConfigSpace E // agreeOn K omega eta}



noncomputable def agreementFiberMeasure
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) (K : Set E)
    (omega : ConfigSpace E) : Measure (AgreementFiberPoint K omega) :=
  Measure.comap Subtype.val
    ((inhomBernoulliProductMeasure p hp).restrict
      {eta | agreeOn K omega eta})

omit [DecidableEq E] in
theorem agreementFiberMeasure_singleton_ne_zero
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (K : Set E) (omega : ConfigSpace E)
    (eta : AgreementFiberPoint K omega) :
    agreementFiberMeasure p (fun e => (hp1 e).le) K omega {eta} ≠ 0 := by
  rw [agreementFiberMeasure, Measure.comap_apply Subtype.val
    Subtype.val_injective (fun _ _ => MeasurableSet.of_discrete)
    _ (measurableSet_singleton eta)]
  have himage : Subtype.val '' ({eta} : Set (AgreementFiberPoint K omega)) =
      {eta.1} := by
    ext z
    simp
  rw [himage, Measure.restrict_apply (measurableSet_singleton eta.1)]
  have hinter : ({eta.1} : Set (ConfigSpace E)) ∩
      {z | agreeOn K omega z} = {eta.1} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro h
      subst z
      exact ⟨rfl, eta.2⟩
  rw [hinter, inhomBernoulliProductMeasure.apply_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  cases h : eta.1 e
  · rw [bernoulliMeasure_apply_false]
    exact ENNReal.coe_ne_zero.mpr
      (ne_of_gt (tsub_pos_iff_lt.mpr (hp1 e)))
  · rw [bernoulliMeasure_apply_true]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (hp0 e))


noncomputable def cylinderEssInf
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (f : ConfigSpace E → ℝ) (K : Set E) (omega : ConfigSpace E) : ℝ :=
  essInf (fun eta : AgreementFiberPoint K omega => f eta.1)
    (agreementFiberMeasure p hp K omega)



theorem cylinderEssInf_eq_cylinderMin
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f : ConfigSpace E → ℝ) (K : Set E) (omega : ConfigSpace E) :
    cylinderEssInf p (fun e => (hp1 e).le) f K omega =
      cylinderMin f K omega := by
  letI : Nonempty (AgreementFiberPoint K omega) :=
    ⟨⟨omega, agreeOn_refl K omega⟩⟩
  have hbdd : BddBelow
      (Set.range fun eta : AgreementFiberPoint K omega => f eta.1) :=
    (Set.toFinite _).bddBelow
  rw [cylinderEssInf, essInf_eq_ciInf
    (agreementFiberMeasure_singleton_ne_zero p hp0 hp1 K omega) hbdd]
  apply le_antisymm
  · obtain ⟨eta, heta, heq⟩ := Finset.exists_mem_eq_inf'
      (agreementFiber_nonempty K omega) f
    calc
      (⨅ a : AgreementFiberPoint K omega, f a.1) ≤
          f (⟨eta, mem_agreementFiber.mp heta⟩ : AgreementFiberPoint K omega).1 :=
        ciInf_le hbdd _
      _ = cylinderMin f K omega := by
        rw [cylinderMin, heq]
  · apply le_ciInf
    intro eta
    exact Finset.inf'_le _ (mem_agreementFiber.mpr eta.2)


noncomputable def functionalDisjointEssMaxAt
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (f g : ConfigSpace E → ℝ) (omega eta : ConfigSpace E) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => cylinderEssInf p hp f pair.1 omega *
      cylinderEssInf p hp g pair.2 eta


noncomputable def functionalDisjointEssMax
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (f g : ConfigSpace E → ℝ) (omega : ConfigSpace E) : ℝ :=
  functionalDisjointEssMaxAt p hp f g omega omega

theorem functionalDisjointEssMaxAt_eq
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ) (omega eta : ConfigSpace E) :
    functionalDisjointEssMaxAt p (fun e => (hp1 e).le) f g omega eta =
      functionalDisjointMaxAt f g omega eta := by
  unfold functionalDisjointEssMaxAt functionalDisjointMaxAt
  apply Finset.sup'_congr (disjointCoordinatePairs_nonempty (E := E)) rfl
  intro pair _
  rw [cylinderEssInf_eq_cylinderMin p hp0 hp1,
    cylinderEssInf_eq_cylinderMin p hp0 hp1]

theorem functionalDisjointEssMax_eq
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ) (omega : ConfigSpace E) :
    functionalDisjointEssMax p (fun e => (hp1 e).le) f g omega =
      functionalDisjointMax f g omega :=
  functionalDisjointEssMaxAt_eq p hp0 hp1 f g omega omega


noncomputable def bernoulliProductWeight
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) : E → Bool → ℝ :=
  fun e b => (bernoulliMeasure (p e) (hp e)).real {b}

omit [Fintype E] [DecidableEq E] in
theorem bernoulliProductWeight_nonneg
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    ∀ e b, 0 ≤ bernoulliProductWeight p hp e b :=
  fun _ _ => measureReal_nonneg

omit [Fintype E] [DecidableEq E] in
theorem bernoulliProductWeight_sum
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    ∀ e, bernoulliProductWeight p hp e false +
      bernoulliProductWeight p hp e true = 1 := by
  intro e
  have hf : (bernoulliMeasure (p e) (hp e)).real {false} =
      ((1 - p e : ℝ≥0) : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
  have ht : (bernoulliMeasure (p e) (hp e)).real {true} = (p e : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
  simp only [bernoulliProductWeight]
  rw [hf, ht, NNReal.coe_sub (hp e), NNReal.coe_one]
  ring



theorem integral_inhomBernoulli_eq_productExpectation
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) (f : ConfigSpace E → ℝ) :
    ∫ omega, f omega ∂(inhomBernoulliProductMeasure p hp) =
      productExpectation (bernoulliProductWeight p hp) f := by
  rw [integral_fintype Integrable.of_finite]
  unfold productExpectation
  apply Finset.sum_congr rfl
  intro omega _
  rw [inhomBernoulliProductMeasure.real_singleton]
  rfl


theorem integral_prod_inhomBernoulli_eq_dualProductExpectation
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (F : ConfigSpace E × ConfigSpace E → ℝ) :
    ∫ pair, F pair ∂((inhomBernoulliProductMeasure p hp).prod
      (inhomBernoulliProductMeasure p hp)) =
      dualProductExpectation (bernoulliProductWeight p hp) F := by
  rw [integral_fintype Integrable.of_finite]
  unfold dualProductExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro omega _
  apply Finset.sum_congr rfl
  intro eta _
  have hsingleton : ({(omega, eta)} : Set
      (ConfigSpace E × ConfigSpace E)) = {omega} ×ˢ {eta} := by
    ext pair
    simp
  rw [hsingleton, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rw [← Measure.real, ← Measure.real,
    inhomBernoulliProductMeasure.real_singleton,
    inhomBernoulliProductMeasure.real_singleton]
  rfl



theorem functionalBKR_essInf_integral
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    ∫ omega, functionalDisjointEssMax p (fun e => (hp1 e).le)
        f g omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) ≤
      (∫ omega, f omega
          ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) *
        ∫ omega, g omega
          ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
  simp_rw [functionalDisjointEssMax_eq p hp0 hp1]
  rw [integral_inhomBernoulli_eq_productExpectation,
    integral_inhomBernoulli_eq_productExpectation,
    integral_inhomBernoulli_eq_productExpectation]
  exact functionalBKR_real _
    (bernoulliProductWeight_nonneg p (fun e => (hp1 e).le))
    (bernoulliProductWeight_sum p (fun e => (hp1 e).le))
    f g hf0 hg0



theorem dualFunctionalBKR_essInf_integral
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    ∫ pair, functionalDisjointEssMaxAt p (fun e => (hp1 e).le)
        f g pair.1 pair.2
      ∂((inhomBernoulliProductMeasure p (fun e => (hp1 e).le)).prod
        (inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) ≤
      ∫ omega, f omega * g omega
        ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
  simp_rw [functionalDisjointEssMaxAt_eq p hp0 hp1]
  rw [integral_prod_inhomBernoulli_eq_dualProductExpectation,
    integral_inhomBernoulli_eq_productExpectation]
  exact dualFunctionalBKR_real _
    (bernoulliProductWeight_nonneg p (fun e => (hp1 e).le))
    (bernoulliProductWeight_sum p (fun e => (hp1 e).le))
    f g hf0 hg0

end StatMech.FrontierA
