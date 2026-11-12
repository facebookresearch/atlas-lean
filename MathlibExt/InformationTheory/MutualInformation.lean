/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import MathlibExt.InformationTheory.ConditionalMutualInformation

@[expose] public section

/-! # Mutual information on finite types, in nats

Mutual information of a joint PMF, in nats: the existing bits API
`InformationTheory.finiteMutualInformation`, scaled by `Real.log 2`.
Nonnegativity, vanishing on independent products, and symmetry under
swapping the coordinates are all derived from that API; the explicit
finite sum is a conversion theorem (`mutualInfo_eq_sum`), not a second
definition. This is the information-calculus core of roadmap package
QCI-32 of the Atlas TCS canon roadmap; the operational channel-coding
statements built on it are follow-ups.

Source: Cover and Thomas, Elements of Information Theory (2006),
Chapter 2.
-/

open Finset

namespace InformationTheory

open MeasureTheory

/-- Mutual information (nats) of a joint PMF on a finite product type:
the bits value `finiteMutualInformation p` scaled by `Real.log 2`. -/
noncomputable def mutualInfo {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : ℝ :=
  finiteMutualInformation p * Real.log 2

/-- Conversion to the existing bits API. -/
theorem mutualInfo_eq_finiteMutualInformation {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    mutualInfo p = finiteMutualInformation p * Real.log 2 :=
  rfl

private theorem pmf_sum_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, p a) = 1 := by
  have h := PMF.tsum_coe p
  rwa [tsum_fintype] at h

/-- The product (independent) joint law of two PMFs. -/
noncomputable def prodJoint {α β : Type*} (p : PMF α) (q : PMF β) :
    PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

/-- The product law charges `(x, y)` with `p x * q y`. -/
theorem prodJoint_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (x : α) (y : β) :
    (prodJoint p q) (x, y) = p x * q y := by
  unfold prodJoint
  rw [PMF.bind_apply, tsum_fintype]
  have h1 : ∀ a ∈ (Finset.univ : Finset α), a ≠ x →
      p a * ((q.map fun b => (a, b)) (x, y)) = 0 := by
    intro a _ hax
    have h0 : (q.map fun b => (a, b)) (x, y) = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      apply Finset.sum_eq_zero
      intro b _
      have hne : (x, y) ≠ (a, b) := by
        intro h
        simp only [Prod.mk.injEq] at h
        exact hax h.1.symm
      simp [hne]
    rw [h0, mul_zero]
  have h2 : x ∉ (Finset.univ : Finset α) →
      p x * ((q.map fun b => (x, b)) (x, y)) = 0 := by
    intro hx
    simp at hx
  have hsum : (∑ a : α, p a * ((q.map fun b => (a, b)) (x, y)))
      = p x * ((q.map fun b => (x, b)) (x, y)) :=
    Finset.sum_eq_single x h1 h2
  rw [hsum]
  congr 1
  rw [PMF.map_apply]
  have h0 : ∀ b : β, b ≠ y →
      (@ite ENNReal ((x, y) = (x, b)) (Classical.propDecidable _) (q b) 0) = 0 := by
    intro b hby
    have hne : (x, y) ≠ (x, b) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact hby h.2.symm
    simp [hne]
  rw [tsum_eq_single y h0]
  simp

private theorem prodJoint_map_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) : (prodJoint p q).map Prod.fst = p := by
  ext a
  rw [map_fst_apply]
  simp only [prodJoint_apply, ← Finset.mul_sum, pmf_sum_one q, mul_one]

private theorem prodJoint_map_snd {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) : (prodJoint p q).map Prod.snd = q := by
  ext b
  rw [map_snd_apply]
  simp only [prodJoint_apply, ← Finset.sum_mul, pmf_sum_one p, one_mul]

/-- The explicit finite-sum form of mutual information in nats:
`∑ x y, p (x, y) log (p (x, y) / (pX x * pY y))`, where the marginals
are the finite sums. Real-arithmetic conventions make terms with
`p (x, y) = 0` contribute `0`. Proved from `toReal_klDiv_prod` and the
bits API, not assumed as a definition. -/
theorem mutualInfo_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    mutualInfo p =
      ∑ x, ∑ y, (p (x, y)).toReal *
        Real.log ((p (x, y)).toReal /
          ((∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal))) := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  haveI : MeasurableSingletonClass β := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hsing : ∀ a b,
      ((p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure).real {(a, b)} =
        ((p.map Prod.fst) a).toReal * ((p.map Prod.snd) b).toReal := fun a b ↦ by
    rw [measureReal_def, ← Set.singleton_prod_singleton, MeasureTheory.Measure.prod_prod,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), ENNReal.toReal_mul]
  rw [mutualInfo, finiteMutualInformation_eq, ← toReal_klDiv_prod p,
    toReal_klDiv_eq_sum (toMeasure_absolutelyContinuous_prod p) (by simp)]
  simp only [Fintype.sum_prod_type, toMeasure_real_singleton, hsing,
    toReal_map_fst_apply, toReal_map_snd_apply]

/-- Mutual information is nonnegative. -/
theorem mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : 0 ≤ mutualInfo p := by
  rw [mutualInfo, finiteMutualInformation_eq]
  exact mul_nonneg (by linarith [shannonEntropy_le_add p]) (Real.log_nonneg one_le_two)

/-- Independent coordinates have zero mutual information. -/
theorem mutualInfo_prodJoint {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) : mutualInfo (prodJoint p q) = 0 := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  haveI : MeasurableSingletonClass β := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hmeas : (prodJoint p q).toMeasure =
      ((prodJoint p q).map Prod.fst).toMeasure.prod
        ((prodJoint p q).map Prod.snd).toMeasure := by
    rw [prodJoint_map_fst, prodJoint_map_snd]
    rw [MeasureTheory.Measure.ext_iff_singleton]
    intro z
    obtain ⟨x, y⟩ := z
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (x, y)),
      prodJoint_apply, ← Set.singleton_prod_singleton,
      MeasureTheory.Measure.prod_prod,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  have hmi : measureMutualInformation
      (⟨(prodJoint p q).toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) = 0 :=
    measureMutualInformation_toMeasure_eq_zero_iff (prodJoint p q) |>.mpr hmeas
  rw [mutualInfo, finiteMutualInformation, hmi, ENNReal.toReal_zero, zero_mul]

/-- Mutual information is symmetric under swapping the
coordinates. -/
theorem mutualInfo_swap {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    mutualInfo (p.map (fun z => (z.2, z.1))) = mutualInfo p := by
  have hf : (p.map fun z => (z.2, z.1)).map Prod.fst = p.map Prod.snd := by
    rw [PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun z : α × β => (z.2, z.1)) = Prod.snd := by
      funext z
      obtain ⟨a, b⟩ := z
      rfl
    rw [hcomp]
  have hs : (p.map fun z => (z.2, z.1)).map Prod.snd = p.map Prod.fst := by
    rw [PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun z : α × β => (z.2, z.1)) = Prod.fst := by
      funext z
      obtain ⟨a, b⟩ := z
      rfl
    rw [hcomp]
  have hH : shannonEntropy (p.map fun z => (z.2, z.1)) = shannonEntropy p :=
    shannonEntropy_map_equiv p (Equiv.prodComm α β)
  rw [mutualInfo, mutualInfo, finiteMutualInformation_eq, finiteMutualInformation_eq,
    hf, hs, hH]
  ring

end InformationTheory
