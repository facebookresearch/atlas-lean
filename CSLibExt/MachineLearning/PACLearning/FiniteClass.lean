/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.MachineLearning.PACLearning.VersionSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite-class realizable PAC bounds

A supplied consistent learner over a finite concept class has failure
probability at most `|C| * exp (-ε * m)` under iid realizable sampling.
The logarithmic sample bound gives the canonical existential PAC predicate
using that same learner, uniformly over a supplied realizable family.

Graphs are explicitly measurable. No measurability of the learner is assumed:
like the canonical PAC predicate, the bounds use the measure's outer measure
on an arbitrary failure event. Accuracy and confidence are in `(0, 1)`.

## Reference

MIT graduate machine-learning notes, *Learnability and VC Dimension*,
section "Finite Hypothesis Class":
https://gradml.mit.edu/supervised/learnability_and_vc
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private theorem error_graph_self (P : Measure α) {c : α → β}
    (hcm : Measurable c)
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) :
    error (P.map (fun x => (x, c x))) c = 0 := by
  have hφ : Measurable (fun x => (x, c x)) :=
    measurable_id.prodMk hcm
  unfold error
  rw [Measure.map_apply hφ (by
    simpa only [compl_ofPred, ne_eq, eq_comm] using hG.compl)]
  simp

private theorem optimalError_graph (P : Measure α)
    {C : ConceptClass α β} {c : α → β} (hc : c ∈ C)
    (hcm : Measurable c)
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) :
    optimalError (P.map (fun x => (x, c x))) C = 0 := by
  apply le_antisymm _ bot_le
  calc
    optimalError (P.map (fun x => (x, c x))) C
        ≤ error (P.map (fun x => (x, c x))) c :=
      iInf_le_of_le c (iInf_le_of_le hc le_rfl)
    _ = 0 := error_graph_self P hcm hG

private theorem graph_mass_le_exp (D : Measure (α × β))
    [IsProbabilityMeasure D] {h : α → β}
    (hG : MeasurableSet {p : α × β | p.2 = h p.1})
    (ε : Ioo (0 : ℝ≥0) 1) (hbad : (ε.val : ℝ≥0∞) < error D h) :
    D {p : α × β | p.2 = h p.1} ≤
      ENNReal.ofReal (Real.exp (-(ε.val : ℝ))) := by
  have hdis : MeasurableSet {p : α × β | h p.1 ≠ p.2} := by
    simpa only [compl_ofPred, ne_eq, eq_comm] using hG.compl
  calc
    D {p : α × β | p.2 = h p.1} = 1 - error D h := by
      simpa only [error, compl_ofPred, ne_eq, not_not, eq_comm] using
        (prob_compl_eq_one_sub (μ := D) hdis)
    _ ≤ 1 - (ε.val : ℝ≥0∞) := tsub_le_tsub_left hbad.le 1
    _ = ENNReal.ofReal (1 - (ε.val : ℝ)) := by
      rw [ENNReal.ofReal_sub _ ε.val.coe_nonneg]
      simp
    _ ≤ ENNReal.ofReal (Real.exp (-(ε.val : ℝ))) :=
      ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg _)

private theorem bad_agreement_le_exp (D : Measure (α × β))
    [IsProbabilityMeasure D] {h : α → β}
    (hG : MeasurableSet {p : α × β | p.2 = h p.1})
    (ε : Ioo (0 : ℝ≥0) 1) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => D))
      {S | (ε.val : ℝ≥0∞) < error D h ∧
        ∀ i : Fin m, h (S i).1 = (S i).2} ≤
      ENNReal.ofReal (Real.exp (-(ε.val : ℝ) * m)) := by
  by_cases hbad : (ε.val : ℝ≥0∞) < error D h
  · have hevent : {S | (ε.val : ℝ≥0∞) < error D h ∧
        ∀ i : Fin m, h (S i).1 = (S i).2} =
        univ.pi (fun _ : Fin m => {p : α × β | p.2 = h p.1}) := by
      ext S
      simp [hbad, eq_comm]
    rw [hevent, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      (D {p : α × β | p.2 = h p.1}) ^ m ≤
          ENNReal.ofReal (Real.exp (-(ε.val : ℝ))) ^ m :=
        pow_le_pow_left' (graph_mass_le_exp D hG ε hbad) m
      _ = ENNReal.ofReal (Real.exp (-(ε.val : ℝ) * m)) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← Real.exp_nat_mul, mul_comm]
  · simp [hbad]

/-- A fixed consistent learner has the finite-class exponential failure bound
under the literal realizable graph distribution and iid sampling. -/
theorem IsConsistent.failure_le_exp {m : ℕ} {C : ConceptClass α β}
    {A : Learner α β m} (hA : IsConsistent A C) (hC : C.Finite)
    (hG : ∀ h ∈ C, MeasurableSet {p : α × β | p.2 = h p.1})
    (ε : Ioo (0 : ℝ≥0) 1) (P : Measure α) [IsProbabilityMeasure P]
    {c : α → β} (hc : c ∈ C) (hcm : Measurable c) :
    (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
      {S | (ε.val : ℝ≥0∞) <
        error (P.map (fun x => (x, c x))) (A S)} ≤
      (C.ncard : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(ε.val : ℝ) * m)) := by
  classical
  let := hC.fintype
  let D := P.map (fun x => (x, c x))
  let μ := Measure.pi (fun _ : Fin m => D)
  let B := fun h : C => {S : LabeledSample α β m |
    (ε.val : ℝ≥0∞) < error D h ∧ ∀ i, h.val (S i).1 = (S i).2}
  have hinc : {S | (ε.val : ℝ≥0∞) < error D (A S)} ≤ᵐ[μ]
      ⋃ h : C, B h := by
    filter_upwards [ae_mem_versionSpace_of_realizable hc hcm (hG c hc)
      P m] with S hS hbad
    have hr : Realizable C S := ⟨c, hc, fun i => (hS.2 i).symm⟩
    have hout := hA S hr
    exact mem_iUnion.mpr ⟨⟨A S, hout.1⟩, hbad, hout.2⟩
  calc
    μ {S | (ε.val : ℝ≥0∞) < error D (A S)} ≤ μ (⋃ h : C, B h) :=
      measure_mono_ae hinc
    _ ≤ ∑ h : C, μ (B h) := measure_iUnion_fintype_le μ B
    _ ≤ ∑ _h : C, ENNReal.ofReal (Real.exp (-(ε.val : ℝ) * m)) :=
      Finset.sum_le_sum fun h _ => bad_agreement_le_exp D (hG h h.2) ε m
    _ = (C.ncard : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(ε.val : ℝ) * m)) := by
      simp [Set.fintypeCard_eq_ncard]

/-- The literal logarithmic sample threshold bounds the failure mass of the
supplied learner. The class is explicitly nonempty, including singletons. -/
theorem IsConsistent.failure_le_of_log_bound {m : ℕ}
    {C : ConceptClass α β} {A : Learner α β m}
    (hA : IsConsistent A C) (hC : C.Finite) (hne : C.Nonempty)
    (hG : ∀ h ∈ C, MeasurableSet {p : α × β | p.2 = h p.1})
    (ε δ : Ioo (0 : ℝ≥0) 1)
    (hm : (Real.log (C.ncard : ℝ) +
      Real.log (1 / (δ.val : ℝ))) / (ε.val : ℝ) ≤ (m : ℝ))
    (P : Measure α) [IsProbabilityMeasure P]
    {c : α → β} (hc : c ∈ C) (hcm : Measurable c) :
    (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
      {S | (ε.val : ℝ≥0∞) <
        error (P.map (fun x => (x, c x))) (A S)} ≤ (δ.val : ℝ≥0∞) := by
  have he : 0 < (ε.val : ℝ) := by exact_mod_cast ε.property.1
  have hd : 0 < (δ.val : ℝ) := by exact_mod_cast δ.property.1
  have hn : 0 < (C.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos hC).mpr hne
  have hmul := (div_le_iff₀ he).mp hm
  simp only [one_div, Real.log_inv] at hmul
  have hexp : (C.ncard : ℝ) * Real.exp (-(ε.val : ℝ) * m) ≤
      (δ.val : ℝ) := by
    calc
      _ = Real.exp (Real.log (C.ncard : ℝ) +
          (-(ε.val : ℝ) * m)) := by rw [Real.exp_add, Real.exp_log hn]
      _ ≤ Real.exp (Real.log (δ.val : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (δ.val : ℝ) := Real.exp_log hd
  refine (hA.failure_le_exp hC hG ε P hc hcm).trans ?_
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal hexp

/-- A single supplied consistent learner witnesses the canonical PAC predicate
for any supplied family of realizable graph distributions at the log threshold.
The learner is fixed before the distribution and target quantifiers. -/
theorem IsConsistent.isPACLearnerFor_of_finite {m : ℕ}
    {C : ConceptClass α β} {A : Learner α β m}
    (hA : IsConsistent A C) (hC : C.Finite) (hne : C.Nonempty)
    (hG : ∀ h ∈ C, MeasurableSet {p : α × β | p.2 = h p.1})
    (ε δ : Ioo (0 : ℝ≥0) 1)
    (hm : (Real.log (C.ncard : ℝ) +
      Real.log (1 / (δ.val : ℝ))) / (ε.val : ℝ) ≤ (m : ℝ))
    (𝒟 : Set (Measure (α × β)))
    (h𝒟 : ∀ D ∈ 𝒟, ∃ P : Measure α, IsProbabilityMeasure P ∧
      ∃ c ∈ C, Measurable c ∧ D = P.map (fun x => (x, c x))) :
    IsPACLearnerFor m ε δ C 𝒟 := by
  refine ⟨A, ?_⟩
  intro D _ hD
  obtain ⟨P, hP, c, hc, hcm, rfl⟩ := h𝒟 D hD
  have : IsProbabilityMeasure P := hP
  rw [optimalError_graph P hc hcm (hG c hc), zero_add]
  exact hA.failure_le_of_log_bound hC hne hG ε δ hm P hc hcm

end Cslib.MachineLearning.PACLearning
