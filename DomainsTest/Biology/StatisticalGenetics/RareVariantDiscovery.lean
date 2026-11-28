/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.RareVariantDiscovery
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.NormNum

/-!
# Tests for the binomial discovery probability of rare variants

The hypotheses of `binomial_discovery_probability` are satisfiable for every number of samples
and all probabilities `φ, c ∈ [0, 1]`: the coordinate events of a product of Bernoulli measures on
`J → Bool` are mutually independent with prescribed probabilities. On that model with
`φ = c = 1/2`, in two samples a rare allele is detected in a sample with probability `7/16`, in
exactly one of the two samples with probability `63/128`, and is discovered (`N = 1`) with
probability `1 - (9/16) ^ 2 = 175/256`; in three samples a rare genotype is detected in a sample
with probability `1/8`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Domains.Biology.StatisticalGenetics.RareVariantDiscovery

namespace DomainsTest.Biology.StatisticalGenetics.RareVariantDiscovery

/-- The product of Bernoulli measures with parameters `p x` on `J → Bool`. -/
noncomputable abbrev bernoulliProduct {J : Type*} [Fintype J] (p : J → unitInterval) :
    Measure (J → Bool) :=
  Measure.pi fun x => bernoulliMeasure true false (p x)

/-- The coordinate events of a product of Bernoulli measures are mutually independent. -/
lemma iIndepSet_coord {J : Type*} [Fintype J] (p : J → unitInterval) :
    iIndepSet (fun x => {ω : J → Bool | ω x = true}) (bernoulliProduct p) := by
  have hf := iIndepFun_pi (μ := fun x => bernoulliMeasure true false (p x))
    (X := fun _ => (id : Bool → Bool)) fun _ => aemeasurable_id
  rw [iIndepSet_iff_meas_biInter fun x => measurableSet_eq_fun (measurable_pi_apply x)
    measurable_const]
  intro S
  exact hf.meas_biInter fun x _ => ⟨{true}, measurableSet_singleton _, rfl⟩

/-- The coordinate event `{ω | ω x = true}` has probability `p x`. -/
lemma measureReal_coord {J : Type*} [Fintype J] (p : J → unitInterval) (x : J) :
    (bernoulliProduct p).real {ω | ω x = true} = p x := by
  have h := (measurePreserving_eval (fun x => bernoulliMeasure true false (p x))
    x).measureReal_preimage (s := {true}) (measurableSet_singleton _).nullMeasurableSet
  rw [show {ω : J → Bool | ω x = true} = Function.eval x ⁻¹' ({true} : Set Bool) from rfl, h]
  simp

/-- **Non-vacuity, rare alleles.** For every number of samples `σ` and all `φ, c ∈ [0, 1]`, the
coordinate events of the product of Bernoulli measures satisfy the hypotheses of the rare-allele
part. -/
example (σ : ℕ) (φ c : unitInterval) :
    let p : (Fin σ × Fin 2) ⊕ (Fin σ × Fin 2) → unitInterval := Sum.elim (fun _ => φ) (fun _ => c)
    let A : Fin σ → Fin 2 → Set ((Fin σ × Fin 2) ⊕ (Fin σ × Fin 2) → Bool) :=
      fun i j => {ω | ω (.inl (i, j)) = true}
    let C : Fin σ → Fin 2 → Set ((Fin σ × Fin 2) ⊕ (Fin σ × Fin 2) → Bool) :=
      fun i j => {ω | ω (.inr (i, j)) = true}
    (∀ i j, MeasurableSet (A i j)) ∧ (∀ i j, MeasurableSet (C i j)) ∧
      iIndepSet (Sum.elim (Function.uncurry A) (Function.uncurry C)) (bernoulliProduct p) ∧
      (∀ i j, (bernoulliProduct p).real (A i j) = φ) ∧
      (∀ i j, (bernoulliProduct p).real (C i j) = c) := by
  intro p A C
  refine ⟨fun i j => measurableSet_eq_fun (measurable_pi_apply _) measurable_const,
    fun i j => measurableSet_eq_fun (measurable_pi_apply _) measurable_const, ?_,
    fun i j => measureReal_coord p _, fun i j => measureReal_coord p _⟩
  convert iIndepSet_coord p using 1
  ext (⟨i, j⟩ | ⟨i, j⟩) <;> rfl

/-- **Non-vacuity, rare genotypes.** For every number of samples `σ` and all `φ, c ∈ [0, 1]`, the
coordinate events of the product of Bernoulli measures satisfy the hypotheses of the rare-genotype
part. -/
example (σ : ℕ) (φ c : unitInterval) :
    let p : Fin σ ⊕ (Fin σ × Fin 2) → unitInterval := Sum.elim (fun _ => φ) (fun _ => c)
    let G : Fin σ → Set (Fin σ ⊕ (Fin σ × Fin 2) → Bool) := fun i => {ω | ω (.inl i) = true}
    let C : Fin σ → Fin 2 → Set (Fin σ ⊕ (Fin σ × Fin 2) → Bool) :=
      fun i j => {ω | ω (.inr (i, j)) = true}
    (∀ i, MeasurableSet (G i)) ∧ (∀ i j, MeasurableSet (C i j)) ∧
      iIndepSet (Sum.elim G (Function.uncurry C)) (bernoulliProduct p) ∧
      (∀ i, (bernoulliProduct p).real (G i) = φ) ∧
      (∀ i j, (bernoulliProduct p).real (C i j) = c) := by
  intro p G C
  refine ⟨fun i => measurableSet_eq_fun (measurable_pi_apply _) measurable_const,
    fun i j => measurableSet_eq_fun (measurable_pi_apply _) measurable_const, ?_,
    fun i => measureReal_coord p _, fun i j => measureReal_coord p _⟩
  convert iIndepSet_coord p using 1
  ext (i | ⟨i, j⟩) <;> rfl

/-- The coordinate model of a rare allele in two samples, with `φ = c = 1/2`. -/
noncomputable abbrev alleleModel : Measure ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → Bool) :=
  bernoulliProduct fun _ => ⟨1 / 2, by norm_num, by norm_num⟩

/-- The allele events `A i j` of `alleleModel`. -/
abbrev alleleEvent (i j : Fin 2) : Set ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → Bool) :=
  {ω | ω (.inl (i, j)) = true}

/-- The coverage events `C i j` of `alleleModel`. -/
abbrev coverageEvent (i j : Fin 2) : Set ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → Bool) :=
  {ω | ω (.inr (i, j)) = true}

lemma alleleModel_hyp :
    iIndepSet (Sum.elim (Function.uncurry alleleEvent) (Function.uncurry coverageEvent))
      alleleModel := by
  convert iIndepSet_coord (fun _ : (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) =>
    (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) using 1
  ext (⟨i, j⟩ | ⟨i, j⟩) <;> rfl

/-- With `φ = c = 1/2`, a rare allele is detected in a sample with probability
`2 · 1/4 - 1/16 = 7/16`. -/
example (i : Fin 2) :
    alleleModel.real ((alleleEvent i 0 ∩ coverageEvent i 0) ∪
      (alleleEvent i 1 ∩ coverageEvent i 1)) = 7 / 16 := by
  rw [((binomial_discovery_probability alleleModel 2 (1 / 2) (1 / 2)).1 alleleEvent coverageEvent
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const) alleleModel_hyp
    (fun _ _ => measureReal_coord _ _) (fun _ _ => measureReal_coord _ _)).1 i]
  norm_num

/-- With two samples and `φ = c = 1/2`, a rare allele is discovered (`N = 1`) with probability
`2 · 7/16 · 9/16 + (7/16) ^ 2 = 175/256 = 1 - (9/16) ^ 2`. -/
example :
    alleleModel.real {ω | 1 ≤ {i | ω ∈ (alleleEvent i 0 ∩ coverageEvent i 0) ∪
      (alleleEvent i 1 ∩ coverageEvent i 1)}.ncard} = 175 / 256 := by
  rw [((binomial_discovery_probability alleleModel 2 (1 / 2) (1 / 2)).1 alleleEvent coverageEvent
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const) alleleModel_hyp
    (fun _ _ => measureReal_coord _ _) (fun _ _ => measureReal_coord _ _)).2.2 1]
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.sum_pair (by norm_num)]
  norm_num

/-- With two samples and `φ = c = 1/2`, a rare allele is detected in exactly one sample with
probability `2 · 7/16 · 9/16 = 63/128`. -/
example :
    alleleModel.real {ω | {i | ω ∈ (alleleEvent i 0 ∩ coverageEvent i 0) ∪
      (alleleEvent i 1 ∩ coverageEvent i 1)}.ncard = 1} = 63 / 128 := by
  rw [((binomial_discovery_probability alleleModel 2 (1 / 2) (1 / 2)).1 alleleEvent coverageEvent
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const) alleleModel_hyp
    (fun _ _ => measureReal_coord _ _) (fun _ _ => measureReal_coord _ _)).2.1 1]
  norm_num

/-- With three samples and `φ = c = 1/2`, a rare genotype is detected in a sample with probability
`φ c ^ 2 = 1/8`. -/
example (i : Fin 3) :
    let μ := bernoulliProduct
      (fun _ : Fin 3 ⊕ (Fin 3 × Fin 2) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
    let G : Fin 3 → Set (Fin 3 ⊕ (Fin 3 × Fin 2) → Bool) := fun i => {ω | ω (.inl i) = true}
    let C : Fin 3 → Fin 2 → Set (Fin 3 ⊕ (Fin 3 × Fin 2) → Bool) :=
      fun i j => {ω | ω (.inr (i, j)) = true}
    μ.real (G i ∩ C i 0 ∩ C i 1) = 1 / 8 := by
  intro μ G C
  have hind : iIndepSet (Sum.elim G (Function.uncurry C)) μ := by
    convert iIndepSet_coord (fun _ : Fin 3 ⊕ (Fin 3 × Fin 2) =>
      (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) using 1
    ext (i | ⟨i, j⟩) <;> rfl
  rw [((binomial_discovery_probability μ 3 (1 / 2) (1 / 2)).2 G C
    (fun _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    (fun _ _ => measurableSet_eq_fun (measurable_pi_apply _) measurable_const) hind
    (fun _ => measureReal_coord _ _) (fun _ _ => measureReal_coord _ _)).1 i]
  norm_num

end DomainsTest.Biology.StatisticalGenetics.RareVariantDiscovery
