/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Probability mass function of a sum of independent Bernoulli variables

If `X₁, …, Xₘ` are independent Bernoulli random variables with
`P(Xᵢ = 1) = pᵢ`, then for any `j`,
`P(∑ᵢ Xᵢ = j) = ∑_{A ⊆ [m], |A| = j} ∏_{i ∈ A} pᵢ · ∏_{i ∉ A} (1 - pᵢ)`,
the `j`-th elementary symmetric polynomial in the `pᵢ` weighted by the
complementary product. In the identically distributed case this reduces to
the binomial mass function `C(m, j) p ^ j (1 - p) ^ (m - j)`.

## Source

This formalizes `bernoulli_sum_pmf` in
`v1/Atlas/TheoryOfProbability/code/PoissonConvergence.lean`, the
fully proved pmf lemma supporting the target "Theorem (Poisson
convergence)" (Lecture 17) of
`v1/Atlas/TheoryOfProbability/targets.yaml`. The analytic core of the
Poisson convergence theorem itself,
`elem_symm_poly_tendsto_poisson` in that file, is left unproved in v1 and is
not claimed here. The i.i.d. binomial corollary is new: it is the
`pᵢ ≡ p` specialization of `bernoulli_sum_pmf`.

## Relation to Mathlib

Mathlib has the Bernoulli and binomial distributions
(`Mathlib.Probability.Distributions.Bernoulli`,
`Mathlib.Probability.Distributions.Binomial`) and the Poisson limit
theorem for the i.i.d. binomial pmf
(`Mathlib.Probability.Distributions.Poisson.PoissonLimitThm`), but no
pmf formula for a sum of independent Bernoulli variables with
*distinct* parameters (the Poisson-binomial distribution).

## Main results

* `ProbabilityTheory.IsBernoulliRV`: `X` is Bernoulli with parameter `p`.
* `ProbabilityTheory.bernoulli_sum_pmf`: pmf of a sum of independent
  Bernoulli variables with distinct parameters.
* `ProbabilityTheory.bernoulli_sum_pmf_iid`: the i.i.d. case, i.e. the
  binomial pmf.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped ENNReal NNReal Topology Nat

namespace ProbabilityTheory

/-- `IsBernoulliRV X μ p` means that `p ∈ [0,1]` and `X : Ω → ℕ` has Mathlib's
Bernoulli law `bernoulliMeasure 1 0 p` under `μ`. The law includes almost-everywhere
measurability and gives mass `p` to `1` and `1 - p` to `0`, with no mass elsewhere. -/
def IsBernoulliRV {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℕ) (μ : Measure Ω) (p : ℝ) : Prop :=
  ∃ hp : p ∈ Set.Icc (0 : ℝ) 1, HasLaw X (bernoulliMeasure 1 0 ⟨p, hp⟩) μ

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℕ} {μ : Measure Ω} {p : ℝ}

/-- A Bernoulli parameter is nonnegative. -/
lemma IsBernoulliRV.nonneg (hX : IsBernoulliRV X μ p) : 0 ≤ p := by
  rcases hX with ⟨hp, _⟩
  exact hp.1

/-- A Bernoulli parameter is at most one. -/
lemma IsBernoulliRV.le_one (hX : IsBernoulliRV X μ p) : p ≤ 1 := by
  rcases hX with ⟨hp, _⟩
  exact hp.2

/-- The real-parameter predicate supplies the standard Nat-valued Bernoulli law. -/
lemma IsBernoulliRV.hasLaw (hX : IsBernoulliRV X μ p) :
    HasLaw X (bernoulliMeasure 1 0 ⟨p, hX.nonneg, hX.le_one⟩) μ := by
  rcases hX with ⟨hp, hLaw⟩
  exact hLaw

/-- A Bernoulli variable has mass `1 - p` at zero. -/
lemma IsBernoulliRV.measure_zero (hX : IsBernoulliRV X μ p) :
    μ (X ⁻¹' {0}) = ENNReal.ofReal (1 - p) := by
  have h := hX.hasLaw.measure_eq (p := fun n : ℕ => n = 0) (measurableSet_singleton 0)
  simpa [Set.preimage_singleton, bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using h

/-- A Bernoulli variable has mass `p` at one. -/
lemma IsBernoulliRV.measure_one (hX : IsBernoulliRV X μ p) :
    μ (X ⁻¹' {1}) = ENNReal.ofReal p := by
  have h := hX.hasLaw.measure_eq (p := fun n : ℕ => n = 1) (measurableSet_singleton 1)
  simpa [Set.preimage_singleton, bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using h

/-- Probability mass function of a sum of independent (possibly nonidentical) Bernoulli random
variables: if `X₁, …, X_m` are independent with `X_i ∼ Bernoulli(p_i)`, then for any `j ∈ ℕ`,
`P(∑ X_i = j) = ∑_{A ⊆ [m], |A| = j} ∏_{i ∈ A} p_i · ∏_{i ∉ A} (1 - p_i)` (the
`j`-th elementary symmetric polynomial in `(p_i)` weighted by the complementary product). -/
theorem bernoulli_sum_pmf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Fin m → Ω → ℕ} {p : Fin m → ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (p i))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      ∑ A ∈ Finset.univ.powersetCard j,
        (∏ i ∈ A, p i) * (∏ i ∈ Finset.univ \ A, (1 - p i)) := by
  classical
  set PC := (Finset.univ : Finset (Fin m)).powersetCard j with hPC_def
  have hFsubS : (⋃ A ∈ PC,
      ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) ⊆
      (fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} := by
    apply Set.iUnion₂_subset; intro A hA ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [Finset.mem_powersetCard] at hA
    calc ∑ i : Fin m, X i ω
        = ∑ i, if i ∈ A then 1 else 0 := Finset.sum_congr rfl (fun i _ => hω i)
      _ = A.card := by simp
      _ = j := hA.2
  have hdiff_null : μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} \
      ⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) = 0 := by
    have hae : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 ∨ X i ω = 1 := by
      rw [Filter.eventually_all]; intro i
      suffices μ {ω | ¬(X i ω = 0 ∨ X i ω = 1)} = 0 from this
      have heq : {ω | ¬(X i ω = 0 ∨ X i ω = 1)} = (X i ⁻¹' {0} ∪ X i ⁻¹' {1})ᶜ := by
        ext; simp
      rw [heq]
      have hd : Disjoint (X i ⁻¹' {0}) (X i ⁻¹' {1}) :=
        Set.disjoint_left.mpr (fun ω h0 h1 => by
          simp [Set.mem_preimage] at h0 h1; omega)
      have hfin : μ (X i ⁻¹' {0} ∪ X i ⁻¹' {1}) ≠ ⊤ := by
        rw [measure_union hd ((hMeas i) (measurableSet_singleton 1)),
          (hBernoulli i).measure_zero, (hBernoulli i).measure_one,
          ← ENNReal.ofReal_add (by linarith [(hBernoulli i).nonneg, (hBernoulli i).le_one])
            (hBernoulli i).nonneg]
        simp
      rw [measure_compl (.union ((hMeas i) (measurableSet_singleton 0))
        ((hMeas i) (measurableSet_singleton 1))) hfin]
      rw [measure_union hd ((hMeas i) (measurableSet_singleton 1)),
        (hBernoulli i).measure_zero, (hBernoulli i).measure_one,
        ← ENNReal.ofReal_add (by linarith [(hBernoulli i).nonneg, (hBernoulli i).le_one])
          (hBernoulli i).nonneg]
      simp
    apply le_antisymm _ (by simp)
    calc μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} \
          ⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ))
        ≤ μ {ω | ¬∀ i, X i ω = 0 ∨ X i ω = 1} := by
          apply measure_mono; intro ω ⟨hω_S, hω_not⟩
          simp only [Set.mem_ofPred_eq]; intro h_all; apply hω_not
          simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
          refine ⟨Finset.univ.filter (fun i => X i ω = 1), ?_, ?_⟩
          · rw [Finset.mem_powersetCard]; exact ⟨Finset.filter_subset _ _, by
              rw [Finset.card_filter]
              simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω_S
              have key : ∀ i : Fin m, X i ω = if X i ω = 1 then 1 else 0 := by
                intro i; rcases h_all i with h | h <;> simp [h]
              rw [Finset.sum_congr rfl (fun i _ => key i)] at hω_S; simpa using hω_S⟩
          · intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases h_all i with h | h <;> simp [h]
      _ ≤ 0 := by rw [ae_iff] at hae; exact hae.le
  have hS_eq : μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j}) =
      μ (⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) :=
    (measure_eq_measure_of_null_sdiff hFsubS hdiff_null).symm
  have hF_disj : (PC : Set (Finset (Fin m))).PairwiseDisjoint
      (fun A => ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) := by
    intro A _ B _ hAB
    simp only [Function.onFun, Set.disjoint_left, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    intro ω hA hB; apply hAB; ext i
    constructor
    · intro hi
      have hAi := hA i; simp only [hi, ↓reduceIte] at hAi
      have hBi := hB i; rw [hAi] at hBi; simpa using hBi
    · intro hi
      have hBi := hB i; simp only [hi, ↓reduceIte] at hBi
      have hAi := hA i; rw [hBi] at hAi; simpa using hAi
  have hF_meas : ∀ A ∈ PC, MeasurableSet
      (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) := by
    intro A _; exact MeasurableSet.iInter (fun i => (hMeas i) (measurableSet_singleton _))
  have hbiUnion : μ (⋃ A ∈ PC,
      ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) =
      ∑ A ∈ PC, μ (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) :=
    measure_biUnion_finset hF_disj hF_meas
  have hF_indep : ∀ A : Finset (Fin m),
      μ (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) =
        ∏ i : Fin m, ENNReal.ofReal (if i ∈ A then p i else 1 - p i) := by
    intro A
    rw [hIndep.meas_iInter (fun i =>
      ⟨{if i ∈ A then 1 else 0}, measurableSet_singleton _, rfl⟩)]
    congr 1; ext i; split_ifs with h
    · exact (hBernoulli i).measure_one
    · exact (hBernoulli i).measure_zero
  rw [hS_eq, hbiUnion]
  rw [ENNReal.toReal_sum (fun A _ => ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    (measure_mono (Set.subset_univ _)))]
  congr 1; ext A
  rw [hF_indep A, ENNReal.toReal_prod]
  have h_toReal : ∀ i : Fin m,
      (ENNReal.ofReal (if i ∈ A then p i else 1 - p i)).toReal =
        if i ∈ A then p i else 1 - p i := by
    intro i; split_ifs with h
    · exact ENNReal.toReal_ofReal (hBernoulli i).nonneg
    · exact ENNReal.toReal_ofReal (by linarith [(hBernoulli i).le_one])
  rw [Finset.prod_congr rfl (fun i _ => h_toReal i)]
  rw [show (∏ i ∈ A, p i) = ∏ i ∈ A, (if i ∈ A then p i else 1 - p i) from
    Finset.prod_congr rfl (fun i hi => by simp [hi])]
  rw [show (∏ i ∈ Finset.univ \ A, (1 - p i)) =
      ∏ i ∈ Finset.univ \ A, (if i ∈ A then p i else 1 - p i) from
    Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi; simp [hi])]
  rw [← Finset.prod_union disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset (Finset.subset_univ A)]

/-- Probability mass function of a sum of independent *identically distributed*
Bernoulli variables: if `X₁, …, X_m` are independent with `X_i ∼ Bernoulli(p)`,
then `P(∑ X_i = j) = C(m, j) p ^ j (1 - p) ^ (m - j)`, the binomial pmf. -/
theorem bernoulli_sum_pmf_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) := by
  have hmain := bernoulli_sum_pmf (μ := μ) (p := fun _ => p) hBernoulli hIndep hMeas j
  rw [hmain]
  have hterm : ∀ A ∈ Finset.univ.powersetCard j,
      (∏ i ∈ A, (fun _ => p) i) *
          (∏ i ∈ (Finset.univ : Finset (Fin m)) \ A, (1 - (fun _ => p) i)) =
        p ^ j * (1 - p) ^ (m - j) := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have hcard : A.card = j := hA.2
    have hcard_compl : ((Finset.univ : Finset (Fin m)) \ A).card = m - j := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
        Fintype.card_fin, hcard]
    simp only [Finset.prod_const, hcard, hcard_compl]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end ProbabilityTheory
