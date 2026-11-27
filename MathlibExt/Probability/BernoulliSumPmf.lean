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

/-- **Bernoulli random variable.** Let $\mu$ be a measure on a measurable space $\Omega$, let
$X : \Omega \to \mathbb{N}$ and let $p$ be a real number. Then $X$ is a Bernoulli random
variable with parameter $p$ under $\mu$ when $0 \le p \le 1$, $X$ is $\mu$-almost everywhere
measurable, and the pushforward of $\mu$ along $X$ is the Bernoulli distribution
$p\,\delta_1 + (1 - p)\,\delta_0$ on $\mathbb{N}$, which gives mass $p$ to $1$, mass $1 - p$
to $0$ and no mass elsewhere. -/
def IsBernoulliRV {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℕ) (μ : Measure Ω) (p : ℝ) : Prop :=
  ∃ hp : p ∈ Set.Icc (0 : ℝ) 1, HasLaw X (bernoulliMeasure 1 0 ⟨p, hp⟩) μ

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℕ} {μ : Measure Ω} {p : ℝ}

/-- **Bernoulli parameters are nonnegative.** If $X$ is a Bernoulli random variable with
parameter $p$ under a measure $\mu$, then $0 \le p$. -/
lemma IsBernoulliRV.nonneg (hX : IsBernoulliRV X μ p) : 0 ≤ p := by
  rcases hX with ⟨hp, _⟩
  exact hp.1

/-- **Bernoulli parameters are at most one.** If $X$ is a Bernoulli random variable with
parameter $p$ under a measure $\mu$, then $p \le 1$. -/
lemma IsBernoulliRV.le_one (hX : IsBernoulliRV X μ p) : p ≤ 1 := by
  rcases hX with ⟨hp, _⟩
  exact hp.2

/-- **Law of a Bernoulli random variable.** If $X : \Omega \to \mathbb{N}$ is a Bernoulli random
variable with parameter $p$ under a measure $\mu$, then $X$ is $\mu$-almost everywhere
measurable and its law under $\mu$, the pushforward of $\mu$ along $X$, is the Bernoulli
distribution $p\,\delta_1 + (1 - p)\,\delta_0$ on $\mathbb{N}$. -/
lemma IsBernoulliRV.hasLaw (hX : IsBernoulliRV X μ p) :
    HasLaw X (bernoulliMeasure 1 0 ⟨p, hX.nonneg, hX.le_one⟩) μ := by
  rcases hX with ⟨hp, hLaw⟩
  exact hLaw

/-- **Probability that a Bernoulli variable equals zero.** If $X : \Omega \to \mathbb{N}$ is a
Bernoulli random variable with parameter $p$ under a measure $\mu$, then
$\mu(\{\omega : X(\omega) = 0\}) = 1 - p$, as an extended nonnegative real. -/
lemma IsBernoulliRV.measure_zero (hX : IsBernoulliRV X μ p) :
    μ (X ⁻¹' {0}) = ENNReal.ofReal (1 - p) := by
  have h := hX.hasLaw.measure_eq (p := fun n : ℕ => n = 0) (measurableSet_singleton 0)
  simpa [Set.preimage_singleton, bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using h

/-- **Probability that a Bernoulli variable equals one.** If $X : \Omega \to \mathbb{N}$ is a
Bernoulli random variable with parameter $p$ under a measure $\mu$, then
$\mu(\{\omega : X(\omega) = 1\}) = p$, as an extended nonnegative real. -/
lemma IsBernoulliRV.measure_one (hX : IsBernoulliRV X μ p) :
    μ (X ⁻¹' {1}) = ENNReal.ofReal p := by
  have h := hX.hasLaw.measure_eq (p := fun n : ℕ => n = 1) (measurableSet_singleton 1)
  simpa [Set.preimage_singleton, bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using h

/-- **Distribution of a sum of independent Bernoulli variables.** Let $\mu$ be a probability
measure on a measurable space $\Omega$, let $m \in \mathbb{N}$, and let
$X_1, \dots, X_m : \Omega \to \mathbb{N}$ be measurable, mutually independent random variables
such that each $X_i$ is a Bernoulli random variable with real parameter $p_i$ under $\mu$.
Then for every $j \in \mathbb{N}$ the probability that $X_1 + \dots + X_m = j$ equals

$$
\sum_{A \subseteq \{1, \dots, m\},\ |A| = j} \ \prod_{i \in A} p_i \prod_{i \notin A} (1 - p_i).
$$

This is the Poisson binomial distribution. -/
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

/-- **Binomial distribution of a sum of i.i.d. Bernoulli variables.** Let $\mu$ be a
probability measure on a measurable space $\Omega$, let $m \in \mathbb{N}$, let $p$ be a real
number, and let $X_1, \dots, X_m : \Omega \to \mathbb{N}$ be measurable, mutually independent
random variables, each a Bernoulli random variable with parameter $p$ under $\mu$. Then for
every $j \in \mathbb{N}$ the probability that $X_1 + \dots + X_m = j$ is
$\binom{m}{j} p^j (1 - p)^{m - j}$, where the exponent $m - j$ is taken to be $0$ when $j > m$. -/
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
