/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Ewens
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Nat.Choose.Cast
import MathlibExt.Probability.Distributions.ExponentialMoments

/-!
# The Ewens sampling formula in allele-count form, and the coalescent with killing

Under the neutral infinite-alleles model with scaled mutation rate `θ = 4Nu > 0`, a sample of
`n` genes is summarized by its **allele-count configuration** `a = (a_1, …, a_n)`, where `a_j` is
the number of alleles carried by exactly `j` genes, so that `∑_j j a_j = n`. The Ewens sampling
formula (Ewens 1972) is

`P(a_1, …, a_n) = n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`,

and the expected number of alleles `K_n = ∑_j a_j` is `E[K_n] = ∑_{i=0}^{n-1} θ / (θ + i)`.

`MathlibExt.Biology.PopulationGenetics.Ewens` already defines the formula on allelic partitions
(`ewensProb`), proves it is a probability distribution, derives it from Hoppe's urn, and computes
`E[K_n]`. This file adds two things on top of it, without redefining the formula.

* **The configuration form.** `ewensConfigProb θ n a` is the displayed formula, indexed by
  `j = 1, …, n`. A partition and its configuration `alleleCount π` determine each other, so the
  law of the configuration is `ewensConfigProb` (`sum_ewensProb_alleleCount_eq`), and a vector
  with `∑ j a_j ≠ n` has probability `0`.
* **The coalescent derivation of `E[K_n]`.** Looking back in time, while the genealogy has `k`
  lineages, coalescences occur at rate `k.choose 2` and mutations at rate `k θ / 2`. In the
  coalescent with killing (`KillingCoalescent`), a mutation removes its lineage and founds one
  allele of the sample, so the number of alleles in a nonempty sample is one plus the number of
  levels at which the mutation clock rings first (the empty sample has none). Competing
  exponential clocks (`ProbabilityTheory.measureReal_lt_of_hasLaw_expMeasure`) give probability
  `(k θ / 2) / (k θ / 2 + k (k - 1) / 2) = θ / (θ + k - 1)` for that event, and summing over
  `k = 2, …, n` gives `E[K_n] = ∑_{i=0}^{n-1} θ / (θ + i)` (`integral_numAlleles`), the Ewens mean
  (`integral_numAlleles_eq_ewens`).

The identification of the alleles of the sample with the killing events is the modeling step
of the coalescent with killing and is built into the definition of `numAlleles`; the joint law
of the full configuration from a gene-labeled genealogy with mutations is not derived here.

## Main results

* `alleleCount`, `sum_mul_alleleCount`, `sum_alleleCount`: the configuration of a partition,
  `∑_j j a_j = n`, and `K_n = ∑_j a_j`.
* `ewensConfigProb`, `ewensProb_eq_ewensConfigProb`: the formula on configurations.
* `sum_ewensProb_alleleCount_eq`, `sum_ewensProb_alleleCount_eq_zero`: **the Ewens sampling
  formula** as the law of the configuration.
* `sum_ewensProb_mul_sum_alleleCount`: `E[∑_j a_j] = ∑_{i<n} θ / (θ + i)`.
* `KillingCoalescent`, `KillingCoalescent.numAlleles`,
  `KillingCoalescent.measureReal_mutation_first`, `KillingCoalescent.integral_numAlleles`,
  `KillingCoalescent.integral_numAlleles_eq_ewens`: the coalescent derivation of `E[K_n]`.
* `killingMeasure`, `KillingCoalescent.ofPi`: a concrete model, so the hypotheses are not
  vacuous.

## References

* W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3
  (1972), 87–112.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), §1.3.
* S. Tavaré, *Ancestral inference in population genetics*, École d'Été de Probabilités de
  Saint-Flour XXXI (2004), §3.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Nat

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

open MathlibExt.Biology.PopulationGenetics.Ewens

/-! ### The allele-count configuration -/

/-- The **allele-count configuration** of an allelic partition `π` of a sample of `n` genes:
`alleleCount π j = a_j` is the number of alleles carried by exactly `j` genes of the sample. -/
def alleleCount {n : ℕ} (π : n.Partition) (j : ℕ) : ℕ := π.parts.count j

/-- The **Ewens sampling formula** written on an allele-count configuration
`a = (a_1, …, a_n)` (Ewens 1972):
`P(a_1, …, a_n) = n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`.
Only the values `a 1, …, a n` enter. The formula is the probability of the configuration `a`
when `∑_{j=1}^n j a_j = n` (`sum_ewensProb_alleleCount_eq`); otherwise no sample has
configuration `a`. -/
def ewensConfigProb (θ : ℝ) (n : ℕ) (a : ℕ → ℕ) : ℝ :=
  (n ! : ℝ) / (ascPochhammer ℝ n).eval θ * ∏ j ∈ Icc 1 n, (θ / j) ^ a j / ((a j)! : ℝ)

variable {n : ℕ}

private lemma toFinset_parts_subset (π : n.Partition) : π.parts.toFinset ⊆ Icc 1 n := by
  intro j hj
  rw [Multiset.mem_toFinset] at hj
  exact mem_Icc.mpr ⟨π.parts_pos hj, Nat.Partition.le_of_mem_parts hj⟩

private lemma alleleCount_eq_zero (π : n.Partition) {j : ℕ} (hj : j ∉ Icc 1 n) :
    alleleCount π j = 0 :=
  Multiset.count_eq_zero.mpr fun h ↦ hj (toFinset_parts_subset π (Multiset.mem_toFinset.mpr h))

/-- The configuration of a sample of `n` genes accounts for every gene:
`∑_{j=1}^n j a_j = n`. -/
theorem sum_mul_alleleCount (π : n.Partition) :
    ∑ j ∈ Icc 1 n, j * alleleCount π j = n := by
  classical
  conv_rhs => rw [← π.parts_sum, sum_multiset_count]
  rw [sum_subset (toFinset_parts_subset π)]
  · exact sum_congr rfl fun j _ ↦ by rw [smul_eq_mul, mul_comm]; rfl
  · intro j _ hj
    rw [Multiset.count_eq_zero.mpr (by simpa using hj), zero_smul]

/-- The number of distinct alleles in the sample is `K = ∑_{j=1}^n a_j`. -/
theorem sum_alleleCount (π : n.Partition) :
    ∑ j ∈ Icc 1 n, alleleCount π j = π.parts.card := by
  classical
  rw [← Multiset.toFinset_sum_count_eq, sum_subset (toFinset_parts_subset π)]
  · rfl
  · intro j _ hj
    exact Multiset.count_eq_zero.mpr (by simpa using hj)

/-- The partition-indexed Ewens formula `ewensProb` is the configuration formula evaluated at
the configuration of the partition. -/
theorem ewensProb_eq_ewensConfigProb (θ : ℝ) (π : n.Partition) :
    ewensProb θ π = ewensConfigProb θ n (alleleCount π) := by
  unfold ewensProb ewensConfigProb
  congr 1
  refine prod_subset (toFinset_parts_subset π) fun j _ hj ↦ ?_
  rw [show π.parts.count j = 0 from Multiset.count_eq_zero.mpr (by simpa using hj)]
  simp

/-- The multiset of allele sizes with `a j` alleles of size `j`, for `1 ≤ j ≤ n`. -/
private def configParts (n : ℕ) (a : ℕ → ℕ) : Multiset ℕ :=
  ∑ j ∈ Icc 1 n, Multiset.replicate (a j) j

private lemma count_configParts (a : ℕ → ℕ) (i : ℕ) :
    (configParts n a).count i = if i ∈ Icc 1 n then a i else 0 := by
  classical
  simp [configParts, Multiset.count_sum', Multiset.count_replicate]

private lemma sum_configParts (a : ℕ → ℕ) :
    (configParts n a).sum = ∑ j ∈ Icc 1 n, j * a j := by
  simp [configParts, Multiset.sum_sum, Multiset.sum_replicate, mul_comm]

open scoped Classical in
/-- **The Ewens sampling formula as the law of the allele-count configuration.** If
`∑_{j=1}^n j a_j = n`, exactly one allelic partition has configuration `a`, and its Ewens
probability is `ewensConfigProb θ n a`; so the probability that the sample has configuration
`a` is `n! / θ^{(n)} · ∏_j (θ / j) ^ {a_j} / a_j!`. -/
theorem sum_ewensProb_alleleCount_eq (θ : ℝ) {a : ℕ → ℕ} (ha : ∑ j ∈ Icc 1 n, j * a j = n) :
    ∑ π : n.Partition with ∀ j ∈ Icc 1 n, alleleCount π j = a j, ewensProb θ π =
      ewensConfigProb θ n a := by
  classical
  set π₀ : n.Partition := Nat.Partition.ofSums n (configParts n a) (by rw [sum_configParts, ha])
  have h₀ : ∀ j ∈ Icc 1 n, alleleCount π₀ j = a j := fun j hj ↦ by
    rw [alleleCount, Nat.Partition.count_ofSums_of_ne_zero _ (by grind), count_configParts,
      ite_eq_left hj]
  have hfilter : ({π | ∀ j ∈ Icc 1 n, alleleCount π j = a j} : Finset n.Partition) = {π₀} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨by simpa using h₀, fun π hπ ↦ ?_⟩
    simp only [mem_filter, mem_univ, true_and] at hπ
    refine Nat.Partition.ext (Multiset.ext.mpr fun j ↦ ?_)
    change alleleCount π j = alleleCount π₀ j
    by_cases hj : j ∈ Icc 1 n
    · rw [hπ j hj, h₀ j hj]
    · rw [alleleCount_eq_zero π hj, alleleCount_eq_zero π₀ hj]
  rw [hfilter, sum_singleton, ewensProb_eq_ewensConfigProb]
  unfold ewensConfigProb
  congr 1
  exact prod_congr rfl fun j hj ↦ by rw [h₀ j hj]

open scoped Classical in
/-- A configuration with `∑_{j=1}^n j a_j ≠ n` is the configuration of no sample of `n` genes,
so it has probability zero. -/
theorem sum_ewensProb_alleleCount_eq_zero (θ : ℝ) {a : ℕ → ℕ}
    (ha : ∑ j ∈ Icc 1 n, j * a j ≠ n) :
    ∑ π : n.Partition with ∀ j ∈ Icc 1 n, alleleCount π j = a j, ewensProb θ π = 0 := by
  refine sum_eq_zero fun π hπ ↦ absurd ?_ ha
  simp only [mem_filter, mem_univ, true_and] at hπ
  exact (sum_congr rfl fun j hj ↦ by rw [hπ j hj]).trans (sum_mul_alleleCount π)

/-- **Expected number of alleles**, in configuration form: under the Ewens sampling formula,
`E[K_n] = E[∑_{j=1}^n a_j] = ∑_{i=0}^{n-1} θ / (θ + i)` (Ewens 1972). -/
theorem sum_ewensProb_mul_sum_alleleCount (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    ∑ π : n.Partition, ewensProb θ π * ∑ j ∈ Icc 1 n, (alleleCount π j : ℝ) =
      ∑ i ∈ range n, θ / (θ + i) := by
  simp_rw [← Nat.cast_sum, sum_alleleCount]
  exact sum_ewensProb_mul_card_parts θ hθ n

/-! ### The coalescent with killing -/

section Killing

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The **coalescent with killing** of a sample of `n` genes under infinite-alleles mutation,
through its competing clocks (time in units of `2N` generations, `θ = 4Nu`, mutations at rate
`θ / 2` per lineage, as in `KingmanTimes`). While the genealogy has `k` lineages
(`2 ≤ k ≤ n`), the next coalescence comes after time `C k ~ Exp(k.choose 2)` and the next
mutation after time `M k ~ Exp(k θ / 2)`, independently. Whichever comes first reduces the
number of lineages to `k - 1`: a coalescence merges two lineages, and a mutation founds an
allele carried by exactly the genes descending from that lineage, which is then removed
("killed") because earlier mutations on it are invisible in the sample. By memorylessness the
clocks restart at each level, so one independent pair of clocks per level determines the
sequence of events. The values of `C k`, `M k` for `k ∉ [2, n]` are irrelevant. -/
structure KillingCoalescent (μ : Measure Ω) (n : ℕ) (θ : ℝ) where
  /-- `C k` is the waiting time to the next coalescence with `k` lineages. -/
  C : ℕ → Ω → ℝ
  /-- `M k` is the waiting time to the next mutation with `k` lineages. -/
  M : ℕ → Ω → ℝ
  /-- Each of the `k.choose 2` pairs of lineages coalesces at rate `1`. -/
  hasLaw_C : ∀ k ∈ Icc 2 n, HasLaw (C k) (expMeasure (k.choose 2 : ℕ)) μ
  /-- Each of the `k` lineages mutates at rate `θ / 2`. -/
  hasLaw_M : ∀ k ∈ Icc 2 n, HasLaw (M k) (expMeasure (k * θ / 2)) μ
  /-- All clocks are mutually independent (`Sum.inl k` is the mutation clock of level `k`,
  `Sum.inr k` its coalescence clock). -/
  indep : iIndepFun (fun i : Icc 2 n ⊕ Icc 2 n ↦ Sum.elim (fun k : Icc 2 n ↦ M k)
    (fun k : Icc 2 n ↦ C k) i) μ

namespace KillingCoalescent

variable {μ : Measure Ω} {n : ℕ} {θ : ℝ} (K : KillingCoalescent μ n θ)

/-- The two clocks of a level are independent. -/
theorem indepFun {k : ℕ} (hk : k ∈ Icc 2 n) : IndepFun (K.M k) (K.C k) μ :=
  K.indep.indepFun (i := .inl ⟨k, hk⟩) (j := .inr ⟨k, hk⟩) Sum.inl_ne_inr

open scoped Classical in
/-- The **number of alleles** `K_n` in the sample: one allele per killing event, i.e. one for
each level `2 ≤ k ≤ n` at which the mutation clock rings before the coalescence clock, plus one
for the allele of the last remaining lineage. The empty sample (`n = 0`) has no alleles, as for
the Ewens statistic `π.parts.card` of the empty partition. -/
def numAlleles (ω : Ω) : ℕ :=
  if n = 0 then 0 else 1 + #{k ∈ Icc 2 n | K.M k ω < K.C k ω}

/-- With `k ≥ 2` lineages, the next event back in time is a mutation with probability
`θ / (θ + k - 1)`. -/
theorem measureReal_mutation_first [IsProbabilityMeasure μ] (hθ : 0 < θ) {k : ℕ}
    (hk : k ∈ Icc 2 n) :
    μ.real {ω | K.M k ω < K.C k ω} = θ / (θ + (k - 1 : ℝ)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have hc : ((k.choose 2 : ℕ) : ℝ) = k * (k - 1) / 2 := Nat.cast_choose_two ℝ k
  rw [measureReal_lt_of_hasLaw_expMeasure (by positivity) (by rw [hc]; nlinarith)
    (K.hasLaw_M k hk) (K.hasLaw_C k hk) (K.indepFun hk), hc]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hd : θ + (k - 1 : ℝ) ≠ 0 := by nlinarith
  field_simp

private lemma sum_Icc_two (θ : ℝ) (hθ : 0 < θ) {n : ℕ} (hn : 1 ≤ n) :
    1 + ∑ k ∈ Icc 2 n, θ / (θ + ((k : ℝ) - 1)) = ∑ i ∈ range n, θ / (θ + i) := by
  induction n, hn using Nat.le_induction with
  | base => simp [hθ.ne']
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega), ← add_assoc, ih, sum_range_succ]
    push_cast
    ring_nf

/-- **Expected number of alleles from the coalescent** (Ewens 1972; Durrett 2008, §1.3):
`E[K_n] = ∑_{i=0}^{n-1} θ / (θ + i)`, summing the probability `θ / (θ + k - 1)` that the event
at level `k` is a killing. -/
theorem integral_numAlleles [IsProbabilityMeasure μ] (hθ : 0 < θ) (hn : 1 ≤ n) :
    ∫ ω, (K.numAlleles ω : ℝ) ∂μ = ∑ i ∈ range n, θ / (θ + i) := by
  classical
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have hmeas : ∀ k ∈ Icc 2 n, AEMeasurable (fun ω ↦ (K.M k ω, K.C k ω)) μ := fun k hk ↦
    (IndepFun.hasLaw_prod (K.hasLaw_M k hk) (K.hasLaw_C k hk) (K.indepFun hk)).aemeasurable
  have hnull : ∀ k ∈ Icc 2 n, NullMeasurableSet {ω | K.M k ω < K.C k ω} μ := fun k hk ↦
    (hmeas k hk).nullMeasurableSet_preimage hS
  have hint : ∀ k ∈ Icc 2 n, Integrable ({ω | K.M k ω < K.C k ω}.indicator (1 : Ω → ℝ)) μ :=
    fun k hk ↦ (integrable_const (1 : ℝ)).indicator₀ (hnull k hk)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hK : (fun ω ↦ (K.numAlleles ω : ℝ)) =
      fun ω ↦ 1 + ∑ k ∈ Icc 2 n, {ω | K.M k ω < K.C k ω}.indicator (1 : Ω → ℝ) ω := by
    funext ω
    simp only [numAlleles, ite_eq_right hn0, Nat.cast_add, Nat.cast_one, card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Set.indicator_apply, Set.mem_ofPred_eq,
      Pi.one_apply]
  rw [hK, integral_add (integrable_const 1) (integrable_finsetSum _ hint),
    integral_finsetSum _ hint, integral_const, probReal_univ, one_smul,
    ← sum_Icc_two θ hθ hn]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  rw [integral_indicator₀ (hnull k hk), Pi.one_def, setIntegral_const, smul_eq_mul, mul_one,
    K.measureReal_mutation_first hθ hk]

/-- The coalescent with killing and the Ewens sampling formula give the same expected number of
alleles. -/
theorem integral_numAlleles_eq_ewens [IsProbabilityMeasure μ] (hθ : 0 < θ) (hn : 1 ≤ n) :
    ∫ ω, (K.numAlleles ω : ℝ) ∂μ = ∑ π : n.Partition, ewensProb θ π * (π.parts.card : ℝ) := by
  rw [K.integral_numAlleles hθ hn, sum_ewensProb_mul_card_parts θ hθ n]

end KillingCoalescent

/-! ### A concrete model -/

/-- Rates of the clocks of the coalescent with killing: `k θ / 2` for the mutation clock
(`Sum.inl k`) and `k.choose 2` for the coalescence clock (`Sum.inr k`) at level `k`. -/
def killingRate (n : ℕ) (θ : ℝ) : Icc 2 n ⊕ Icc 2 n → ℝ
  | .inl k => (k : ℕ) * θ / 2
  | .inr k => ((k : ℕ).choose 2 : ℕ)

/-- The clock rates are positive for `θ > 0`. -/
theorem killingRate_pos {n : ℕ} {θ : ℝ} (hθ : 0 < θ) (i : Icc 2 n ⊕ Icc 2 n) :
    0 < killingRate n θ i := by
  rcases i with ⟨k, hk⟩ | ⟨k, hk⟩
  · have : (0 : ℝ) < k := by exact_mod_cast (by grind : 0 < k)
    simp only [killingRate]
    positivity
  · simp only [killingRate, Nat.cast_pos]
    exact Nat.choose_pos (by grind)

/-- The canonical probability space for the coalescent with killing: independent exponential
clocks with rates `killingRate n θ`. -/
def killingMeasure (n : ℕ) (θ : ℝ) : Measure (Icc 2 n ⊕ Icc 2 n → ℝ) :=
  Measure.pi fun i => expMeasure (killingRate n θ i)

/-- `killingMeasure n θ` is a probability measure for `θ > 0`. -/
theorem isProbabilityMeasure_killingMeasure (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    IsProbabilityMeasure (killingMeasure n θ) := by
  have := fun i ↦ isProbabilityMeasure_expMeasure (killingRate_pos (n := n) hθ i)
  unfold killingMeasure
  infer_instance

/-- The coordinate clocks of `killingMeasure n θ` form a coalescent with killing, so
`KillingCoalescent` is inhabited for every sample size and every `θ > 0`. -/
def KillingCoalescent.ofPi (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    KillingCoalescent (killingMeasure n θ) n θ where
  C k ω := if h : k ∈ Icc 2 n then ω (.inr ⟨k, h⟩) else 0
  M k ω := if h : k ∈ Icc 2 n then ω (.inl ⟨k, h⟩) else 0
  hasLaw_C k hk := by
    have := fun i ↦ isProbabilityMeasure_expMeasure (killingRate_pos (n := n) hθ i)
    have hT : (fun ω : Icc 2 n ⊕ Icc 2 n → ℝ ↦ if h : k ∈ Icc 2 n then ω (.inr ⟨k, h⟩) else 0) =
        Function.eval (.inr ⟨k, hk⟩) := by
      funext ω
      simp [hk]
    rw [hT]
    exact (measurePreserving_eval (fun i ↦ expMeasure (killingRate n θ i)) (.inr ⟨k, hk⟩)).hasLaw
  hasLaw_M k hk := by
    have := fun i ↦ isProbabilityMeasure_expMeasure (killingRate_pos (n := n) hθ i)
    have hT : (fun ω : Icc 2 n ⊕ Icc 2 n → ℝ ↦ if h : k ∈ Icc 2 n then ω (.inl ⟨k, h⟩) else 0) =
        Function.eval (.inl ⟨k, hk⟩) := by
      funext ω
      simp [hk]
    rw [hT]
    exact (measurePreserving_eval (fun i ↦ expMeasure (killingRate n θ i)) (.inl ⟨k, hk⟩)).hasLaw
  indep := by
    have := fun i ↦ isProbabilityMeasure_expMeasure (killingRate_pos (n := n) hθ i)
    have hT : (fun i : Icc 2 n ⊕ Icc 2 n ↦ Sum.elim
        (fun k : Icc 2 n ↦ fun ω : Icc 2 n ⊕ Icc 2 n → ℝ ↦
          if h : (k : ℕ) ∈ Icc 2 n then ω (.inl ⟨k, h⟩) else 0)
        (fun k : Icc 2 n ↦ fun ω : Icc 2 n ⊕ Icc 2 n → ℝ ↦
          if h : (k : ℕ) ∈ Icc 2 n then ω (.inr ⟨k, h⟩) else 0) i) =
        fun i ω ↦ id (ω i) := by
      funext i ω
      rcases i with k | k <;> simp
    rw [hT]
    exact iIndepFun_pi (μ := fun i ↦ expMeasure (killingRate n θ i)) fun _ ↦ aemeasurable_id

end Killing

end MathlibExt.Biology.PopulationGenetics.Coalescent
