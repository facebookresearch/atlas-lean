/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Ewens
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ewens–Watterson test: the conditional law of the allelic partition given `K`

Under the Ewens sampling formula (`ewensProb`), the probability of an allelic partition `π` of
`n` genes with `K(π) = π.parts.card` distinct alleles factors as

`P_θ(π) = θ ^ K(π) / θ^{(n)} * w(π)`,  `w(π) = n! / ∏ j, j ^ (a j) * (a j)!`

(`a j = π.parts.count j`; `w(π)` is the number of permutations of `n` letters with cycle type
`π`). Hence the number of alleles `K` is sufficient for `θ`: the conditional law of `π` given
`K = k` is `w(π) / ∑_{K(π') = k} w(π')`, the same for every `θ > 0` (Ewens 1972). The
normalizer is the unsigned Stirling number of the first kind, `∑_{K(π) = k} w(π) = |s(n, k)|`,
so `P_θ(K = k) = |s(n, k)| θ ^ k / θ^{(n)}` and `P(π | K = k) = w(π) / |s(n, k)|`.

Watterson (1978) used this `θ`-free conditional law as the exact null distribution of the
sample homozygosity `F(π) = ∑_i (n_i / n)²` (`n_i` the allele counts), testing neutrality
against both tails: excess homozygosity (directional selection) and a deficit (balancing
selection). We define the conditional upper-tail p-value of an arbitrary statistic `T` of the
partition (`condUpperPValue`) and prove that it is valid both conditionally on `K` and
unconditionally, for every `θ > 0`; the two homozygosity tests are the cases `T = F` and
`T = -F`.

All results assume `θ > 0`; the definitions are total (for instance `ewensCondProb θ π` is
`0 / 0 = 0` for `θ = 0` and `n ≥ 1`).

## Main results

* `ewensProb_eq_mul_cycleTypeWeight`: `P_θ(π) = θ ^ K(π) / θ^{(n)} * w(π)`.
* `ewensCondProb_eq`: the conditional law given `K` does not depend on `θ > 0`.
* `sum_cycleTypeWeight_eq_stirlingFirst`: `∑_{K(π) = k} w(π) = |s(n, k)|`.
* `numAllelesProb_eq`: `P_θ(K = k) = |s(n, k)| θ ^ k / θ^{(n)}` (Ewens 1972).
* `ewensCondProb_eq_stirlingFirst`: `P(π | K = k) = w(π) / |s(n, k)|`.
* `sum_condUpperPValue_le_cond`, `sum_condUpperPValue_le`: the conditional upper-tail p-value
  of any statistic is valid given `K` and unconditionally, for every `θ > 0`.
* `homozygosity`: Watterson's test statistic.

## References

* W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3
  (1972), 87–112.
* G. A. Watterson, *The homozygosity test of neutrality*, Genetics 88 (1978), 405–417.
* S. Tavaré, *Ancestral inference in population genetics*, École d'Été de Probabilités de
  Saint-Flour XXXI (2004), §3.
-/

@[expose] public section

noncomputable section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Ewens

variable {n : ℕ}

/-- The number of permutations of `n` letters with cycle type `π`,
`w(π) = n! / ∏ j, j ^ (a j) * (a j)!` with `a j = π.parts.count j` (Cauchy's formula). -/
def cycleTypeWeight (π : n.Partition) : ℝ :=
  (n.factorial : ℝ) /
    ∏ j ∈ π.parts.toFinset, ((j : ℝ) ^ π.parts.count j * ((π.parts.count j).factorial : ℝ))

/-- The probability `P_θ(K = k)` that a sample of `n` genes carries exactly `k` distinct
alleles under the Ewens sampling formula. -/
def numAllelesProb (θ : ℝ) (n k : ℕ) : ℝ :=
  ∑ π : n.Partition with π.parts.card = k, ewensProb θ π

/-- The conditional probability of the allelic partition `π` given that the number of alleles
is `K = K(π) = π.parts.card`, under the Ewens sampling formula with parameter `θ`. -/
def ewensCondProb (θ : ℝ) (π : n.Partition) : ℝ :=
  ewensProb θ π / numAllelesProb θ n π.parts.card

/-- The **conditional upper-tail p-value** of a statistic `T` of the allelic partition: the
conditional probability, given the observed number of alleles `K(π)`, that `T` is at least
its observed value `T π`. It is written with the cycle-type weights and so does not involve
`θ` (by `ewensCondProb_eq` it is the conditional tail probability for every `θ > 0`). -/
def condUpperPValue (T : n.Partition → ℝ) (π : n.Partition) : ℝ :=
  (∑ π' : n.Partition with π'.parts.card = π.parts.card ∧ T π ≤ T π', cycleTypeWeight π') /
    ∑ π' : n.Partition with π'.parts.card = π.parts.card, cycleTypeWeight π'

/-- The **sample homozygosity** `F(π) = ∑_i (n_i / n)²`, the sum over the alleles of the
squared sample frequencies (Watterson 1978); `n_i` ranges over the parts of `π`. -/
def homozygosity (π : n.Partition) : ℝ :=
  (π.parts.map fun j : ℕ => ((j : ℝ) / n) ^ 2).sum

/-- The cycle-type weight is positive. -/
theorem cycleTypeWeight_pos (π : n.Partition) : 0 < cycleTypeWeight π := by
  unfold cycleTypeWeight
  refine div_pos (by exact_mod_cast n.factorial_pos) (prod_pos fun j hj => ?_)
  have hj0 : 0 < j := π.parts_pos (Multiset.mem_toFinset.mp hj)
  positivity

/-- **Factorization of the Ewens sampling formula** (Ewens 1972):
`P_θ(π) = θ ^ K(π) / θ^{(n)} * w(π)`, with `K(π) = π.parts.card` the number of alleles. -/
theorem ewensProb_eq_mul_cycleTypeWeight (θ : ℝ) (π : n.Partition) :
    ewensProb θ π = θ ^ π.parts.card / (ascPochhammer ℝ n).eval θ * cycleTypeWeight π := by
  unfold ewensProb cycleTypeWeight
  have h : ∏ j ∈ π.parts.toFinset,
      (θ / j) ^ (π.parts.count j) / ((π.parts.count j).factorial : ℝ) =
      (∏ j ∈ π.parts.toFinset, θ ^ π.parts.count j) /
        ∏ j ∈ π.parts.toFinset,
          ((j : ℝ) ^ π.parts.count j * ((π.parts.count j).factorial : ℝ)) := by
    rw [← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [div_pow, div_div]
  rw [h, prod_pow_eq_pow_sum, Multiset.toFinset_sum_count_eq]
  ring

/-- `P_θ(K = k) = θ ^ k / θ^{(n)} * ∑_{K(π) = k} w(π)`. -/
private theorem numAllelesProb_eq_mul (θ : ℝ) (k : ℕ) :
    numAllelesProb θ n k = θ ^ k / (ascPochhammer ℝ n).eval θ *
      ∑ π : n.Partition with π.parts.card = k, cycleTypeWeight π := by
  rw [numAllelesProb, mul_sum]
  refine sum_congr rfl fun π hπ => ?_
  rw [ewensProb_eq_mul_cycleTypeWeight, (mem_filter.mp hπ).2]

/-- **`K` is sufficient for `θ`** (Ewens 1972): for `θ > 0`, the conditional law of the
allelic partition given the number of alleles is `w(π) / ∑_{K(π') = K(π)} w(π')`, which does
not depend on `θ`. -/
theorem ewensCondProb_eq {θ : ℝ} (hθ : 0 < θ) (π : n.Partition) :
    ewensCondProb θ π =
      cycleTypeWeight π /
        ∑ π' : n.Partition with π'.parts.card = π.parts.card, cycleTypeWeight π' := by
  rw [ewensCondProb, numAllelesProb_eq_mul θ]
  have hc : θ ^ π.parts.card / (ascPochhammer ℝ n).eval θ ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hθ.ne') (ascPochhammer_pos n θ hθ).ne'
  rw [ewensProb_eq_mul_cycleTypeWeight, mul_div_mul_left _ _ hc]

private theorem card_parts_le {n : ℕ} (π : n.Partition) : π.parts.card ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := π.parts) (a := 1) fun x hx => π.parts_pos hx
  simpa [π.parts_sum] using h

private theorem ascPochhammer_eval_eq_sum (n : ℕ) (θ : ℝ) :
    (ascPochhammer ℝ n).eval θ = ∑ k ∈ range (n + 1), (n.stirlingFirst k : ℝ) * θ ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingFirst_succ_succ, Nat.stirlingFirst_succ_zero, Nat.cast_zero,
      zero_mul, add_zero, Nat.cast_add, Nat.cast_mul]
    have h1 : ∑ k ∈ range (n + 1), ((n : ℝ) * (n.stirlingFirst (k + 1) : ℝ)) * θ ^ (k + 1) =
        ∑ k ∈ range (n + 1), (n : ℝ) * (n.stirlingFirst k : ℝ) * θ ^ k := by
      rw [sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega), sum_range_succ' _ n]
      cases n with
      | zero => simp
      | succ m => simp [Nat.stirlingFirst_succ_zero]
    rw [sum_mul]
    calc ∑ i ∈ range (n + 1), (n.stirlingFirst i : ℝ) * θ ^ i * (θ + n)
        = ∑ i ∈ range (n + 1), (n : ℝ) * (n.stirlingFirst i : ℝ) * θ ^ i +
            ∑ i ∈ range (n + 1), (n.stirlingFirst i : ℝ) * θ ^ (i + 1) := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [← h1, ← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring

/-- Grouping the Ewens law by the number of alleles. -/
private theorem sum_ewensProb_eq_sum (θ : ℝ) (n : ℕ) :
    ∑ π : n.Partition, ewensProb θ π = (∑ k ∈ range (n + 1), θ ^ k *
      ∑ π : n.Partition with π.parts.card = k, cycleTypeWeight π) /
        (ascPochhammer ℝ n).eval θ := by
  have hmaps : ∀ π ∈ (univ : Finset n.Partition), π.parts.card ∈ range (n + 1) :=
    fun π _ => mem_range.mpr (Nat.lt_succ_of_le (card_parts_le π))
  rw [← sum_fiberwise_of_maps_to hmaps, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun π hπ => ?_
  rw [ewensProb_eq_mul_cycleTypeWeight, (mem_filter.mp hπ).2]
  ring

open Polynomial in
/-- **Cauchy's count by number of cycles**: the cycle-type weights of the partitions of `n`
into `k` parts sum to the unsigned Stirling number of the first kind `|s(n, k)|`. -/
theorem sum_cycleTypeWeight_eq_stirlingFirst (n k : ℕ) :
    ∑ π : n.Partition with π.parts.card = k, cycleTypeWeight π = (n.stirlingFirst k : ℝ) := by
  set W : ℕ → ℝ := fun k => ∑ π : n.Partition with π.parts.card = k, cycleTypeWeight π
    with hW
  change W k = _
  have hpoly : (∑ j ∈ range (n + 1), C (W j) * X ^ j : ℝ[X]) =
      ∑ j ∈ range (n + 1), C (n.stirlingFirst j : ℝ) * X ^ j := by
    apply eq_of_infinite_eval_eq
    refine Set.Infinite.mono (fun θ (hθ : 0 < θ) => ?_) (Set.Ioi_infinite 0)
    simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    have h := sum_ewensProb_eq_sum θ n
    rw [sum_ewensProb θ hθ n, eq_div_iff (ascPochhammer_pos n θ hθ).ne', one_mul,
      ascPochhammer_eval_eq_sum] at h
    rw [h]
    exact sum_congr rfl fun j _ => mul_comm _ _
  rcases Nat.lt_or_ge n k with hk | hk
  · rw [Nat.stirlingFirst_eq_zero_of_lt hk, Nat.cast_zero, hW]
    refine sum_eq_zero fun π hπ => ?_
    have := card_parts_le π
    rw [(mem_filter.mp hπ).2] at this
    omega
  · have hc := congrArg (fun p : ℝ[X] => p.coeff k) hpoly
    have hk' : k ∈ range (n + 1) := mem_range.mpr (by omega)
    simpa [finsetSum_coeff, coeff_C_mul_X_pow, hk'] using hc

/-- **Law of the number of alleles** (Ewens 1972):
`P_θ(K = k) = |s(n, k)| θ ^ k / θ^{(n)}`. As an identity between the defining sums it holds
for every real `θ`; it is a probability for `θ > 0`. -/
theorem numAllelesProb_eq (θ : ℝ) (n k : ℕ) :
    numAllelesProb θ n k = (n.stirlingFirst k : ℝ) * θ ^ k / (ascPochhammer ℝ n).eval θ := by
  rw [numAllelesProb_eq_mul θ, sum_cycleTypeWeight_eq_stirlingFirst]
  ring

/-- **The Ewens–Watterson conditional law** (Ewens 1972; Watterson 1978): for `θ > 0`,
`P(π | K = K(π)) = w(π) / |s(n, K(π))| = n! / (|s(n, k)| ∏ j, j ^ (a j) (a j)!)`. -/
theorem ewensCondProb_eq_stirlingFirst {θ : ℝ} (hθ : 0 < θ) (π : n.Partition) :
    ewensCondProb θ π = cycleTypeWeight π / (n.stirlingFirst π.parts.card : ℝ) := by
  rw [ewensCondProb_eq hθ, sum_cycleTypeWeight_eq_stirlingFirst]

/-- **Validity of a discrete upper-tail p-value.** For nonnegative masses `q` on a finite set
`s` and a statistic `T`, the upper-tail p-value `p x = ∑_{y ∈ s, T x ≤ T y} q y` satisfies
`∑_{x ∈ s, p x ≤ t} q x ≤ t` for every `t ≥ 0`. -/
theorem sum_upperTail_le {ι : Type*} (s : Finset ι) (q T : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ x ∈ s with ∑ y ∈ s with T x ≤ T y, q y ≤ t, q x ≤ t := by
  classical
  set A := s.filter fun x => ∑ y ∈ s with T x ≤ T y, q y ≤ t with hA
  rcases A.eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
    exact ht
  obtain ⟨x₀, hx₀, hmin⟩ := A.exists_min_image T h
  calc ∑ x ∈ A, q x ≤ ∑ y ∈ s with T x₀ ≤ T y, q y := by
        refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun y hy _ => ?_
        · exact mem_filter.mpr ⟨(mem_filter.mp hx).1, hmin x hx⟩
        · exact hq y (mem_filter.mp hy).1
    _ ≤ t := (mem_filter.mp hx₀).2

/-- **Conditional validity of the Ewens–Watterson test**: for `θ > 0`, every number of alleles
`k` and every level `t ≥ 0`, the conditional probability given `K = k` that the conditional
upper-tail p-value of `T` is at most `t` is at most `t`. -/
theorem sum_condUpperPValue_le_cond {θ : ℝ} (hθ : 0 < θ) (T : n.Partition → ℝ) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ π : n.Partition with π.parts.card = k ∧ condUpperPValue T π ≤ t, ewensCondProb θ π ≤ t := by
  classical
  set s : Finset n.Partition := univ.filter fun π => π.parts.card = k with hs
  set W := ∑ π ∈ s, cycleTypeWeight π with hW
  have hq : ∀ π ∈ s, 0 ≤ cycleTypeWeight π / W := fun π _ =>
    div_nonneg (cycleTypeWeight_pos π).le (sum_nonneg fun _ _ => (cycleTypeWeight_pos _).le)
  have hp : ∀ π ∈ s,
      condUpperPValue T π = ∑ y ∈ s with T π ≤ T y, cycleTypeWeight y / W := by
    intro π hπ
    rw [condUpperPValue, (mem_filter.mp hπ).2, ← sum_div, hs, filter_filter]
  have hc : ∀ π ∈ s, ewensCondProb θ π = cycleTypeWeight π / W := by
    intro π hπ
    rw [ewensCondProb_eq hθ, (mem_filter.mp hπ).2]
  calc ∑ π : n.Partition with π.parts.card = k ∧ condUpperPValue T π ≤ t, ewensCondProb θ π
        = ∑ π ∈ s with ∑ y ∈ s with T π ≤ T y, cycleTypeWeight y / W ≤ t,
            cycleTypeWeight π / W := by
        rw [hs, filter_filter]
        refine sum_congr ?_ fun π hπ => hc π (by simpa [hs] using (mem_filter.mp hπ).2.1)
        ext π
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hk, h⟩
          refine ⟨hk, ?_⟩
          rw [hp π (by simpa [hs] using hk)] at h
          exact h
        · rintro ⟨hk, h⟩
          refine ⟨hk, ?_⟩
          rw [hp π (by simpa [hs] using hk)]
          exact h
    _ ≤ t := sum_upperTail_le s _ T hq ht

/-- **Validity of the Ewens–Watterson test** (Watterson 1978): for every `θ > 0` and every
level `t ≥ 0`, the Ewens probability that the conditional upper-tail p-value of `T` is at most
`t` is at most `t`. With `T = homozygosity` this is the test against excess homozygosity, with
`T = -homozygosity` the test against a deficit of homozygosity. -/
theorem sum_condUpperPValue_le {θ : ℝ} (hθ : 0 < θ) (T : n.Partition → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∑ π : n.Partition with condUpperPValue T π ≤ t, ewensProb θ π ≤ t := by
  classical
  set K : Finset ℕ := univ.image fun π : n.Partition => π.parts.card with hK
  have hmaps : ∀ π ∈ (univ : Finset n.Partition), π.parts.card ∈ K :=
    fun π _ => mem_image_of_mem _ (mem_univ π)
  have hmaps' : ∀ π ∈ (univ.filter fun π : n.Partition => condUpperPValue T π ≤ t),
      π.parts.card ∈ K := fun π _ => hmaps π (mem_univ π)
  have hpos : ∀ π : n.Partition, 0 < ewensProb θ π := fun π => by
    rw [ewensProb_eq_mul_cycleTypeWeight]
    exact mul_pos (div_pos (pow_pos hθ _) (ascPochhammer_pos n θ hθ)) (cycleTypeWeight_pos π)
  have hfactor : ∀ π : n.Partition,
      ewensProb θ π = numAllelesProb θ n π.parts.card * ewensCondProb θ π := fun π => by
    have hN : 0 < numAllelesProb θ n π.parts.card :=
      sum_pos (fun π' _ => hpos π') ⟨π, mem_filter.mpr ⟨mem_univ π, rfl⟩⟩
    rw [ewensCondProb, mul_div_cancel₀ _ hN.ne']
  rw [← sum_fiberwise_of_maps_to hmaps']
  calc ∑ k ∈ K, ∑ π ∈ univ.filter (fun π : n.Partition => condUpperPValue T π ≤ t) with
        π.parts.card = k, ewensProb θ π
      = ∑ k ∈ K, numAllelesProb θ n k *
          ∑ π : n.Partition with π.parts.card = k ∧ condUpperPValue T π ≤ t,
            ewensCondProb θ π := by
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, filter_filter]
        refine sum_congr (by ext π; simp [and_comm]) fun π hπ => ?_
        rw [hfactor π, (mem_filter.mp hπ).2.1]
    _ ≤ ∑ k ∈ K, numAllelesProb θ n k * t := by
        refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (sum_condUpperPValue_le_cond hθ T k ht) ?_
        exact sum_nonneg fun π _ => (hpos π).le
    _ = t := by
        rw [← sum_mul]
        simp only [numAllelesProb]
        rw [sum_fiberwise_of_maps_to hmaps, sum_ewensProb θ hθ n, one_mul]

end MathlibExt.Biology.PopulationGenetics.Ewens
