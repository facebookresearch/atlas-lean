/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ewens sampling formula and the Hoppe urn

Under the neutral infinite-alleles model with scaled mutation rate `θ = 4Nu > 0`, a sample of
`n` genes is summarized by its allelic partition: a partition `π` of `n` in which
`a j = π.parts.count j` alleles are each carried by exactly `j` genes. Ewens (1972) showed

`P(π) = n! * (∏ j, (θ / j) ^ (a j) / (a j)!) / θ^{(n)}`,

where `θ^{(n)} = θ (θ + 1) ⋯ (θ + n - 1)` is the rising factorial (`ascPochhammer`).

Hoppe (1984) obtained the same law from an urn (the Chinese restaurant process): genes are
sampled one at a time; when `k` genes have been sampled, the next one carries a new allele
with probability `θ / (θ + k)`, and otherwise copies an earlier gene chosen uniformly, so an
existing allele carried by `j` genes gains a copy with probability `j / (θ + k)`. On allelic
partitions this is a Markov chain: from `π ⊢ k` it moves to `π + {1}` with probability
`θ / (θ + k)`, and replaces one part `j` by `j + 1` with probability `j * a j / (θ + k)`.
We formalize the urn directly as this chain on allelic partitions (`hoppeStep`, `hoppeLaw`);
the reduction from the urn on individual genes to the chain on partitions is not formalized.

All results assume `θ > 0`. The definitions are total: for instance, for `θ = 0` and `n ≥ 1`
the rising factorial vanishes and `ewensProb` returns Lean's junk value `0`.

## Main results

* `ewensProb`: the Ewens sampling formula.
* `ewensProb_nonneg`, `sum_ewensProb`: it is a probability distribution on the partitions of
  `n` (nonnegative weights summing to one).
* `sum_ewensProb_mul_card_parts`: the expected number of alleles is `∑_{i < n} θ / (θ + i)`.
* `hoppeStep`, `hoppeStep_nonneg`, `sum_hoppeStep`: the Hoppe-urn transition on allelic
  partitions is a stochastic matrix.
* `hoppeLaw`, `hoppeLaw_eq_ewensProb`, `hoppeLaw_nonneg`: the law of the Hoppe urn after `n`
  draws is the Ewens sampling formula.

## References

* W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3
  (1972), 87–112.
* F. M. Hoppe, *Pólya-like urns and the Ewens sampling formula*, J. Math. Biol. 20 (1984),
  91–94.
* S. Tavaré, *Ancestral inference in population genetics*, École d'Été de Probabilités de
  Saint-Flour XXXI (2004), §3.
-/

@[expose] public section

noncomputable section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Ewens

/-- The **Ewens sampling formula**: the probability, under the neutral infinite-alleles model
with scaled mutation rate `θ = 4Nu`, that a sample of `n` genes has allelic partition `π`
(`π.parts.count j` alleles carried by exactly `j` genes each):
`n! * (∏ j, (θ / j) ^ (a j) / (a j)!) / θ^{(n)}` (Ewens 1972), for `θ > 0`. -/
def ewensProb (θ : ℝ) {n : ℕ} (π : n.Partition) : ℝ :=
  (n.factorial : ℝ) / (ascPochhammer ℝ n).eval θ *
    ∏ j ∈ π.parts.toFinset,
      (θ / j) ^ (π.parts.count j) / ((π.parts.count j).factorial : ℝ)

private def weight (θ : ℝ) (m : Multiset ℕ) : ℝ :=
  ∏ j ∈ m.toFinset, (θ / j) ^ m.count j / (m.count j).factorial

private lemma weight_cons (θ : ℝ) (m : Multiset ℕ) (j : ℕ) :
    weight θ (j ::ₘ m) * ((m.count j + 1 : ℕ) : ℝ) = θ / j * weight θ m := by
  classical
  have hfac : ((m.count j).factorial : ℝ) ≠ 0 := by positivity
  have hsucc : ((m.count j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : (θ / j) ^ (m.count j + 1) / ((m.count j + 1).factorial : ℝ) *
      ((m.count j + 1 : ℕ) : ℝ) = θ / j * ((θ / j) ^ m.count j /
        ((m.count j).factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
  unfold weight
  rw [Multiset.toFinset_cons]
  by_cases hj : j ∈ m.toFinset
  · rw [insert_eq_of_mem hj]
    rw [← prod_erase_mul _ _ hj, ← prod_erase_mul m.toFinset _ hj]
    have hp : (∏ k ∈ m.toFinset.erase j,
        (θ / k) ^ (j ::ₘ m).count k / ((j ::ₘ m).count k).factorial) =
        ∏ k ∈ m.toFinset.erase j, (θ / k) ^ m.count k / (m.count k).factorial := by
      apply prod_congr rfl
      intro k hk
      simp only [Multiset.count_cons, ite_eq_right (mem_erase.mp hk).1, add_zero]
    rw [hp]
    simp only [Multiset.count_cons_self]
    calc
      _ = (∏ k ∈ m.toFinset.erase j, (θ / k) ^ m.count k / (m.count k).factorial) *
          ((θ / j) ^ (m.count j + 1) / ((m.count j + 1).factorial : ℝ) *
            ((m.count j + 1 : ℕ) : ℝ)) := by ring
      _ = _ := by rw [hc]; ring
  · rw [prod_insert hj]
    have hj' : j ∉ m := by simpa using hj
    have hp : (∏ k ∈ m.toFinset,
        (θ / k) ^ (j ::ₘ m).count k / ((j ::ₘ m).count k).factorial) =
        ∏ k ∈ m.toFinset, (θ / k) ^ m.count k / (m.count k).factorial := by
      apply prod_congr rfl
      intro k hk
      have hkj : k ≠ j := by intro h; subst k; exact hj hk
      simp [hkj]
    rw [hp]
    simp [Multiset.count_eq_zero_of_notMem hj']

private def weightedSum (θ : ℝ) (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p : n.Partition, weight θ p.parts * f p.parts.card

private lemma marked_sum (θ : ℝ) (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (f : ℕ → ℝ) :
    (∑ p : n.Partition, weight θ p.parts * (p.parts.count j : ℝ) * f p.parts.card) =
      θ / j * weightedSum θ (n - j) (fun c ↦ f (c + 1)) := by
  classical
  let e := Nat.Partition.partitionWithPartEquiv hj hjn
  have hs : (∑ p : n.Partition,
      weight θ p.parts * (p.parts.count j : ℝ) * f p.parts.card) =
      ∑ p : {p : n.Partition // j ∈ p.parts},
        weight θ p.val.parts * (p.val.parts.count j : ℝ) * f p.val.parts.card := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun p : n.Partition ↦ j ∈ p.parts)
      (fun p ↦ weight θ p.parts * (p.parts.count j : ℝ) * f p.parts.card)]
    have hz : (∑ p : {p : n.Partition // j ∉ p.parts},
        weight θ p.val.parts * (p.val.parts.count j : ℝ) * f p.val.parts.card) = 0 := by
      apply sum_eq_zero
      intro p _
      simp [Multiset.count_eq_zero_of_notMem p.property]
    rw [hz, add_zero]
  rw [hs]
  calc
    _ = ∑ q : (n - j).Partition, θ / j *
        (weight θ q.parts * f (q.parts.card + 1)) := by
      apply (Fintype.sum_equiv e _ _ _)
      intro p
      have hm : p.val.parts = j ::ₘ (e p).parts := by
        exact (Multiset.cons_erase p.property).symm
      rw [hm, Multiset.count_cons_self, Multiset.card_cons, weight_cons]
      ring
    _ = _ := by rw [← mul_sum]; rfl

private lemma parts_sum_range (n : ℕ) (p : n.Partition) :
    (∑ i ∈ range n, (p.parts.count (i + 1) : ℝ) * (i + 1 : ℕ)) = n := by
  have h : (∑ j ∈ range (n + 1), p.parts.count j * j) = n := by
    calc
      _ = p.parts.sum := by
        rw [sum_multiset_count]
        symm
        apply sum_subset
        · intro j hj
          exact mem_range.mpr (Nat.lt_succ_of_le (p.le_of_mem_parts (by simpa using hj)))
        · intro j _ hj
          simp [Multiset.count_eq_zero_of_notMem (by simpa using hj)]
      _ = n := p.parts_sum
  rw [sum_range_succ'] at h
  simp only [mul_zero, add_zero] at h
  exact_mod_cast h

private lemma weighted_sum_removal (θ : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    (n : ℝ) * weightedSum θ n f =
      θ * ∑ k ∈ range n, weightedSum θ k (fun c ↦ f (c + 1)) := by
  classical
  calc
    _ = ∑ p : n.Partition, ∑ i ∈ range n,
        (i + 1 : ℕ) * (weight θ p.parts * (p.parts.count (i + 1) : ℝ) *
          f p.parts.card) := by
      change (n : ℝ) * (∑ p : n.Partition, weight θ p.parts * f p.parts.card) = _
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      rw [← parts_sum_range n p]
      simp only [sum_mul]
      apply sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ range n, (i + 1 : ℕ) *
        ∑ p : n.Partition, weight θ p.parts * (p.parts.count (i + 1) : ℝ) *
          f p.parts.card := by rw [sum_comm]; simp_rw [mul_sum]
    _ = ∑ i ∈ range n, θ * weightedSum θ (n - (i + 1)) (fun c ↦ f (c + 1)) := by
      apply sum_congr rfl
      intro i hi
      have hi' : i + 1 ≤ n := mem_range.mp hi
      rw [marked_sum θ n (i + 1) (by omega) hi' f]
      have hne : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simpa only [Nat.sub_sub, Nat.add_comm] using
        sum_range_reflect (fun k ↦ weightedSum θ k (fun c ↦ f (c + 1))) n

private lemma weighted_sum_succ (θ : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    ((n + 1 : ℕ) : ℝ) * weightedSum θ (n + 1) f =
      (n : ℝ) * weightedSum θ n f + θ * weightedSum θ n (fun c ↦ f (c + 1)) := by
  rw [weighted_sum_removal, sum_range_succ, mul_add, ← weighted_sum_removal]

private lemma weighted_sum_one_succ (θ : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * weightedSum θ (n + 1) (fun _ ↦ 1) =
      (θ + n) * weightedSum θ n (fun _ ↦ 1) := by
  rw [weighted_sum_succ]
  ring

private lemma weighted_sum_card_succ (θ : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * weightedSum θ (n + 1) (fun c ↦ c) =
      (θ + n) * weightedSum θ n (fun c ↦ c) +
        θ * weightedSum θ n (fun _ ↦ 1) := by
  rw [weighted_sum_succ]
  have hs : weightedSum θ n (fun c ↦ ((c + 1 : ℕ) : ℝ)) =
      weightedSum θ n (fun c ↦ c) + weightedSum θ n (fun _ ↦ 1) := by
    simp [weightedSum, mul_add, sum_add_distrib]
  rw [hs]
  ring

private lemma weighted_totals (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    (n.factorial : ℝ) * weightedSum θ n (fun _ ↦ 1) =
        (ascPochhammer ℝ n).eval θ ∧
      (n.factorial : ℝ) * weightedSum θ n (fun c ↦ c) =
        (ascPochhammer ℝ n).eval θ * ∑ i ∈ range n, θ / (θ + i) := by
  induction n with
  | zero => simp [weightedSum, weight]
  | succ n ih =>
    have hn : θ + (n : ℝ) ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hθ (by positivity))
    constructor
    · calc
        _ = (n.factorial : ℝ) *
            (((n + 1 : ℕ) : ℝ) * weightedSum θ (n + 1) (fun _ ↦ 1)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ = (θ + n) * ((n.factorial : ℝ) * weightedSum θ n (fun _ ↦ 1)) := by
          rw [weighted_sum_one_succ]
          ring
        _ = _ := by rw [ih.1, ascPochhammer_succ_eval]; ring
    · calc
        _ = (n.factorial : ℝ) *
            (((n + 1 : ℕ) : ℝ) * weightedSum θ (n + 1) (fun c ↦ c)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ = (θ + n) * ((n.factorial : ℝ) * weightedSum θ n (fun c ↦ c)) +
            θ * ((n.factorial : ℝ) * weightedSum θ n (fun _ ↦ 1)) := by
          rw [weighted_sum_card_succ]
          ring
        _ = _ := by
          rw [ih.1, ih.2, ascPochhammer_succ_eval, sum_range_succ]
          field_simp

/-- **The Ewens sampling formula is a probability distribution** on the partitions of `n`
(Ewens 1972; equivalently, Cauchy's cycle-type formula `∑_{σ ∈ S_n} θ^{#cycles σ} = θ^{(n)}`).
-/
theorem sum_ewensProb (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    ∑ π : n.Partition, ewensProb θ π = 1 := by
  classical
  have hpos := ne_of_gt (ascPochhammer_pos n θ hθ)
  change (∑ p : n.Partition,
    (n.factorial : ℝ) / (ascPochhammer ℝ n).eval θ * weight θ p.parts) = 1
  rw [← mul_sum, div_mul_eq_mul_div]
  have hs := (weighted_totals θ hθ n).1
  simp only [weightedSum, mul_one] at hs
  rw [hs, div_self hpos]

/-- The Ewens sampling formula is nonnegative for `θ > 0`; with `sum_ewensProb` it is a
probability distribution on the partitions of `n`. -/
theorem ewensProb_nonneg {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : n.Partition) :
    0 ≤ ewensProb θ π := by
  unfold ewensProb
  have hpos := ascPochhammer_pos n θ hθ
  refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) hpos.le) (prod_nonneg fun j _ => ?_)
  exact div_nonneg (pow_nonneg (div_nonneg hθ.le (Nat.cast_nonneg _)) _) (Nat.cast_nonneg _)

/-- **Expected number of alleles** in a sample of `n` genes under the Ewens sampling formula:
`E[K_n] = ∑_{i < n} θ / (θ + i)` (Ewens 1972). -/
theorem sum_ewensProb_mul_card_parts (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    ∑ π : n.Partition, ewensProb θ π * (π.parts.card : ℝ) =
      ∑ i ∈ range n, θ / (θ + i) := by
  classical
  have hpos := ne_of_gt (ascPochhammer_pos n θ hθ)
  change (∑ p : n.Partition,
    ((n.factorial : ℝ) / (ascPochhammer ℝ n).eval θ * weight θ p.parts) *
      (p.parts.card : ℝ)) = _
  simp_rw [mul_assoc]
  rw [← mul_sum, div_mul_eq_mul_div]
  change ((n.factorial : ℝ) * weightedSum θ n (fun c ↦ c)) /
    (ascPochhammer ℝ n).eval θ = _
  rw [(weighted_totals θ hθ n).2, mul_div_cancel_left₀ _ hpos]

/-- One step of **Hoppe's urn** on allelic partitions (Hoppe 1984): from a partition `π` of
`k`, the next gene carries a new allele with probability `θ / (θ + k)` (target parts
`1 ::ₘ π.parts`), and copies an allele carried by `j` genes with probability
`j * a j / (θ + k)`, where `a j = π.parts.count j` (target parts
`(j + 1) ::ₘ π.parts.erase j`). The value is the transition probability from `π` to `π'`. -/
def hoppeStep (θ : ℝ) {k : ℕ} (π : k.Partition) (π' : (k + 1).Partition) : ℝ :=
  (if π'.parts = 1 ::ₘ π.parts then θ / (θ + k) else 0) +
    ∑ j ∈ π.parts.toFinset,
      if π'.parts = (j + 1) ::ₘ π.parts.erase j then
        (j * π.parts.count j : ℝ) / (θ + k) else 0

/-- The law of the allelic partition after `n` draws from Hoppe's urn, started from the empty
sample: `hoppeLaw θ (n + 1) π' = ∑ π, hoppeLaw θ n π * hoppeStep θ π π'`. -/
def hoppeLaw (θ : ℝ) : (n : ℕ) → n.Partition → ℝ
  | 0, _ => 1
  | n + 1, π' => ∑ π : n.Partition, hoppeLaw θ n π * hoppeStep θ π π'

/-- Hoppe-urn transition probabilities are nonnegative. -/
theorem hoppeStep_nonneg {θ : ℝ} (hθ : 0 < θ) {k : ℕ} (π : k.Partition)
    (π' : (k + 1).Partition) : 0 ≤ hoppeStep θ π π' := by
  unfold hoppeStep
  have hd : 0 ≤ θ + (k : ℝ) := by positivity
  apply add_nonneg
  · split_ifs <;> positivity
  · apply sum_nonneg
    intro j hj
    split_ifs <;> positivity

private def addSingleton {k : ℕ} (π : k.Partition) : (k + 1).Partition :=
  ⟨1 ::ₘ π.parts, by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact Nat.zero_lt_one
    · exact π.parts_pos hi,
    by simp [π.parts_sum, Nat.add_comm]⟩

private def growPart {k : ℕ} (π : k.Partition) (j : ℕ) (hj : j ∈ π.parts) :
    (k + 1).Partition :=
  ⟨(j + 1) ::ₘ π.parts.erase j, by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · omega
    · exact π.parts_pos (Multiset.mem_of_mem_erase hi), by
    have hs := congrArg Multiset.sum (Multiset.cons_erase hj)
    simp only [Multiset.sum_cons, π.parts_sum] at hs ⊢
    omega⟩

private theorem sum_parts_indicator {m : ℕ} (q : m.Partition) (c : ℝ) :
    (∑ p : m.Partition, if p.parts = q.parts then c else 0) = c := by
  simp only [← Nat.Partition.ext_iff]
  simp

private theorem sum_size_count {k : ℕ} (π : k.Partition) :
    (∑ j ∈ π.parts.toFinset, (j * π.parts.count j : ℝ)) = k := by
  have hs : (∑ j ∈ π.parts.toFinset, π.parts.count j * j) = k := by
    simpa [nsmul_eq_mul] using (Finset.sum_multiset_count π.parts).symm.trans π.parts_sum
  exact_mod_cast (by simpa only [Nat.mul_comm] using hs)

/-- The Hoppe-urn transition is stochastic: from every partition of `k` the probabilities of
the partitions of `k + 1` sum to one. -/
theorem sum_hoppeStep {θ : ℝ} (hθ : 0 < θ) {k : ℕ} (π : k.Partition) :
    ∑ π' : (k + 1).Partition, hoppeStep θ π π' = 1 := by
  classical
  unfold hoppeStep
  rw [sum_add_distrib]
  have hn : (∑ p : (k + 1).Partition,
      if p.parts = 1 ::ₘ π.parts then θ / (θ + k) else 0) = θ / (θ + k) :=
    sum_parts_indicator (addSingleton π) _
  rw [hn, sum_comm]
  have hg : ∀ j ∈ π.parts.toFinset,
      (∑ p : (k + 1).Partition,
        if p.parts = (j + 1) ::ₘ π.parts.erase j then
          (j * π.parts.count j : ℝ) / (θ + k) else 0) =
        (j * π.parts.count j : ℝ) / (θ + k) := by
    intro j hj
    exact sum_parts_indicator (growPart π j (Multiset.mem_toFinset.mp hj)) _
  rw [sum_congr rfl hg]
  rw [← sum_div, sum_size_count, ← add_div]
  exact div_self (by positivity)

private theorem hoppeWeight_split (θ : ℝ) (s : Multiset ℕ) (a : ℕ) :
    weight θ s = (θ / a) ^ s.count a / (s.count a).factorial *
      ∏ j ∈ s.toFinset.erase a, (θ / j) ^ s.count j / (s.count j).factorial := by
  classical
  by_cases ha : a ∈ s.toFinset
  · exact (Finset.mul_prod_erase _ _ ha).symm
  · have hc : s.count a = 0 := Multiset.count_eq_zero.mpr (by simpa using ha)
    simp [weight, hc, Finset.erase_eq_of_notMem ha]

private theorem hoppeWeight_cons_split (θ : ℝ) (s : Multiset ℕ) (a : ℕ) :
    weight θ (a ::ₘ s) = (θ / a) ^ (s.count a + 1) / (s.count a + 1).factorial *
      ∏ j ∈ s.toFinset.erase a, (θ / j) ^ s.count j / (s.count j).factorial := by
  classical
  rw [hoppeWeight_split θ (a ::ₘ s) a]
  simp only [Multiset.count_cons_self, Multiset.toFinset_cons, Finset.erase_insert_eq_erase]
  congr 1
  apply prod_congr rfl
  intro j hj
  simp [Multiset.count_cons_of_ne (Finset.mem_erase.mp hj).1]

private theorem hoppeWeight_cons (θ : ℝ) (s : Multiset ℕ) (a : ℕ) (ha : a ≠ 0) :
    weight θ (a ::ₘ s) * (a * (a ::ₘ s).count a : ℝ) = θ * weight θ s := by
  rw [hoppeWeight_cons_split, hoppeWeight_split θ s a]
  simp only [Multiset.count_cons_self, Nat.cast_add, Nat.cast_one, Nat.factorial_succ,
    Nat.cast_mul, pow_succ]
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hf : ((s.count a).factorial : ℝ) ≠ 0 := by positivity
  have hc : (s.count a : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private def removeSingleton {n : ℕ} (q : (n + 1).Partition) (hq : 1 ∈ q.parts) :
    n.Partition :=
  ⟨q.parts.erase 1, by
    intro i hi
    exact q.parts_pos (Multiset.mem_of_mem_erase hi), by
    have hs := congrArg Multiset.sum (Multiset.cons_erase hq)
    simp only [Multiset.sum_cons, q.parts_sum] at hs
    omega⟩

private def shrinkPart {n : ℕ} (q : (n + 1).Partition) (j : ℕ) (hj : 0 < j)
    (hq : j + 1 ∈ q.parts) : n.Partition :=
  ⟨j ::ₘ q.parts.erase (j + 1), by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact q.parts_pos (Multiset.mem_of_mem_erase hi), by
    have hs := congrArg Multiset.sum (Multiset.cons_erase hq)
    simp only [Multiset.sum_cons, q.parts_sum] at hs ⊢
    omega⟩

private theorem incoming_singleton (θ : ℝ) {n : ℕ} (q : (n + 1).Partition) :
    (∑ p : n.Partition,
      if q.parts = 1 ::ₘ p.parts then θ * weight θ p.parts else 0) =
      weight θ q.parts * (q.parts.count 1 : ℝ) := by
  classical
  by_cases hq : 1 ∈ q.parts
  · let p := removeSingleton q hq
    have hp : q.parts = 1 ::ₘ p.parts := (Multiset.cons_erase hq).symm
    have he : ∀ r : n.Partition, q.parts = 1 ::ₘ r.parts ↔ r = p := by
      intro r
      rw [hp, Multiset.cons_inj_right, ← Nat.Partition.ext_iff, eq_comm]
    simp_rw [he]
    simp only [sum_ite_eq', mem_univ, ite_true]
    rw [hp]
    symm
    simpa using hoppeWeight_cons θ p.parts 1 (by decide)
  · have hz : q.parts.count 1 = 0 := Multiset.count_eq_zero.mpr hq
    have he : ∀ p : n.Partition, q.parts ≠ 1 ::ₘ p.parts := by
      intro p hp
      exact hq (hp ▸ Multiset.mem_cons_self _ _)
    simp [he, hz]

private theorem growth_member {n : ℕ} (p : n.Partition) (q : (n + 1).Partition)
    (j : ℕ) (hj : 0 < j) (h : q.parts = (j + 1) ::ₘ p.parts.erase j) :
    j ∈ p.parts := by
  by_contra hm
  have hs := congrArg Multiset.sum h
  simp only [Multiset.erase_of_notMem hm, Multiset.sum_cons, p.parts_sum, q.parts_sum] at hs
  omega

private theorem incoming_growth (θ : ℝ) {n : ℕ} (q : (n + 1).Partition)
    (j : ℕ) (hj : 0 < j) :
    (∑ p : n.Partition,
      if q.parts = (j + 1) ::ₘ p.parts.erase j then
        weight θ p.parts * (j * p.parts.count j : ℝ) else 0) =
      weight θ q.parts * ((j + 1) * q.parts.count (j + 1) : ℝ) := by
  classical
  by_cases hq : j + 1 ∈ q.parts
  · let p := shrinkPart q j hj hq
    have hp : p.parts = j ::ₘ q.parts.erase (j + 1) := rfl
    have hq' : q.parts = (j + 1) ::ₘ q.parts.erase (j + 1) :=
      (Multiset.cons_erase hq).symm
    have he : ∀ r : n.Partition,
        q.parts = (j + 1) ::ₘ r.parts.erase j ↔ r = p := by
      intro r
      constructor
      · intro h
        have hm := growth_member r q j hj h
        have ht : q.parts.erase (j + 1) = r.parts.erase j := by
          rw [h, Multiset.erase_cons_head]
        apply Nat.Partition.ext
        rw [hp, ht, Multiset.cons_erase hm]
      · rintro rfl
        rw [hp, Multiset.erase_cons_head]
        exact hq'
    simp_rw [he]
    simp only [sum_ite_eq', mem_univ, ite_true]
    calc
      weight θ p.parts * (j * p.parts.count j : ℝ) =
          θ * weight θ (q.parts.erase (j + 1)) := by
        rw [hp]
        exact hoppeWeight_cons θ _ j (Nat.ne_of_gt hj)
      _ = weight θ q.parts * ((j + 1) * q.parts.count (j + 1) : ℝ) := by
        simpa only [← hq', Nat.cast_add, Nat.cast_one] using
          (hoppeWeight_cons θ (q.parts.erase (j + 1)) (j + 1) (by omega)).symm
  · have hz : q.parts.count (j + 1) = 0 := Multiset.count_eq_zero.mpr hq
    have he : ∀ p : n.Partition, q.parts ≠ (j + 1) ::ₘ p.parts.erase j := by
      intro p hp
      exact hq (hp ▸ Multiset.mem_cons_self _ _)
    simp [he, hz]

private theorem sum_size_count_range {n : ℕ} (p : n.Partition) :
    (∑ j ∈ range (n + 1), (j * p.parts.count j : ℝ)) = n := by
  have hb : p.parts.toFinset ⊆ range (n + 1) := by
    intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le
      (p.le_of_mem_parts (Multiset.mem_toFinset.mp hj)))
  rw [← sum_size_count p]
  symm
  apply sum_subset hb
  intro j _ hj
  have hc : p.parts.count j = 0 := Multiset.count_eq_zero.mpr (by simpa using hj)
  simp [hc]

private theorem weighted_step (θ : ℝ) {n : ℕ} (p : n.Partition)
    (q : (n + 1).Partition) :
    weight θ p.parts * hoppeStep θ p q =
      ((if q.parts = 1 ::ₘ p.parts then θ * weight θ p.parts else 0) +
        ∑ j ∈ range (n + 1),
          if q.parts = (j + 1) ::ₘ p.parts.erase j then
            weight θ p.parts * (j * p.parts.count j : ℝ) else 0) / (θ + n) := by
  classical
  have hb : p.parts.toFinset ⊆ range (n + 1) := by
    intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le
      (p.le_of_mem_parts (Multiset.mem_toFinset.mp hj)))
  have hs : (∑ j ∈ p.parts.toFinset,
      if q.parts = (j + 1) ::ₘ p.parts.erase j then
        weight θ p.parts * (j * p.parts.count j : ℝ) else 0) =
      ∑ j ∈ range (n + 1),
        if q.parts = (j + 1) ::ₘ p.parts.erase j then
          weight θ p.parts * (j * p.parts.count j : ℝ) else 0 := by
    apply sum_subset hb
    intro j _ hj
    have hc : p.parts.count j = 0 := Multiset.count_eq_zero.mpr (by simpa using hj)
    simp [hc]
  rw [← hs]
  simp only [hoppeStep, mul_add, mul_sum, add_div, sum_div]
  congr 1
  · split_ifs <;> ring
  · apply sum_congr rfl
    intro j _
    split_ifs <;> ring

private theorem hoppeWeight_recurrence (θ : ℝ) {n : ℕ} (q : (n + 1).Partition) :
    (∑ p : n.Partition, weight θ p.parts * hoppeStep θ p q) =
      weight θ q.parts * (n + 1) / (θ + n) := by
  classical
  simp_rw [weighted_step]
  rw [← sum_div, sum_add_distrib, incoming_singleton, sum_comm, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, ite_self, sum_const_zero, add_zero]
  simp only [Nat.cast_add, Nat.cast_one]
  have hg : ∀ j : ℕ,
      (∑ p : n.Partition,
        if q.parts = (j + 1 + 1) ::ₘ p.parts.erase (j + 1) then
          weight θ p.parts * ((j + 1) * p.parts.count (j + 1) : ℝ) else 0) =
        weight θ q.parts * ((j + 1 + 1) * q.parts.count (j + 1 + 1) : ℝ) := by
    intro j
    simpa only [Nat.cast_add, Nat.cast_one] using incoming_growth θ q (j + 1) (by omega)
  simp_rw [hg]
  rw [← mul_sum, ← mul_add]
  have hc := sum_size_count_range q
  rw [sum_range_succ', sum_range_succ'] at hc
  simp only [Nat.zero_add, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    zero_mul, one_mul, add_zero] at hc
  rw [add_comm] at hc
  rw [hc]

/-- **Hoppe's urn generates the Ewens sampling formula** (Hoppe 1984): after `n` draws, the
allelic partition has law `ewensProb θ`. -/
theorem hoppeLaw_eq_ewensProb {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : n.Partition) :
    hoppeLaw θ n π = ewensProb θ π := by
  induction n with
  | zero => simp [hoppeLaw, ewensProb]
  | succ n ih =>
    change (∑ p : n.Partition, hoppeLaw θ n p * hoppeStep θ p π) = ewensProb θ π
    simp_rw [ih]
    change (∑ p : n.Partition,
      ((n.factorial : ℝ) / (ascPochhammer ℝ n).eval θ * weight θ p.parts) *
        hoppeStep θ p π) =
      ((n + 1).factorial : ℝ) / (ascPochhammer ℝ (n + 1)).eval θ * weight θ π.parts
    simp_rw [mul_assoc]
    rw [← mul_sum, hoppeWeight_recurrence, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, ascPochhammer_succ_eval]
    have hp : (ascPochhammer ℝ n).eval θ ≠ 0 := (ascPochhammer_pos n θ hθ).ne'
    have hd : θ + (n : ℝ) ≠ 0 := by positivity
    field_simp

/-- The law of Hoppe's urn after `n` draws is nonnegative for `θ > 0`. -/
theorem hoppeLaw_nonneg {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : n.Partition) :
    0 ≤ hoppeLaw θ n π := by
  rw [hoppeLaw_eq_ewensProb hθ]
  exact ewensProb_nonneg hθ π

end MathlibExt.Biology.PopulationGenetics.Ewens
