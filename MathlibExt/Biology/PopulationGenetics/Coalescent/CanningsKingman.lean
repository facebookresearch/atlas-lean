/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings
public import MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
public import MathlibExt.Analysis.Normed.Algebra.ExponentialLimit
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype

/-!
# Cannings models: convergence of the genealogy to Kingman's coalescent

A **Cannings model** (Cannings 1974) with population size `N` is a neutral haploid model with
non-overlapping generations: in each generation the `N` parents have offspring numbers
`(ν_1, …, ν_N)`, `∑ ν_j = N`, with an exchangeable joint law, independently across
generations. One generation is the model `Cannings.CanningsModel` of `Cannings.lean`, shared with
the Λ-coalescent limit `CanningsLambda`: a `PMF` law on the random parent map `f : Fin N → Fin N`
(child `c` descends from parent `f c`, so `ν_j = offspring f j = #{c | f c = j}`), invariant
under relabeling the parents (exchangeable offspring numbers, `expect_offspring_comp_perm`) and
under relabeling the children (children are listed in uniformly random order, so any set of
distinct children may serve as the sample). Labeling the children of an exchangeable offspring
vector uniformly at random gives such a law. Expectations use the masses `(law f).toReal`
(`CanningsModel.expect`, from `Cannings.lean`).

**The Möhle–Sagitov conditions** (`MohleSagitov`). Let
`c_N = E[ν₁ (ν₁ - 1)] / (N - 1)` (`CanningsModel.pairCoalescence`), the probability that two
distinct children have the same parent (`CanningsModel.expect_pair`). Assume `c_N > 0`
eventually, `c_N → 0`, and `E[ν₁ (ν₁ - 1) (ν₁ - 2)] / (N² c_N) → 0` (triple mergers are
negligible on the time scale of pair mergers). The factorial moments are
`CanningsModel.factorialMoment`.

**The ancestral process.** For a sample of `n` genes, the ancestral partition of the sample is
a Markov chain on `SamplePartition n`: from a partition `ξ` with `b` blocks, the `b` ancestral
lineages sit at `b` distinct children of the current generation and two blocks merge iff their
lineages pick the same parent (`step`). Its one-generation transition matrix is
`ancestralMatrix (W N) n` (row-stochastic, `sum_ancestralMatrix`). As in `PartitionCoalescent`,
the processes are given by their transition matrices and no path space is built. The
finite-dimensional distribution of a chain started from the sample in singletons (`⊥`) at time
`0` is the probability of the first observed state, reached from `⊥`, times the transition
probabilities between consecutive observations (`chainFDD`, `kingmanFDD`).

**The theorem** (Möhle 2000; Möhle–Sagitov 2001). Under the Möhle–Sagitov conditions, with time
measured in units of `1 / c_N` generations, the ancestral process converges to Kingman's
coalescent in finite-dimensional distributions (`MohleSagitov.tendsto_chainFDD`): started from
singletons at generation `0` and observed at the generations `⌊t_i / c_N⌋`,
`0 ≤ t_0 ≤ ⋯ ≤ t_k`, its finite-dimensional distributions converge to those of Kingman's
`n`-coalescent (`PartitionCoalescent.partitionRate`), started from singletons, at the times `t_i`.

**Proof.** By exchangeability of the children, `(N)_m P(F of a sample of m distinct children)`
is the expected number of ordered `m`-samples with property `F`
(`CanningsModel.descFactorial_mul_expect`). Hence `m + 1` distinct children have a common
parent with probability `N E[(ν₁)_{m+1}] / (N)_{m+1}`, and two disjoint pairs both have
common parents with probability at most `E[X²] / (N)_4`, `X = ∑_j ν_j (ν_j - 1)`. The pointwise
bound `X ≤ a N + ∑_j (ν_j)_3 / a` (`a ≥ 1`) and `X ≤ N²` turn this into
`≤ c_N (2 √r N⁴ + N³) / (N)_4` with `r = E[(ν₁)_3] / (N² c_N)`, so under the Möhle–Sagitov
conditions simultaneous double mergers are negligible as well; this is derived, not assumed
(`MohleSagitov.tendsto_multiple`). Counting coalescing pairs of lineages (Bonferroni) gives,
from a partition with `b` blocks, the probability `c_N + O(triple + double)` of each of the
`b.choose 2` single mergers and `O(triple + double)` of every other change, so
`c_N⁻¹ (Π_N - 1) → Q` entrywise (`MohleSagitov.tendsto_generator`). A compound-interest limit
on the general time scale `c_N` (`NormedSpace.tendsto_one_add_smul_pow`) then gives
`Π_N ^ (⌊t / c_N⌋ - ⌊s / c_N⌋) → exp ((t - s) • Q)` (`MohleSagitov.tendsto_ancestralMatrix_pow`).
The finite-dimensional distributions are products of such matrix entries: the factor from
singletons at generation `0` to the first observation converges to `timeLaw n (t_0)`
(`MohleSagitov.tendsto_ancestralMatrix_pow_bot`), and each transition factor converges to an
entry of `exp ((t_{i+1} - t_i) • Q)`.

## Main results

* `CanningsModel.sum_offspring`: the offspring numbers add up to `N`.
  The expectation `CanningsModel.expect` and its lemmas, including the exchangeable offspring
  numbers `CanningsModel.expect_offspring_comp_perm`, are in `Cannings.lean`.
* `CanningsModel.expect_pair`, `CanningsModel.expect_triple`, `CanningsModel.expect_double_le`:
  coalescence probabilities in terms of offspring factorial moments.
* `MohleSagitov`: the Möhle–Sagitov conditions; `MohleSagitov.tendsto_multiple`: triple and
  simultaneous double mergers are negligible.
* `ancestralMatrix`, `sum_ancestralMatrix`: the ancestral partition chain of a sample.
* `MohleSagitov.tendsto_generator`: `c_N⁻¹ (Π_N - 1) → partitionRate n`.
* `MohleSagitov.tendsto_ancestralMatrix_pow`, `MohleSagitov.tendsto_ancestralMatrix_pow_bot`:
  transition matrices on the time scale `1 / c_N` converge to Kingman's; from singletons the
  time-`t` law converges to `timeLaw n t`.
* `MohleSagitov.tendsto_chainFDD`: **convergence of the finite-dimensional distributions to
  Kingman's coalescent.**

## References

* C. Cannings, "The latent roots of certain Markov chains arising in genetics: a new approach,
  I. Haploid models", Adv. Appl. Probab. 6 (1974) 260–290.
* J. F. C. Kingman, "The coalescent", Stochastic Process. Appl. 13 (1982) 235–248.
* M. Möhle, "Total variation distances and rates of convergence for ancestral coalescent
  processes in exchangeable population models", Adv. Appl. Probab. 32 (2000) 983–993.
* M. Möhle, S. Sagitov, "A classification of coalescent processes for haploid exchangeable
  population models", Ann. Probab. 29 (2001) 1547–1562.
-/

@[expose] public section

open Finset Filter Topology Matrix

/-! ### Expectations under a Cannings model

The model and its expectation `CanningsModel.expect` are in `Cannings.lean`. The results below
are stated in the namespace of the shared model, so that they apply by dot notation to every
`CanningsModel`. -/

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

/-- The offspring numbers add up to the population size. -/
theorem sum_offspring {N : ℕ} (f : Fin N → Fin N) : ∑ j, offspring f j = N := by
  simp only [offspring]
  rw [← card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) (fun _ _ => mem_univ _)]
  simp

variable {N : ℕ} (W : CanningsModel N)

/-- The `m`-th factorial moment `E[(ν)_m] = E[ν (ν - 1) ⋯ (ν - m + 1)]` of the offspring number
of a parent, averaged over the parents (by exchangeability every parent has the same law,
`factorialMoment_eq`). -/
noncomputable def factorialMoment (m : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, W.expect fun f => ((offspring f j).descFactorial m : ℝ)

/-- The **pair-coalescence probability** `c_N = E[ν₁ (ν₁ - 1)] / (N - 1)`: the probability that
two distinct children have the same parent (`expect_pair`). -/
noncomputable def pairCoalescence : ℝ := W.factorialMoment 2 / ((N : ℝ) - 1)

/-- Every parent has the same offspring factorial moments. -/
theorem factorialMoment_eq (m : ℕ) (j : Fin N) :
    W.factorialMoment m = W.expect fun f => ((offspring f j).descFactorial m : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by
    have := j.pos
    positivity
  have h : ∀ k : Fin N, (W.expect fun f => ((offspring f k).descFactorial m : ℝ)) =
      W.expect fun f => ((offspring f j).descFactorial m : ℝ) := by
    intro k
    have := W.expect_offspring_comp_perm (Equiv.swap j k)
      (fun ν => ((ν j).descFactorial m : ℝ))
    simpa using this
  rw [factorialMoment, sum_congr rfl fun k _ => h k]
  simp [hN]

theorem factorialMoment_nonneg (m : ℕ) : 0 ≤ W.factorialMoment m :=
  mul_nonneg (by positivity) (sum_nonneg fun _ _ => W.expect_nonneg fun _ => by positivity)

/-! ### Sampling distinct children -/

/-- There are `(#S)_m` injective maps `Fin m → S`. -/
theorem card_injective_mem {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (m : ℕ) :
    #{g : Fin m → α | Function.Injective g ∧ ∀ i, g i ∈ S} = (#S).descFactorial m := by
  rw [← Fintype.card_subtype]
  let e : {g : Fin m → α // Function.Injective g ∧ ∀ i, g i ∈ S} ≃ (Fin m ↪ S) :=
    { toFun := fun g => ⟨fun i => ⟨g.1 i, g.2.2 i⟩, fun i j h => g.2.1 (congrArg Subtype.val h)⟩
      invFun := fun e => ⟨fun i => (e i : α), fun i j h => e.injective (Subtype.ext h),
        fun i => (e i).2⟩
      left_inv := fun g => rfl
      right_inv := fun e => by ext; rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]

theorem card_injective (m : ℕ) :
    #{g : Fin m → Fin N | Function.Injective g} = N.descFactorial m := by
  simpa using card_injective_mem (univ : Finset (Fin N)) m

/-- **Averaging over samples.** For an injective `g : Fin m → Fin N` (a sample of `m` distinct
children), `(N)_m E[F (f ∘ g)] = E[∑_{g' injective} F (f ∘ g')]`: by exchangeability of the
children, every sample of `m` distinct children has the same law. -/
theorem descFactorial_mul_expect {m : ℕ} {g : Fin m → Fin N} (hg : Function.Injective g)
    (F : (Fin m → Fin N) → ℝ) :
    (N.descFactorial m : ℝ) * W.expect (fun f => F (f ∘ g)) =
      W.expect fun f => ∑ g' ∈ {g' : Fin m → Fin N | Function.Injective g'}, F (f ∘ g') := by
  rw [W.expect_sum, ← card_injective, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun g' hg' => ?_
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair g g' hg (mem_filter.1 hg').2
  have : (fun f : Fin N → Fin N => F (f ∘ g')) = fun f => (fun h => F (h ∘ g)) (f ∘ σ) := by
    funext f
    congr 1
    funext i
    simp [hσ]
  rw [this]
  exact (W.expect_comp_perm σ (fun h => F (h ∘ g))).symm

/-- The number of samples of `m + 1` distinct children with a common parent is
`∑_j (ν_j)_{m+1}`. -/
theorem sum_injective_allEq (f : Fin N → Fin N) (m : ℕ) :
    (∑ g ∈ {g : Fin (m + 1) → Fin N | Function.Injective g},
        if ∀ i, f (g i) = f (g 0) then (1 : ℝ) else 0) =
      ∑ j, ((offspring f j).descFactorial (m + 1) : ℝ) := by
  rw [sum_boole, filter_filter]
  norm_cast
  rw [card_eq_sum_card_fiberwise (f := fun g : Fin (m + 1) → Fin N => f (g 0)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [filter_filter, offspring, ← card_injective_mem]
  congr 1
  ext g
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hg, hall⟩, hj⟩
    exact ⟨hg, fun i => by rw [hall i, hj]⟩
  · rintro ⟨hg, hall⟩
    exact ⟨⟨hg, fun i => by rw [hall i, hall 0]⟩, hall 0⟩

/-- **Coalescence probabilities from factorial moments.** For a sample `g` of `m + 1` distinct
children, `P(all have the same parent) · (N)_{m+1} = N E[(ν₁)_{m+1}]`. -/
theorem descFactorial_mul_expect_allEq {m : ℕ} {g : Fin (m + 1) → Fin N}
    (hg : Function.Injective g) :
    (N.descFactorial (m + 1) : ℝ) *
        W.expect (fun f => if ∀ i, f (g i) = f (g 0) then 1 else 0) =
      N * W.factorialMoment (m + 1) := by
  have hN : (N : ℝ) ≠ 0 := by
    have := (g 0).pos
    positivity
  have := W.descFactorial_mul_expect hg (fun h => if ∀ i, h i = h 0 then (1 : ℝ) else 0)
  simp only [Function.comp_apply] at this
  rw [this]
  simp_rw [sum_injective_allEq]
  rw [W.expect_sum, factorialMoment, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

theorem descFactorial_pos_of_injective {m : ℕ} {g : Fin m → Fin N}
    (hg : Function.Injective g) : (0 : ℝ) < N.descFactorial m := by
  have := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at this
  exact_mod_cast Nat.descFactorial_pos.2 this

/-- **The pair-coalescence probability.** Two distinct children `a ≠ b` have the same parent
with probability `c_N = E[(ν₁)_2] / (N - 1)`. -/
theorem expect_pair {a b : Fin N} (hab : a ≠ b) :
    W.expect (fun f => if f a = f b then 1 else 0) = W.pairCoalescence := by
  have hg : Function.Injective ![a, b] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have h : (N.descFactorial 2 : ℝ) * W.expect (fun f => if f a = f b then 1 else 0) =
      N * W.factorialMoment 2 := by
    have h0 := W.descFactorial_mul_expect_allEq (m := 1) hg
    convert h0 using 3
    funext f
    by_cases hf : f a = f b <;> simp [Fin.forall_fin_two, hf, eq_comm]
  have hN1 : (1 : ℝ) < N := by
    have := Fintype.card_le_of_injective _ hg
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  rw [pairCoalescence, eq_div_iff (by linarith)]
  have hd : (N.descFactorial 2 : ℝ) = N * (N - 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, Nat.cast_mul,
      Nat.cast_sub (by exact_mod_cast hN1.le)]
    push_cast
    ring
  rw [hd] at h
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hN0
  linear_combination h

/-- The pair-coalescence probability `c_N` is the shared model's coalescence probability
`coalProb` (two sampled lineages have the same parent), so the time scale of this file is the one
of `CanningsLambda`. -/
theorem coalProb_eq_pairCoalescence (hN : 2 ≤ N) : W.coalProb = W.pairCoalescence := by
  rw [← W.expect_pair (a := Fin.castLE hN 0) (b := Fin.castLE hN 1)
    (fun h => by simpa using congrArg Fin.val h), coalProb, mergeProb, sampleProb_of_le _ _ hN]
  refine sum_congr rfl fun f _ => ?_
  congr 1
  refine if_congr ⟨fun h => h 0 1, fun h i j => ?_⟩ rfl rfl
  fin_cases i <;> fin_cases j <;> simp [h]

/-! ### Triple and simultaneous coalescences -/

/-- The number of ordered pairs of distinct children with a common parent,
`∑_j ν_j (ν_j - 1)`. -/
noncomputable def pairCount (f : Fin N → Fin N) : ℝ :=
  ∑ j, ((offspring f j).descFactorial 2 : ℝ)

/-- The number of ordered triples of distinct children with a common parent,
`∑_j ν_j (ν_j - 1) (ν_j - 2)`. -/
noncomputable def tripleCount (f : Fin N → Fin N) : ℝ :=
  ∑ j, ((offspring f j).descFactorial 3 : ℝ)

/-- The probability `N E[(ν₁)_3] / (N)_3` that three distinct children have a common parent
(`expect_triple`). -/
noncomputable def tripleCoalescence : ℝ :=
  N * W.factorialMoment 3 / (N.descFactorial 3 : ℝ)

/-- An upper bound `E[pairCount²] / (N)_4` for the probability that two disjoint pairs of
children each have a common parent (`expect_double_le`). -/
noncomputable def doubleBound : ℝ :=
  W.expect (fun f => pairCount f ^ 2) / (N.descFactorial 4 : ℝ)

theorem natCast_mul_factorialMoment (m : ℕ) :
    N * W.factorialMoment m = W.expect fun f => ∑ j, ((offspring f j).descFactorial m : ℝ) := by
  rw [W.expect_sum, factorialMoment]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- Three distinct children have a common parent with probability `N E[(ν₁)_3] / (N)_3`. -/
theorem expect_triple {g : Fin 3 → Fin N} (hg : Function.Injective g) :
    W.expect (fun f => if ∀ i, f (g i) = f (g 0) then 1 else 0) = W.tripleCoalescence := by
  have h := W.descFactorial_mul_expect_allEq (m := 2) hg
  have hpos := descFactorial_pos_of_injective hg
  rw [tripleCoalescence, eq_div_iff hpos.ne', mul_comm]
  exact h

theorem pairCount_eq_sum (f : Fin N → Fin N) :
    pairCount f = ∑ g ∈ {g : Fin 2 → Fin N | Function.Injective g},
        if ∀ i, f (g i) = f (g 0) then (1 : ℝ) else 0 :=
  (sum_injective_allEq f 1).symm

theorem pairCount_nonneg (f : Fin N → Fin N) : 0 ≤ pairCount f :=
  sum_nonneg fun _ _ => by positivity

theorem tripleCount_nonneg (f : Fin N → Fin N) : 0 ≤ tripleCount f :=
  sum_nonneg fun _ _ => by positivity

theorem pairCount_le (f : Fin N → Fin N) : pairCount f ≤ (N : ℝ) ^ 2 := by
  rw [pairCount_eq_sum]
  calc _ ≤ ∑ _g ∈ {g : Fin 2 → Fin N | Function.Injective g}, (1 : ℝ) :=
        sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = (N.descFactorial 2 : ℝ) := by rw [sum_const, card_injective]; simp
    _ ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.descFactorial_le_pow N 2

/-- `(ν)_2 ≤ a ν + (ν)_3 / a` for `a ≥ 1`. -/
theorem descFactorial_two_le (ν : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (ν.descFactorial 2 : ℝ) ≤ a * ν + (ν.descFactorial 3 : ℝ) / a := by
  have ha0 : 0 < a := by linarith
  have h2 : (ν.descFactorial 2 : ℝ) = ν * (ν - 1) := by
    rcases ν with _ | _ | k <;> simp [Nat.descFactorial_succ]; ring
  have h3 : (ν.descFactorial 3 : ℝ) = ν * (ν - 1) * (ν - 2) := by
    rcases ν with _ | _ | _ | k <;> simp [Nat.descFactorial_succ]; ring
  rw [h2, h3]
  have hν : (0 : ℝ) ≤ ν := by positivity
  have hin : 0 ≤ ((ν : ℝ) - 1) * (ν - 2) + a * a - a * (ν - 1) := by
    nlinarith [sq_nonneg (2 * ((ν : ℝ) - 1) - (1 + a)), mul_nonneg (by linarith : (0:ℝ) ≤ a - 1)
      (by linarith : (0:ℝ) ≤ 3 * a + 1)]
  have key : a * ν + ν * (ν - 1) * (ν - 2) / a - ν * (ν - 1) =
      (ν * (((ν : ℝ) - 1) * (ν - 2) + a * a - a * (ν - 1))) / a := by
    field_simp
    ring
  rw [← sub_nonneg, key]
  exact div_nonneg (mul_nonneg hν hin) ha0.le

/-- Pointwise: `pairCount ≤ a N + tripleCount / a` for `a ≥ 1`. -/
theorem pairCount_le_add (f : Fin N → Fin N) {a : ℝ} (ha : 1 ≤ a) :
    pairCount f ≤ a * N + tripleCount f / a := by
  have hsum : ((∑ j, offspring f j : ℕ) : ℝ) = N := by rw [sum_offspring]
  calc pairCount f ≤ ∑ j, (a * (offspring f j : ℝ) + ((offspring f j).descFactorial 3 : ℝ) / a) :=
        sum_le_sum fun j _ => descFactorial_two_le _ ha
    _ = a * N + tripleCount f / a := by
        rw [sum_add_distrib, ← mul_sum, ← sum_div, tripleCount]
        push_cast at hsum
        rw [hsum]

/-- Pointwise: `pairCount² ≤ a N pairCount + N² tripleCount / a` for `a ≥ 1`. -/
theorem pairCount_sq_le (f : Fin N → Fin N) {a : ℝ} (ha : 1 ≤ a) :
    pairCount f ^ 2 ≤ a * N * pairCount f + (N : ℝ) ^ 2 * tripleCount f / a := by
  have ha0 : 0 < a := by linarith
  have hX := pairCount_nonneg f
  have hT := tripleCount_nonneg f
  have h1 := pairCount_le_add f ha
  have h2 := pairCount_le f
  calc pairCount f ^ 2 = pairCount f * pairCount f := sq _
    _ ≤ pairCount f * (a * N + tripleCount f / a) := mul_le_mul_of_nonneg_left h1 hX
    _ = a * N * pairCount f + pairCount f * (tripleCount f / a) := by ring
    _ ≤ a * N * pairCount f + (N : ℝ) ^ 2 * (tripleCount f / a) := by
        gcongr
    _ = _ := by ring

/-- Pointwise: the number of samples of four distinct children forming two pairs with common
parents is at most `pairCount²`. -/
theorem sum_injective_double_le (f : Fin N → Fin N) :
    (∑ g ∈ {g : Fin 4 → Fin N | Function.Injective g},
        if f (g 0) = f (g 1) ∧ f (g 2) = f (g 3) then (1 : ℝ) else 0) ≤ pairCount f ^ 2 := by
  rw [pairCount_eq_sum, sum_boole, sum_boole, filter_filter, sq]
  norm_cast
  rw [← card_product]
  refine card_le_card_of_injOn (fun g => (![g 0, g 1], ![g 2, g 3])) ?_ ?_
  · intro g hg
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hg
    obtain ⟨hinj, h01, h23⟩ := hg
    simp only [mem_coe, mem_product, mem_filter, mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [hinj.eq_iff]
    · intro i
      fin_cases i <;> simp [h01]
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [hinj.eq_iff]
    · intro i
      fin_cases i <;> simp [h23]
  · intro g _ g' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    funext i
    fin_cases i
    · exact congrFun h1 0
    · exact congrFun h1 1
    · exact congrFun h2 0
    · exact congrFun h2 1

/-- Two disjoint pairs of distinct children both have common parents with probability at most
`E[pairCount²] / (N)_4`. -/
theorem expect_double_le {g : Fin 4 → Fin N} (hg : Function.Injective g) :
    W.expect (fun f => if f (g 0) = f (g 1) ∧ f (g 2) = f (g 3) then 1 else 0) ≤
      W.doubleBound := by
  have hpos := descFactorial_pos_of_injective hg
  rw [doubleBound, le_div_iff₀ hpos, mul_comm]
  have h := W.descFactorial_mul_expect hg
    (fun h => if h 0 = h 1 ∧ h 2 = h 3 then (1 : ℝ) else 0)
  simp only [Function.comp_apply] at h
  rw [h]
  exact W.expect_mono fun f => sum_injective_double_le f

/-- `doubleBound ≤ c_N (2 √r N⁴ + N³) / (N)_4` where `r = E[(ν₁)_3] / (N² c_N)`. -/
theorem doubleBound_le (hN : 4 ≤ N) (hc : 0 < W.pairCoalescence) :
    W.doubleBound ≤ W.pairCoalescence *
      (2 * √(W.factorialMoment 3 / ((N : ℝ) ^ 2 * W.pairCoalescence)) * (N : ℝ) ^ 4 +
        (N : ℝ) ^ 3) / (N.descFactorial 4 : ℝ) := by
  set c := W.pairCoalescence with hc_def
  set r := W.factorialMoment 3 / ((N : ℝ) ^ 2 * c) with hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hr0 : 0 ≤ r := div_nonneg (W.factorialMoment_nonneg 3) (by positivity)
  have hs0 : 0 ≤ √r := Real.sqrt_nonneg r
  set a := N * √r + 1 with ha
  have ha1 : 1 ≤ a := by nlinarith
  have ha0 : 0 < a := by linarith
  have hD : (0 : ℝ) < N.descFactorial 4 := by exact_mod_cast Nat.descFactorial_pos.2 hN
  rw [doubleBound, div_le_div_iff_of_pos_right hD]
  -- moments in terms of `c` and `r`
  have hμ2 : W.factorialMoment 2 = c * (N - 1) := by
    rw [hc_def, pairCoalescence, div_mul_cancel₀ _ (by linarith)]
  have hμ3 : W.factorialMoment 3 = r * N ^ 2 * c := by
    rw [hr, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (by positivity)]
    ring
  have hEX : W.expect pairCount = N * (c * (N - 1)) := by
    rw [← hμ2, natCast_mul_factorialMoment]
    rfl
  have hET : W.expect tripleCount = N * (r * N ^ 2 * c) := by
    rw [← hμ3, natCast_mul_factorialMoment]
    rfl
  have hmain : W.expect (fun f => pairCount f ^ 2) ≤
      a * N * W.expect pairCount + ((N : ℝ) ^ 2 / a) * W.expect tripleCount := by
    calc _ ≤ W.expect (fun f => a * N * pairCount f + ((N : ℝ) ^ 2 / a) * tripleCount f) :=
          W.expect_mono fun f => (pairCount_sq_le f ha1).trans_eq (by ring)
      _ = _ := by rw [W.expect_add, W.expect_const_mul, W.expect_const_mul]
  have hra : r / a ≤ √r / N := by
    rw [div_le_div_iff₀ ha0 hN0]
    have : √r * √r = r := Real.mul_self_sqrt hr0
    nlinarith
  calc W.expect (fun f => pairCount f ^ 2)
      ≤ a * N * (N * (c * (N - 1))) + ((N : ℝ) ^ 2 / a) * (N * (r * N ^ 2 * c)) := by
        rw [← hEX, ← hET]; exact hmain
    _ = c * (a * N ^ 2 * (N - 1) + N ^ 5 * (r / a)) := by ring
    _ ≤ c * (a * N ^ 2 * N + N ^ 5 * (√r / N)) := by
        gcongr
        · linarith
    _ = c * (2 * √r * N ^ 4 + N ^ 3) := by
        rw [ha]
        field_simp
        ring

theorem tripleCoalescence_nonneg : 0 ≤ W.tripleCoalescence :=
  div_nonneg (mul_nonneg (by positivity) (W.factorialMoment_nonneg 3)) (by positivity)

theorem doubleBound_nonneg : 0 ≤ W.doubleBound :=
  div_nonneg (W.expect_nonneg fun _ => sq_nonneg _) (by positivity)

end MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman

open Cannings

/-! ### The Möhle–Sagitov conditions -/

/-- **The Möhle–Sagitov conditions** for a sequence of Cannings models `W N` (population size
`N`) to have Kingman's coalescent as genealogical limit (Möhle 2000; Möhle–Sagitov 2001):
the pair-coalescence probability `c_N = E[ν₁ (ν₁ - 1)] / (N - 1)` is positive and tends to `0`
(so `⌊t / c_N⌋` generations is a nondegenerate time scale), and triple mergers are negligible
on that time scale, `E[ν₁ (ν₁ - 1) (ν₁ - 2)] / (N² c_N) → 0`. -/
structure MohleSagitov (W : ∀ N, CanningsModel N) : Prop where
  pairCoalescence_pos : ∀ᶠ N in atTop, 0 < (W N).pairCoalescence
  tendsto_pairCoalescence : Tendsto (fun N => (W N).pairCoalescence) atTop (𝓝 0)
  tendsto_triple : Tendsto
    (fun N => (W N).factorialMoment 3 / ((N : ℝ) ^ 2 * (W N).pairCoalescence)) atTop (𝓝 0)

/-- `N ^ k / (N)_k → 1`. -/
theorem tendsto_pow_div_descFactorial (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k / N.descFactorial k) atTop (𝓝 1) := by
  have h := (tendsto_noCoalProb_one k).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [noCoalProb_eq_descFactorial_div hN, inv_div]

/-- Under the Möhle–Sagitov conditions, triple mergers and simultaneous double mergers are
negligible on the coalescent time scale: `(P(triple) + doubleBound) / c_N → 0`. The bound on
simultaneous mergers is derived from the triple-merger condition. -/
theorem MohleSagitov.tendsto_multiple {W : ∀ N, CanningsModel N} (hW : MohleSagitov W) :
    Tendsto (fun N => ((W N).tripleCoalescence + (W N).doubleBound) / (W N).pairCoalescence)
      atTop (𝓝 0) := by
  set r := fun N : ℕ => (W N).factorialMoment 3 / ((N : ℝ) ^ 2 * (W N).pairCoalescence) with hr
  have hr0 : Tendsto r atTop (𝓝 0) := hW.tendsto_triple
  have hsq : Tendsto (fun N => √(r N)) atTop (𝓝 0) := by
    simpa using hr0.sqrt
  have h3 := tendsto_pow_div_descFactorial 3
  have h4 := tendsto_pow_div_descFactorial 4
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => r N * ((N : ℝ) ^ 3 / N.descFactorial 3) +
      (2 * √(r N) * ((N : ℝ) ^ 4 / N.descFactorial 4) +
        (N : ℝ) ^ 4 / N.descFactorial 4 * (N : ℝ)⁻¹)) atTop
      (𝓝 (0 * 1 + (2 * 0 * 1 + 1 * 0))) :=
    (hr0.mul h3).add (((hsq.const_mul 2).mul h4).add (h4.mul hinv))
  simp only [mul_zero, add_zero, mul_one] at hbound
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [hW.pairCoalescence_pos] with N hc
    exact div_nonneg (add_nonneg (W N).tripleCoalescence_nonneg (W N).doubleBound_nonneg) hc.le
  · filter_upwards [hW.pairCoalescence_pos, eventually_ge_atTop 4] with N hc hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hD3 : (0 : ℝ) < N.descFactorial 3 := by exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    have hD4 : (0 : ℝ) < N.descFactorial 4 := by exact_mod_cast Nat.descFactorial_pos.2 hN
    have hT : (W N).tripleCoalescence / (W N).pairCoalescence =
        r N * ((N : ℝ) ^ 3 / N.descFactorial 3) := by
      simp only [hr, CanningsModel.tripleCoalescence]
      field_simp
    have hDle := (W N).doubleBound_le hN hc
    have hD : (W N).doubleBound / (W N).pairCoalescence ≤
        2 * √(r N) * ((N : ℝ) ^ 4 / N.descFactorial 4) +
          (N : ℝ) ^ 4 / N.descFactorial 4 * (N : ℝ)⁻¹ := by
      rw [div_le_iff₀ hc]
      calc _ ≤ _ := hDle
        _ = _ := by
          simp only [hr]
          field_simp
    rw [add_div, hT]
    linarith

/-! ### Partitions: blocks, kernels -/

section Partitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The blocks of a partition of a finite type are the blocks of its points. -/
theorem parts_eq_image_part (P : Finpartition (univ : Finset α)) :
    P.parts = univ.image P.part := by
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    exact mem_image.2 ⟨i, mem_univ _, P.part_eq_of_mem hB hi⟩
  · intro hB
    obtain ⟨i, -, rfl⟩ := mem_image.1 hB
    exact P.part_mem.2 (mem_univ i)

/-- Two partitions of a finite type with the same "same block" relation are equal. -/
theorem eq_of_mem_part_iff {P Q : Finpartition (univ : Finset α)}
    (h : ∀ i j, j ∈ P.part i ↔ j ∈ Q.part i) : P = Q := by
  have hpart : P.part = Q.part := by
    funext i
    ext j
    exact h i j
  exact Finpartition.ext (by rw [parts_eq_image_part P, parts_eq_image_part Q, hpart])

/-- A partition whose blocks are the level sets of `u` has `#(range u)` blocks. -/
theorem card_parts_eq_card_image {β : Type*} [DecidableEq β] (P : Finpartition (univ : Finset α))
    (u : α → β) (h : ∀ i j, j ∈ P.part i ↔ u i = u j) :
    #P.parts = #(univ.image u) := by
  have hpart : P.part = fun i => univ.filter fun j => u i = u j := by
    funext i
    ext j
    simp [h]
  rw [parts_eq_image_part, hpart]
  change #(univ.image ((fun y => univ.filter fun j => y = u j) ∘ u)) = _
  rw [← image_image]
  refine card_image_of_injOn fun y hy y' _ hyy => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
  have : i ∈ univ.filter fun j => u i = u j := by simp
  rw [hyy] at this
  simpa [eq_comm] using this

end Partitions

/-! ### Pairs of lineages -/

/-- The ordered pairs `k < l` of lineage labels. -/
def lineagePairs (b : ℕ) : Finset (Fin b × Fin b) := univ.filter fun p => p.1 < p.2

theorem card_lineagePairs (b : ℕ) : #(lineagePairs b) = b.choose 2 := by
  have hsplit : (univ : Finset (Fin b)).offDiag =
      lineagePairs b ∪ (lineagePairs b).image Prod.swap := by
    ext ⟨k, l⟩
    simp only [mem_offDiag, mem_univ, true_and, mem_union, lineagePairs, mem_filter, mem_image,
      Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨l, k, h, rfl, rfl⟩
    · rintro (h | ⟨a, b', h, rfl, rfl⟩)
      · exact h.ne
      · exact h.ne'
  have hdisj : Disjoint (lineagePairs b) ((lineagePairs b).image Prod.swap) := by
    rw [disjoint_left]
    rintro ⟨k, l⟩ hp hp'
    simp only [lineagePairs, mem_filter, mem_univ, true_and, mem_image, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hp hp'
    obtain ⟨a, b', h, rfl, rfl⟩ := hp'
    exact lt_asymm h hp
  have hcard := congrArg card hsplit
  rw [offDiag_card, card_union_of_disjoint hdisj, card_image_of_injective _ Prod.swap_injective,
    card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right]
  have : b * (b - 1) = b * b - b := Nat.mul_sub_one b b
  omega

/-- The number of pairs of lineages `k < l` that pick the same parent under `φ`. -/
def collCount {b N : ℕ} (φ : Fin b → Fin N) : ℕ := #{p ∈ lineagePairs b | φ p.1 = φ p.2}

theorem injective_of_collCount_eq_zero {b N : ℕ} {φ : Fin b → Fin N} (h : collCount φ = 0) :
    Function.Injective φ := by
  have hmem : ∀ k l, k < l → φ k ≠ φ l := by
    intro k l hkl hφ
    have : (k, l) ∈ (lineagePairs b).filter fun p => φ p.1 = φ p.2 := by
      simp [lineagePairs, hkl, hφ]
    rw [collCount, card_eq_zero] at h
    simp [h] at this
  intro k l hkl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hmem k l hlt hkl
  · exact hmem l k hlt hkl.symm

theorem card_image_add_one_of_collCount_eq_one {b N : ℕ} {φ : Fin b → Fin N}
    (h : collCount φ = 1) : #(univ.image φ) + 1 = b := by
  rw [collCount, card_eq_one] at h
  obtain ⟨⟨k, l⟩, hp⟩ := h
  have hkl : (k, l) ∈ (lineagePairs b).filter fun p => φ p.1 = φ p.2 := by
    rw [hp]
    exact mem_singleton_self _
  simp only [lineagePairs, mem_filter, mem_univ, true_and] at hkl
  have huniq : ∀ x y, x < y → φ x = φ y → x = k ∧ y = l := by
    intro x y hxy hφ
    have : (x, y) ∈ (lineagePairs b).filter fun p => φ p.1 = φ p.2 := by
      simp [lineagePairs, hxy, hφ]
    rw [hp, mem_singleton, Prod.mk.injEq] at this
    exact this
  have himage : univ.image φ = (univ.erase l).image φ := by
    ext y
    simp only [mem_image, mem_univ, true_and, mem_erase, and_true]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x = l
      · exact ⟨k, hkl.1.ne, by rw [hx, hkl.2]⟩
      · exact ⟨x, hx, rfl⟩
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
  have hinj : Set.InjOn φ (univ.erase l : Finset (Fin b)) := by
    intro x hx y hy hxy
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact hy (huniq x y h' hxy).2
    · exact hx (huniq y x h' hxy.symm).2
  rw [himage, card_image_of_injOn hinj, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]
  have := l.pos
  omega

/-! ### The ancestral process of a sample -/

open PartitionCoalescent

variable {n N : ℕ}

/-- The label in `Fin #ξ.parts` of the block of `ξ` that contains gene `i`. -/
noncomputable def blockIndex (ξ : SamplePartition n) (i : Fin n) : Fin #ξ.parts :=
  ξ.parts.equivFin ⟨ξ.part i, ξ.part_mem.2 (mem_univ i)⟩

theorem blockIndex_eq_iff (ξ : SamplePartition n) (i j : Fin n) :
    blockIndex ξ i = blockIndex ξ j ↔ j ∈ ξ.part i := by
  rw [blockIndex, blockIndex, Equiv.apply_eq_iff_eq, Subtype.mk.injEq, eq_comm,
    ξ.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)]

theorem blockIndex_surjective (ξ : SamplePartition n) : Function.Surjective (blockIndex ξ) := by
  intro k
  obtain ⟨i, hi⟩ := ξ.nonempty_of_mem_parts (ξ.parts.equivFin.symm k).2
  refine ⟨i, ?_⟩
  rw [blockIndex, ← Equiv.eq_symm_apply]
  exact Subtype.ext (ξ.part_eq_of_mem (ξ.parts.equivFin.symm k).2 hi)

open scoped Classical in
/-- **One generation of the ancestral process.** The `b = #ξ.parts` ancestral lineages of the
sample, one per block of `ξ`, sit at the distinct children `0, …, b - 1` (any `b` distinct
children have the same joint law, `CanningsModel.descFactorial_mul_expect`); under the parent
map `f`, two blocks merge iff their lineages pick the same parent. -/
noncomputable def step (ξ : SamplePartition n) (h : #ξ.parts ≤ N) (f : Fin N → Fin N) :
    SamplePartition n :=
  Finpartition.ofSetoid (Setoid.ker fun i => f (Fin.castLE h (blockIndex ξ i)))

section Step

variable {ξ : SamplePartition n} {h : #ξ.parts ≤ N} {f : Fin N → Fin N}

theorem mem_part_step {i j : Fin n} :
    j ∈ (step ξ h f).part i ↔
      f (Fin.castLE h (blockIndex ξ i)) = f (Fin.castLE h (blockIndex ξ j)) := by
  classical
  rw [step]
  convert Finpartition.mem_part_ofSetoid_iff_rel using 1

theorem step_eq_self_of_injective (hφ : Function.Injective (f ∘ Fin.castLE h)) :
    step ξ h f = ξ :=
  eq_of_mem_part_iff fun i j => by
    rw [mem_part_step, ← blockIndex_eq_iff]
    exact hφ.eq_iff

theorem le_step : ξ ≤ step ξ h f := by
  intro B hB
  obtain ⟨i, hi⟩ := ξ.nonempty_of_mem_parts hB
  refine ⟨(step ξ h f).part i, (step ξ h f).part_mem.2 (mem_univ i), fun j hj => ?_⟩
  rw [mem_part_step]
  have : blockIndex ξ i = blockIndex ξ j :=
    (blockIndex_eq_iff ξ i j).2 (by rwa [ξ.part_eq_of_mem hB hi])
  rw [this]

theorem card_parts_step : #(step ξ h f).parts = #(univ.image (f ∘ Fin.castLE h)) := by
  rw [card_parts_eq_card_image (step ξ h f) (fun i => f (Fin.castLE h (blockIndex ξ i)))
    (fun i j => mem_part_step)]
  change #(univ.image ((f ∘ Fin.castLE h) ∘ blockIndex ξ)) = _
  rw [← image_image, image_univ_of_surjective (blockIndex_surjective ξ)]

theorem isMerge_step (hc : collCount (f ∘ Fin.castLE h) = 1) : IsMerge ξ (step ξ h f) :=
  ⟨le_step, by rw [card_parts_step]; exact card_image_add_one_of_collCount_eq_one hc⟩

theorem not_isMerge_self (ξ : SamplePartition n) : ¬IsMerge ξ ξ := fun hM => by
  have := hM.2
  omega

/-- The pair of lineages that must coalesce for one generation to produce a given merger. -/
theorem exists_pair_of_isMerge {η : SamplePartition n} (hM : IsMerge ξ η) {f₀ : Fin N → Fin N}
    (hf₀ : step ξ h f₀ = η) :
    ∃ k l : Fin #ξ.parts, k < l ∧
      ∀ f, step ξ h f = η → f (Fin.castLE h k) = f (Fin.castLE h l) := by
  have hni : ¬Function.Injective (f₀ ∘ Fin.castLE h) := fun hi => by
    have : η = ξ := hf₀.symm.trans (step_eq_self_of_injective hi)
    exact not_isMerge_self ξ (this ▸ hM)
  obtain ⟨k, l, hkl, hne⟩ := Function.not_injective_iff.1 hni
  have key : ∀ k l, (f₀ ∘ Fin.castLE h) k = (f₀ ∘ Fin.castLE h) l →
      ∀ f, step ξ h f = η → f (Fin.castLE h k) = f (Fin.castLE h l) := by
    intro k l hkl f hf
    obtain ⟨i, rfl⟩ := blockIndex_surjective ξ k
    obtain ⟨j, rfl⟩ := blockIndex_surjective ξ l
    have hj : j ∈ η.part i := by
      rw [← hf₀, mem_part_step]
      exact hkl
    rw [← hf, mem_part_step] at hj
    exact hj
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨k, l, hlt, key k l hkl⟩
  · exact ⟨l, k, hlt, key l k hkl.symm⟩

end Step

/-- The one-generation transition matrix of the ancestral process of a sample of `n` genes in
the Cannings model `W`, on the partitions of the sample: the probability that the blocks of `ξ`
merge into `η`. (When the sample has more blocks than the population, which does not occur for
`n ≤ N`, the matrix is set to the identity.) -/
noncomputable def ancestralMatrix (W : CanningsModel N) (n : ℕ) :
    Matrix (SamplePartition n) (SamplePartition n) ℝ :=
  Matrix.of fun ξ η =>
    if h : #ξ.parts ≤ N then W.expect (fun f => if step ξ h f = η then 1 else 0)
    else if ξ = η then 1 else 0

theorem ancestralMatrix_nonneg (W : CanningsModel N) (ξ η : SamplePartition n) :
    0 ≤ ancestralMatrix W n ξ η := by
  simp only [ancestralMatrix, Matrix.of_apply]
  split_ifs
  · exact W.expect_nonneg fun f => by split_ifs <;> norm_num
  · norm_num
  · norm_num

/-- The ancestral matrix is row-stochastic. -/
theorem sum_ancestralMatrix (W : CanningsModel N) (ξ : SamplePartition n) :
    ∑ η, ancestralMatrix W n ξ η = 1 := by
  simp only [ancestralMatrix, Matrix.of_apply]
  split_ifs with h
  · rw [← W.expect_sum]
    simp only [Finset.sum_ite_eq, mem_univ, ite_true]
    exact W.expect_const 1
  · simp

/-! ### One-generation transition probabilities -/

theorem collCount_cast {b : ℕ} (φ : Fin b → Fin N) :
    (collCount φ : ℝ) = ∑ p ∈ lineagePairs b, if φ p.1 = φ p.2 then (1 : ℝ) else 0 := by
  rw [collCount, sum_boole]

theorem sum_sum_ne {b : ℕ} (φ : Fin b → Fin N) :
    (∑ p ∈ lineagePairs b, ∑ q ∈ lineagePairs b,
        if p ≠ q then (if φ p.1 = φ p.2 then (1 : ℝ) else 0) * (if φ q.1 = φ q.2 then 1 else 0)
        else 0) = (collCount φ : ℝ) ^ 2 - collCount φ := by
  set S := lineagePairs b
  set a : Fin b × Fin b → ℝ := fun p => if φ p.1 = φ p.2 then 1 else 0 with ha_def
  have ha : ∀ p, a p * a p = a p := by
    intro p
    simp only [ha_def]
    split_ifs <;> norm_num
  have h1 : ∀ p ∈ S, (∑ q ∈ S, if p ≠ q then a p * a q else 0) = (∑ q ∈ S, a p * a q) - a p := by
    intro p hp
    have hsplit : ∀ q, (if p ≠ q then a p * a q else 0) =
        a p * a q - (if p = q then a p * a q else 0) := by
      intro q
      by_cases hpq : p = q <;> simp [hpq]
    rw [sum_congr rfl fun q _ => hsplit q, sum_sub_distrib, sum_ite_eq, ite_eq_left hp, ha]
  rw [sum_congr rfl h1, sum_sub_distrib, ← sum_mul_sum, collCount_cast, sq]

end MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

open CanningsKingman

variable {N : ℕ} (W : CanningsModel N)

/-- Three distinct children with a common parent: bound by `tripleCoalescence`. -/
theorem expect_le_triple {Q : (Fin N → Fin N) → Prop} [DecidablePred Q] {x y z : Fin N}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hQ : ∀ f, Q f → f x = f y ∧ f y = f z) :
    W.expect (fun f => if Q f then 1 else 0) ≤ W.tripleCoalescence := by
  have hyx := hxy.symm
  have hzy := hyz.symm
  have hzx := hxz.symm
  have hg : Function.Injective ![x, y, z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rw [← W.expect_triple hg]
  refine W.expect_mono fun f => ?_
  by_cases h1 : Q f
  · obtain ⟨e1, e2⟩ := hQ f h1
    have : ∀ i, f (![x, y, z] i) = f (![x, y, z] 0) := by
      intro i
      fin_cases i <;> simp [e1, e2]
    simp [h1, this]
  · simp only [h1, ite_false]
    split_ifs <;> norm_num

/-- Two disjoint pairs of distinct children with common parents: bound by `doubleBound`. -/
theorem expect_le_double {w x y z : Fin N} (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    W.expect (fun f => if f w = f x ∧ f y = f z then 1 else 0) ≤ W.doubleBound := by
  have := hwx.symm
  have := hwy.symm
  have := hwz.symm
  have := hxy.symm
  have := hxz.symm
  have := hyz.symm
  have hg : Function.Injective ![w, x, y, z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := W.expect_double_le hg
  convert h using 3 with f
  by_cases hf : f w = f x ∧ f y = f z
  · rw [ite_eq_left hf, ite_eq_left (by simpa using hf)]
  · rw [ite_eq_right hf, ite_eq_right (by simpa using hf)]

/-- Two distinct pairs of lineages both coalescing in one generation: probability at most
`tripleCoalescence + doubleBound`. -/
theorem expect_two_pairs_le {b : ℕ} {e : Fin b → Fin N} (he : Function.Injective e)
    {p q : Fin b × Fin b} (hp : p ∈ lineagePairs b) (hq : q ∈ lineagePairs b) (hpq : p ≠ q) :
    W.expect (fun f => if f (e p.1) = f (e p.2) ∧ f (e q.1) = f (e q.2) then 1 else 0) ≤
      W.tripleCoalescence + W.doubleBound := by
  obtain ⟨k, l⟩ := p
  obtain ⟨k', l'⟩ := q
  simp only [lineagePairs, mem_filter, mem_univ, true_and] at hp hq
  have ht := W.tripleCoalescence_nonneg
  have hd := W.doubleBound_nonneg
  have hne : ∀ {a a' : Fin b}, a ≠ a' → e a ≠ e a' := fun h h' => h (he h')
  by_cases h1 : k = k'
  · subst h1
    have hll : l ≠ l' := fun h' => hpq (by rw [h'])
    have := W.expect_le_triple (Q := fun f => f (e k) = f (e l) ∧ f (e k) = f (e l'))
      (hne hp.ne) (hne hll) (hne hq.ne) fun f ⟨e1, e2⟩ => ⟨e1, e1 ▸ e2⟩
    linarith
  by_cases h2 : k = l'
  · subst h2
    have := W.expect_le_triple (Q := fun f => f (e k) = f (e l) ∧ f (e k') = f (e k))
      (hne hq.ne) (hne hp.ne) (hne (hq.trans hp).ne) fun f ⟨e1, e2⟩ => ⟨e2, e1⟩
    linarith
  by_cases h3 : l = k'
  · subst h3
    have := W.expect_le_triple (Q := fun f => f (e k) = f (e l) ∧ f (e l) = f (e l'))
      (hne hp.ne) (hne hq.ne) (hne (hp.trans hq).ne) fun f ⟨e1, e2⟩ => ⟨e1, e2⟩
    linarith
  by_cases h4 : l = l'
  · subst h4
    have := W.expect_le_triple (Q := fun f => f (e k) = f (e l) ∧ f (e k') = f (e l))
      (hne h1) (hne hq.ne) (hne hp.ne) fun f ⟨e1, e2⟩ => ⟨e1.trans e2.symm, e2⟩
    linarith
  · have := W.expect_le_double (w := e k) (x := e l) (y := e k') (z := e l')
      (hne hp.ne) (hne h1) (hne h2) (hne h3) (hne h4) (hne hq.ne)
    linarith

/-- Expected number of coalescing pairs among `b` lineages: `(b.choose 2) c_N`. -/
theorem expect_collCount {b : ℕ} (h : b ≤ N) :
    W.expect (fun f => (collCount (f ∘ Fin.castLE h) : ℝ)) =
      #(lineagePairs b) * W.pairCoalescence := by
  simp_rw [collCount_cast]
  rw [W.expect_sum, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun p hp => ?_
  simp only [lineagePairs, mem_filter, mem_univ, true_and] at hp
  exact W.expect_pair fun h' => hp.ne (Fin.castLE_injective h h')

/-- `E[k² - k] ≤ #pairs (#pairs - 1) (P(triple) + doubleBound)`, `k` the number of coalescing
pairs. -/
theorem expect_collCount_sq_le {b : ℕ} (h : b ≤ N) :
    W.expect (fun f => (collCount (f ∘ Fin.castLE h) : ℝ) ^ 2 - collCount (f ∘ Fin.castLE h)) ≤
      #(lineagePairs b) * (#(lineagePairs b) - 1) *
        (W.tripleCoalescence + W.doubleBound) := by
  simp_rw [← sum_sum_ne]
  rw [W.expect_sum]
  simp_rw [W.expect_sum]
  set S := lineagePairs b
  set K := W.tripleCoalescence + W.doubleBound
  have hK : 0 ≤ K := add_nonneg W.tripleCoalescence_nonneg W.doubleBound_nonneg
  have hle : ∀ p ∈ S, ∀ q ∈ S, W.expect (fun f => if p ≠ q then
      (if (f ∘ Fin.castLE h) p.1 = (f ∘ Fin.castLE h) p.2 then (1 : ℝ) else 0) *
        (if (f ∘ Fin.castLE h) q.1 = (f ∘ Fin.castLE h) q.2 then 1 else 0) else 0) ≤
      if p ≠ q then K else 0 := by
    intro p hp q hq
    by_cases hpq : p = q
    · simp only [hpq, ne_eq, not_true_eq_false, ite_false]
      rw [W.expect_const]
    · simp only [hpq, ne_eq, not_false_eq_true, ite_true, ite_zero_mul_ite_zero, mul_one,
        Function.comp_apply]
      exact W.expect_two_pairs_le (Fin.castLE_injective h) hp hq hpq
  calc _ ≤ ∑ p ∈ S, ∑ q ∈ S, (if p ≠ q then K else 0) :=
        sum_le_sum fun p hp => sum_le_sum fun q hq => hle p hp q hq
    _ = ∑ p ∈ S, ((#S : ℝ) - 1) * K := by
        refine sum_congr rfl fun p hp => ?_
        rw [← sum_filter, sum_const, filter_ne, card_erase_of_mem hp, nsmul_eq_mul,
          Nat.cast_sub (card_pos.2 ⟨p, hp⟩)]
        simp
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman

open Cannings PartitionCoalescent

variable {n N : ℕ}

section Entries

variable (W : CanningsModel N) {ξ : SamplePartition n} (h : #ξ.parts ≤ N)

/-- The probability that one generation takes the partition `ξ` to `η`. -/
noncomputable def stepProb (η : SamplePartition n) : ℝ :=
  W.expect fun f => if step ξ h f = η then 1 else 0

theorem stepProb_nonneg (η : SamplePartition n) : 0 ≤ stepProb W h η :=
  W.expect_nonneg fun f => by split_ifs <;> norm_num

theorem sum_stepProb : ∑ η, stepProb W h η = 1 := by
  simp only [stepProb]
  rw [← W.expect_sum]
  simp only [Finset.sum_ite_eq, mem_univ, ite_true]
  exact W.expect_const 1

theorem one_sub_stepProb_self_le :
    1 - stepProb W h ξ ≤ #(lineagePairs #ξ.parts) * W.pairCoalescence := by
  have h1 : 1 - stepProb W h ξ = W.expect (fun f => 1 - if step ξ h f = ξ then (1 : ℝ) else 0) := by
    rw [W.expect_sub, W.expect_const, stepProb]
  rw [h1, ← W.expect_collCount h]
  refine W.expect_mono fun f => ?_
  by_cases hs : step ξ h f = ξ
  · simp [hs]
  · have hk : collCount (f ∘ Fin.castLE h) ≠ 0 := fun hk =>
      hs (step_eq_self_of_injective (injective_of_collCount_eq_zero hk))
    have : (1 : ℝ) ≤ collCount (f ∘ Fin.castLE h) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    simp [hs, this]

open scoped Classical in
theorem sum_stepProb_isMerge_ge :
    #(lineagePairs #ξ.parts) * W.pairCoalescence -
        #(lineagePairs #ξ.parts) * (#(lineagePairs #ξ.parts) - 1) *
          (W.tripleCoalescence + W.doubleBound) ≤
      ∑ η with IsMerge ξ η, stepProb W h η := by
  have h1 := W.expect_collCount h
  have h2 := W.expect_collCount_sq_le h
  have hpw : W.expect (fun f => (collCount (f ∘ Fin.castLE h) : ℝ) -
      ((collCount (f ∘ Fin.castLE h) : ℝ) ^ 2 - collCount (f ∘ Fin.castLE h))) ≤
      ∑ η with IsMerge ξ η, stepProb W h η := by
    simp only [stepProb]
    rw [← W.expect_sum]
    refine W.expect_mono fun f => ?_
    rw [Finset.sum_ite_eq]
    have hnn : (0 : ℝ) ≤ if step ξ h f ∈ univ.filter (IsMerge ξ) then 1 else 0 := by
      split_ifs <;> norm_num
    rcases Nat.lt_or_ge (collCount (f ∘ Fin.castLE h)) 2 with hk | hk
    · interval_cases hk' : collCount (f ∘ Fin.castLE h)
      · simpa using hnn
      · have hM := isMerge_step (ξ := ξ) (h := h) (f := f) hk'
        simp [hM]
    · have : (2 : ℝ) ≤ collCount (f ∘ Fin.castLE h) := by exact_mod_cast hk
      nlinarith
  rw [W.expect_sub, h1] at hpw
  linarith

/-- A one-generation merger of two given blocks has probability at most `c_N`. -/
theorem stepProb_le_of_isMerge (hc : 0 ≤ W.pairCoalescence) {η : SamplePartition n}
    (hM : IsMerge ξ η) : stepProb W h η ≤ W.pairCoalescence := by
  by_cases hex : ∃ f₀, step ξ h f₀ = η
  · obtain ⟨f₀, hf₀⟩ := hex
    obtain ⟨k, l, hkl, hkey⟩ := exists_pair_of_isMerge hM hf₀
    rw [← W.expect_pair (a := Fin.castLE h k) (b := Fin.castLE h l)
      fun h' => hkl.ne (Fin.castLE_injective h h')]
    refine W.expect_mono fun f => ?_
    by_cases hs : step ξ h f = η
    · simp [hs, hkey f hs]
    · simp only [hs, ite_false]
      split_ifs <;> norm_num
  · simp only [not_exists] at hex
    have : stepProb W h η = 0 := by
      simp only [stepProb, hex, ite_false]
      exact W.expect_const 0
    rw [this]
    exact hc

/-- Any other change of partition needs two coalescing pairs. -/
theorem stepProb_le_of_not_isMerge {η : SamplePartition n} (hM : ¬IsMerge ξ η) (hne : η ≠ ξ) :
    stepProb W h η ≤ #(lineagePairs #ξ.parts) * (#(lineagePairs #ξ.parts) - 1) *
      (W.tripleCoalescence + W.doubleBound) := by
  refine le_trans ?_ (W.expect_collCount_sq_le h)
  refine W.expect_mono fun f => ?_
  by_cases hs : step ξ h f = η
  · have hk0 : collCount (f ∘ Fin.castLE h) ≠ 0 := fun hk =>
      hne (hs.symm.trans (step_eq_self_of_injective (injective_of_collCount_eq_zero hk)))
    have hk1 : collCount (f ∘ Fin.castLE h) ≠ 1 := fun hk => hM (hs ▸ isMerge_step hk)
    have : (2 : ℝ) ≤ collCount (f ∘ Fin.castLE h) := by
      exact_mod_cast (by omega : 2 ≤ collCount (f ∘ Fin.castLE h))
    simp only [hs, ite_true]
    nlinarith
  · simp only [hs, ite_false]
    have : (0 : ℝ) ≤ collCount (f ∘ Fin.castLE h) := by positivity
    rcases Nat.eq_zero_or_pos (collCount (f ∘ Fin.castLE h)) with hk | hk
    · simp [hk]
    · have : (1 : ℝ) ≤ collCount (f ∘ Fin.castLE h) := by exact_mod_cast hk
      nlinarith

open scoped Classical in
theorem sum_stepProb_isMerge_le : ∑ η with IsMerge ξ η, stepProb W h η ≤ 1 - stepProb W h ξ := by
  rw [← sum_stepProb W h, ← add_sum_erase _ _ (mem_univ ξ), add_sub_cancel_left]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun η _ _ => stepProb_nonneg W h η
  intro η hη
  simp only [mem_filter, mem_univ, true_and] at hη
  exact mem_erase.2 ⟨fun he => not_isMerge_self ξ (he ▸ hη), mem_univ η⟩

open scoped Classical in
/-- A one-generation merger has probability at least `c_N - #pairs (#pairs - 1) (P(triple) +
doubleBound)`. -/
theorem stepProb_ge_of_isMerge (hc : 0 ≤ W.pairCoalescence) {η : SamplePartition n}
    (hM : IsMerge ξ η) :
    W.pairCoalescence - #(lineagePairs #ξ.parts) * (#(lineagePairs #ξ.parts) - 1) *
      (W.tripleCoalescence + W.doubleBound) ≤ stepProb W h η := by
  have hge := sum_stepProb_isMerge_ge W h
  have hmem : η ∈ univ.filter (IsMerge ξ) := by simp [hM]
  rw [← add_sum_erase _ _ hmem] at hge
  have hcard : #((univ.filter (IsMerge ξ)).erase η) = #(lineagePairs #ξ.parts) - 1 := by
    rw [card_erase_of_mem hmem, card_lineagePairs]
    congr 1
    exact card_isMerge ξ
  have hrest : ∑ x ∈ (univ.filter (IsMerge ξ)).erase η, stepProb W h x ≤
      ((#(lineagePairs #ξ.parts) : ℝ) - 1) * W.pairCoalescence := by
    calc _ ≤ ∑ x ∈ (univ.filter (IsMerge ξ)).erase η, W.pairCoalescence :=
          sum_le_sum fun x hx => stepProb_le_of_isMerge W h hc
            (by simpa using (mem_erase.1 hx).2)
      _ = _ := by
          rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_sub]
          · simp
          · rw [card_lineagePairs, ← card_isMerge ξ]
            exact card_pos.2 ⟨η, hmem⟩
  nlinarith

end Entries

/-! ### Kingman's limit -/

open scoped Classical in
/-- **The generator limit.** Under the Möhle–Sagitov conditions, the one-generation transition
matrix of the ancestral partition of a sample of `n` genes satisfies
`c_N⁻¹ (Π_N - 1) → Q`, the rate matrix of Kingman's `n`-coalescent: each pair of blocks merges at
rate `1`, and every other change of partition has rate `0`. -/
theorem MohleSagitov.tendsto_generator {W : ∀ N, CanningsModel N} (hW : MohleSagitov W)
    (n : ℕ) :
    Tendsto (fun N => (W N).pairCoalescence⁻¹ • (ancestralMatrix (W N) n - 1)) atTop
      (𝓝 (partitionRate n)) := by
  refine tendsto_pi_nhds.2 fun ξ => tendsto_pi_nhds.2 fun η => ?_
  set B : ℝ := ((#(lineagePairs #ξ.parts) : ℕ) : ℝ)
  set c := fun N => (W N).pairCoalescence
  set ε := fun N => B * (B - 1) * ((W N).tripleCoalescence + (W N).doubleBound) / c N
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := hW.tendsto_multiple.const_mul (B * (B - 1))
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    simp only [ε, c]
    ring
  have hev : ∀ᶠ N in atTop, n ≤ N ∧ 0 < c N :=
    (eventually_ge_atTop n).and hW.pairCoalescence_pos
  have hentry : ∀ N (hN : n ≤ N), ((W N).pairCoalescence⁻¹ • (ancestralMatrix (W N) n - 1)) ξ η =
      (c N)⁻¹ * (stepProb (W N) (ξ.card_parts_le_card.trans (by simpa using hN)) η -
        if ξ = η then 1 else 0) := by
    intro N hN
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul,
      ancestralMatrix, Matrix.of_apply, stepProb, c]
    rw [dite_eq_left]
  have hB : B = (((#ξ.parts).choose 2 : ℕ) : ℝ) := by simp only [B, card_lineagePairs]
  have hrate : partitionRate n ξ η =
      if IsMerge ξ η then 1 else if ξ = η then -B else 0 := by
    simp only [partitionRate, Matrix.of_apply, hB]
  rw [hrate]
  by_cases hM : IsMerge ξ η
  · have hne : ξ ≠ η := fun he => not_isMerge_self ξ (he ▸ hM)
    simp only [hM, ite_true]
    have hlow : Tendsto (fun N => 1 - ε N) atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ite_eq_right hne, sub_zero, ← div_eq_inv_mul, le_div_iff₀ hc]
      have := stepProb_ge_of_isMerge (W N) (ξ.card_parts_le_card.trans (by simpa using hN))
        hc.le hM
      simp only [ε]
      rw [sub_mul, div_mul_cancel₀ _ hc.ne', one_mul]
      exact this
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ite_eq_right hne, sub_zero, ← div_eq_inv_mul, div_le_one hc]
      exact stepProb_le_of_isMerge (W N) _ hc.le hM
  by_cases hξη : ξ = η
  · subst hξη
    simp only [hM, ite_false, ite_true]
    have hup : Tendsto (fun N => -B + ε N) atTop (𝓝 (-B)) := by
      simpa using tendsto_const_nhds.add hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ← div_eq_inv_mul, le_div_iff₀ hc]
      have := one_sub_stepProb_self_le (W N) (ξ.card_parts_le_card.trans (by simpa using hN))
      simp only [B, c, ite_true] at *
      linarith
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ← div_eq_inv_mul, div_le_iff₀ hc]
      have h1 := sum_stepProb_isMerge_ge (W N) (ξ.card_parts_le_card.trans (by simpa using hN))
      have h2 := sum_stepProb_isMerge_le (W N) (ξ.card_parts_le_card.trans (by simpa using hN))
      simp only [ε, B, c, ite_true] at *
      rw [add_mul, div_mul_cancel₀ _ hc.ne']
      linarith
  · simp only [hM, hξη, ite_false]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hε ?_ ?_
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ite_eq_right hξη, sub_zero]
      exact mul_nonneg (inv_nonneg.2 hc.le) (stepProb_nonneg _ _ _)
    · filter_upwards [hev] with N ⟨hN, hc⟩
      rw [hentry N hN, ite_eq_right hξη, sub_zero, ← div_eq_inv_mul]
      simp only [ε]
      exact div_le_div_of_nonneg_right
        (stepProb_le_of_not_isMerge (W N) _ hM (Ne.symm hξη)) hc.le

/-- `⌊x / c⌋ c → x` as `c → 0⁺`. -/
theorem tendsto_floor_div_mul {c : ℕ → ℝ} (hc0 : ∀ᶠ N in atTop, 0 < c N)
    (hc : Tendsto c atTop (𝓝 0)) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun N => (⌊x / c N⌋₊ : ℝ) * c N) atTop (𝓝 x) := by
  have hlow : Tendsto (fun N => x - c N) atTop (𝓝 x) := by simpa using tendsto_const_nhds.sub hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hc0] with N hcN
    have := Nat.lt_floor_add_one (x / c N)
    rw [div_lt_iff₀ hcN] at this
    nlinarith
  · filter_upwards [hc0] with N hcN
    have := Nat.floor_le (div_nonneg hx hcN.le)
    rwa [le_div_iff₀ hcN] at this

/-- **Kingman's limit for Cannings models** (Möhle 2000; Möhle–Sagitov 2001). Under the
Möhle–Sagitov conditions, for `0 ≤ s ≤ t` the transition matrix of the ancestral partition
process of a sample of `n` genes over the generations `⌊s / c_N⌋, …, ⌊t / c_N⌋` converges to the
transition matrix `exp ((t - s) • Q)` of Kingman's `n`-coalescent. -/
theorem MohleSagitov.tendsto_ancestralMatrix_pow {W : ∀ N, CanningsModel N}
    (hW : MohleSagitov W) (n : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun N => ancestralMatrix (W N) n ^
        (⌊t / (W N).pairCoalescence⌋₊ - ⌊s / (W N).pairCoalescence⌋₊)) atTop
      (𝓝 (NormedSpace.exp ((t - s) • partitionRate n))) := by
  set c := fun N => (W N).pairCoalescence
  have hm : Tendsto (fun N => ((⌊t / c N⌋₊ - ⌊s / c N⌋₊ : ℕ) : ℝ) * c N) atTop (𝓝 (t - s)) := by
    have h := (tendsto_floor_div_mul hW.pairCoalescence_pos hW.tendsto_pairCoalescence
      (hs.trans hst)).sub
      (tendsto_floor_div_mul hW.pairCoalescence_pos hW.tendsto_pairCoalescence hs)
    refine h.congr' ?_
    filter_upwards [hW.pairCoalescence_pos] with N hcN
    rw [Nat.cast_sub (Nat.floor_le_floor (div_le_div_of_nonneg_right hst hcN.le)), sub_mul]
  open scoped Matrix.Norms.Operator in
  refine (NormedSpace.tendsto_one_add_smul_pow hW.tendsto_pairCoalescence hW.pairCoalescence_pos
    (hW.tendsto_generator n) hm).congr' ?_
  filter_upwards [hW.pairCoalescence_pos] with N hcN
  rw [smul_smul, mul_inv_cancel₀ hcN.ne', one_smul, add_sub_cancel]

/-- From the sample in singletons: after `⌊t / c_N⌋` generations the ancestral partition has
the law `timeLaw n t` of Kingman's `n`-coalescent at time `t` in the limit. -/
theorem MohleSagitov.tendsto_ancestralMatrix_pow_bot {W : ∀ N, CanningsModel N}
    (hW : MohleSagitov W) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (π : SamplePartition n) :
    Tendsto (fun N => (ancestralMatrix (W N) n ^ ⌊t / (W N).pairCoalescence⌋₊) ⊥ π) atTop
      (𝓝 (timeLaw n t π)) := by
  have h := hW.tendsto_ancestralMatrix_pow n le_rfl ht
  simp only [zero_div, Nat.floor_zero, Nat.sub_zero, sub_zero] at h
  exact ((continuous_apply π).comp (continuous_apply ⊥)).continuousAt.tendsto.comp h

/-- The finite-dimensional distribution of a Markov chain with transition matrix `P`, started
from `x₀` at time `0` and observed at the times `m 0 ≤ m 1 ≤ ⋯ ≤ m k`: the probability of being
at `x i` at time `m i` for every `i`. By the Markov property it is the time-`m 0` law
`(P ^ m 0) x₀ (x 0)` times the transition probabilities between consecutive observations. -/
noncomputable def chainFDD {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (x₀ : S)
    {k : ℕ} (m : Fin (k + 1) → ℕ) (x : Fin (k + 1) → S) : ℝ :=
  (P ^ m 0) x₀ (x 0) * ∏ i : Fin k, (P ^ (m i.succ - m i.castSucc)) (x i.castSucc) (x i.succ)

/-- The finite-dimensional distribution of Kingman's `n`-coalescent, started from singletons at
time `0` and observed at the times `t 0 ≤ t 1 ≤ ⋯ ≤ t k`: the time-`t 0` law
`timeLaw n (t 0) (x 0) = exp (t 0 • Q) ⊥ (x 0)` times the transition probabilities
`exp ((t (i + 1) - t i) • Q) (x i) (x (i + 1))`. -/
noncomputable def kingmanFDD (n : ℕ) {k : ℕ} (t : Fin (k + 1) → ℝ)
    (x : Fin (k + 1) → SamplePartition n) : ℝ :=
  timeLaw n (t 0) (x 0) * ∏ i : Fin k,
    NormedSpace.exp ((t i.succ - t i.castSucc) • partitionRate n) (x i.castSucc) (x i.succ)

/-- **Cannings genealogies converge to Kingman's coalescent** (finite-dimensional
distributions; Möhle 2000, Möhle–Sagitov 2001). Under the Möhle–Sagitov conditions, the
ancestral partition process of a sample of `n` genes, started from singletons at generation `0`
and observed at the generations `⌊t i / c_N⌋` for times `0 ≤ t 0 ≤ t 1 ≤ ⋯ ≤ t k`, has
finite-dimensional distributions converging to those of Kingman's `n`-coalescent, started from
singletons, at the times `t i`. -/
theorem MohleSagitov.tendsto_chainFDD {W : ∀ N, CanningsModel N} (hW : MohleSagitov W)
    (n : ℕ) {k : ℕ} (t : Fin (k + 1) → ℝ) (ht0 : 0 ≤ t 0) (ht : Monotone t)
    (x : Fin (k + 1) → SamplePartition n) :
    Tendsto (fun N => chainFDD (ancestralMatrix (W N) n) ⊥
        (fun i => ⌊t i / (W N).pairCoalescence⌋₊) x) atTop (𝓝 (kingmanFDD n t x)) := by
  unfold chainFDD kingmanFDD
  refine (hW.tendsto_ancestralMatrix_pow_bot n ht0 (x 0)).mul
    (tendsto_finsetProd _ fun i _ => ?_)
  have hs : 0 ≤ t i.castSucc := ht0.trans (ht (Fin.zero_le _))
  have hst : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  exact ((continuous_apply (x i.succ)).comp
    (continuous_apply (x i.castSucc))).continuousAt.tendsto.comp
    (hW.tendsto_ancestralMatrix_pow n hs hst)

end MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman
