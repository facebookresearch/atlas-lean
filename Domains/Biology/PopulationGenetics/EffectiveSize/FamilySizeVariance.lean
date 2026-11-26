/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Effective population size and the variance in family size

A population of `N` monoecious diploid parents produces the `2N` gene copies of the next
generation. The data of one generation is its *parent map* `parent : Fin (2 * N) → Fin N`: gene
copy `c` of the offspring generation comes from a gamete of parent `parent c`. Parent `i`
contributes `n_i = #{c | parent c = i}` gametes (`gameteContribution`), so `∑ n_i = 2N`, and
`V_n = (1/N) ∑ (n_i - 2)^2` is the variance of the contributions (`contributionVariance`).

`sameParentProb` is the probability that two distinct gene copies of the offspring generation,
chosen uniformly at random, come from the same parent, and `familyEffectiveSize` is the `N_e`
defined by `P = 1/N_e`. If each gamete carries one of its parent's two genes, chosen uniformly
and independently, `sameParentalGeneProb` is the probability that the two gene copies are copies
of the same parental gene. How the gametes are paired into offspring (selfing included) plays no
part in these quantities.

## Main results

* `effective_size_and_variance_in_family_size`:
  `P = ∑ n_i (n_i - 1) / (2N (2N - 1)) = (V_n + 2) / (2 (2N - 1))`, so
  `N_e = (4N - 2) / (V_n + 2)`, with the cases `V_n = 0` (`N_e = 2N - 1`) and
  `V_n = 2 - 2/N` (`N_e = N`). Under Wright–Fisher sampling (the parent map uniform over all
  `N^{2N}` maps) `V_n` has expectation `2 - 2/N` and `P` has expectation `1/N`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, version of December 2019,
  Section VI.7, equations (VI-50)–(VI-54).
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory

namespace Domains.Biology.PopulationGenetics.EffectiveSize

variable {N : ℕ}

/-- **Gamete contributions.** Let `parent : Fin (2 * N) → Fin N` assign each of the $2N$ gene
copies of the offspring generation to the parent, among $N$ diploid parents, whose gamete it
comes from. The contribution of parent $i$ is the number
$n_i = \#\{c \mid \mathrm{parent}(c) = i\}$ of gene copies of the offspring generation that come
from it. -/
def gameteContribution (parent : Fin (2 * N) → Fin N) (i : Fin N) : ℕ :=
  #{c | parent c = i}

/-- **Variance of the gamete contributions.** For a parent map
`parent : Fin (2 * N) → Fin N` with contributions $n_i$ (`gameteContribution`), the variance
$V_n = \frac1N \sum_i (n_i - 2)^2$ of the contributions about their mean $2$ (the contributions
sum to $2N$). For $N = 0$ the value is $0$, by Lean's convention $x / 0 = 0$. -/
noncomputable def contributionVariance (parent : Fin (2 * N) → Fin N) : ℝ :=
  (∑ i, ((gameteContribution parent i : ℝ) - 2) ^ 2) / N

/-- **Probability that two gene copies come from the same parent.** For a parent map
`parent : Fin (2 * N) → Fin N`, the probability that an ordered pair $(a, b)$ of distinct gene
copies of the offspring generation, chosen uniformly at random among the $2N(2N - 1)$ such pairs,
has $\mathrm{parent}(a) = \mathrm{parent}(b)$. It is $0$ when $N = 0$, as there is no such
pair. -/
noncomputable def sameParentProb (parent : Fin (2 * N) → Fin N) : ℝ :=
  (uniformOn {p : Fin (2 * N) × Fin (2 * N) | p.1 ≠ p.2}).real {p | parent p.1 = parent p.2}

/-- **Probability that two gene copies are copies of the same parental gene.** For a parent map
`parent : Fin (2 * N) → Fin N`, let each gene copy $c$ of the offspring generation carry one of
its parent's two genes, the gene $(\mathrm{parent}(c), s(c))$ with $s(c) \in \{0, 1\}$, the choice
map $s$ being uniform over all $2^{2N}$ maps (independent fair choices). This is the probability,
for $s$ uniform and an independent ordered pair $(a, b)$ of distinct gene copies uniform among the
$2N(2N - 1)$ such pairs, that $a$ and $b$ are copies of the same parental gene,
$(\mathrm{parent}(a), s(a)) = (\mathrm{parent}(b), s(b))$. It is $0$ when $N = 0$, as there is
no such pair. -/
noncomputable def sameParentalGeneProb (parent : Fin (2 * N) → Fin N) : ℝ :=
  (uniformOn {x : (Fin (2 * N) → Fin 2) × Fin (2 * N) × Fin (2 * N) | x.2.1 ≠ x.2.2}).real
    {x | (parent x.2.1, x.1 x.2.1) = (parent x.2.2, x.1 x.2.2)}

/-- **Effective population size from the family sizes.** For a parent map
`parent : Fin (2 * N) → Fin N`, the effective size $N_e$ defined by $P = 1/N_e$, where $P$ is the
probability that two distinct gene copies of the offspring generation come from the same parent
(`sameParentProb`): $N_e = 1/P$, which is $0$ if $P = 0$ (Lean's convention $1/0 = 0$). -/
noncomputable def familyEffectiveSize (parent : Fin (2 * N) → Fin N) : ℝ :=
  1 / sameParentProb parent

/-! ### Counting -/

/-- For `a ≠ b`, the maps `f : α → β` with `f a = f b` number `|β| ^ (|α| - 1)`. -/
private theorem card_filter_apply_eq_apply {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {a b : α} (hab : a ≠ b) :
    #{f : α → β | f a = f b} = Fintype.card β ^ (Fintype.card α - 1) := by
  let e : {f : α → β // f a = f b} ≃ ({c : α // c ≠ b} → β) :=
    { toFun := fun f c => f.1 c.1
      invFun := fun g => ⟨fun c => if h : c = b then g ⟨a, hab⟩ else g ⟨c, h⟩, by simp [hab]⟩
      left_inv := by
        rintro ⟨f, hf⟩
        ext c
        by_cases h : c = b
        · subst h; simp [hf]
        · simp [h]
      right_inv := by
        intro g
        ext ⟨c, hc⟩
        simp [hc] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_subtype,
    filter_ne' univ b, card_erase_of_mem (mem_univ b), card_univ]

/-- The contributions of the parents sum to the number `2N` of gene copies. -/
private theorem sum_gameteContribution (parent : Fin (2 * N) → Fin N) :
    ∑ i, gameteContribution parent i = 2 * N := by
  rw [← Fintype.card_fin (2 * N), ← card_univ,
    card_eq_sum_card_fiberwise (f := parent) (t := univ) (fun _ _ => mem_univ _)]
  rfl

/-- The ordered pairs of distinct gene copies with the same parent number
`∑ i, (n_i * n_i - n_i)`. -/
private theorem card_offDiag_filter_parent (parent : Fin (2 * N) → Fin N) :
    #{p ∈ (univ : Finset (Fin (2 * N))).offDiag | parent p.1 = parent p.2} =
      ∑ i, (gameteContribution parent i * gameteContribution parent i -
        gameteContribution parent i) := by
  rw [card_eq_sum_card_fiberwise (f := fun p => parent p.1) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun i _ => ?_
  rw [gameteContribution, ← offDiag_card, filter_filter]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_offDiag, mem_univ, true_and]
  constructor
  · rintro ⟨hab, h, rfl⟩
    exact ⟨rfl, h.symm, hab⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨hab, ha.trans hb.symm, ha⟩

private theorem sum_gameteContribution_real (parent : Fin (2 * N) → Fin N) :
    ∑ i, (gameteContribution parent i : ℝ) = 2 * N := by
  exact_mod_cast sum_gameteContribution parent

/-- The same-parent pair count, as a real number, is `∑ i, n_i (n_i - 1)`. -/
private theorem card_offDiag_filter_parent_real (parent : Fin (2 * N) → Fin N) :
    (#{p ∈ (univ : Finset (Fin (2 * N))).offDiag | parent p.1 = parent p.2} : ℝ) =
      ∑ i, (gameteContribution parent i : ℝ) * (gameteContribution parent i - 1) := by
  rw [card_offDiag_filter_parent, Nat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

private theorem card_offDiag_univ_real :
    ((univ : Finset (Fin (2 * N))).offDiag.card : ℝ) = 2 * N * (2 * N - 1) := by
  rw [offDiag_card, card_univ, Fintype.card_fin, Nat.cast_sub (Nat.le_mul_self _)]
  push_cast
  ring

private theorem coe_offDiag_univ :
    (((univ : Finset (Fin (2 * N))).offDiag : Finset _) : Set (Fin (2 * N) × Fin (2 * N))) =
      {p | p.1 ≠ p.2} := by
  ext p
  simp

/-- `P = ∑ n_i (n_i - 1) / (2N (2N - 1))`. -/
private theorem sameParentProb_eq_sum (parent : Fin (2 * N) → Fin N) :
    sameParentProb parent =
      (∑ i, (gameteContribution parent i : ℝ) * (gameteContribution parent i - 1)) /
        (2 * N * (2 * N - 1)) := by
  have ht : {p : Fin (2 * N) × Fin (2 * N) | parent p.1 = parent p.2} =
      ((univ.filter fun p : Fin (2 * N) × Fin (2 * N) => parent p.1 = parent p.2 :
        Finset _) : Set _) := by
    ext p
    simp
  rw [sameParentProb, ← coe_offDiag_univ, ht, measureReal_def, uniformOn_apply_finset,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, inter_filter,
    inter_univ, card_offDiag_filter_parent_real, card_offDiag_univ_real]

/-- `∑ n_i ^ 2 = N (V_n + 4)`. -/
private theorem sum_sq_gameteContribution (hN : 0 < N) (parent : Fin (2 * N) → Fin N) :
    ∑ i, (gameteContribution parent i : ℝ) ^ 2 = N * (contributionVariance parent + 4) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum := sum_gameteContribution_real parent
  have h : ∑ i, ((gameteContribution parent i : ℝ) - 2) ^ 2 =
      ∑ i, (gameteContribution parent i : ℝ) ^ 2 - 4 * ∑ i, (gameteContribution parent i : ℝ) +
        4 * N := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring_nf
  rw [contributionVariance, h, hsum]
  field_simp
  ring

/-- `P = (V_n + 2) / (2 (2N - 1))`. -/
private theorem sameParentProb_eq_variance (hN : 0 < N) (parent : Fin (2 * N) → Fin N) :
    sameParentProb parent = (contributionVariance parent + 2) / (2 * (2 * N - 1)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : ∑ i, (gameteContribution parent i : ℝ) * (gameteContribution parent i - 1) =
      ∑ i, (gameteContribution parent i : ℝ) ^ 2 - ∑ i, (gameteContribution parent i : ℝ) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [sameParentProb_eq_sum, h, sum_sq_gameteContribution hN, sum_gameteContribution_real]
  field_simp
  ring

/-- `V_n = 0` exactly when every parent contributes two gametes. -/
private theorem contributionVariance_eq_zero_iff (hN : 0 < N) (parent : Fin (2 * N) → Fin N) :
    contributionVariance parent = 0 ↔ ∀ i, gameteContribution parent i = 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [contributionVariance, div_eq_zero_iff, or_iff_left hN',
    sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  simp only [mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  exact forall_congr' fun i => by exact_mod_cast Iff.rfl

/-- `N_e = (4N - 2) / (V_n + 2)`. -/
private theorem familyEffectiveSize_eq (hN : 0 < N) (parent : Fin (2 * N) → Fin N) :
    familyEffectiveSize parent = (4 * N - 2) / (contributionVariance parent + 2) := by
  rw [familyEffectiveSize, sameParentProb_eq_variance hN, one_div_div]
  ring

/-- Two distinct gene copies with the same parent are copies of the same parental gene with
probability `1/2`, so `sameParentalGeneProb = P / 2`. -/
private theorem sameParentalGeneProb_eq (hN : 0 < N) (parent : Fin (2 * N) → Fin N) :
    sameParentalGeneProb parent = sameParentProb parent / 2 := by
  set D := (univ : Finset (Fin (2 * N))).offDiag
  have hX : {x : (Fin (2 * N) → Fin 2) × Fin (2 * N) × Fin (2 * N) | x.2.1 ≠ x.2.2} =
      (((univ : Finset (Fin (2 * N) → Fin 2)) ×ˢ D : Finset _) : Set _) := by
    ext x
    simp [D]
  have hE : {x : (Fin (2 * N) → Fin 2) × Fin (2 * N) × Fin (2 * N) |
      (parent x.2.1, x.1 x.2.1) = (parent x.2.2, x.1 x.2.2)} =
      ((univ.filter fun x : (Fin (2 * N) → Fin 2) × Fin (2 * N) × Fin (2 * N) =>
        (parent x.2.1, x.1 x.2.1) = (parent x.2.2, x.1 x.2.2) : Finset _) : Set _) := by
    ext x
    simp
  have hfib : ∀ p ∈ D, #{s : Fin (2 * N) → Fin 2 | (parent p.1, s p.1) = (parent p.2, s p.2)} =
      if parent p.1 = parent p.2 then 2 ^ (2 * N - 1) else 0 := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (mem_offDiag.1 hp).2.2
    split_ifs with h
    · simp only [Prod.mk.injEq, h, true_and]
      rw [card_filter_apply_eq_apply hp', Fintype.card_fin, Fintype.card_fin]
    · simp [h]
  have hnum : #((univ ×ˢ D).filter fun x : (Fin (2 * N) → Fin 2) × Fin (2 * N) × Fin (2 * N) =>
      (parent x.2.1, x.1 x.2.1) = (parent x.2.2, x.1 x.2.2)) =
      #{p ∈ D | parent p.1 = parent p.2} * 2 ^ (2 * N - 1) := by
    rw [card_filter, sum_product_right]
    rw [sum_congr rfl fun p hp => (card_filter _ _).symm.trans (hfib p hp), ← sum_filter,
      sum_const, smul_eq_mul]
  have hden : #((univ : Finset (Fin (2 * N) → Fin 2)) ×ˢ D) = 2 ^ (2 * N) * #D := by
    rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h2 : (2 : ℝ) ^ (2 * N) = 2 * 2 ^ (2 * N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  rw [sameParentalGeneProb, hX, hE, measureReal_def, uniformOn_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, inter_filter, inter_univ, hnum, hden,
    sameParentProb_eq_sum, ← card_offDiag_filter_parent_real, ← card_offDiag_univ_real]
  push_cast
  rw [h2]
  have hD : (#D : ℝ) ≠ 0 := by
    rw [card_offDiag_univ_real]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact mul_ne_zero (by positivity) (by linarith)
  field_simp
  change _ = (#D : ℝ) * #{p ∈ D | parent p.1 = parent p.2} / #D
  field_simp

/-- Every contribution vector `n` with `∑ n_i = 2N` is that of some parent map. -/
private theorem exists_gameteContribution_eq (n : Fin N → ℕ) (hn : ∑ i, n i = 2 * N) :
    ∃ parent : Fin (2 * N) → Fin N, gameteContribution parent = n := by
  have hcard : Fintype.card (Fin (2 * N)) = Fintype.card ((i : Fin N) × Fin (n i)) := by
    simp [Fintype.card_sigma, hn]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun c => (e c).1, funext fun i => ?_⟩
  have h1 : #{c : Fin (2 * N) | (e c).1 = i} = #{x : (j : Fin N) × Fin (n j) | x.1 = i} :=
    card_equiv e fun c => by simp
  have h2 : ({x : (j : Fin N) × Fin (n j) | x.1 = i} : Finset _) =
      ({i} : Finset (Fin N)).sigma fun _ => univ := by
    ext ⟨j, k⟩
    simp
  rw [gameteContribution, h1, h2, card_sigma]
  simp

/-! ### Wright–Fisher sampling -/

/-- The expectation under the uniform law on a finite type is the average. -/
private theorem integral_uniformOn_univ {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (g : Ω → ℝ) :
    ∫ x, g x ∂(uniformOn Set.univ) = (∑ x, g x) / Fintype.card Ω := by
  rw [integral_fintype Integrable.of_finite, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_natCast, smul_eq_mul]
  ring

/-- Summed over all parent maps, the same-parent pairs number `2N (2N - 1) N ^ (2N - 1)`. -/
private theorem sum_card_offDiag_filter_parent :
    ∑ parent : Fin (2 * N) → Fin N,
        (#{p ∈ (univ : Finset (Fin (2 * N))).offDiag | parent p.1 = parent p.2} : ℝ) =
      2 * N * (2 * N - 1) * (N : ℝ) ^ (2 * N - 1) := by
  have h : ∑ parent : Fin (2 * N) → Fin N,
      #{p ∈ (univ : Finset (Fin (2 * N))).offDiag | parent p.1 = parent p.2} =
      #(univ : Finset (Fin (2 * N))).offDiag * N ^ (2 * N - 1) := by
    simp_rw [card_filter]
    rw [sum_comm]
    rw [sum_congr rfl fun p hp => (card_filter _ _).symm.trans
      ((card_filter_apply_eq_apply (mem_offDiag.1 hp).2.2).trans (by
        rw [Fintype.card_fin, Fintype.card_fin])), sum_const, smul_eq_mul]
  rw [← Nat.cast_sum, h, Nat.cast_mul, card_offDiag_univ_real, Nat.cast_pow]

/-- Under Wright–Fisher sampling `V_n` has expectation `2 - 2/N`. -/
private theorem integral_contributionVariance (hN : 0 < N) :
    ∫ parent, contributionVariance parent ∂(uniformOn (Set.univ : Set (Fin (2 * N) → Fin N))) =
      2 - 2 / N := by
  have : NeZero N := ⟨hN.ne'⟩
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hV : ∀ parent : Fin (2 * N) → Fin N, contributionVariance parent =
      ((#{p ∈ (univ : Finset (Fin (2 * N))).offDiag | parent p.1 = parent p.2} : ℝ) + 2 * N) /
        N - 4 := by
    intro parent
    have h1 := sum_sq_gameteContribution hN parent
    have h2 : ∑ i, (gameteContribution parent i : ℝ) ^ 2 =
        ∑ i, (gameteContribution parent i : ℝ) * (gameteContribution parent i - 1) +
          ∑ i, (gameteContribution parent i : ℝ) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [card_offDiag_filter_parent_real, ← sum_gameteContribution_real parent, ← h2, h1]
    field_simp
    ring
  have hpow : (N : ℝ) ^ (2 * N) = N * (N : ℝ) ^ (2 * N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  simp_rw [integral_uniformOn_univ, hV]
  rw [sum_sub_distrib, ← sum_div, sum_add_distrib, sum_card_offDiag_filter_parent]
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow]
  rw [hpow]
  have : (N : ℝ) ^ (2 * N - 1) ≠ 0 := pow_ne_zero _ hN'
  field_simp
  ring

/-- Under Wright–Fisher sampling `P` has expectation `1/N`. -/
private theorem integral_sameParentProb (hN : 0 < N) :
    ∫ parent, sameParentProb parent ∂(uniformOn (Set.univ : Set (Fin (2 * N) → Fin N))) =
      1 / N := by
  have : NeZero N := ⟨hN.ne'⟩
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2N : (2 * N - 1 : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpow : (N : ℝ) ^ (2 * N) = N * (N : ℝ) ^ (2 * N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  simp_rw [integral_uniformOn_univ, sameParentProb_eq_sum, ← card_offDiag_filter_parent_real]
  rw [← sum_div, sum_card_offDiag_filter_parent]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [hpow]
  have : (N : ℝ) ^ (2 * N - 1) ≠ 0 := pow_ne_zero _ hN'
  field_simp

/-! ### The main theorem -/

/-- **Effective population size and the variance in family size.** Let $N \ge 1$ monoecious
diploid parents produce the $2N$ gene copies of the offspring generation, gene copy $c$ coming
from a gamete of parent $\mathrm{parent}(c)$, for a map `parent : Fin (2 * N) → Fin N`; how the
gametes are paired into offspring does not enter. Parent $i$ contributes
$n_i = \#\{c \mid \mathrm{parent}(c) = i\}$ gametes (`gameteContribution`), and
$V_n = \frac1N \sum_i (n_i - 2)^2$ (`contributionVariance`). Write $P$ for the probability that
an ordered pair of distinct gene copies of the offspring generation, chosen uniformly at random
among the $2N(2N - 1)$ such pairs, comes from the same parent (`sameParentProb`), and
$N_e = 1/P$ (`familyEffectiveSize`).

A vector $(n_i)$ of natural numbers is the vector of contributions of some parent map if and
only if $\sum_i n_i = 2N$. For every parent map:

1. $P = \frac{\sum_i n_i (n_i - 1)}{2N (2N - 1)}$, $\sum_i n_i^2 = N (V_n + 4)$ and
   $P = \frac{V_n + 2}{2 (2N - 1)}$;
2. if each gene copy carries one of its parent's two genes, chosen uniformly and independently
   of the other choices and of the pair, the two gene copies of the pair are copies of the same
   parental gene with probability $P/2$ (`sameParentalGeneProb`);
3. $P = 1/N_e$ and $N_e = \frac{4N - 2}{V_n + 2}$;
4. $V_n = 0$ if and only if $n_i = 2$ for every $i$, and then $N_e = 2N - 1$, so $N \le N_e$,
   with $N < N_e$ when $N > 1$;
5. if $V_n = 2 - 2/N$ then $N_e = N$.

Under Wright–Fisher sampling, the parent map uniform over all $N^{2N}$ maps
`Fin (2 * N) → Fin N` (each gene copy choosing its parent uniformly and independently), $V_n$
has expectation $2 - 2/N$ and $P$ has expectation $1/N$. The probabilities and expectations are
taken under Mathlib's uniform measure `uniformOn`.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics*, version of December 2019,
Section VI.7, equations (VI-50)–(VI-54). -/
theorem effective_size_and_variance_in_family_size (hN : 0 < N) :
    (∀ n : Fin N → ℕ,
      ∑ i, n i = 2 * N ↔ ∃ parent : Fin (2 * N) → Fin N, gameteContribution parent = n) ∧
    (∀ parent : Fin (2 * N) → Fin N,
      sameParentProb parent =
          (∑ i, (gameteContribution parent i : ℝ) * (gameteContribution parent i - 1)) /
            (2 * N * (2 * N - 1)) ∧
        ∑ i, (gameteContribution parent i : ℝ) ^ 2 = N * (contributionVariance parent + 4) ∧
        sameParentProb parent = (contributionVariance parent + 2) / (2 * (2 * N - 1)) ∧
        sameParentalGeneProb parent = sameParentProb parent / 2 ∧
        sameParentProb parent = 1 / familyEffectiveSize parent ∧
        familyEffectiveSize parent = (4 * N - 2) / (contributionVariance parent + 2) ∧
        (contributionVariance parent = 0 ↔ ∀ i, gameteContribution parent i = 2) ∧
        (contributionVariance parent = 0 →
          familyEffectiveSize parent = 2 * N - 1 ∧ (N : ℝ) ≤ familyEffectiveSize parent ∧
            (1 < N → (N : ℝ) < familyEffectiveSize parent)) ∧
        (contributionVariance parent = 2 - 2 / N → familyEffectiveSize parent = N)) ∧
    ∫ parent, contributionVariance parent
        ∂(uniformOn (Set.univ : Set (Fin (2 * N) → Fin N))) = 2 - 2 / N ∧
    ∫ parent, sameParentProb parent
        ∂(uniformOn (Set.univ : Set (Fin (2 * N) → Fin N))) = 1 / N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨fun n => ⟨exists_gameteContribution_eq n, ?_⟩, fun parent => ?_,
    integral_contributionVariance hN, integral_sameParentProb hN⟩
  · rintro ⟨parent, rfl⟩
    exact sum_gameteContribution parent
  have hNe := familyEffectiveSize_eq hN parent
  refine ⟨sameParentProb_eq_sum parent, sum_sq_gameteContribution hN parent,
    sameParentProb_eq_variance hN parent, sameParentalGeneProb_eq hN parent,
    by rw [familyEffectiveSize, one_div_one_div], hNe, contributionVariance_eq_zero_iff hN parent,
    fun hV => ?_, fun hV => ?_⟩
  · have h : familyEffectiveSize parent = 2 * N - 1 := by
      rw [hNe, hV]
      ring
    refine ⟨h, by rw [h]; linarith, fun h1 => ?_⟩
    have : (1 : ℝ) < N := by exact_mod_cast h1
    rw [h]
    linarith
  · have hN' : (N : ℝ) ≠ 0 := by positivity
    have hden : (2 - 2 / N + 2 : ℝ) ≠ 0 := by
      have : 2 / (N : ℝ) ≤ 2 := div_le_self zero_le_two hN1
      linarith
    rw [hNe, hV, div_eq_iff hden]
    field_simp
    ring

end Domains.Biology.PopulationGenetics.EffectiveSize
