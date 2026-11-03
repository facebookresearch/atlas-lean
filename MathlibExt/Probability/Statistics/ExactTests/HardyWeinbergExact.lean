/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Levene's exact null distribution for the Hardy–Weinberg test

Consider `N` diploid individuals carrying `n_A` copies of allele `A` and `n_B = 2N - n_A`
copies of allele `B` among their `2N` gametes. Under Hardy–Weinberg equilibrium (random union
of gametes), conditional on `n_A`, the `n_A` copies of `A` occupy a uniformly random
`n_A`-subset of the `2N` gamete slots: individual `j` carries the slots `(j, 0)` and
`(j, 1)`. Levene (1949) showed that the number `n_AB` of heterozygotes then has the law

`P(n_AB | n_A) = N! n_A! n_B! 2^{n_AB} / (n_AA! n_AB! n_BB! (2N)!)`,

with `n_AA = (n_A - n_AB) / 2` and `n_BB = (n_B - n_AB) / 2`, supported on the admissible
values: `n_AB ≤ min(n_A, n_B)` with `n_AB ≡ n_A (mod 2)`. This is the null distribution of the
exact test of Hardy–Weinberg proportions (Wigginton, Cutler and Abecasis 2005).

## Main definitions

* `leveneProb N nA h`: Levene's probability of `h` heterozygotes (`0` if `h` is not
  admissible).
* `hetCount s`: the number of heterozygous individuals when the `A` gametes occupy the slots
  in `s : Finset (Fin N × Fin 2)`.

## Main results

* `card_hetCount_div_choose`: the fraction of the `C(2N, n_A)` gamete arrangements with
  exactly `h` heterozygotes is `leveneProb N nA h`, i.e. Levene's formula is the law of `n_AB`
  when the arrangement of the `A` gametes is uniform (the uniform-arrangement model is assumed,
  not derived from independent gametes).
* `sum_leveneProb`: the probabilities over admissible `n_AB` sum to one.

## References

* H. Levene, *On a matching problem arising in genetics*, Ann. Math. Statist. 20 (1949),
  91–94.
* J. E. Wigginton, D. J. Cutler and G. R. Abecasis, *A note on exact tests of Hardy–Weinberg
  equilibrium*, Am. J. Hum. Genet. 76 (2005), 887–893.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Statistics.ExactTests

/-- Levene's conditional probability of `h` heterozygotes among `N` diploid individuals given
`nA` copies of allele `A` (and `nB = 2N - nA` of `B`) under Hardy–Weinberg equilibrium:
`N! nA! nB! 2^h / (nAA! h! nBB! (2N)!)` with `nAA = (nA - h) / 2`, `nBB = (nB - h) / 2`, when
`h ≤ nA`, `h ≤ nB` and `nA - h` is even, and `0` otherwise. The parameter domain is
`nA ≤ 2N`; for `nA > 2N` the value is `0`. -/
noncomputable def leveneProb (N nA h : ℕ) : ℝ :=
  if h ≤ nA ∧ h + nA ≤ 2 * N ∧ Even (nA - h) then
    (N.factorial * nA.factorial * (2 * N - nA).factorial * 2 ^ h : ℝ) /
      (((nA - h) / 2).factorial * h.factorial * ((2 * N - nA - h) / 2).factorial *
        (2 * N).factorial)
  else 0

/-- The number of heterozygous individuals when the `A` gametes occupy the slots `s`:
individuals `j` carrying exactly one of the slots `(j, 0)`, `(j, 1)`. -/
def hetCount {N : ℕ} (s : Finset (Fin N × Fin 2)) : ℕ :=
  (univ.filter fun j : Fin N => ¬((j, 0) ∈ s ↔ (j, 1) ∈ s)).card

/-- The homozygous `AA` individuals of an arrangement. -/
private def aaSet {N : ℕ} (s : Finset (Fin N × Fin 2)) : Finset (Fin N) :=
  univ.filter fun j => (j, 0) ∈ s ∧ (j, 1) ∈ s

/-- The heterozygous individuals of an arrangement. -/
private def hetSet {N : ℕ} (s : Finset (Fin N × Fin 2)) : Finset (Fin N) :=
  univ.filter fun j => ¬((j, 0) ∈ s ↔ (j, 1) ∈ s)

/-- The heterozygotes whose `A` gamete is in slot `0`. -/
private def orientSet {N : ℕ} (s : Finset (Fin N × Fin 2)) : Finset (Fin N) :=
  (hetSet s).filter fun j => (j, 0) ∈ s

/-- The arrangement with `AA` set `A`, heterozygotes `H`, and orientation set `O ⊆ H`. -/
private def arrangement {N : ℕ} (A H O : Finset (Fin N)) : Finset (Fin N × Fin 2) :=
  (A ×ˢ univ) ∪ (O ×ˢ {0}) ∪ ((H \ O) ×ˢ {1})

private theorem aa_het_disjoint {N : ℕ} (s : Finset (Fin N × Fin 2)) :
    Disjoint (aaSet s) (hetSet s) := by
  simp only [disjoint_left, aaSet, hetSet, mem_filter, mem_univ, true_and]
  tauto

private theorem orient_subset {N : ℕ} (s : Finset (Fin N × Fin 2)) :
    orientSet s ⊆ hetSet s := filter_subset _ _

private theorem arrangement_recover {N : ℕ} (s : Finset (Fin N × Fin 2)) :
    arrangement (aaSet s) (hetSet s) (orientSet s) = s := by
  ext ⟨j, b⟩
  fin_cases b <;> simp [arrangement, aaSet, hetSet, orientSet] <;> tauto

private theorem arrangement_sets {N : ℕ} (A H O : Finset (Fin N))
    (hd : Disjoint A H) (ho : O ⊆ H) :
    aaSet (arrangement A H O) = A ∧ hetSet (arrangement A H O) = H ∧
      orientSet (arrangement A H O) = O := by
  have hd' := disjoint_left.mp hd
  have hmem (j : Fin N) : j ∈ A → j ∉ H := fun ha hh => hd' ha hh
  have hmemO (j : Fin N) : j ∈ O → j ∈ H := fun hj => ho hj
  constructor
  · ext j
    simp [aaSet, arrangement]
    grind
  constructor
  · ext j
    simp [hetSet, arrangement]
    grind
  · ext j
    simp [orientSet, hetSet, arrangement]
    grind

private theorem arrangement_card {N : ℕ} (A H O : Finset (Fin N))
    (hd : Disjoint A H) (ho : O ⊆ H) :
    (arrangement A H O).card = 2 * A.card + H.card := by
  have hAO : Disjoint (A ×ˢ (univ : Finset (Fin 2))) (O ×ˢ {0}) := by
    rw [disjoint_left]
    intro x hx hy
    exact disjoint_left.mp hd (mem_product.mp hx).1 (ho (mem_product.mp hy).1)
  have hAH : Disjoint ((A ×ˢ (univ : Finset (Fin 2))) ∪ (O ×ˢ {0}))
      ((H \ O) ×ˢ {1}) := by
    rw [disjoint_left]
    intro x hx hy
    rcases mem_union.mp hx with hx | hx
    · exact disjoint_left.mp hd (mem_product.mp hx).1
        (mem_sdiff.mp (mem_product.mp hy).1).1
    · exact (mem_sdiff.mp (mem_product.mp hy).1).2 (mem_product.mp hx).1
  simp only [arrangement, card_union_of_disjoint hAH, card_union_of_disjoint hAO,
    card_product, card_univ, Fintype.card_fin, card_singleton, mul_one,
    card_sdiff_of_subset ho]
  have := card_le_card ho
  omega

private theorem genotype_accounting {N : ℕ} (s : Finset (Fin N × Fin 2)) :
    s.card = 2 * (aaSet s).card + hetCount s ∧
      (aaSet s).card + hetCount s ≤ N := by
  have hc := arrangement_card (aaSet s) (hetSet s) (orientSet s)
    (aa_het_disjoint s) (orient_subset s)
  rw [arrangement_recover] at hc
  have hb := card_le_card (subset_univ (aaSet s ∪ hetSet s))
  rw [card_union_of_disjoint (aa_het_disjoint s)] at hb
  simpa [hetCount, hetSet] using And.intro hc hb

/-- Triples `(H, A, O)` with `|H| = h`, `|A| = k`, `A ∩ H = ∅`, `O ⊆ H`. -/
private def configurations (N k h : ℕ) :
    Finset (Σ _ : Finset (Fin N), Finset (Fin N) × Finset (Fin N)) :=
  (univ.powersetCard h).sigma fun H => ((univ \ H).powersetCard k) ×ˢ H.powerset

private theorem mem_configurations {N k h : ℕ}
    (H A O : Finset (Fin N)) :
    (⟨H, A, O⟩ : Σ _ : Finset (Fin N), Finset (Fin N) × Finset (Fin N)) ∈
        configurations N k h ↔
      H.card = h ∧ A.card = k ∧ Disjoint A H ∧ O ⊆ H := by
  simp only [configurations, mem_sigma, mem_product, mem_powersetCard,
    subset_univ, true_and, mem_powerset]
  have hd : A ⊆ univ \ H ↔ Disjoint A H := by
    simp [subset_iff, disjoint_left]
  rw [hd]
  tauto

private theorem card_configurations (N k h : ℕ) :
    (configurations N k h).card = N.choose h * (N - h).choose k * 2 ^ h := by
  rw [configurations, card_sigma]
  calc
    _ = ∑ H ∈ univ.powersetCard h, (N - h).choose k * 2 ^ h := by
      apply sum_congr rfl
      intro H hH
      have hc := (mem_powersetCard.mp hH).2
      simp [card_product, card_powersetCard, card_powerset,
        card_sdiff_of_subset (subset_univ H), hc]
    _ = _ := by simp [card_powersetCard, Nat.mul_assoc]

private theorem card_arrangements (N k h : ℕ) :
    (univ.filter fun s : Finset (Fin N × Fin 2) =>
      s.card = 2 * k + h ∧ hetCount s = h).card =
        N.choose h * (N - h).choose k * 2 ^ h := by
  classical
  rw [← card_configurations]
  symm
  apply card_bij (fun x _ => arrangement x.2.1 x.1 x.2.2)
  · rintro ⟨H, A, O⟩ hx
    obtain ⟨hH, hA, hd, ho⟩ := (mem_configurations H A O).mp hx
    have hs := arrangement_sets A H O hd ho
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rw [arrangement_card A H O hd ho, hA, hH]
    · change (hetSet (arrangement A H O)).card = h
      rw [hs.2.1, hH]
  · rintro ⟨H, A, O⟩ hx ⟨H', A', O'⟩ hy he
    obtain ⟨_, _, hd, ho⟩ := (mem_configurations H A O).mp hx
    obtain ⟨_, _, hd', ho'⟩ := (mem_configurations H' A' O').mp hy
    have hs := arrangement_sets A H O hd ho
    have hs' := arrangement_sets A' H' O' hd' ho'
    have hH : H = H' := hs.2.1.symm.trans ((congrArg hetSet he).trans hs'.2.1)
    have hA : A = A' := hs.1.symm.trans ((congrArg aaSet he).trans hs'.1)
    have hO : O = O' := hs.2.2.symm.trans ((congrArg orientSet he).trans hs'.2.2)
    subst H'; subst A'; subst O'
    rfl
  · intro s hs
    obtain ⟨hc, hh⟩ := (mem_filter.mp hs).2
    have ha : (aaSet s).card = k := by
      have := (genotype_accounting s).1
      omega
    refine ⟨⟨hetSet s, aaSet s, orientSet s⟩, ?_, arrangement_recover s⟩
    exact (mem_configurations _ _ _).mpr
      ⟨hh, ha, aa_het_disjoint s, orient_subset s⟩

private theorem arrangement_admissible {N : ℕ} (s : Finset (Fin N × Fin 2)) :
    hetCount s ≤ s.card ∧ hetCount s + s.card ≤ 2 * N ∧
      Even (s.card - hetCount s) := by
  obtain ⟨hc, hb⟩ := genotype_accounting s
  refine ⟨by omega, by omega, (aaSet s).card, ?_⟩
  omega

private theorem factorial_ratio (N nA h k : ℕ)
    (hk : 2 * k + h = nA) (hkh : k + h ≤ N) :
    ((N.choose h * (N - h).choose k * 2 ^ h : ℕ) : ℝ) / (2 * N).choose nA =
      (N.factorial * nA.factorial * (2 * N - nA).factorial * 2 ^ h : ℝ) /
        (k.factorial * h.factorial * (N - h - k).factorial * (2 * N).factorial) := by
  have hh : h ≤ N := by omega
  have hk' : k ≤ N - h := by omega
  have hnA : nA ≤ 2 * N := by omega
  have c1 : (N.choose h : ℝ) * h.factorial * (N - h).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hh
  have c2 : ((N - h).choose k : ℝ) * k.factorial * (N - h - k).factorial =
      (N - h).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have c3 : ((2 * N).choose nA : ℝ) * nA.factorial * (2 * N - nA).factorial =
      (2 * N).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hnA
  have hden : ((2 * N).choose nA : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hnA).ne'
  have hf (m : ℕ) : (m.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  push_cast
  apply (div_eq_div_iff hden (by positivity)).mpr
  calc
    _ = ((N.choose h : ℝ) * h.factorial *
        (((N - h).choose k : ℝ) * k.factorial * (N - h - k).factorial)) *
        (2 : ℝ) ^ h * (2 * N).factorial := by ring
    _ = (N.factorial : ℝ) * (2 : ℝ) ^ h * (2 * N).factorial := by rw [c2, c1]
    _ = _ := by rw [← c3]; ring

/-- **Levene's formula is the conditional law under random union of gametes.** Among the
`C(2N, nA)` equally likely placements of the `nA` copies of `A` in the `2N` gamete slots, the
fraction with exactly `h` heterozygous individuals is `leveneProb N nA h`.

No hypothesis `nA ≤ 2N` is needed: for `nA > 2N` there is no placement and `C(2N, nA) = 0`, so
the left side is `0 / 0 = 0`, matching `leveneProb N nA h = 0`; the statement is meaningful for
`nA ≤ 2N`. The uniform law on placements is taken as the model; deriving it from independent
gametes conditioned on `nA` is not part of this file.

Source: Levene (1949); Wigginton, Cutler and Abecasis (2005). -/
theorem card_hetCount_div_choose (N nA h : ℕ) :
    ((univ.filter fun s : Finset (Fin N × Fin 2) => s.card = nA ∧ hetCount s = h).card : ℝ) /
      (2 * N).choose nA = leveneProb N nA h := by
  classical
  unfold leveneProb
  split_ifs with hadm
  · obtain ⟨ha, hb, he⟩ := hadm
    let k := (nA - h) / 2
    have hk : 2 * k + h = nA := by
      have := Nat.two_mul_div_two_of_even he
      dsimp [k]
      omega
    have hkh : k + h ≤ N := by omega
    have hbb : (2 * N - nA - h) / 2 = N - h - k := by omega
    have hc := card_arrangements N k h
    rw [hk] at hc
    rw [hc, hbb]
    exact factorial_ratio N nA h k hk hkh
  · have hempty : (univ.filter fun s : Finset (Fin N × Fin 2) =>
        s.card = nA ∧ hetCount s = h) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro s _ hs
      have hadm' := arrangement_admissible s
      rw [hs.1, hs.2] at hadm'
      exact hadm hadm'
    rw [hempty]
    simp

/-- **Normalization of Levene's distribution.** For `nA ≤ 2N` the probabilities
`leveneProb N nA h` over the admissible heterozygote counts `h` sum to one.

Source: Levene (1949); Wigginton, Cutler and Abecasis (2005). -/
theorem sum_leveneProb {N nA : ℕ} (hnA : nA ≤ 2 * N) :
    ∑ h ∈ range (nA + 1), leveneProb N nA h = 1 := by
  classical
  let S := univ.filter fun s : Finset (Fin N × Fin 2) => s.card = nA
  have hc : S.card = (2 * N).choose nA := by
    simp [S, card_powersetCard, Nat.mul_comm]
  have hf : S.card = ∑ h ∈ range (nA + 1), (S.filter fun s => hetCount s = h).card := by
    apply card_eq_sum_card_fiberwise
    intro s hs
    have hs' : s.card = nA := (mem_filter.mp hs).2
    have hh := (arrangement_admissible s).1
    exact mem_range.mpr (by omega)
  have hsum : (∑ h ∈ range (nA + 1),
      (univ.filter fun s : Finset (Fin N × Fin 2) =>
        s.card = nA ∧ hetCount s = h).card) = (2 * N).choose nA := by
    rw [← hc]
    simpa only [S, filter_filter] using hf.symm
  simp_rw [← card_hetCount_div_choose]
  rw [← sum_div, ← Nat.cast_sum, hsum]
  apply div_self
  exact_mod_cast (Nat.choose_pos hnA).ne'

end MathlibExt.Probability.Statistics.ExactTests
