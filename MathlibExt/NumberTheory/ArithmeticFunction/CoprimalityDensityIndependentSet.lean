/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuples
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Powerset

/-!
# Hu's independent-set formula for the coprimality density

The independent-set and edge-subset formulas agree prime by prime by weighted
inclusion–exclusion.
-/

open Finset

namespace MetaMathlibExt

namespace CoprimalityDensityIndependentSet

-- The total weight of configurations containing U is the weight of requiring U.
private lemma sum_weight_supersets {k : ℕ} (U : Finset (Fin k)) (x : ℝ) :
    ∑ S ∈ univ.filter (U ⊆ ·), x ^ S.card * (1 - x) ^ (k - S.card) = x ^ U.card := by
  classical
  let b (i : Fin k) := if i ∉ U then 1 - x else 0
  have hprod : (∏ i : Fin k, (x + b i)) = x ^ U.card := by
    calc
      _ = ∏ i : Fin k, if i ∈ U then x else 1 := by
        apply prod_congr rfl
        intro i _
        by_cases hi : i ∈ U <;> simp [b, hi]
      _ = _ := by
        rw [Fintype.prod_ite_mem, prod_const]
  rw [← hprod, prod_add, powerset_univ, sum_filter]
  apply sum_congr rfl
  intro S _
  have h : (∀ i ∈ univ \ S, i ∉ U) ↔ U ⊆ S := by
    simp only [mem_sdiff, mem_univ, true_and, subset_iff]
    exact forall_congr' fun _ => not_imp_not
  simp only [b, prod_ite_zero, h, mul_ite, mul_zero, prod_const,
    card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]

private lemma sum_edges_eq_sum_independent {k : ℕ} (E : Finset (Fin k × Fin k)) (x : ℝ) :
    (∑ F ∈ E.powerset,
      (-1 : ℝ) ^ F.card * x ^ (univ.filter fun i => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card) =
      ∑ S ∈ univ.filter (fun S : Finset (Fin k) => ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)),
        x ^ S.card * (1 - x) ^ (k - S.card) := by
  classical
  let bad (e : Fin k × Fin k) := univ.filter fun S : Finset (Fin k) => e.1 ∈ S ∧ e.2 ∈ S
  let weight (S : Finset (Fin k)) := x ^ S.card * (1 - x) ^ (k - S.card)
  have mem_inf (F : Finset (Fin k × Fin k)) (A : Fin k × Fin k → Finset (Finset (Fin k)))
      (S : Finset (Fin k)) : S ∈ F.inf A ↔ ∀ e ∈ F, S ∈ A e := by
    rw [← compl_compl (F.inf A), Finset.compl_inf]
    simp only [mem_compl, mem_sup, not_exists, not_and, not_not]
  have independent : (E.inf fun e => (bad e)ᶜ) =
      univ.filter (fun S : Finset (Fin k) => ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)) := by
    ext S
    simp only [mem_inf, mem_compl, bad, mem_filter, mem_univ, true_and]
  have allBad (F : Finset (Fin k × Fin k)) :
      F.inf bad = univ.filter
        ((univ.filter fun i => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ ·) := by
    ext S
    simp only [mem_inf, bad, mem_filter, mem_univ, true_and, subset_iff]
    constructor
    · rintro h i ⟨e, he, rfl | rfl⟩
      · exact (h e he).1
      · exact (h e he).2
    · intro h e he
      exact ⟨h ⟨e, he, Or.inl rfl⟩, h ⟨e, he, Or.inr rfl⟩⟩
  rw [← independent]
  change _ = ∑ S ∈ E.inf (fun e => (bad e)ᶜ), weight S
  rw [inclusion_exclusion_sum_inf_compl]
  apply sum_congr rfl
  intro F _
  rw [allBad]
  simp only [weight, sum_weight_supersets, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

private lemma sum_independent_by_card {k : ℕ} (E : Finset (Fin k × Fin k)) (x : ℝ) :
    (∑ S ∈ univ.filter (fun S : Finset (Fin k) => ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)),
        x ^ S.card * (1 - x) ^ (k - S.card)) =
      ∑ m ∈ range (k + 1),
        ((univ.filter fun S : Finset (Fin k) =>
            S.card = m ∧ ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) *
          x ^ m * (1 - x) ^ (k - m) := by
  classical
  let independent := univ.filter (fun S : Finset (Fin k) => ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S))
  have hcard (S : Finset (Fin k)) (_ : S ∈ independent) : S.card ∈ range (k + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (by simpa using card_le_univ S))
  change (∑ S ∈ independent, x ^ S.card * (1 - x) ^ (k - S.card)) = _
  rw [← sum_fiberwise_of_maps_to' hcard (fun m => x ^ m * (1 - x) ^ (k - m))]
  apply sum_congr rfl
  intro m _
  simp only [independent, filter_filter, and_comm (b := _ = _), sum_const, nsmul_eq_mul, mul_assoc]

end CoprimalityDensityIndependentSet

-- The factor identity holds for every finite set of ordered pairs.
set_option linter.unusedVariables false in
/-- **Hu's independent-set formula for the coprimality density.** Let $k$ be a natural number, let
$E$ be a set of pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$
with edge set $E$, and let $A_G$ be its coprimality density. For $0 \le m \le k$, let $i_m(G)$ be
the number of independent sets of $G$ of size $m$, that is, of sets $S \subseteq \{1, \dots, k\}$
with $|S| = m$ such that no edge of $E$ has both endpoints in $S$. Then
$$A_G = \prod_p \sum_{m=0}^{k} \frac{i_m(G)}{p^m} \left(1 - \frac{1}{p}\right)^{k-m},$$
the product running over all primes $p$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`). -/
public theorem coprimalityDensity_eq_independent_set_product {k : ℕ}
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ m ∈ range (k + 1),
        ((univ.filter fun S : Finset (Fin k) =>
            S.card = m ∧ ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) /
          ((p : ℕ) : ℝ) ^ m * (1 - 1 / ((p : ℕ) : ℝ)) ^ (k - m) := by
  unfold coprimalityDensity
  apply tprod_congr
  intro p
  have h := (CoprimalityDensityIndependentSet.sum_edges_eq_sum_independent E
    (1 / ((p : ℕ) : ℝ))).trans
    (CoprimalityDensityIndependentSet.sum_independent_by_card E (1 / ((p : ℕ) : ℝ)))
  simpa only [one_div_pow, mul_one_div] using h

end MetaMathlibExt
