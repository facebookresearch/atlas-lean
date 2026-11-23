/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.Perm.Basic
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
import Mathlib.Tactic.Ring

/-!
# Inversions of a random permutation

An inversion of a permutation `σ` of `Fin n` (in one-line notation `σ 0, σ 1, …, σ (n - 1)`)
is a pair of positions `i < j` with `σ j < σ i`. Each of the `n (n - 1) / 2` pairs of positions
is inverted in exactly half of the `n!` permutations, so the expected number of inversions of a
uniformly random permutation is `n (n - 1) / 4`. Inversions measure the work of sorting by
adjacent exchanges: straight insertion sort moves an element past each element that forms an
inversion with it.

Source: T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
3rd ed., MIT Press, 2009, Exercise 5.2-5 (inversions of a uniform random permutation, to be
computed with indicator random variables; inversions are defined in Problem 2-4). The exercise
asks for the expectation without stating it; the indicator computation gives `n (n - 1) / 4`,
which is the statement proved here.

## Main definitions

* `permInversions σ`, `permInversionCount σ`: the inversions of `σ` and their number.

## Main results

* `permInversionCount_inv`: `inv(σ⁻¹) = inv(σ)` (Stanley, *Enumerative Combinatorics*, Vol. 1,
  2nd ed., Proposition 1.3.14).
* `two_mul_card_filter_lt`: for distinct positions `i ≠ j`, exactly half of the permutations put
  `σ j` below `σ i`.
* `four_mul_sum_permInversionCount`: `4 ∑_σ inv(σ) = n! · n (n - 1)`.
* `expectENN_permInversionCount`, `expectENN_permInversionCount_toReal`: under the uniform
  distribution on permutations of `Fin n`, the expected number of inversions is `n (n - 1) / 4`.
-/

@[expose] public section

open scoped ENNReal

namespace MetaMathlibExt

variable {n : ℕ}

/-- **Inversions of a permutation.** The pairs of positions `(i, j)` with `i < j` and
`σ j < σ i`, for a permutation `σ` of `Fin n` read in one-line notation. -/
def permInversions (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- **Number of inversions of a permutation.** The number `inv(σ)` of pairs of positions
`i < j` with `σ j < σ i`. -/
def permInversionCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (permInversions σ).card

/-- **A permutation and its inverse have the same number of inversions** (Stanley,
*Enumerative Combinatorics*, Vol. 1, 2nd ed., Proposition 1.3.14). The pair of positions
`(i, j)` is an inversion of `σ` exactly when the pair `(σ j, σ i)` is an inversion of `σ⁻¹`. -/
theorem permInversionCount_inv (σ : Equiv.Perm (Fin n)) :
    permInversionCount σ⁻¹ = permInversionCount σ := by
  refine Finset.card_bij' (fun p _ => (σ⁻¹ p.2, σ⁻¹ p.1)) (fun p _ => (σ p.2, σ p.1))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [permInversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · intro p hp
    simp only [permInversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · intro p _; simp
  · intro p _; simp

/-- **Each pair of positions is inverted by exactly half of the permutations.** For distinct
positions `i ≠ j` of `Fin n`, twice the number of permutations `σ` with `σ j < σ i` is `n!`. -/
theorem two_mul_card_filter_lt (i j : Fin n) (hij : i ≠ j) :
    2 * (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ j < σ i).card = n.factorial := by
  set A := Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ j < σ i
  set B := Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i < σ j
  have hAB : A.card = B.card := by
    refine Finset.card_bij' (fun σ _ => σ * Equiv.swap i j) (fun σ _ => σ * Equiv.swap i j)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using hσ
    · intro σ hσ
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using hσ
    · intro σ _
      simp [mul_assoc]
    · intro σ _
      simp [mul_assoc]
  have hunion : A ∪ B = Finset.univ := by
    ext σ
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hne : σ j ≠ σ i := fun h => hij (σ.injective h).symm
    exact lt_or_gt_of_ne hne
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro σ _ h1 h2
    exact lt_asymm h1 h2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hcard
  omega

/-- **Number of pairs of positions.** Twice the number of pairs of positions `i < j` in `Fin n`
is `n (n - 1)`. -/
theorem two_mul_card_filter_fst_lt_snd :
    2 * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n * (n - 1) := by
  set L := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
  set G := Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1
  have hLG : L.card = G.card := by
    refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_ <;>
      simp [L, G]
  have hunion : L ∪ G = (Finset.univ : Finset (Fin n)).offDiag := by
    ext p
    simp only [L, G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag]
    exact ⟨fun h => h.elim ne_of_lt (fun h => (ne_of_lt h).symm), lt_or_gt_of_ne⟩
  have hdisj : Disjoint L G := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1 h2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  have : n * n - n = n * (n - 1) := by
    rw [Nat.mul_sub, mul_one]
  omega

/-- **Total number of inversions over all permutations.** For every `n`,
`4 ∑_{σ ∈ S_n} inv(σ) = n! · n (n - 1)`. -/
theorem four_mul_sum_permInversionCount :
    4 * ∑ σ : Equiv.Perm (Fin n), permInversionCount σ = n.factorial * (n * (n - 1)) := by
  have hswap : ∑ σ : Equiv.Perm (Fin n), permInversionCount σ =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ p.2 < σ p.1).card := by
    simp only [permInversionCount, permInversions, Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.1 < p.2 <;> simp [hp]
  have hpair : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      2 * (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ p.2 < σ p.1).card =
        n.factorial := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact two_mul_card_filter_lt p.1 p.2 (ne_of_lt hp)
  have h2 : 2 * ∑ σ : Equiv.Perm (Fin n), permInversionCount σ =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card * n.factorial := by
    rw [hswap, Finset.mul_sum, Finset.sum_congr rfl hpair, Finset.sum_const, smul_eq_mul]
  have hL := two_mul_card_filter_fst_lt_snd (n := n)
  calc 4 * ∑ σ : Equiv.Perm (Fin n), permInversionCount σ
      = 2 * (2 * ∑ σ : Equiv.Perm (Fin n), permInversionCount σ) := by ring
    _ = 2 * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card * n.factorial := by
        rw [h2]; ring
    _ = n.factorial * (n * (n - 1)) := by rw [hL]; ring

/-- **Expected number of inversions of a random permutation.** Under the uniform distribution
on the permutations of `Fin n`, the expected number of inversions, valued in `[0, ∞]`, is
`n (n - 1) / 4`. -/
theorem expectENN_permInversionCount :
    (PMF.uniformFintype (Equiv.Perm (Fin n))).expectENN
        (fun σ => (permInversionCount σ : ℝ≥0∞)) =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / 4 := by
  rw [PMF.expectENN_uniformOfFintype, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_sum]
  have h4 := four_mul_sum_permInversionCount (n := n)
  set S := ∑ σ : Equiv.Perm (Fin n), permInversionCount σ
  have hfac : ((n.factorial : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfac' : ((n.factorial : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hS : (S : ℝ≥0∞) = ((n.factorial : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / 4 := by
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
    exact_mod_cast h4
  rw [hS, mul_div_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hfac hfac', one_mul]

/-- **Expected number of inversions, as a real number.** Under the uniform distribution on the
permutations of `Fin n`, the expected number of inversions is `n (n - 1) / 4`. -/
theorem expectENN_permInversionCount_toReal :
    ((PMF.uniformFintype (Equiv.Perm (Fin n))).expectENN
        (fun σ => (permInversionCount σ : ℝ≥0∞))).toReal =
      (n : ℝ) * (n - 1) / 4 := by
  rw [expectENN_permInversionCount, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rcases n with _ | n
  · simp
  · push_cast
    norm_num

end MetaMathlibExt
