/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# The overlap statistic on pairs of words

The overlap of a pair of words `(u, v)` is the number of positions of `v` whose letter occurs in
`u`. For a fixed first word using `j` distinct letters out of `k`, summing `q ^ overlap` over the
second words of length `r` gives `(q j + k - j) ^ r`, and `C(k, j) j! S(n, j)` words of length `n`
use exactly `j` distinct letters. Together these give the sum of `q ^ overlap` over all pairs of
words of equal length (`wordPairs_sameLength_overlap_sum`).
-/

namespace MetaMathlibExt

namespace WordPairOverlap

open Finset

/-- Summing `q ^ #{i | v i ∈ S}` over the words `v` of length `r` gives `(q #S + k - #S) ^ r`:
each position contributes `q` for a letter of `S` and `1` for any other letter. -/
private theorem sum_pow_card_filter_mem {k : ℕ} (S : Finset (Fin k)) (r : ℕ) (q : ℚ) :
    ∑ v : Fin r → Fin k, q ^ (univ.filter fun i => v i ∈ S).card =
      (q * S.card + (k - S.card : ℕ)) ^ r := by
  have hv (v : Fin r → Fin k) :
      q ^ (univ.filter fun i => v i ∈ S).card = ∏ i, if v i ∈ S then q else 1 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [hv]
  rw [← Fintype.sum_pow (fun c => if c ∈ S then q else 1) r, sum_ite, sum_const, sum_const,
    filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff, ← compl_eq_univ_sdiff, card_compl,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_comm]

/-- The letters of `Fin.cons a u` are `a` and the letters of `u`. -/
private theorem image_cons {k n : ℕ} (a : Fin k) (u : Fin n → Fin k) :
    univ.image (Fin.cons a u : Fin (n + 1) → Fin k) = insert a (univ.image u) := by
  ext b
  simp [Fin.exists_fin_succ, eq_comm]

/-- The number of words of length `n` over `k` letters that use exactly `j` distinct letters is
`k (k - 1) ⋯ (k - j + 1) S(n, j)`. -/
private theorem card_filter_card_image (k n j : ℕ) :
    (univ.filter fun u : Fin n → Fin k => (univ.image u).card = j).card =
      k.descFactorial j * n.stirlingSecond j := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ j => simp
  | succ n ih =>
    cases j with
    | zero =>
      rw [Nat.stirlingSecond_succ_zero, mul_zero, card_eq_zero, filter_eq_empty_iff]
      intro u _
      rw [card_eq_zero, image_eq_empty]
      exact univ_nonempty.ne_empty
    | succ j =>
      -- Adding a first letter `a` to a word with letter set `S` keeps `#S` letters if `a ∈ S`
      -- and adds one letter otherwise.
      have hinner (S : Finset (Fin k)) :
          (∑ a : Fin k, if (insert a S).card = j + 1 then 1 else 0) =
            (if S.card = j + 1 then j + 1 else 0) + (if S.card = j then k - j else 0) := by
        rw [← sum_add_sum_compl S]
        congr 1
        · have h (a : Fin k) (ha : a ∈ S) : (if (insert a S).card = j + 1 then 1 else 0) =
              if S.card = j + 1 then 1 else 0 := by
            rw [insert_eq_of_mem ha]
          rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_boole]
          split_ifs with hS <;> simp [hS]
        · have h (a : Fin k) (ha : a ∈ Sᶜ) : (if (insert a S).card = j + 1 then 1 else 0) =
              if S.card + 1 = j + 1 then 1 else 0 := by
            rw [card_insert_of_notMem (mem_compl.1 ha)]
          rw [sum_congr rfl h, sum_const, smul_eq_mul, card_compl, Fintype.card_fin]
          split_ifs <;> omega
      calc (univ.filter fun u : Fin (n + 1) → Fin k => (univ.image u).card = j + 1).card
          = ∑ u : Fin (n + 1) → Fin k, if (univ.image u).card = j + 1 then 1 else 0 :=
            card_filter _ _
        _ = ∑ p : Fin k × (Fin n → Fin k),
              if (univ.image (Fin.cons p.1 p.2 : Fin (n + 1) → Fin k)).card = j + 1 then 1 else 0 :=
            (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin k) _ _ fun _ => rfl).symm
        _ = ∑ u : Fin n → Fin k, ∑ a : Fin k,
              if (insert a (univ.image u)).card = j + 1 then 1 else 0 := by
            rw [Fintype.sum_prod_type, sum_comm]
            simp only [image_cons]
        _ = ∑ u : Fin n → Fin k, ((if (univ.image u).card = j + 1 then j + 1 else 0) +
              (if (univ.image u).card = j then k - j else 0)) := by
            simp only [hinner]
        _ = (univ.filter fun u : Fin n → Fin k => (univ.image u).card = j + 1).card * (j + 1) +
              (univ.filter fun u : Fin n → Fin k => (univ.image u).card = j).card * (k - j) := by
            rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, smul_eq_mul,
              smul_eq_mul]
        _ = _ := by
          rw [ih, ih, Nat.stirlingSecond_succ_succ, Nat.descFactorial_succ]
          ring

/-- The sum of `q ^ overlap` over pairs `(u, v)` of words over `k` letters, `u` of length `n ≥ 1`
and `v` of length `r`. -/
private theorem sum_overlap (k n r : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p ∈ (univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))),
        q ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card =
      ∑ j ∈ Icc 1 k, (k.choose j : ℚ) * j.factorial * n.stirlingSecond j *
        (q * j + (k - j : ℕ)) ^ r := by
  have hmaps : ∀ u ∈ (univ : Finset (Fin n → Fin k)), (univ.image u).card ∈ Icc 1 k := by
    intro u _
    rw [mem_Icc]
    refine ⟨card_pos.2 (Nonempty.image ⟨⟨0, hn⟩, mem_univ _⟩ u), ?_⟩
    exact (card_le_univ _).trans (Fintype.card_fin k).le
  rw [Fintype.sum_prod_type]
  simp only [sum_pow_card_filter_mem]
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun j _ => ?_
  have h (u : Fin n → Fin k)
      (hu : u ∈ univ.filter fun u : Fin n → Fin k => (univ.image u).card = j) :
      (q * ((univ.image u).card : ℚ) + ((k - (univ.image u).card : ℕ) : ℚ)) ^ r =
        (q * j + ((k - j : ℕ) : ℚ)) ^ r := by
    rw [(mem_filter.1 hu).2]
  rw [sum_congr rfl h, sum_const, card_filter_card_image, nsmul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

end WordPairOverlap

open WordPairOverlap

/-- **Overlap statistic on pairs of words of equal length.** Fix natural numbers $k$ and $n \ge 1$
and a rational number $q$. For words $u$ and $v$ over an alphabet of $k$ letters, the overlap of
$(u, v)$ is the number of positions of $v$ whose letter occurs in $u$. Let $S(n, j)$ denote the
Stirling numbers of the second kind. Then the sum of $q^{\text{overlap}}$ over all pairs $(u, v)$
of words of length $n$ equals $\sum_{j=1}^{k} \binom{k}{j} \, j! \, S(n, j) \, (qj + k - j)^n$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24
(2024), Article A107, Corollary 3 (`integers-2024-A107-cor-3`). -/
public theorem wordPairs_sameLength_overlap_sum (k n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))),
        q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
      ∑ j ∈ Finset.Icc 1 k,
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * (q * j + (k - j : ℕ)) ^ n :=
  sum_overlap k n n hn q

end MetaMathlibExt
