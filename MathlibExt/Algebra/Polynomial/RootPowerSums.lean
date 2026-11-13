/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The support-sum argument and Vandermonde strategy are adapted from
`P2M/Sol/S_Polynomial_eq_of_forall_sum_roots_pow_eq.lean` in
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, lines 15-111.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: the source repository's AI agents; no individual author is named
for this file in its NOTICE or ATTRIBUTION.md.
-/

module

public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Reconstruction from positive power sums

Equal cardinality and equal positive power sums determine a multiset over a
characteristic-zero field, including its zero multiplicity. Consequently,
split monic polynomials of equal degree are determined by those root sums.
-/

public section

open scoped BigOperators

namespace Multiset

variable {K : Type*} [Field K]

private lemma sum_pow_eq_sum_count [DecidableEq K] (s : Multiset K)
    (U : Finset K) (hs : s.toFinset ⊆ U) (n : ℕ) :
    (s.map (fun x => x ^ n)).sum = ∑ x ∈ U, (s.count x : K) * x ^ n := by
  rw [Finset.sum_multiset_map_count]
  simp_rw [nsmul_eq_mul]
  exact Finset.sum_subset hs fun x _ hx => by
    rw [count_eq_zero_of_notMem (by simpa using hx), Nat.cast_zero, zero_mul]

/-- Equal cardinality and equal positive power sums determine a multiset.
Zero entries and repeated entries are allowed. -/
theorem eq_of_card_eq_of_forall_sum_pow_eq [CharZero K] (s t : Multiset K)
    (hcard : s.card = t.card)
    (h : ∀ n : ℕ, 0 < n →
      (s.map (fun x => x ^ n)).sum = (t.map (fun x => x ^ n)).sum) :
    s = t := by
  classical
  have hall (n : ℕ) :
      (s.map (fun x => x ^ n)).sum = (t.map (fun x => x ^ n)).sum := by
    cases n with
    | zero => simp [hcard]
    | succ n => exact h _ (Nat.succ_pos n)
  let U := s.toFinset ∪ t.toFinset
  let e : Fin U.card ≃ U := U.equivFin.symm
  let f : Fin U.card → K := fun i => (e i : K)
  let w : Fin U.card → K := fun i => (s.count (f i) : K) - t.count (f i)
  have hf : Function.Injective f := fun _ _ hij => e.injective (Subtype.ext hij)
  have hw : w = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro i
    change (∑ j, ((s.count (f j) : K) - t.count (f j)) * f j ^ (i : ℕ)) = 0
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have hs (a : Multiset K) (ha : a.toFinset ⊆ U) :
        (∑ j, (a.count (f j) : K) * f j ^ (i : ℕ)) =
          (a.map (fun x => x ^ (i : ℕ))).sum := by
      rw [sum_pow_eq_sum_count a U ha, ← Finset.sum_coe_sort U]
      exact e.sum_comp (fun x : U => (a.count (x : K) : K) * (x : K) ^ (i : ℕ))
    rw [hs s Finset.subset_union_left, hs t Finset.subset_union_right, hall,
      sub_self]
  ext x
  by_cases hx : x ∈ U
  · have he := congr_fun hw (e.symm ⟨x, hx⟩)
    simp only [w, f, Equiv.apply_symm_apply, Pi.zero_apply, sub_eq_zero] at he
    exact_mod_cast he
  · have hs : x ∉ s := fun hxs =>
      hx (Finset.mem_union_left _ (mem_toFinset.mpr hxs))
    have ht : x ∉ t := fun hxt =>
      hx (Finset.mem_union_right _ (mem_toFinset.mpr hxt))
    rw [count_eq_zero_of_notMem hs, count_eq_zero_of_notMem ht]

end Multiset

namespace Polynomial

/-- Split monic polynomials of equal degree over a characteristic-zero field
are equal if every positive power sum of their roots agrees.

Source: anthropics/fermats-last-theorem, entry433,
`Theorems/Thm_Polynomial_eq_of_forall_sum_roots_pow_eq.lean`, lines 7-12,
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
theorem eq_of_forall_sum_roots_pow_eq {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic)
    (hPs : P.Splits) (hQs : Q.Splits) (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum =
        (Q.roots.map (fun z => z ^ n)).sum) : P = Q := by
  have hcard : P.roots.card = Q.roots.card := by
    rw [← hPs.natDegree_eq_card_roots, ← hQs.natDegree_eq_card_roots, hdeg]
  have hroots := Multiset.eq_of_card_eq_of_forall_sum_pow_eq _ _ hcard h
  rw [hPs.eq_prod_roots_of_monic hP, hQs.eq_prod_roots_of_monic hQ, hroots]

end Polynomial
