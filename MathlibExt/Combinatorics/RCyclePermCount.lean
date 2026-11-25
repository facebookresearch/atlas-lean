/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Counting permutations with all cycles of length $r$

Mathlib counts permutations of a given nontrivial cycle type. For $r \ge 2$, an $r$-cycle
permutation has no fixed points, so its cycle type consists of exactly $n/r$ copies of $r$.
-/

namespace MetaMathlibExt

private theorem isRCyclePerm_iff_cycleType_replicate {r n : ℕ} (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin n)) :
    IsRCyclePerm r n σ ↔ r ∣ n ∧ σ.cycleType = Multiset.replicate (n / r) r := by
  rw [isRCyclePerm_iff]
  constructor
  · rintro ⟨hfixed, hlength⟩
    have hs : σ.support = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i =>
      Equiv.Perm.mem_support.mpr fun hi => by
        have h := hfixed i hi
        omega
    have ht : σ.cycleType = Multiset.replicate σ.cycleType.card r :=
      Multiset.eq_replicate.mpr ⟨rfl, hlength⟩
    have hn : σ.cycleType.card * r = n := by
      have hsum := congrArg Multiset.sum ht
      rw [σ.sum_cycleType, hs, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate,
        nsmul_eq_mul, Nat.cast_id] at hsum
      exact hsum.symm
    have hdiv : n / r = σ.cycleType.card :=
      (congrArg (· / r) hn.symm).trans (Nat.mul_div_cancel _ (by omega))
    refine ⟨⟨σ.cycleType.card, by simpa [Nat.mul_comm] using hn.symm⟩, ?_⟩
    rwa [hdiv]
  · rintro ⟨hdvd, ht⟩
    have hs : σ.support.card = Fintype.card (Fin n) := by
      rw [← σ.sum_cycleType, ht, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
        Nat.div_mul_cancel hdvd, Fintype.card_fin]
    have hu := Finset.eq_univ_of_card _ hs
    refine ⟨fun i hi => ?_, fun k hk => ?_⟩
    · exact False.elim (Equiv.Perm.mem_support.mp (hu ▸ Finset.mem_univ i) hi)
    · exact (Multiset.eq_replicate.mp ht).2 k hk

/-- **Number of permutations with all cycles of length $r$.** Let $r \ge 2$ and $n \ge 0$. The
number of permutations of $n$ objects all of whose cycles, fixed points counted as cycles of
length one, have length exactly $r$ equals $n!/(r^{n/r}\,(n/r)!)$ if $r$ divides $n$, and $0$
otherwise.

When $r$ divides $n$ the quotient is an integer, so the natural-number division is exact.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 25 (`jis-2025-25.5.7-cor-25`). -/
public theorem card_rCyclePerm (r n : ℕ) (hr : 2 ≤ r) :
    (Finset.univ.filter (IsRCyclePerm r n)).card =
      if r ∣ n then n.factorial / (r ^ (n / r) * (n / r).factorial) else 0 := by
  by_cases hdvd : r ∣ n
  · rw [ite_eq_left hdvd]
    have hfilter : Finset.univ.filter (IsRCyclePerm r n) =
        Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          σ.cycleType = Multiset.replicate (n / r) r) :=
      Finset.filter_congr fun σ _ => (isRCyclePerm_iff_cycleType_replicate hr σ).trans
        (and_iff_right hdvd)
    have hsum : (Multiset.replicate (n / r) r).sum = n := by
      rw [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Nat.div_mul_cancel hdvd]
    have hlength : ∀ k ∈ Multiset.replicate (n / r) r, 2 ≤ k := by
      intro k hk
      rw [Multiset.eq_of_mem_replicate hk]
      exact hr
    rw [hfilter, Equiv.Perm.card_of_cycleType, Fintype.card_fin, hsum,
      ite_eq_left ⟨le_rfl, hlength⟩, Nat.sub_self, Nat.factorial_zero, one_mul,
      Multiset.prod_replicate]
    by_cases hzero : n / r = 0 <;>
      simp [Multiset.toFinset_replicate, hzero, Multiset.count_replicate]
  · rw [ite_eq_right hdvd, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun {σ} _ hσ => hdvd ((isRCyclePerm_iff_cycleType_replicate hr σ).mp hσ).1

end MetaMathlibExt
