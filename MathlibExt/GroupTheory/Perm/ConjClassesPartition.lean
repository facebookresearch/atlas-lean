/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-!
# Conjugacy classes of permutations and integer partitions

The conjugacy class of a permutation is determined by its partition of cycle lengths. To
realize a partition, use Mathlib's existence theorem for the parts of size at least two;
the sum of the parts then determines the number of fixed points.

## References

* Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
  pp. 1–41, Lemma 4 (p. 38).
-/

namespace MetaMathlibExt

private theorem exists_perm_partition {n : ℕ} (p : (Fintype.card (Fin n)).Partition) :
    ∃ σ : Equiv.Perm (Fin n), σ.partition = p := by
  let m := p.parts.filter (2 ≤ ·)
  let k := p.parts.count 1
  have hparts : m + Multiset.replicate k 1 = p.parts := by
    have hones : p.parts.filter (fun a => ¬ 2 ≤ a) = p.parts.filter (· = 1) := by
      apply Multiset.filter_congr
      intro a ha
      have := p.parts_pos ha
      omega
    rw [show k = p.parts.count 1 from rfl, ← Multiset.filter_eq', ← hones]
    exact Multiset.filter_add_not _ _
  have hsum : m.sum + k = Fintype.card (Fin n) := by
    simpa [Multiset.sum_add, Multiset.sum_replicate] using
      (congrArg Multiset.sum hparts).trans p.parts_sum
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n) (m := m)).2
    ⟨by omega, fun _ h => (Multiset.mem_filter.mp h).2⟩
  have hsupp : σ.support.card = m.sum :=
    (Equiv.Perm.sum_cycleType σ).symm.trans (congrArg Multiset.sum hσ)
  have hk : Fintype.card (Fin n) - m.sum = k := by omega
  refine ⟨σ, Nat.Partition.ext ?_⟩
  rw [Equiv.Perm.parts_partition, hσ, hsupp, hk, hparts]

/-- **Cycle type classifies conjugacy classes of permutations.** For every natural number $n$,
there is a bijection from the set of conjugacy classes of the symmetric group $S_n$ to the set
of partitions of $n$ that sends the class of each permutation $\sigma$ to the cycle type of
$\sigma$: the partition of $n$ formed by the lengths of the cycles of $\sigma$, fixed points
counting as cycles of length $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem exists_conjClasses_perm_equiv_partition (n : ℕ) :
    ∃ e : ConjClasses (Equiv.Perm (Fin n)) ≃ (Fintype.card (Fin n)).Partition,
      ∀ σ : Equiv.Perm (Fin n), e (ConjClasses.mk σ) = σ.partition := by
  let f : ConjClasses (Equiv.Perm (Fin n)) → (Fintype.card (Fin n)).Partition :=
    Quotient.lift Equiv.Perm.partition fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep a
      obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep b
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (Equiv.Perm.partition_eq_of_isConj.mpr h)
    · intro p
      obtain ⟨σ, hσ⟩ := exists_perm_partition p
      exact ⟨ConjClasses.mk σ, hσ⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

end MetaMathlibExt
