/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.MultipleZeta.CyclicSumFormula
public import MathlibExt.NumberTheory.MultipleZeta.OOZDuality
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Conjugacy classes of the symmetric group

The number of conjugacy classes of permutations of `Fin n` equals the number of
partitions of `n`, using the partition given by cycle lengths, including fixed points.

Reference: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (arXiv:2111.00051).
-/

namespace MetaMathlibExt

private theorem partition_surjective (α : Type*) [Fintype α] [DecidableEq α] :
    Function.Surjective (Equiv.Perm.partition (α := α)) := by
  intro p
  let m := p.parts.filter fun a => 2 ≤ a
  let ones := p.parts.filter fun a => ¬2 ≤ a
  have hones : ones = Multiset.replicate ones.card 1 := by
    apply Multiset.eq_replicate_card.mpr
    intro a ha
    obtain ⟨ha, hlt⟩ := Multiset.mem_filter.mp ha
    have hpos := p.parts_pos ha
    omega
  have hsum : m.sum + ones.card = Fintype.card α := by
    have h := Multiset.sum_filter_add_sum_filter_not (s := p.parts) (fun a => 2 ≤ a)
    change m.sum + ones.sum = p.parts.sum at h
    rw [hones] at h
    simpa only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one, p.parts_sum] using h
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff α (m := m)).mpr
    ⟨by omega, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  refine ⟨σ, Nat.Partition.ext ?_⟩
  rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
  have hcard : Fintype.card α - m.sum = ones.card := by omega
  rw [hcard, ← hones]
  exact Multiset.filter_add_not (fun a => 2 ≤ a) p.parts

/-- **Number of conjugacy classes of the symmetric group.** For every natural number $n$, the
number of conjugacy classes of the symmetric group $S_n$ equals the number $p(n)$ of partitions
of $n$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem card_conjClasses_perm_eq_card_partition (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card n.Partition := by
  let f : ConjClasses (Equiv.Perm (Fin n)) → (Fintype.card (Fin n)).Partition :=
    Quotient.lift Equiv.Perm.partition
      (fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective a
      obtain ⟨τ, rfl⟩ := ConjClasses.mk_surjective b
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr
        (Equiv.Perm.partition_eq_of_isConj.mpr hab)
    · intro p
      obtain ⟨σ, hσ⟩ := partition_surjective (Fin n) p
      exact ⟨ConjClasses.mk σ, hσ⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using Nat.card_eq_of_bijective f hf

end MetaMathlibExt
