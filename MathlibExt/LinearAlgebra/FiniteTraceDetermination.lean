/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Vandermonde
import MathlibExt.LinearAlgebra.Eigenspace.CharpolyPowTrace

/-!
# Characteristic polynomials from finitely many power traces

We compare the roots in an algebraic closure. The difference of their multiplicities, weighted
by the first power in the given interval, is in the kernel of a Vandermonde matrix.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.FiniteTraceDeterminationWanted

open Polynomial

private theorem multiset_eq_of_shifted_power_sums {E : Type*} [Field E] [CharZero E]
    (s t : Multiset E) (start : ℕ) (hs : 0 ∉ s) (ht : 0 ∉ t)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ s.card + t.card →
      (s.map (fun x ↦ x ^ (start + k))).sum = (t.map (fun x ↦ x ^ (start + k))).sum) : s = t := by
  classical
  let support := (s + t).toFinset
  let e : Fin support.card ≃ support := (Finset.equivFin support).symm
  let x (i : Fin support.card) : E := e i
  let weight (i : Fin support.card) : E :=
    ((s.count (x i) : E) - t.count (x i)) * x i ^ (start + 1)
  have hcard : support.card ≤ s.card + t.card := by
    simpa only [support, Multiset.card_add] using Multiset.toFinset_card_le (s + t)
  -- Extend the multiplicity sum for either multiset to the common support.
  have sum_counts (m : Multiset E) (hm : m.toFinset ⊆ support) (n : ℕ) :
      (m.map (fun a ↦ a ^ n)).sum = ∑ i, (m.count (x i) : E) * x i ^ n := by
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    calc
      ∑ a ∈ m.toFinset, (m.count a : E) * a ^ n =
          ∑ a ∈ support, (m.count a : E) * a ^ n := by
        apply Finset.sum_subset hm
        intro a _ ha
        have : a ∉ m := by simpa only [Multiset.mem_toFinset] using ha
        simp [Multiset.count_eq_zero.mpr this]
      _ = ∑ a : support, (m.count (a : E) : E) * (a : E) ^ n := by
        exact (Finset.sum_coe_sort support (fun a ↦ (m.count a : E) * a ^ n)).symm
      _ = _ := (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
  have hweight : weight = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := x)
    · exact Subtype.val_injective.comp e.injective
    intro i
    have hpow := h ((i : ℕ) + 1) (by omega) ((Nat.succ_le_of_lt i.isLt).trans hcard)
    have hleft : s.toFinset ⊆ support := by
      intro a ha
      simp [support, Multiset.mem_toFinset.mp ha]
    have hright : t.toFinset ⊆ support := by
      intro a ha
      simp [support, Multiset.mem_toFinset.mp ha]
    rw [sum_counts s hleft, sum_counts t hright] at hpow
    have hexp : start + 1 + (i : ℕ) = start + ((i : ℕ) + 1) := by omega
    simpa only [weight, mul_assoc, ← pow_add, hexp, sub_mul, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr hpow
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a ∈ support
  · let i := e.symm ⟨a, ha⟩
    have hi : x i = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
    have hne : a ≠ 0 := by
      rintro rfl
      simp [support, hs, ht] at ha
    have hw : ((s.count a : E) - t.count a) * a ^ (start + 1) = 0 := by
      simpa only [weight, hi, Pi.zero_apply] using congrFun hweight i
    have hcount := (mul_eq_zero.mp hw).resolve_right (pow_ne_zero _ hne)
    exact Nat.cast_injective (sub_eq_zero.mp hcount)
  · have hab : a ∉ s ∧ a ∉ t := by simpa [support, Multiset.mem_add] using ha
    rw [Multiset.count_eq_zero.mpr hab.1, Multiset.count_eq_zero.mpr hab.2]

universe u v w

private theorem zero_notMem_roots_charpoly_map {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) (hA : IsUnit A) :
    0 ∉ (A.charpoly.map (algebraMap K (AlgebraicClosure K))).roots := by
  intro h
  have he := Polynomial.isRoot_of_mem_roots h
  rw [Polynomial.IsRoot, ← map_zero (algebraMap K (AlgebraicClosure K)),
    Polynomial.eval_map, Polynomial.eval₂_at_apply] at he
  have he' : A.charpoly.eval 0 = 0 := (algebraMap K (AlgebraicClosure K)).injective he
  rw [A.eval_charpoly, map_zero, zero_sub] at he'
  exact ((LinearMap.isUnit_iff_isUnit_det (-A)).mp hA.neg).ne_zero he'

/-- The characteristic polynomial of an invertible endomorphism on a space of
dimension at most `r` is determined by traces on `2 * r` consecutive positive
powers. The starting offset `start` is arbitrary, and the two dimensions need
not be supplied as equal. This is the power-sum determination underlying
Deligne's Lemma 2.9, as used in Rojas León's proof of Theorem 4. -/
public theorem charpoly_eq_of_trace_powers
    {K : Type u} [Field K] [CharZero K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : Module.End K V) (B : Module.End K W) (r start : ℕ)
    (hV : Module.finrank K V ≤ r) (hW : Module.finrank K W ≤ r)
    (hA : IsUnit A) (hB : IsUnit B)
    (htrace : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * r →
      LinearMap.trace K V (A ^ (start + k)) =
        LinearMap.trace K W (B ^ (start + k))) :
    A.charpoly = B.charpoly := by
  let E := AlgebraicClosure K
  let f := algebraMap K E
  let p := A.charpoly.map f
  let q := B.charpoly.map f
  have hp : p.roots.card ≤ r := by
    apply (Polynomial.card_roots' p).trans
    change (A.charpoly.map f).natDegree ≤ r
    rwa [Polynomial.natDegree_map_eq_of_injective f.injective, A.charpoly_natDegree]
  have hq : q.roots.card ≤ r := by
    apply (Polynomial.card_roots' q).trans
    change (B.charpoly.map f).natDegree ≤ r
    rwa [Polynomial.natDegree_map_eq_of_injective f.injective, B.charpoly_natDegree]
  have hr : p.roots = q.roots := by
    apply multiset_eq_of_shifted_power_sums p.roots q.roots start
      (zero_notMem_roots_charpoly_map A hA) (zero_notMem_roots_charpoly_map B hB)
    intro k hk hkr
    have hbound : k ≤ 2 * r := by omega
    rw [LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow E A,
      LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow E B, htrace k hk hbound]
  apply Polynomial.map_injective f f.injective
  change p = q
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic (A.charpoly_monic.map f),
    (IsAlgClosed.splits q).eq_prod_roots_of_monic (B.charpoly_monic.map f), hr]

end MathlibExt.LinearAlgebra.FiniteTraceDeterminationWanted
