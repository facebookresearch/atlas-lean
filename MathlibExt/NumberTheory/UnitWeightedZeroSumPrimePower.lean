/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Unit-weighted zero sums modulo an odd prime power

Every residue is a sum of two units. Multiplication by a unit permutes the units, so the
two selected terms can contribute the negative of the sum of the remaining terms.
-/

namespace MetaMathlibExt
namespace unit_weighted_zero_sum_prime_power

private theorem exists_units_add_eq {R : Type*} [CommRing R] [IsLocalRing R]
    (h₂ : IsUnit (2 : R)) (t : R) : ∃ u v : Rˣ, (u : R) + v = t := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self t with ⟨u, rfl⟩ | ⟨v, hv⟩
  · exact ⟨h₂.unit * u, -u, by simp [two_mul]⟩
  · exact ⟨1, -v, by simp [hv]⟩

end unit_weighted_zero_sum_prime_power

open unit_weighted_zero_sum_prime_power in
/-- **Unit-weighted zero sums modulo an odd prime power.** Let $p$ be an odd prime, let $r$ and
$k$ be natural numbers, and let $x_1, \dots, x_k \in \mathbb{Z}/p^r\mathbb{Z}$. Suppose that for
at least two indices $i$ the least nonnegative representative of $x_i$ is coprime to $p$. Then
there are units $a_1, \dots, a_k$ of $\mathbb{Z}/p^r\mathbb{Z}$ with
$a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 16
(`jis-2024-24.1.7-lem-16`). -/
public theorem unit_weighted_zero_sum_prime_power (p r k : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (x : Fin k → ZMod (p ^ r))
    (h : 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    ∃ a : Fin k → ZMod (p ^ r), (∀ i, a i ∈ {z : ZMod (p ^ r) | IsUnit z}) ∧
      ∑ i, a i * x i = 0 := by
  classical
  by_cases hr : r = 0
  · have : Subsingleton (ZMod (p ^ r)) := by
      rw [hr, pow_zero]
      infer_instance
    exact ⟨fun _ => 1, fun _ => isUnit_one, Subsingleton.elim _ _⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨hr⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h
  have unit_of_mem (l : Fin k) (hl : l ∈ Finset.univ.filter fun l => Nat.Coprime (x l).val p) :
      IsUnit (x l) := by
    have hcop := (Finset.mem_filter.mp hl).2.pow_right r
    simpa using (ZMod.isUnit_iff_coprime _ _).mpr hcop
  obtain ⟨ui, hui⟩ := unit_of_mem i hi
  obtain ⟨uj, huj⟩ := unit_of_mem j hj
  have h₂ : IsUnit (2 : ZMod (p ^ r)) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr
      ((Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_right r)
  let rest := (Finset.univ.erase i).erase j
  obtain ⟨u, v, huv⟩ := exists_units_add_eq h₂ (-(∑ l ∈ rest, x l))
  let a (l : Fin k) : (ZMod (p ^ r))ˣ := if l = i then u / ui else if l = j then v / uj else 1
  refine ⟨fun l => a l, fun l => (a l).isUnit, ?_⟩
  have hj' : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ hj']
  have hrest : ∑ l ∈ rest, (a l : ZMod (p ^ r)) * x l = ∑ l ∈ rest, x l := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hlj, hli⟩ := Finset.mem_erase.mp hl
    simp [a, hlj, (Finset.mem_erase.mp hli).1]
  rw [hrest]
  simp [a, hij.symm, ← hui, ← huj, ← Units.val_mul, ← add_assoc, huv]

end MetaMathlibExt
