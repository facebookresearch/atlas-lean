/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Fixed-size subsets with even intersections

Append a coordinate `1` to each incidence vector so that a zero sum also records even
cardinality. The augmented vectors of a smallest subset with the same sum as the full interval
are linearly independent. The complement has even cardinality and at least `m` elements.
Pairs with the same incidence vector can then be deleted until exactly `m` elements remain.

## References

- Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants of `ℤ_n`*,
  INTEGERS 24 (2024), Article A38, pp. 1–16, Lemma 5.4.
- Simon Griffiths, *The Erdős–Ginzberg–Ziv theorem with units*, Discrete Mathematics 308 (2008),
  pp. 5473–5484, Lemma 2.5 (the original result cited in Lemma 5.4).
-/

namespace MetaMathlibExt

private def withParity {a : ℕ} (x : Fin a → ZMod 2) : Option (Fin a) → ZMod 2 :=
  fun i => i.elim 1 x

private theorem even_card_of_sum_withParity_eq_zero {ι : Type*} {a : ℕ}
    (v : ι → Fin a → ZMod 2) (s : Finset ι) (hs : ∑ j ∈ s, withParity (v j) = 0) :
    Even s.card := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  simpa [Finset.sum_apply, withParity] using congrFun hs none

private theorem exists_small_complement {ι : Type*} [DecidableEq ι] {a : ℕ}
    (v : ι → Option (Fin a) → ZMod 2) (s : Finset ι) :
    ∃ t ⊆ s, t.card ≤ a + 1 ∧ ∑ j ∈ s \ t, v j = 0 := by
  classical
  let P (n : ℕ) := ∃ t ⊆ s, t.card = n ∧ ∑ j ∈ t, v j = ∑ j ∈ s, v j
  have hex : ∃ n, P n := ⟨s.card, s, Finset.Subset.rfl, rfl, rfl⟩
  obtain ⟨t, hts, htcard, htsum⟩ := Nat.find_spec hex
  have hlin : LinearIndepOn (ZMod 2) v t := by
    -- Over `ZMod 2` a nonzero relation is the sum over its nonempty support.
    by_contra h
    obtain ⟨c, hc, j, hj, hjc⟩ := not_linearIndepOn_finset_iff.mp h
    let u := t.filter fun i => c i ≠ 0
    have hut : u ⊆ t := Finset.filter_subset _ _
    have hu : u.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hjc⟩⟩
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have huzero : ∑ i ∈ u, v i = 0 := by
      change ∑ i ∈ t.filter (fun i => c i ≠ 0), v i = 0
      rw [Finset.sum_filter]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
      rcases h01 (c i) with hzero | hone
      · simp [hzero]
      · simp [hone]
    have hrem : ∑ i ∈ t \ u, v i = ∑ i ∈ s, v i := by
      rw [Finset.sum_sdiff_eq_sub hut, huzero, sub_zero, htsum]
    have hlt : (t \ u).card < Nat.find hex := by
      rw [← htcard]
      exact Finset.card_lt_card (Finset.sdiff_ssubset hut hu)
    exact Nat.find_min hex hlt ⟨t \ u, Finset.sdiff_subset.trans hts, rfl, hrem⟩
  have hbound := LinearIndependent.fintype_card_le_finrank hlin
  refine ⟨t, hts, ?_, ?_⟩
  · simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_option] using hbound
  · rw [Finset.sum_sdiff_eq_sub hts, htsum, sub_self]

private theorem exists_subset_card_sum_withParity_eq_zero {ι : Type*} {a m : ℕ}
    (v : ι → Fin a → ZMod 2) (hm : 2 ^ a ≤ m) (hme : Even m) (s : Finset ι) :
    m ≤ s.card → (∑ j ∈ s, withParity (v j)) = 0 →
      ∃ t ⊆ s, t.card = m ∧ ∑ j ∈ t, withParity (v j) = 0 := by
  classical
  refine s.strongInductionOn ?_
  intro s ih hle hs
  by_cases heq : s.card = m
  · exact ⟨s, Finset.Subset.rfl, heq, hs⟩
  -- There are only `2 ^ a` incidence vectors: above the target size, two must be equal.
  have hnoninj : ¬ Function.Injective (fun j : s => v j) := by
    intro hinj
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_coe, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnoninj
  change v x.val = v y.val at hxy
  have hne' : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  let p : Finset ι := {x.val, y.val}
  have hp : p ⊆ s := by simp [p, Finset.insert_subset_iff, x.property, y.property]
  have hpcard : p.card = 2 := by simp [p, hne']
  have hpzero : ∑ j ∈ p, withParity (v j) = 0 := by
    change ∑ j ∈ ({x.val, y.val} : Finset ι), withParity (v j) = 0
    rw [Finset.sum_pair hne', hxy]
    have hself : ∀ z : ZMod 2, z + z = 0 := by decide
    exact funext fun i => hself _
  have hsum : ∑ j ∈ s \ p, withParity (v j) = 0 := by
    rw [Finset.sum_sdiff_eq_sub hp, hpzero, hs, sub_zero]
  have hcard : (s \ p).card = s.card - 2 := by
    rw [Finset.card_sdiff_of_subset hp, hpcard]
  have htarget : m ≤ (s \ p).card := by
    have hse := even_card_of_sum_withParity_eq_zero v s hs
    rw [Nat.even_iff] at hse hme
    omega
  obtain ⟨t, ht, htm, htz⟩ := ih _ (Finset.sdiff_ssubset hp ⟨x.val, by simp [p]⟩) htarget hsum
  exact ⟨t, ht.trans Finset.sdiff_subset, htm, htz⟩

/-- **An $m$-subset of $\{1, \dots, m + a\}$ meeting $a$ given sets evenly.** Let $m$ be even with
$2^a \le m$, and let $X_1, \dots, X_a$ be finite sets of natural numbers. Then there is a set
$Y \subseteq \{1, \dots, m + a\}$ with $|Y| = m$ such that $|Y \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 5.4 (`integers-2024-A38-lem-5-4`). -/
public theorem exists_card_even_inter {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 (m + a) ∧ Y.card = m ∧ ∀ i, Even (Y ∩ X i).card := by
  classical
  let s := Finset.Icc 1 (m + a)
  let v (j : ℕ) (i : Fin a) : ZMod 2 := if j ∈ X i then 1 else 0
  have hs : s.card = m + a := by simp [s, Nat.card_Icc]
  obtain ⟨t, hts, htcard, hsum⟩ := exists_small_complement (fun j => withParity (v j)) s
  have hge : m ≤ (s \ t).card := by
    have hcard := Finset.card_sdiff_of_subset hts
    have hpar := even_card_of_sum_withParity_eq_zero v (s \ t) hsum
    rw [Nat.even_iff] at hpar hme
    omega
  obtain ⟨Y, hY, hYm, hYsum⟩ := exists_subset_card_sum_withParity_eq_zero v hm hme _ hge hsum
  refine ⟨Y, hY.trans Finset.sdiff_subset, hYm, fun i => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, ← Finset.filter_mem_eq_inter, Finset.natCast_card_filter]
  simpa [Finset.sum_apply, withParity, v] using congrFun hYsum (some i)

end MetaMathlibExt
