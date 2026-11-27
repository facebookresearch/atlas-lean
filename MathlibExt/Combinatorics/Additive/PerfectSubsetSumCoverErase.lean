/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover

/-!
# Removing one element from a perfect subset-sum cover

Erasing one element leaves unique representations of exactly half the group.
Translation by the erased element interchanges covered and uncovered elements.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

namespace perfectCover_erase_coverCount

private theorem coverCount_eq_sum_powerset {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (g : G) :
    coverCount (fun x : S => (x : G)) g =
      ∑ T ∈ S.powerset, if (∑ x ∈ T, x) = g then 1 else 0 := by
  calc
    coverCount (fun x : S => (x : G)) g =
        ∑ T : Finset S, if (∑ x ∈ T, (x : G)) = g then 1 else 0 := by simp [coverCount]
    _ = _ := by
      apply Finset.sum_nbij (fun T => T.map (Function.Embedding.subtype (· ∈ S)))
      · intro T _
        exact Finset.mem_powerset.mpr (fun _ hx => T.property_of_mem_map_subtype hx)
      · intro T _ U _ h
        exact Finset.map_injective _ h
      · intro T hT
        exact ⟨T.subtype (· ∈ S), Finset.mem_univ _, Finset.subtype_map_of_mem
          (Finset.mem_powerset.mp hT)⟩
      · intro T _
        rw [Finset.sum_map]
        rfl

end perfectCover_erase_coverCount

/-- **Removing one element from a perfect cover.** Let $G$ be a finite abelian group of order $2^n$,
let $S$ be a perfect cover of $G$, let $z \in S$ and let $S_1 = S \setminus \{z\}$. Then (a) every
element of $G$ is the sum of at most one subset of $S_1$, and exactly half of the $2^n$ elements
of $G$ are the sum of a subset of $S_1$; (b) if $g \in G$ is the sum of a subset of $S_1$ and $j$
is an integer with $j \ge 1$, then $g + 2jz$ is the sum of a subset of $S_1$ and $g + (2j-1)z$ is
not.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 7
(`jis-2025-25.7.8-lem-7`). -/
public theorem perfectCover_erase_coverCount {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {S : Finset G}
    (hS : IsPerfectCover S) {z : G} (hz : z ∈ S) :
    ((∀ g : G, coverCount (fun x : S.erase z => (x : G)) g ≤ 1) ∧
      2 * (Finset.univ.filter fun g : G =>
        coverCount (fun x : S.erase z => (x : G)) g = 1).card = 2 ^ n) ∧
    ∀ g : G, 1 ≤ coverCount (fun x : S.erase z => (x : G)) g → ∀ j : ℕ, 1 ≤ j →
      1 ≤ coverCount (fun x : S.erase z => (x : G)) (g + (2 * j) • z) ∧
        coverCount (fun x : S.erase z => (x : G)) (g + (2 * j - 1) • z) = 0 := by
  let c := coverCount (fun x : S.erase z => (x : G))
  have hsplit (g : G) : c g + c (g - z) = 1 := by
    have hfull : coverCount (fun x : S => (x : G)) g = 1 := hS g
    rw [← hfull]
    simp only [c, perfectCover_erase_coverCount.coverCount_eq_sum_powerset]
    conv_rhs => rw [← Finset.insert_erase hz, Finset.sum_powerset_insert (Finset.notMem_erase z S)]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    have hzT : z ∉ T := Finset.notMem_of_mem_powerset_of_notMem hT (Finset.notMem_erase z S)
    simp only [Finset.sum_insert hzT, add_comm z, eq_sub_iff_add_eq]
  have hstep (g : G) : c (g + z) + c g = 1 := by
    simpa only [add_sub_cancel_right] using hsplit (g + z)
  have hle (g : G) : c g ≤ 1 := by
    have := hsplit g
    omega
  have hcard : (Finset.univ.filter fun g => c g = 1).card = ∑ g, c g := by
    calc
      _ = ∑ g : G, if c g = 1 then 1 else 0 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g _
        have := hle g
        split <;> omega
  have hshift : (∑ g, c (g + z)) = ∑ g, c g := Equiv.sum_comp (Equiv.addRight z) c
  refine ⟨⟨hle, ?_⟩, ?_⟩
  · calc
      2 * (Finset.univ.filter fun g => c g = 1).card =
          (∑ g, c (g + z)) + ∑ g, c g := by rw [hcard, hshift, two_mul]
      _ = Fintype.card G := by
        rw [← Finset.sum_add_distrib]
        simp [hstep]
      _ = 2 ^ n := hG
  · intro g hg j hj
    change 1 ≤ c g at hg
    have hperiod (a : G) : c (a + (2 : ℕ) • z) = c a := by
      rw [two_nsmul, ← add_assoc]
      have := hstep a
      have := hstep (a + z)
      omega
    have heven (k : ℕ) : c (g + (2 * k) • z) = c g := by
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, add_nsmul, ← add_assoc, hperiod, ih]
    change 1 ≤ c (g + (2 * j) • z) ∧ c (g + (2 * j - 1) • z) = 0
    refine ⟨(heven j).symm ▸ hg, ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, add_nsmul, one_nsmul, ← add_assoc]
    have hodd := hstep (g + (2 * k) • z)
    rw [heven] at hodd
    omega

end MetaMathlibExt
