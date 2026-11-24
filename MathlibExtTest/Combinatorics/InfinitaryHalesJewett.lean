/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfinitaryHalesJewett
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.OfFn

/-! Tests for Hales–Jewett configurations in J-sets of words. -/

open MetaMathlibExt

-- With no variables, the unique substitution gives a member of D even at an empty level.
example {D : Set (FreeSemigroup ℕ)} (hD : IsMulJSet D) : D.Nonempty := by
  obtain ⟨w, _, hw⟩ := exists_variableWord_subst_mem_of_isMulJSet Finset.range
    Finset.range_mono (fun x => ⟨x + 1, Finset.mem_range.mpr (Nat.lt_succ_self x)⟩) 0 0 hD
  exact ⟨_, hw Fin.elim0 (fun i => i.elim0)⟩

-- Over the two-letter alphabet, one word realizes all four binary substitutions.
example {D : Set (FreeSemigroup Bool)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (Bool ⊕ Fin 2), Sum.inr 0 ∈ w.head :: w.tail ∧
      Sum.inr 1 ∈ w.head :: w.tail ∧
      ∀ a : Fin 2 → Bool, FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  obtain ⟨w, hvars, hw⟩ := exists_variableWord_subst_mem_of_isMulJSet
    (fun _ => Finset.univ) monotone_const (fun x => ⟨0, Finset.mem_univ x⟩) 0 2 hD
  exact ⟨w, hvars 0, hvars 1, fun a => hw a (fun i => Finset.mem_univ (a i))⟩

namespace MetaMathlibExt.InfinitaryHalesJewettTest

-- The empty alphabet still admits variable words, even for the empty J-set.
example : ∃ w : FreeSemigroup (Empty ⊕ Fin 2), ∀ i, Sum.inr i ∈ w.head :: w.tail := by
  have hD : IsMulJSet (∅ : Set (FreeSemigroup Empty)) := fun _ hF => (hF.choose 0).head.elim
  obtain ⟨w, hvars, _, _⟩ :=
    exists_variableWords_subst_mem_prod_pattern_mem_finiteProducts_of_isMulJSet
      (fun _ => ∅) monotone_const (fun x => x.elim) (k := 1) (n := 2) (by decide) (by decide)
      (fun _ => [0]) (fun _ i => by simp [Subsingleton.elim i 0]) hD
  exact ⟨w 0, hvars 0⟩

private def firstTwo (w : FreeSemigroup (Bool ⊕ Fin 3)) : List (Fin 2) :=
  (w.head :: w.tail).filterMap (Sum.elim (fun _ => none) fun i : Fin 3 =>
    if h : (i : ℕ) < 2 then some ⟨i, h⟩ else none)

-- The zero runs distinguish the prescribed patterns and record their order in a product.
private def runs (j : ℕ) : List (Fin 2) := [1, 0] ++ List.replicate j 0

example {D : Set (FreeSemigroup Bool)} (hD : IsMulJSet D) :
    ∃ w : ℕ → FreeSemigroup (Bool ⊕ Fin 3),
      (∀ m (a : Fin 3 → Bool), FreeSemigroup.map (Sum.elim id a) (w m) ∈ D) ∧
      ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧
        firstTwo (w 0) ++ firstTwo (w 2) = (List.ofFn fun j => runs (t j)).flatten := by
  have hy : ∀ i : Fin 2, i ∈ [1, 0] := by decide
  obtain ⟨w, _, hmem, hpat⟩ :=
    exists_variableWords_subst_mem_prod_pattern_mem_finiteProducts_of_isMulJSet
      (fun _ => Finset.univ) monotone_const (fun x => ⟨0, Finset.mem_univ x⟩)
      (k := 2) (n := 3) (by decide) (by decide) runs (fun _ i => List.mem_append_left _ (hy i)) hD
  have hm : StrictMono (fun j : Fin 2 => 2 * j.val) :=
    fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide)
  obtain ⟨r, t, ht, he⟩ := hpat 1 _ hm
  refine ⟨w, fun m a => hmem m a (fun i => Finset.mem_univ _), r, t, ht, ?_⟩
  change (List.ofFn fun j : Fin 2 => firstTwo (w (2 * j.val))).flatten = _ at he
  simpa [List.ofFn_succ] using he

-- An empty alphabet has no substitutions, but a positive count is still required.
-- With every input equal to two, even a single word must have at least two variables.
example : ∃ w : FreeSemigroup (Empty ⊕ Fin 1), 2 ≤ (w.head :: w.tail).countP Sum.isRight := by
  have hD : IsMulJSet (∅ : Set (FreeSemigroup Empty)) := fun _ hF => (hF.choose 0).head.elim
  obtain ⟨w, _, _, hsum⟩ := exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet
    (fun _ => ∅) monotone_const (fun a => a.elim) hD (fun _ => 2) (fun _ => by decide)
  obtain ⟨H, hH, he⟩ := hsum {0} (Finset.singleton_nonempty _)
  have he' : ((w 0).head :: (w 0).tail).countP Sum.isRight = H.card * 2 := by simpa using he
  have := Finset.card_pos.mpr hH
  exact ⟨w 0, by omega⟩

-- Counts from nonconsecutive levels add to a sum of distinct powers of three.
example {D : Set (FreeSemigroup Bool)} (hD : IsMulJSet D) :
    ∃ w : ℕ → FreeSemigroup (Bool ⊕ Fin 1),
      (∀ m a, FreeSemigroup.map (Sum.elim id fun _ => a) (w m) ∈ D) ∧
      ∃ H : Finset ℕ, H.Nonempty ∧
        ((w 0).head :: (w 0).tail).countP Sum.isRight +
          ((w 2).head :: (w 2).tail).countP Sum.isRight = ∑ j ∈ H, 3 ^ j := by
  obtain ⟨w, _, hw, hsum⟩ := exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet
    (fun _ => Finset.univ) monotone_const (fun a => ⟨0, Finset.mem_univ a⟩) hD
    (fun j => 3 ^ j) (fun _ => Nat.pow_pos (by decide))
  refine ⟨w, fun m a => hw m a (Finset.mem_univ _), ?_⟩
  simpa using hsum {0, 2} (by simp)

end MetaMathlibExt.InfinitaryHalesJewettTest
