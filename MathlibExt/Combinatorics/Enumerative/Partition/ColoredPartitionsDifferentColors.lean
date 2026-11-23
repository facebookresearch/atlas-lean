/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Colored partitions with distinct colors

Count bounded colored partitions by recording, independently for each color, its part size
or zero if that color is absent.
-/

namespace MetaMathlibExt

open Finset

namespace card_coloredPartitions_differentColors

private def parts (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun x : ℕ × ℕ => x.2 ≤ x.1

private lemma mem_parts {n m j : ℕ} :
    (m, j) ∈ parts n ↔ 1 ≤ j ∧ j ≤ m ∧ m ≤ n := by
  simp only [parts, mem_filter, mem_product, mem_Icc]
  omega

/-- Form a colored part from each nonzero choice of size. -/
private def selectedParts {s : Finset ℕ} (f : ∀ j ∈ s, ℕ) : Finset (ℕ × ℕ) :=
  (s.attach.image fun j : s => (f j j.property, j.val)).filter fun p => p.1 ≠ 0

private lemma mem_selectedParts {s : Finset ℕ} {f : ∀ j ∈ s, ℕ} {m j : ℕ} :
    (m, j) ∈ selectedParts f ↔ ∃ hj : j ∈ s, f j hj = m ∧ m ≠ 0 := by
  simp [selectedParts, Prod.ext_iff, Subtype.exists]

private lemma card_including_empty (n : ℕ) :
    ((parts n).powerset.filter fun T => (T.image Prod.snd).card = T.card).card =
      ((Icc 1 n).pi fun j => insert 0 (Icc j n)).card := by
  classical
  symm
  apply card_bij (fun f _ => selectedParts f)
  · intro f hf
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, card_image_iff.mpr ?_⟩
    · rintro ⟨m, j⟩ hp
      obtain ⟨hj, heq, hm⟩ := mem_selectedParts.mp hp
      have hsize := mem_pi.mp hf j hj
      rw [heq, mem_insert, mem_Icc] at hsize
      exact mem_parts.mpr ⟨(mem_Icc.mp hj).1, hsize.resolve_left hm⟩
    · rintro ⟨a, j⟩ ha ⟨b, k⟩ hb (rfl : j = k)
      obtain ⟨_, h₁, _⟩ := mem_selectedParts.mp ha
      obtain ⟨_, h₂, _⟩ := mem_selectedParts.mp hb
      exact Prod.ext (h₁.symm.trans h₂) rfl
  · intro f _ g _ h
    funext j hj
    have hmem (m : ℕ) : (f j hj = m ∧ m ≠ 0) ↔ (g j hj = m ∧ m ≠ 0) := by
      simpa only [mem_selectedParts, exists_prop_of_true hj] using
        (show (m, j) ∈ selectedParts f ↔ (m, j) ∈ selectedParts g by rw [h])
    grind [hmem (f j hj), hmem (g j hj)]
  · intro T hT
    obtain ⟨hsub, hinj⟩ := mem_filter.mp hT
    have bounds {m j : ℕ} (hm : (m, j) ∈ T) := mem_parts.mp (mem_powerset.mp hsub hm)
    have choice (j : ℕ) : ∃ v ∈ insert 0 (Icc j n),
        ∀ m, (m, j) ∈ T ↔ v = m ∧ m ≠ 0 := by
      by_cases h : ∃ v, (v, j) ∈ T
      · obtain ⟨v, hv⟩ := h
        refine ⟨v, mem_insert_of_mem (mem_Icc.mpr (bounds hv).2), fun m => ⟨fun hm => ?_, ?_⟩⟩
        · have heq := card_image_iff.mp hinj hv hm rfl
          have hpos := bounds hm
          exact ⟨congrArg Prod.fst heq, by omega⟩
        · rintro ⟨rfl, _⟩
          exact hv
      · exact ⟨0, mem_insert_self .., fun m => by grind⟩
    choose f hf hmem using choice
    refine ⟨fun j _ => f j, mem_pi.mpr (fun j _ => hf j), ?_⟩
    ext ⟨m, j⟩
    rw [mem_selectedParts]
    constructor
    · rintro ⟨_, h⟩
      exact (hmem j m).mpr h
    · intro hm
      obtain ⟨hj, hjm, hmn⟩ := bounds hm
      exact ⟨mem_Icc.mpr ⟨hj, hjm.trans hmn⟩, (hmem j m).mp hm⟩

private lemma card_choices (n : ℕ) :
    ((Icc 1 n).pi fun j => insert 0 (Icc j n)).card = (n + 1).factorial := by
  rw [card_pi, ← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  calc
    _ = (n + 1).descFactorial n := by
      rw [Nat.descFactorial_eq_prod_range]
      refine prod_congr rfl fun i hi => ?_
      rw [card_insert_of_notMem (by simp), Nat.card_Icc]
      have := mem_range.mp hi
      omega
    _ = _ := by simpa using Nat.factorial_mul_descFactorial (Nat.le_succ n)

end card_coloredPartitions_differentColors

open card_coloredPartitions_differentColors

/-- **Colored partitions with distinct colors.** A colored part is a pair $(m, j)$ of integers
with $1 \le j \le m$, read as the part $m$ in color $j$. For every $n \ge 0$, the number of
nonempty finite sets of colored parts $(m, j)$ with $m \le n$ in which no two colored parts have
the same color $j$ is $(n + 1)! - 1$.

A colored partition whose parts have pairwise different colors has no repeated colored part, so
it is the same as a finite set of colored parts; the empty partition is not counted.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 1 (`integers-2026-A20-thm-1`). -/
public theorem card_coloredPartitions_differentColors (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.snd).card = T.card)).card = (n + 1).factorial - 1 := by
  let all := (parts n).powerset.filter fun T => (T.image Prod.snd).card = T.card
  have hempty : ∅ ∈ all := by simp [all]
  have herase : ((parts n).powerset.filter fun T =>
      T.Nonempty ∧ (T.image Prod.snd).card = T.card) = all.erase ∅ := by
    ext T
    simp only [all, mem_filter, mem_erase, nonempty_iff_ne_empty]
    tauto
  rw [← parts, herase, card_erase_of_mem hempty, card_including_empty, card_choices]

end MetaMathlibExt
