/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree

/-!
# Braun-tree public API tests

Restatements of the headline contracts across all `BraunTree`
modules, mirroring the per-module test files: the shape theorems,
the array / flexible-array specs, the linear-time conversions with
their running-time bounds, and the `bal` specification. All proofs
are the production theorems themselves.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeAPITests

open BraunTree

/-- Lemma 11.2: every Braun tree is almost complete. -/
example {α : Type u} {t : Tree α} (h : braun t) : acomplete t :=
  braun_acomplete h

/-- The book's `acomplete` definition, as an iff. -/
example {α : Type u} {t : Tree α} :
    acomplete t ↔ height t ≤ minHeight t + 1 :=
  acomplete_iff

/-- Exercise 11.1: a nonempty Braun tree has logarithmic height. -/
example {α : Type u} {t : Tree α} (h : braun t) (hne : t ≠ .Leaf) :
    height t = Nat.log2 (size t) + 1 :=
  braun_height_log h hne

/-- Lemma 4.6: an almost-complete tree has minimal height. -/
example {α : Type u} {s t : Tree α} (hs : acomplete s)
    (h : size s ≤ size t) : height s ≤ height t :=
  acomplete_height_optimal hs h

/-- Corollary 4.5: completeness is the size equation. -/
example {α : Type u} {t : Tree α} :
    complete t ↔ size t + 1 = 2 ^ height t :=
  complete_iff_size

/-- (11.1): 1-based lookup reads the index-order list. -/
example {α : Type u} {t : Tree α} (h : braun t) (i : ℕ) (hi : 1 ≤ i) :
    lookup1 i t = (list t)[i - 1]? :=
  lookup1_list h i hi

/-- (11.2): the list is the map of 1-based lookups. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    (List.range (size t)).map (fun i => lookup1 (i + 1) t) = (list t).map some :=
  list_eq_map_lookup1 h

/-- Lemma 11.4: `braun_list` gives Braunness and the list. -/
example {α : Type u} {t : Tree α} {xs : List α} (h : braun_list t xs) :
    braun t ∧ xs = list t :=
  braun_list_eq h

/-- Lemma 11.3: `size_fast` is the size on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) : size_fast t = size t :=
  size_fast_correct h

/-- Exercise 11.7: the naive construction lists the constant value. -/
example {α : Type u} (x : α) (n : ℕ) :
    list (braun_of_naive x n) = List.replicate n x :=
  braun_of_naive_list x n

/-- Exercise 11.8: `Tsize_fast` is quadratic in the height. -/
example {α : Type u} (t : Tree α) : Tsize_fast t ≤ (height t) ^ 2 :=
  size_fast_time_le t

/-- (lookup) for the array built from a list. -/
example {α : Type u} (xs : List α) (i : ℕ) :
    (Array.ofList xs).lookup i = xs[i]? :=
  array_lookup_spec xs i

/-- (update) for the array built from a list. -/
example {α : Type u} (xs : List α) (i : ℕ) (x : α) (hi : i < xs.length) :
    ((Array.ofList xs).update i x).toList = xs.set i x :=
  array_update_spec xs i x hi

/-- Flex `add_lo` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) (x : α) :
    ((a.add_lo x).toList = x :: a.toList) ∧ (a.add_lo x).invar :=
  flex_add_lo_invar h x

/-- Flex `del_hi` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) :
    (a.del_hi.toList = a.toList.dropLast) ∧ (a.del_hi).invar :=
  flex_del_hi_invar h

/-- Exercise 11.6: `del_lo2` is `del_lo`. -/
example {α : Type u} (t : Tree α) : del_lo2 t = del_lo t :=
  del_lo2_eq t

/-- (#10): Braunness is the index-set characterisation. -/
example {α : Type u} {t : Tree α} :
    braun t ↔ braun_indices t = Set.Icc 1 (size t) :=
  braun_iff_indices

/-- Theorem 11.5: every `brauns` tree is in the `braun_list` relation. -/
example {α : Type u} {xs : List α} {k : ℕ} {i : ℕ}
    (hi : i < min xs.length (2 ^ k)) :
    ∃ t, (brauns k xs)[i]? = some t ∧ braun_list t (take_nths i k xs) :=
  brauns_correct hi

/-- Corollary 11.6: `brauns1` builds the Braun tree for a list. -/
example {α : Type u} (xs : List α) :
    braun (brauns1 xs) ∧ list (brauns1 xs) = xs :=
  brauns1_correct xs

/-- Lemma 11.7: `brauns` runs in linear time. -/
example {α : Type u} (k : ℕ) (xs : List α) :
    Tbrauns k xs ≤ 9 * (xs.length + 1) :=
  Tbrauns_le k xs

/-- Theorem 11.8: breadth-first traversal of a level of Braun trees. -/
example {α : Type u} {k : ℕ} {xs : List α} {ts : List (Tree α)}
    (hlen : ts.length = 2 ^ k)
    (h : ∀ i (hi : i < ts.length), braun_list (ts[i]'hi) (take_nths i k xs)) :
    list_fast_rec ts = xs :=
  list_fast_rec_correct hlen h

/-- `list_fast` recovers the index-order list of a Braun tree. -/
example {α : Type u} {t : Tree α} (h : braun t) : list_fast t = list t :=
  list_fast_correct h

/-- Theorem 11.9: `list_fast_rec` runs in linear time in the total size. -/
example {α : Type u} (ts : List (Tree α)) :
    Tlist_fast_rec ts ≤ 14 * (ts.map size).sum + ts.length + 2 :=
  Tlist_fast_rec_le ts

/-- (#34): `list` is O(n lg n) on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    Tlist t ≤ (size t + 1) * (Nat.log2 (size t) + 2) :=
  Tlist_le_braun h

/-- (#34): building an array from a list costs O(n lg n). -/
example {α : Type u} (xs : List α) :
    Tadds xs 0 (.Leaf : Tree α) ≤ (xs.length + 1) * (Nat.log2 xs.length + 3) :=
  Tadds_le_array xs

/-- (§11.4): `del_lo` is logarithmic on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    Tdel_lo t ≤ Nat.log2 (size t) + 2 :=
  Tdel_lo_le_braun h

/-- (§11.4): `merge` is logarithmic (in its first argument) on Braun trees. -/
example {α : Type u} {t₁ t₂ : Tree α} (h : braun t₁) :
    Tmerge t₁ t₂ ≤ Nat.log2 (size t₁) + 2 :=
  Tmerge_le_braun h

/-- `bal` returns a Braun tree (Exercise 11.4). -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) : braun t :=
  bal_braun hn h

/-- Exercise 4.9: `bal` runs in linear time. -/
example {α : Type u} (n : ℕ) (xs : List α) : Tbal n xs ≤ 4 * n + 1 :=
  Tbal_le n xs

end Cslib.Algorithms.Lean.BraunTreeAPITests
