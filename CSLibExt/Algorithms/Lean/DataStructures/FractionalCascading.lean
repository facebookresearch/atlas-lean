/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Order.Basic

/-!
# Fractional cascading

This file defines the static fractional-cascading construction at
specification level, following Bernard Chazelle and Leonidas J. Guibas,
"Fractional cascading: I. A data structuring technique", *Algorithmica* 1
(1986), 133-162, as presented in Erik Demaine's MIT 6.851 *Advanced Data
Structures*, Spring 2012, Lecture 3 (MIT OpenCourseWare). The input is a
list of `k`
catalogs, each a list sorted under `· ≤ ·` (`List.Pairwise (· ≤ ·)`). The
augmented catalogs are built from the last catalog backwards: the last
augmented catalog is the last catalog itself, and each earlier augmented
catalog is the merge of its own catalog with every other element (the
*sample*) of the next augmented catalog. The sampled elements are the bridge
elements; a bridge pointer for a value `v` into the next catalog is recorded
as an index, the number of elements of that catalog that are `≤ v`.

The verified core is the search specification. The lower-bound specification
`lowerBound x xs` counts the elements of `xs` that are `< x`; the scan
`countLT` computes the same count directly, and `searchAll x catalogs`
applies it to every catalog. The main theorems state that `searchAll` agrees
with the specification at every index, that every augmented catalog is
sorted, that a lower-bound search in an augmented catalog splits as the sum
of the searches in the original catalog and in the sample (the transfer
identity a bridge walk relies on), and that `|augmentOne c a| ≤
|c| + (|a| + 1) / 2`, with every augmented catalog bounded in length by the
total input size.

## Main definitions

* `FractionalCascading.sample` takes every other element of a catalog.
* `FractionalCascading.sortedMerge` merges two catalogs into a sorted one.
* `FractionalCascading.augmentOne` merges a catalog with the sample of the
  next augmented catalog.
* `FractionalCascading.augmented` builds all augmented catalogs.
* `FractionalCascading.bridgePtr` and `FractionalCascading.bridges` give the
  bridge pointers, as indices into the next catalog.
* `FractionalCascading.lowerBound` is the lower-bound specification and
  `FractionalCascading.searchAll` searches every catalog for one value.

## Deferred

The `O(log n + k)` search bound is not proved; no cost model is carried. The
merge of two catalogs is modelled as `List.mergeSort` of their
concatenation, not the linear-time merge, and `searchAll` scans each
catalog directly rather than performing one binary search followed by a
bridge-pointer walk. Dynamic fractional cascading is out of scope.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

namespace FractionalCascading

variable {α : Type*}

/-- Keeps the head of the list exactly when the flag is set, then flips it. -/
def sampleAux : Bool → List α → List α
  | _, [] => []
  | true, a :: xs => a :: sampleAux false xs
  | false, _ :: xs => sampleAux true xs

/-- Every other element of a catalog, starting with the first. -/
def sample (xs : List α) : List α :=
  sampleAux true xs

/-- The elements kept by `sampleAux` form a sublist of the input. -/
theorem sampleAux_sublist :
    ∀ (b : Bool) (xs : List α), (sampleAux b xs).Sublist xs
  | _, [] => List.Sublist.slnil
  | true, a :: xs => List.Sublist.cons_cons a (sampleAux_sublist false xs)
  | false, a :: xs => List.Sublist.cons a (sampleAux_sublist true xs)

/-- The sample of a catalog is a sublist of that catalog. -/
theorem sample_sublist (xs : List α) : (sample xs).Sublist xs :=
  sampleAux_sublist true xs

/-- Membership in a sample implies membership in the sampled catalog. -/
theorem mem_of_mem_sample {v : α} {xs : List α} (hv : v ∈ sample xs) :
    v ∈ xs :=
  (sample_sublist xs).subset hv

private theorem sampleAux_bounds : ∀ xs : List α,
    2 * (sampleAux true xs).length ≤ xs.length + 1 ∧
      2 * (sampleAux false xs).length ≤ xs.length
  | [] => by simp [sampleAux]
  | _ :: xs => by
      obtain ⟨h1, h2⟩ := sampleAux_bounds xs
      constructor <;> simp only [sampleAux, List.length_cons] <;> omega

/-- Twice the sample length is at most the catalog length plus one. -/
theorem two_mul_length_sample_le (xs : List α) :
    2 * (sample xs).length ≤ xs.length + 1 :=
  (sampleAux_bounds xs).1

/-- The sample length is at most half the catalog length, rounded up:
for an even length `2m` this is `m`, and for an odd length `2m + 1` it is
`m + 1`, matching `(xs.length + 1) / 2` exactly. -/
theorem length_sample_le (xs : List α) :
    (sample xs).length ≤ (xs.length + 1) / 2 := by
  have h := two_mul_length_sample_le xs
  omega

/-- The sample is no longer than the catalog. -/
theorem length_sample_le_length (xs : List α) :
    (sample xs).length ≤ xs.length :=
  (sample_sublist xs).length_le

variable [LinearOrder α]

/-- The sample of a sorted catalog is sorted. -/
theorem pairwise_sample {xs : List α} (hxs : xs.Pairwise (· ≤ ·)) :
    (sample xs).Pairwise (· ≤ ·) :=
  List.Pairwise.sublist (sample_sublist xs) hxs

/--
The sorted merge of two catalogs, modelled as the merge sort of their
concatenation.
-/
def sortedMerge (xs ys : List α) : List α :=
  (xs ++ ys).mergeSort (· ≤ ·)

/-- A sorted merge is a permutation of the concatenation. -/
theorem perm_sortedMerge (xs ys : List α) :
    (sortedMerge xs ys).Perm (xs ++ ys) :=
  List.mergeSort_perm _ _

/-- The length of a sorted merge is the sum of the input lengths. -/
theorem length_sortedMerge (xs ys : List α) :
    (sortedMerge xs ys).length = xs.length + ys.length := by
  rw [sortedMerge, List.length_mergeSort, List.length_append]

/-- A sorted merge is sorted. -/
theorem pairwise_sortedMerge (xs ys : List α) :
    (sortedMerge xs ys).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (by intro a b c h1 h2
        simp only [decide_eq_true_eq] at h1 h2 ⊢
        exact le_trans h1 h2)
    (by intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total a b) (xs ++ ys)
  rw [sortedMerge]
  exact h.imp (fun {a b} h => by simpa using h)

/-- Membership in a sorted merge is membership in one of the inputs. -/
theorem mem_sortedMerge_iff {v : α} {xs ys : List α} :
    v ∈ sortedMerge xs ys ↔ v ∈ xs ∨ v ∈ ys := by
  rw [(perm_sortedMerge xs ys).mem_iff, List.mem_append]

/--
The lower-bound specification: the number of elements of a catalog that are
`< x`, which for a sorted catalog is the first index whose element is
not `< x`.
-/
def lowerBound (x : α) (xs : List α) : Nat :=
  (xs.filter (· < x)).length

/-- The lower bound of a catalog is at most its length. -/
theorem lowerBound_le_length (x : α) (xs : List α) :
    lowerBound x xs ≤ xs.length :=
  List.length_filter_le _ _

/-- A lower-bound search in a sorted merge splits over the two inputs. -/
theorem lowerBound_sortedMerge (x : α) (xs ys : List α) :
    lowerBound x (sortedMerge xs ys) = lowerBound x xs + lowerBound x ys := by
  rw [lowerBound, lowerBound, lowerBound,
    (List.Perm.filter _ (perm_sortedMerge xs ys)).length_eq,
    List.filter_append, List.length_append]

/-- A lower-bound search in a sample counts no more than in the catalog. -/
theorem lowerBound_sample_le (x : α) (xs : List α) :
    lowerBound x (sample xs) ≤ lowerBound x xs :=
  (List.Sublist.filter _ (sample_sublist xs)).length_le

/-- A direct scan counting the elements of a catalog that are `< x`. -/
def countLT (x : α) : List α → Nat
  | [] => 0
  | a :: xs => countLT x xs + (if a < x then 1 else 0)

/-- The direct scan computes the lower-bound specification. -/
theorem countLT_eq_lowerBound (x : α) (xs : List α) :
    countLT x xs = lowerBound x xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a < x
      · simp [countLT, lowerBound, h, ih]
      · simp [countLT, lowerBound, h, ih]

/--
One augmented catalog: the merge of a catalog with the sample of the next
augmented catalog.
-/
def augmentOne (c a : List α) : List α :=
  sortedMerge c (sample a)

/-- An augmented catalog is sorted. -/
theorem pairwise_augmentOne (c a : List α) :
    (augmentOne c a).Pairwise (· ≤ ·) :=
  pairwise_sortedMerge _ _

/-- The length of an augmented catalog splits over its two parts. -/
theorem length_augmentOne (c a : List α) :
    (augmentOne c a).length = c.length + (sample a).length :=
  length_sortedMerge _ _

/-- The augmented length is the catalog plus the rounded-up half of the next. -/
theorem length_augmentOne_le (c a : List α) :
    (augmentOne c a).length ≤ c.length + (a.length + 1) / 2 := by
  have h := length_sample_le a
  rw [length_augmentOne]
  omega

/-- Membership in an augmented catalog is membership in one of its parts. -/
theorem mem_augmentOne_iff {v : α} {c a : List α} :
    v ∈ augmentOne c a ↔ v ∈ c ∨ v ∈ sample a :=
  mem_sortedMerge_iff

/-- An augmented entry comes from the catalog or from the next catalog. -/
theorem mem_augmentOne_imp {v : α} {c a : List α}
    (hv : v ∈ augmentOne c a) : v ∈ c ∨ v ∈ a := by
  cases mem_augmentOne_iff.mp hv with
  | inl hv => exact Or.inl hv
  | inr hv => exact Or.inr (mem_of_mem_sample hv)

/--
A lower-bound search in an augmented catalog splits as the sum of the
searches in the original catalog and in the sample of the next catalog.
-/
theorem lowerBound_augmentOne (x : α) (c a : List α) :
    lowerBound x (augmentOne c a) =
      lowerBound x c + lowerBound x (sample a) :=
  lowerBound_sortedMerge _ _ _

/-- The augmented search counts no more than the two separate searches. -/
theorem lowerBound_augmentOne_le (x : α) (c a : List α) :
    lowerBound x (augmentOne c a) ≤ lowerBound x c + lowerBound x a := by
  rw [lowerBound_augmentOne]
  have h := lowerBound_sample_le x a
  omega

/-- The first augmented catalog built on top of the later augmented ones. -/
def augmentHead (c : List α) : List (List α) → List α
  | [] => c
  | a :: _ => augmentOne c a

/--
All augmented catalogs: the last catalog is unchanged, and each earlier
catalog is augmented with the sample of the next augmented catalog.
-/
def augmented : List (List α) → List (List α)
  | [] => []
  | c :: cs =>
      let rest := augmented cs
      augmentHead c rest :: rest

/-- There is one augmented catalog per catalog. -/
@[simp]
theorem length_augmented (cs : List (List α)) :
    (augmented cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [augmented, List.length_cons, ih]

/-- The augmented list of a single catalog is that catalog. -/
theorem augmented_singleton (c : List α) : augmented [c] = [c] := by
  simp [augmented, augmentHead]

/-- Every augmented catalog of sorted catalogs is sorted. -/
theorem pairwise_augmented {cs : List (List α)}
    (hcs : ∀ c ∈ cs, c.Pairwise (· ≤ ·)) :
    ∀ a ∈ augmented cs, a.Pairwise (· ≤ ·) := by
  induction cs with
  | nil => intro a ha; simp [augmented] at ha
  | cons c cs ih =>
      intro a ha
      have htail : ∀ c ∈ cs, c.Pairwise (· ≤ ·) :=
        fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      have ih' := ih htail
      cases hacc : augmented cs with
      | nil =>
          have heq : augmented (c :: cs) = [c] := by
            simp only [augmented, hacc, augmentHead]
          rw [heq] at ha
          have hac : a = c := by simpa using ha
          rw [hac]
          exact hcs c (by simp)
      | cons nxt acc =>
          have heq : augmented (c :: cs) =
              augmentOne c nxt :: (nxt :: acc) := by
            simp only [augmented, hacc, augmentHead]
          rw [heq] at ha
          cases List.mem_cons.mp ha with
          | inl h => rw [h]; exact pairwise_augmentOne _ _
          | inr h =>
              apply ih'
              rw [hacc]
              exact h

/-- Every augmented catalog is at most the total input size. -/
theorem length_mem_augmented_le (cs : List (List α)) :
    ∀ a ∈ augmented cs, a.length ≤ (cs.map List.length).sum := by
  induction cs with
  | nil => intro a ha; simp [augmented] at ha
  | cons c cs ih =>
      intro a ha
      cases hacc : augmented cs with
      | nil =>
          have heq : augmented (c :: cs) = [c] := by
            simp only [augmented, hacc, augmentHead]
          rw [heq] at ha
          have hac : a = c := by simpa using ha
          rw [hac]
          simp [List.map_cons, List.sum_cons]
      | cons nxt acc =>
          have heq : augmented (c :: cs) =
              augmentOne c nxt :: (nxt :: acc) := by
            simp only [augmented, hacc, augmentHead]
          rw [heq] at ha
          have hnxt : nxt.length ≤ (cs.map List.length).sum := by
            apply ih
            rw [hacc]
            exact List.mem_cons_self
          cases List.mem_cons.mp ha with
          | inl h =>
              rw [h, length_augmentOne]
              have hs := length_sample_le_length nxt
              simp only [List.map_cons, List.sum_cons]
              omega
          | inr h =>
              have hle : a.length ≤ (cs.map List.length).sum := by
                apply ih
                rw [hacc]
                exact h
              simp only [List.map_cons, List.sum_cons]
              omega

/--
The bridge pointer for a value into the next catalog: the index just past
the elements of that catalog that are `≤ v`.
-/
def bridgePtr (next : List α) (v : α) : Nat :=
  (next.filter (· ≤ v)).length

/-- A bridge pointer is a valid boundary index of the next catalog. -/
theorem bridgePtr_le_length (next : List α) (v : α) :
    bridgePtr next v ≤ next.length :=
  List.length_filter_le _ _

/-- The bridge pointers of every entry of one catalog into the next. -/
def bridges (cur next : List α) : List Nat :=
  cur.map (bridgePtr next)

/-- There is one bridge pointer per entry of the current catalog. -/
@[simp]
theorem length_bridges (cur next : List α) :
    (bridges cur next).length = cur.length :=
  List.length_map _

/-- Every recorded bridge pointer is a boundary index of the next catalog. -/
theorem le_length_of_mem_bridges {cur next : List α} {p : Nat}
    (hp : p ∈ bridges cur next) : p ≤ next.length := by
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hp
  exact bridgePtr_le_length next v

/--
Searches every catalog for `x`, returning the lower-bound position in each
catalog, computed by a direct scan of each catalog.
-/
def searchAll (x : α) (catalogs : List (List α)) : List Nat :=
  catalogs.map (countLT x)

/-- Searching no catalogs gives no positions. -/
@[simp]
theorem searchAll_nil (x : α) : searchAll x ([] : List (List α)) = [] :=
  rfl

/-- Searching a head catalog and the rest splits over the cons. -/
@[simp]
theorem searchAll_cons (x : α) (c : List α) (cs : List (List α)) :
    searchAll x (c :: cs) = countLT x c :: searchAll x cs :=
  rfl

/-- There is one search position per catalog. -/
@[simp]
theorem length_searchAll (x : α) (cs : List (List α)) :
    (searchAll x cs).length = cs.length :=
  List.length_map _

/-- `searchAll` computes the lower-bound specification in every catalog. -/
theorem searchAll_eq_map_lowerBound (x : α) (cs : List (List α)) :
    searchAll x cs = cs.map (lowerBound x) := by
  rw [searchAll, List.map_congr_left (fun c _ => countLT_eq_lowerBound x c)]

/-- The position at every index is that catalog's lower bound. -/
theorem getElem?_searchAll (x : α) (cs : List (List α)) (i : Nat) :
    (searchAll x cs)[i]? = (cs[i]?).map (lowerBound x) := by
  rw [searchAll_eq_map_lowerBound, List.getElem?_map]

/-- Every reported position is a boundary index of its catalog. -/
theorem searchAll_le_of_mem {x : α} {cs : List (List α)} {i : Nat}
    {c : List α} (hc : cs[i]? = some c) :
    (searchAll x cs)[i]? = some (lowerBound x c) ∧
      lowerBound x c ≤ c.length := by
  rw [getElem?_searchAll, hc]
  exact ⟨rfl, lowerBound_le_length x c⟩

/-- Searches every augmented catalog for `x` by the same direct scan. -/
def searchAugmented (x : α) (cs : List (List α)) : List Nat :=
  (augmented cs).map (countLT x)

/-- There is one augmented search position per catalog. -/
theorem length_searchAugmented (x : α) (cs : List (List α)) :
    (searchAugmented x cs).length = cs.length := by
  rw [searchAugmented, List.length_map, length_augmented]

/-- Augmented search computes the lower bound in every augmented catalog. -/
theorem searchAugmented_eq_map_lowerBound (x : α) (cs : List (List α)) :
    searchAugmented x cs = (augmented cs).map (lowerBound x) := by
  rw [searchAugmented,
    List.map_congr_left (fun c _ => countLT_eq_lowerBound x c)]

end FractionalCascading

end Cslib.Algorithms.Lean
