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

/-- **Alternating selection with a flag.** For a flag $b$ (true or false) and a list $\ell$, the
alternating selection of $\ell$ with initial flag $b$ is defined by recursion on $\ell$: the empty
list gives the empty list; for a list with head $a$ and tail $\ell'$, if $b$ is true it keeps $a$
and continues on $\ell'$ with flag false, and if $b$ is false it drops $a$ and continues on
$\ell'$ with flag true. -/
def sampleAux : Bool → List α → List α
  | _, [] => []
  | true, a :: xs => a :: sampleAux false xs
  | false, _ :: xs => sampleAux true xs

/-- **Sample of a catalog.** The sample of a list $[x_0, x_1, x_2, \dots]$ is the list
$[x_0, x_2, x_4, \dots]$ of every other element, starting with the first, in their original
order. -/
def sample (xs : List α) : List α :=
  sampleAux true xs

/-- **Alternating selection gives a sublist.** For every flag $b$ (true or false) and every list
$\ell$, the alternating selection of $\ell$ with initial flag $b$ is a sublist of $\ell$: it is
obtained from $\ell$ by deleting some elements and keeping the rest in order. -/
theorem sampleAux_sublist :
    ∀ (b : Bool) (xs : List α), (sampleAux b xs).Sublist xs
  | _, [] => List.Sublist.slnil
  | true, a :: xs => List.Sublist.cons_cons a (sampleAux_sublist false xs)
  | false, a :: xs => List.Sublist.cons a (sampleAux_sublist true xs)

/-- **The sample is a sublist.** For every list $\ell$, the sample of $\ell$ is a sublist of
$\ell$: it is obtained from $\ell$ by deleting some elements and keeping the rest in order. -/
theorem sample_sublist (xs : List α) : (sample xs).Sublist xs :=
  sampleAux_sublist true xs

/-- **Entries of a sample are entries of the catalog.** For a catalog (finite list) $L$, every
entry of the sample of $L$ (every other entry of $L$, starting with the first) is an entry of
$L$. -/
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

/-- **Doubled sample length bound.** For every catalog $L$, twice the length of the sample of $L$
is at most the length of $L$ plus one. -/
theorem two_mul_length_sample_le (xs : List α) :
    2 * (sample xs).length ≤ xs.length + 1 :=
  (sampleAux_bounds xs).1

/-- **The sample has at most half the length, rounded up.** For every list $xs$ (over any
type), the sample of $xs$ has length at most $\lfloor (|xs| + 1)/2 \rfloor$, half the length of
$xs$ rounded up: for an even length $2m$ the bound is $m$, and for an odd length $2m + 1$ it is
$m + 1$. -/
theorem length_sample_le (xs : List α) :
    (sample xs).length ≤ (xs.length + 1) / 2 := by
  have h := two_mul_length_sample_le xs
  omega

/-- **The sample is no longer than the list.** For every list $xs$ (over any type), the sample
of $xs$, every other element starting with the first, has length at most the length of $xs$. -/
theorem length_sample_le_length (xs : List α) :
    (sample xs).length ≤ xs.length :=
  (sample_sublist xs).length_le

variable [LinearOrder α]

/-- **The sample of a sorted list is sorted.** If a list over a linear order is sorted in
nondecreasing order, then so is its sample. -/
theorem pairwise_sample {xs : List α} (hxs : xs.Pairwise (· ≤ ·)) :
    (sample xs).Pairwise (· ≤ ·) :=
  List.Pairwise.sublist (sample_sublist xs) hxs

/-- **Sorted merge of two catalogs.** For lists $\ell_1$ and $\ell_2$ over a linearly ordered
type, their sorted merge is the result of merge sort, with respect to $\le$, applied to the
concatenation of $\ell_1$ followed by $\ell_2$.

This models the merge of two sorted catalogs; the linear-time merge itself is not formalized. -/
def sortedMerge (xs ys : List α) : List α :=
  (xs ++ ys).mergeSort (· ≤ ·)

/-- **A sorted merge rearranges the concatenation.** For any lists $\ell_1$ and $\ell_2$ over a
linear order, the sorted merge of $\ell_1$ and $\ell_2$ is a permutation of the concatenation of
$\ell_1$ followed by $\ell_2$. -/
theorem perm_sortedMerge (xs ys : List α) :
    (sortedMerge xs ys).Perm (xs ++ ys) :=
  List.mergeSort_perm _ _

/-- **Length of a sorted merge.** For catalogs (finite lists) $L$ and $M$ over a linearly ordered
type, the sorted merge of $L$ and $M$ has length equal to the length of $L$ plus the length of
$M$. -/
theorem length_sortedMerge (xs ys : List α) :
    (sortedMerge xs ys).length = xs.length + ys.length := by
  rw [sortedMerge, List.length_mergeSort, List.length_append]

/-- **A sorted merge is sorted.** For any lists $\ell_1$ and $\ell_2$ over a linear order, sorted
or not, their sorted merge is sorted in nondecreasing order. -/
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

/-- **Elements of a sorted merge.** For lists $\ell_1$ and $\ell_2$ over a linear order and any
element $v$, $v$ belongs to the sorted merge of $\ell_1$ and $\ell_2$ if and only if $v$ belongs
to $\ell_1$ or to $\ell_2$. -/
theorem mem_sortedMerge_iff {v : α} {xs ys : List α} :
    v ∈ sortedMerge xs ys ↔ v ∈ xs ∨ v ∈ ys := by
  rw [(perm_sortedMerge xs ys).mem_iff, List.mem_append]

/--
**Lower bound of a value in a catalog.** For a value $x$ of a linearly ordered type and a catalog
(finite list) $L$, the lower bound of $x$ in $L$ is the number of entries of $L$ that are less
than $x$, counted with multiplicity. For a sorted catalog this is the first index whose entry is
not less than $x$, or the length of $L$ if there is none.
-/
def lowerBound (x : α) (xs : List α) : Nat :=
  (xs.filter (· < x)).length

/-- **Lower bound is at most the catalog length.** For a value $x$ and a catalog $L$ over a
linearly ordered type, the lower bound of $x$ in $L$ (the number of entries of $L$ less than $x$)
is at most the length of $L$. -/
theorem lowerBound_le_length (x : α) (xs : List α) :
    lowerBound x xs ≤ xs.length :=
  List.length_filter_le _ _

/-- **Lower bound in a sorted merge splits.** For a value $x$ and catalogs $L$ and $M$ over a
linearly ordered type, the lower bound of $x$ in the sorted merge of $L$ and $M$ equals the lower
bound of $x$ in $L$ plus the lower bound of $x$ in $M$, where the lower bound of $x$ in a catalog
is the number of its entries less than $x$. -/
theorem lowerBound_sortedMerge (x : α) (xs ys : List α) :
    lowerBound x (sortedMerge xs ys) = lowerBound x xs + lowerBound x ys := by
  rw [lowerBound, lowerBound, lowerBound,
    (List.Perm.filter _ (perm_sortedMerge xs ys)).length_eq,
    List.filter_append, List.length_append]

/-- **Lower bound in a sample is at most the lower bound in the catalog.** For a value $x$ and a
catalog $L$ over a linearly ordered type, the number of entries less than $x$ in the sample of
$L$ (every other entry of $L$, starting with the first) is at most the number of entries of $L$
less than $x$. -/
theorem lowerBound_sample_le (x : α) (xs : List α) :
    lowerBound x (sample xs) ≤ lowerBound x xs :=
  (List.Sublist.filter _ (sample_sublist xs)).length_le

/--
**Scan count of smaller elements.** For a value $x$ and a catalog $L$, the scan count of $x$ in
$L$ is the number of elements of $L$ that are $< x$, computed by a direct scan: it is $0$ for
the empty catalog, and for a catalog with head $a$ and tail $L'$ it is the scan count of $x$ in
$L'$, plus $1$ if $a < x$.
-/
def countLT (x : α) : List α → Nat
  | [] => 0
  | a :: xs => countLT x xs + (if a < x then 1 else 0)

/--
**The scan count equals the lower bound.** For every value $x$ and every catalog $L$, the scan
count of elements of $L$ that are $< x$ equals the lower bound of $x$ in $L$.
-/
theorem countLT_eq_lowerBound (x : α) (xs : List α) :
    countLT x xs = lowerBound x xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a < x
      · simp [countLT, lowerBound, h, ih]
      · simp [countLT, lowerBound, h, ih]

/--
**Augmenting a catalog by the next one.** For catalogs $c$ and $a$, the augmentation of $c$
by $a$ is the sorted merge of $c$ with the sample of $a$ (every other element of $a$, starting
with the first). In fractional cascading, $a$ is the next augmented catalog.
-/
def augmentOne (c a : List α) : List α :=
  sortedMerge c (sample a)

/-- **One augmentation step yields a sorted list.** For any lists $c$ and $a$ over a linear order,
sorted or not, the augmented catalog obtained by merging $c$ with the sample of $a$ is sorted in
nondecreasing order. -/
theorem pairwise_augmentOne (c a : List α) :
    (augmentOne c a).Pairwise (· ≤ ·) :=
  pairwise_sortedMerge _ _

/-- **Length of one augmented catalog.** For lists $c$ and $a$ over a linearly ordered type, the
augmented catalog obtained by merging $c$ with the sample $s(a)$ of $a$ has length
$|c| + |s(a)|$. -/
theorem length_augmentOne (c a : List α) :
    (augmentOne c a).length = c.length + (sample a).length :=
  length_sortedMerge _ _

/-- **Length bound for one augmented catalog.** For lists $c$ and $a$ over a linearly ordered
type, the augmented catalog obtained by merging $c$ with the sample of $a$ has length at most
$|c| + \lfloor (|a| + 1)/2 \rfloor$, the length of $c$ plus half the length of $a$ rounded up. -/
theorem length_augmentOne_le (c a : List α) :
    (augmentOne c a).length ≤ c.length + (a.length + 1) / 2 := by
  have h := length_sample_le a
  rw [length_augmentOne]
  omega

/-- **Membership in an augmented catalog.** For catalogs $c$ and $a$ over a linearly ordered type,
a value $v$ is an entry of the augmented catalog of $c$ with $a$ (the sorted merge of $c$ with the
sample of $a$) if and only if $v$ is an entry of $c$ or an entry of the sample of $a$. -/
theorem mem_augmentOne_iff {v : α} {c a : List α} :
    v ∈ augmentOne c a ↔ v ∈ c ∨ v ∈ sample a :=
  mem_sortedMerge_iff

/-- **Entries of an augmented catalog come from the two catalogs.** For catalogs $c$ and $a$ over
a linearly ordered type, every entry $v$ of the augmented catalog of $c$ with $a$ (the sorted
merge of $c$ with the sample of $a$) is an entry of $c$ or an entry of $a$. -/
theorem mem_augmentOne_imp {v : α} {c a : List α}
    (hv : v ∈ augmentOne c a) : v ∈ c ∨ v ∈ a := by
  cases mem_augmentOne_iff.mp hv with
  | inl hv => exact Or.inl hv
  | inr hv => exact Or.inr (mem_of_mem_sample hv)

/--
**Lower bound in an augmented catalog splits.** For a value $x$ and catalogs $c$ and $a$ over a
linearly ordered type, the lower bound of $x$ in the augmented catalog of $c$ with $a$ (the sorted
merge of $c$ with the sample of $a$) equals the lower bound of $x$ in $c$ plus the lower bound of
$x$ in the sample of $a$, where the lower bound of $x$ in a catalog is the number of its entries
less than $x$.
-/
theorem lowerBound_augmentOne (x : α) (c a : List α) :
    lowerBound x (augmentOne c a) =
      lowerBound x c + lowerBound x (sample a) :=
  lowerBound_sortedMerge _ _ _

/-- **Lower bound in an augmented catalog is at most the sum.** For a value $x$ and catalogs $c$
and $a$ over a linearly ordered type, the lower bound of $x$ in the augmented catalog of $c$ with
$a$ (the sorted merge of $c$ with the sample of $a$) is at most the lower bound of $x$ in $c$
plus the lower bound of $x$ in $a$, where the lower bound of $x$ in a catalog is the number of
its entries less than $x$. -/
theorem lowerBound_augmentOne_le (x : α) (c a : List α) :
    lowerBound x (augmentOne c a) ≤ lowerBound x c + lowerBound x a := by
  rw [lowerBound_augmentOne]
  have h := lowerBound_sample_le x a
  omega

/--
**Augmenting a catalog by the head of a list.** Given a catalog $c$ and a list $L$ of
catalogs, the result is $c$ itself if $L$ is empty, and otherwise the sorted merge of $c$
with the sample (every other element, starting with the first) of the first catalog of $L$.
-/
def augmentHead (c : List α) : List (List α) → List α
  | [] => c
  | a :: _ => augmentOne c a

/--
**Augmented catalogs.** For a list of catalogs $c_1, \dots, c_k$, the augmented catalogs
$A_1, \dots, A_k$ are built from the last one backwards: $A_k = c_k$, and for $i < k$, $A_i$ is
the sorted merge of $c_i$ with the sample (every other element, starting with the first) of
$A_{i+1}$. The empty list of catalogs has no augmented catalogs.
-/
def augmented : List (List α) → List (List α)
  | [] => []
  | c :: cs =>
      let rest := augmented cs
      augmentHead c rest :: rest

/-- **Number of augmented catalogs.** For every list $cs$ of catalogs over a linearly ordered
type, the list of augmented catalogs built from $cs$ has the same length as $cs$: there is one
augmented catalog per catalog. -/
@[simp]
theorem length_augmented (cs : List (List α)) :
    (augmented cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [augmented, List.length_cons, ih]

/--
**Augmenting a single catalog.** For every catalog $c$, the list of augmented catalogs of the
one-element list $[c]$ is $[c]$: the only augmented catalog is $c$ itself.
-/
theorem augmented_singleton (c : List α) : augmented [c] = [c] := by
  simp [augmented, augmentHead]

/-- **The augmented catalogs of sorted catalogs are sorted.** If every catalog in a list of
catalogs over a linear order is sorted in nondecreasing order, then every augmented catalog built
from that list is sorted in nondecreasing order. -/
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

/-- **Augmented catalogs are bounded by the total input size.** For every list
$cs = [c_1, \dots, c_k]$ of catalogs over a linearly ordered type, every augmented catalog built
from $cs$ has length at most $|c_1| + \dots + |c_k|$. -/
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
**Bridge pointer.** For a catalog $L$ and a value $v$, the bridge pointer of $v$ into $L$ is
the number of elements of $L$ that are $\le v$.

When $L$ is sorted, this is the index just past the elements of $L$ that are $\le v$.
-/
def bridgePtr (next : List α) (v : α) : Nat :=
  (next.filter (· ≤ v)).length

/--
**Bridge pointers are at most the catalog length.** For every catalog $L$ and value $v$, the
bridge pointer of $v$ into $L$ is at most the length of $L$.
-/
theorem bridgePtr_le_length (next : List α) (v : α) :
    bridgePtr next v ≤ next.length :=
  List.length_filter_le _ _

/--
**Bridge pointer list.** For catalogs $C$ and $L$, the bridge pointers of $C$ into $L$ form the
list obtained by replacing each entry $v$ of $C$, in order, by the bridge pointer of $v$ into
$L$.
-/
def bridges (cur next : List α) : List Nat :=
  cur.map (bridgePtr next)

/-- **Number of bridge pointers.** For lists $c$ and $d$ over a linearly ordered type, the list
of bridge pointers of $c$ into $d$ has the same length as $c$: there is one bridge pointer per
entry of $c$. -/
@[simp]
theorem length_bridges (cur next : List α) :
    (bridges cur next).length = cur.length :=
  List.length_map _

/-- **Bridge pointers are at most the next catalog's length.** For lists $c$ and $d$ over a
linearly ordered type, every entry $p$ of the list of bridge pointers of $c$ into $d$ satisfies
$p \le |d|$, where $|d|$ is the length of $d$; so every recorded bridge pointer is a boundary
index of $d$. -/
theorem le_length_of_mem_bridges {cur next : List α} {p : Nat}
    (hp : p ∈ bridges cur next) : p ≤ next.length := by
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hp
  exact bridgePtr_le_length next v

/-- **Searching every catalog.** For a value $x$ and a list of catalogs, the search returns, for
each catalog in order, the number of its elements that are $< x$, computed by a direct scan of
that catalog. This is the lower-bound position of $x$ in each catalog. -/
def searchAll (x : α) (catalogs : List (List α)) : List Nat :=
  catalogs.map (countLT x)

/-- **Searching no catalogs.** Searching the empty list of catalogs for any value $x$ gives the
empty list of positions. -/
@[simp]
theorem searchAll_nil (x : α) : searchAll x ([] : List (List α)) = [] :=
  rfl

/-- **Searching a nonempty list of catalogs.** For a value $x$, a catalog $c$ and a list of
catalogs $cs$, searching $c$ followed by $cs$ for $x$ gives first the direct-scan count of the
elements of $c$ that are $< x$, followed by the positions obtained by searching $cs$ for $x$. -/
@[simp]
theorem searchAll_cons (x : α) (c : List α) (cs : List (List α)) :
    searchAll x (c :: cs) = countLT x c :: searchAll x cs :=
  rfl

/-- **One search position per catalog.** For every value $x$ and every list $cs$ of catalogs
over a linearly ordered type, searching each catalog of $cs$ for $x$ gives a list of positions
of the same length as $cs$. -/
@[simp]
theorem length_searchAll (x : α) (cs : List (List α)) :
    (searchAll x cs).length = cs.length :=
  List.length_map _

/-- **Correctness of searching every catalog.** For a value $x$ and a list of catalogs
$c_1, \dots, c_k$, searching every catalog for $x$ returns the list whose $i$-th entry is the
lower bound of $x$ in $c_i$, that is, the number of elements of $c_i$ that are $< x$. -/
theorem searchAll_eq_map_lowerBound (x : α) (cs : List (List α)) :
    searchAll x cs = cs.map (lowerBound x) := by
  rw [searchAll, List.map_congr_left (fun c _ => countLT_eq_lowerBound x c)]

/--
**Search positions are lower bounds, index by index.** For every value $x$, list of catalogs
$C_0, \dots, C_{k-1}$ and index $i$: if $i < k$, the $i$-th position returned by searching all
catalogs for $x$ is the lower bound of $x$ in $C_i$; if $i \ge k$, the search result has no
$i$-th entry.
-/
theorem getElem?_searchAll (x : α) (cs : List (List α)) (i : Nat) :
    (searchAll x cs)[i]? = (cs[i]?).map (lowerBound x) := by
  rw [searchAll_eq_map_lowerBound, List.getElem?_map]

/-- **Search positions are boundary indices.** Let $x$ be a value and let $cs$ be a list of
catalogs whose entry at index $i$ is the catalog $c$. Then searching every catalog of $cs$ for
$x$ gives, at index $i$, the lower bound of $x$ in $c$ (the number of elements of $c$ that are
$< x$), and this lower bound is at most the length of $c$. -/
theorem searchAll_le_of_mem {x : α} {cs : List (List α)} {i : Nat}
    {c : List α} (hc : cs[i]? = some c) :
    (searchAll x cs)[i]? = some (lowerBound x c) ∧
      lowerBound x c ≤ c.length := by
  rw [getElem?_searchAll, hc]
  exact ⟨rfl, lowerBound_le_length x c⟩

/-- **Searching every augmented catalog.** For a value $x$ and a list of catalogs, the augmented
search builds the augmented catalogs and returns, for each augmented catalog in order, the number
of its elements that are $< x$, computed by a direct scan of that catalog. -/
def searchAugmented (x : α) (cs : List (List α)) : List Nat :=
  (augmented cs).map (countLT x)

/-- **One augmented search position per catalog.** For every value $x$ and every list $cs$ of
catalogs over a linearly ordered type, searching each augmented catalog built from $cs$ for $x$
gives a list of positions of the same length as $cs$. -/
theorem length_searchAugmented (x : α) (cs : List (List α)) :
    (searchAugmented x cs).length = cs.length := by
  rw [searchAugmented, List.length_map, length_augmented]

/-- **Correctness of augmented search.** For a value $x$ and a list of catalogs $cs$, searching
every augmented catalog of $cs$ for $x$ returns, for each augmented catalog in order, the lower
bound of $x$ in it, that is, the number of its elements that are $< x$. -/
theorem searchAugmented_eq_map_lowerBound (x : α) (cs : List (List α)) :
    searchAugmented x cs = (augmented cs).map (lowerBound x) := by
  rw [searchAugmented,
    List.map_congr_left (fun c _ => countLT_eq_lowerBound x c)]

end FractionalCascading

end Cslib.Algorithms.Lean
