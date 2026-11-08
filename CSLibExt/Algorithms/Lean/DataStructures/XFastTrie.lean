/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Basic

/-!
# x-fast tries (and a y-fast skeleton)

An x-fast trie (Demaine, MIT 6.851 *Advanced Data Structures*, Lecture 11) stores a set of
`w`-bit keys as a binary trie together with one hash table per trie level: level `l` holds
the `l`-bit prefixes of all stored keys. Membership is a single probe of the deepest level,
and successor search binary-searches the levels for the longest prefix shared with the
query, then descends.

This file gives the simplest verified form of that design. Keys are `Fin (2 ^ w)`, the
per-level hash tables are modeled plainly as `Finset`s of prefixes (prefixes are `Nat`s),
and no running-time bound is claimed anywhere: a `Finset` probe is not a hash probe. What
is verified is the level invariant and the exact semantics of the operations.

## Main definitions

* `XFastTrie.prefixOf l x` is the top `l` bits of `x`, as a `Nat` below `2 ^ l`.
* `XFastTrie` stores the key set `contents` and the level family
  `levels : Fin (w + 1) → Finset Nat`.
* `XFastTrie.Valid` says each level is exactly the image of `contents` under the prefix
  map for that level.
* `XFastTrie.member` probes the deepest level, as in the classical structure.
* `XFastTrie.successor` and `XFastTrie.predecessor` are defined directly from `contents`
  (least greater / greatest smaller element). The classical longest-prefix binary search
  over levels is not formalized; instead `XFastTrie.hasPrefix` characterizes level probes
  against `contents`, and successor/predecessor are proved to meet their order-theoretic
  specification.

## Main statements

Insertion preserves `Valid`; under `Valid`, `member` agrees exactly with `contents`
membership, and `hasPrefix l x` holds exactly when some stored key shares the `l`-bit
prefix of `x`. The successor of `x` is `some y` exactly when `y` is the least stored key
greater than `x`, and `none` exactly when no stored key is greater; dually for
predecessor.

## y-fast tries

A y-fast trie stores only Θ(n / w) representative keys in an x-fast trie and keeps the
remaining keys in balanced search trees ("buckets") of Θ(w) keys hung off the
representatives, reducing space to O(n) while keeping O(log w) queries. Only the skeleton
is given here: `YFastTrie` pairs a representative `XFastTrie` with a bucket family, its
`contents` is the union of the representatives' buckets (computed from
`reps.contents`, never by enumerating the `2 ^ w` key universe), and
`YFastTrie.Valid` requires, pointwise, the representatives to be exactly the
owners of nonempty buckets, and each representative to be a stored key in
its own bucket, as in the classical sampled-representatives reading. The bucket ordering
invariant (each bucket holds the keys in the interval up to its representative), the
balanced-tree buckets, and the split/merge maintenance that keeps buckets at Θ(w) keys
are explicitly deferred, as is any complexity statement.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/--
An x-fast trie over `w`-bit keys: the stored key set together with one prefix set per
level. The classical per-level hash tables are modeled as `Finset`s, so no O(log w)
successor bound (or any other running-time bound) is claimed.
-/
public structure XFastTrie (w : Nat) where
  /-- The stored keys. -/
  contents : Finset (Fin (2 ^ w))
  /-- `levels l` holds the `l`-bit prefixes of the stored keys, for `l ≤ w`. -/
  levels : Fin (w + 1) → Finset Nat

namespace XFastTrie

/-- The top `l` bits of a `w`-bit key, as a number below `2 ^ l` (for `l ≤ w`). -/
public def prefixOf {w : Nat} (l : Nat) (x : Fin (2 ^ w)) : Nat :=
  x.val / 2 ^ (w - l)

/-- The empty prefix (the trie root) is `0`. -/
public theorem prefixOf_zero {w : Nat} (x : Fin (2 ^ w)) : prefixOf 0 x = 0 := by
  show x.val / 2 ^ (w - 0) = 0
  rw [Nat.sub_zero]
  exact Nat.div_eq_of_lt x.isLt

/-- The full-length prefix of a key is the key itself. -/
public theorem prefixOf_full {w : Nat} (x : Fin (2 ^ w)) : prefixOf w x = x.val := by
  simp [prefixOf]

/-- An `l`-bit prefix fits in `l` bits. -/
public theorem prefixOf_lt {w l : Nat} (hl : l ≤ w) (x : Fin (2 ^ w)) :
    prefixOf l x < 2 ^ l := by
  show x.val / 2 ^ (w - l) < 2 ^ l
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
  calc
    x.val < 2 ^ w := x.isLt
    _ = 2 ^ l * 2 ^ (w - l) := by rw [← pow_add, Nat.add_sub_cancel' hl]

/-- Every level holds exactly the prefixes of the stored keys at that length. -/
public def Valid {w : Nat} (t : XFastTrie w) : Prop :=
  ∀ l : Fin (w + 1), t.levels l = t.contents.image (fun y => prefixOf l.val y)

/-- The empty x-fast trie: no keys, every level empty. -/
public def empty {w : Nat} : XFastTrie w :=
  ⟨∅, fun _ => ∅⟩

/-- Inserts a key and adds its prefix to every level. -/
public def insert {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) : XFastTrie w :=
  ⟨Insert.insert x t.contents, fun l => Insert.insert (prefixOf l.val x) (t.levels l)⟩

/-- The empty trie satisfies the level invariant. -/
public theorem valid_empty {w : Nat} : (empty : XFastTrie w).Valid := by
  intro l
  show (∅ : Finset Nat) = (∅ : Finset (Fin (2 ^ w))).image (fun y => prefixOf l.val y)
  simp

/-- Insertion preserves the level invariant. -/
public theorem valid_insert {w : Nat} (t : XFastTrie w) (hv : t.Valid)
    (x : Fin (2 ^ w)) : (t.insert x).Valid := by
  intro l
  show Insert.insert (prefixOf l.val x) (t.levels l) =
    (Insert.insert x t.contents).image (fun y => prefixOf l.val y)
  simp only [Finset.image_insert, hv l]

/-- The key set after insertion is the key set with the new key inserted. -/
@[simp]
public theorem contents_insert {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    (t.insert x).contents = Insert.insert x t.contents :=
  rfl

/-- Whether some stored key shares the length-`l` prefix of `x`: the level-`l` probe. -/
public def hasPrefix {w : Nat} (t : XFastTrie w) (l : Fin (w + 1)) (x : Fin (2 ^ w)) :
    Bool :=
  decide (prefixOf l.val x ∈ t.levels l)

/-- Under `Valid`, the level-`l` probe succeeds exactly on shared prefixes. -/
public theorem hasPrefix_iff {w : Nat} (t : XFastTrie w) (hv : t.Valid)
    (l : Fin (w + 1)) (x : Fin (2 ^ w)) :
    t.hasPrefix l x = true ↔ ∃ y ∈ t.contents, prefixOf l.val y = prefixOf l.val x := by
  show decide (prefixOf l.val x ∈ t.levels l) = true ↔ _
  rw [decide_eq_true_eq, hv l, Finset.mem_image]

/-- Membership by a single probe of the deepest level, as in the classical structure. -/
public def member {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) : Bool :=
  t.hasPrefix ⟨w, Nat.lt_succ_self w⟩ x

/-- Under `Valid`, the deepest-level probe decides membership exactly. -/
public theorem member_iff {w : Nat} (t : XFastTrie w) (hv : t.Valid) (x : Fin (2 ^ w)) :
    t.member x = true ↔ x ∈ t.contents := by
  show t.hasPrefix ⟨w, Nat.lt_succ_self w⟩ x = true ↔ _
  rw [hasPrefix_iff t hv]
  constructor
  · rintro ⟨y, hy, hval⟩
    have hyx : y = x := Fin.ext (by simpa [prefixOf_full] using hval)
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A key is a member immediately after its own insertion, with no
validity assumption on `t`: insertion puts the full-length prefix of `x`
directly into the deepest level that `member` probes. -/
public theorem member_insert_self {w : Nat} (t : XFastTrie w)
    (x : Fin (2 ^ w)) : (t.insert x).member x = true := by
  show (t.insert x).hasPrefix ⟨w, Nat.lt_succ_self w⟩ x = true
  show decide (prefixOf w x ∈
    (t.insert x).levels ⟨w, Nat.lt_succ_self w⟩) = true
  rw [decide_eq_true_eq]
  exact Finset.mem_insert_self _ _

/--
The successor of `x`: the least stored key greater than `x`, if one exists. Defined from
`contents`; the classical binary search over levels is not formalized, so no O(log w)
bound is claimed.
-/
public def successor {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  if h : (t.contents.filter (fun y => x < y)).Nonempty then
    some ((t.contents.filter (fun y => x < y)).min' h)
  else
    none

/-- The predecessor of `x`: the greatest stored key smaller than `x`, if one exists. -/
public def predecessor {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  if h : (t.contents.filter (fun y => y < x)).Nonempty then
    some ((t.contents.filter (fun y => y < x)).max' h)
  else
    none

/-- The successor is `some y` exactly when `y` is the least stored key above `x`. -/
public theorem successor_eq_some_iff {w : Nat} (t : XFastTrie w) (x y : Fin (2 ^ w)) :
    t.successor x = some y ↔
      y ∈ t.contents ∧ x < y ∧ ∀ z ∈ t.contents, x < z → y ≤ z := by
  by_cases h : (t.contents.filter (fun y => x < y)).Nonempty
  · have hsucc : t.successor x = some ((t.contents.filter (fun y => x < y)).min' h) := by
      simp [successor, h]
    rw [hsucc]
    constructor
    · intro hsome
      have hym : (t.contents.filter (fun y => x < y)).min' h = y := Option.some.inj hsome
      have hmem := Finset.min'_mem (t.contents.filter (fun y => x < y)) h
      rw [Finset.mem_filter] at hmem
      refine ⟨?_, ?_, ?_⟩
      · rw [← hym]
        exact hmem.1
      · rw [← hym]
        exact hmem.2
      · intro z hz hxz
        rw [← hym]
        exact Finset.min'_le _ z (Finset.mem_filter.mpr ⟨hz, hxz⟩)
    · rintro ⟨hy, hxy, hleast⟩
      have hle1 : (t.contents.filter (fun y => x < y)).min' h ≤ y :=
        Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hxy⟩)
      have hmem := Finset.min'_mem (t.contents.filter (fun y => x < y)) h
      rw [Finset.mem_filter] at hmem
      have hle2 : y ≤ (t.contents.filter (fun y => x < y)).min' h :=
        hleast _ hmem.1 hmem.2
      exact congrArg some (le_antisymm hle1 hle2)
  · have hsucc : t.successor x = none := by
      simp [successor, h]
    rw [hsucc]
    constructor
    · intro hnone
      simp at hnone
    · rintro ⟨hy, hxy, -⟩
      exact absurd ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩ h

/-- The successor is `none` exactly when no stored key is greater than `x`. -/
public theorem successor_eq_none_iff {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    t.successor x = none ↔ ∀ z ∈ t.contents, ¬ x < z := by
  by_cases h : (t.contents.filter (fun y => x < y)).Nonempty
  · have hsucc : t.successor x = some ((t.contents.filter (fun y => x < y)).min' h) := by
      simp [successor, h]
    rw [hsucc]
    constructor
    · intro hEq
      simp at hEq
    · intro hall
      obtain ⟨z, hz⟩ := h
      rw [Finset.mem_filter] at hz
      exact absurd hz.2 (hall z hz.1)
  · have hsucc : t.successor x = none := by
      simp [successor, h]
    rw [hsucc]
    constructor
    · intro _ z hz hxz
      exact absurd ⟨z, Finset.mem_filter.mpr ⟨hz, hxz⟩⟩ h
    · intro _
      rfl

/-- The predecessor is `some y` exactly when `y` is the greatest stored key below `x`. -/
public theorem predecessor_eq_some_iff {w : Nat} (t : XFastTrie w) (x y : Fin (2 ^ w)) :
    t.predecessor x = some y ↔
      y ∈ t.contents ∧ y < x ∧ ∀ z ∈ t.contents, z < x → z ≤ y := by
  by_cases h : (t.contents.filter (fun y => y < x)).Nonempty
  · have hpred : t.predecessor x = some ((t.contents.filter (fun y => y < x)).max' h) := by
      simp [predecessor, h]
    rw [hpred]
    constructor
    · intro hsome
      have hym : (t.contents.filter (fun y => y < x)).max' h = y := Option.some.inj hsome
      have hmem := Finset.max'_mem (t.contents.filter (fun y => y < x)) h
      rw [Finset.mem_filter] at hmem
      refine ⟨?_, ?_, ?_⟩
      · rw [← hym]
        exact hmem.1
      · rw [← hym]
        exact hmem.2
      · intro z hz hzx
        rw [← hym]
        exact Finset.le_max' _ z (Finset.mem_filter.mpr ⟨hz, hzx⟩)
    · rintro ⟨hy, hyx, hgreatest⟩
      have hle1 : y ≤ (t.contents.filter (fun y => y < x)).max' h :=
        Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy, hyx⟩)
      have hmem := Finset.max'_mem (t.contents.filter (fun y => y < x)) h
      rw [Finset.mem_filter] at hmem
      have hle2 : (t.contents.filter (fun y => y < x)).max' h ≤ y :=
        hgreatest _ hmem.1 hmem.2
      exact congrArg some (le_antisymm hle2 hle1)
  · have hpred : t.predecessor x = none := by
      simp [predecessor, h]
    rw [hpred]
    constructor
    · intro hnone
      simp at hnone
    · rintro ⟨hy, hyx, -⟩
      exact absurd ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩ h

/-- The predecessor is `none` exactly when no stored key is smaller than `x`. -/
public theorem predecessor_eq_none_iff {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    t.predecessor x = none ↔ ∀ z ∈ t.contents, ¬ z < x := by
  by_cases h : (t.contents.filter (fun y => y < x)).Nonempty
  · have hpred : t.predecessor x = some ((t.contents.filter (fun y => y < x)).max' h) := by
      simp [predecessor, h]
    rw [hpred]
    constructor
    · intro hEq
      simp at hEq
    · intro hall
      obtain ⟨z, hz⟩ := h
      rw [Finset.mem_filter] at hz
      exact absurd hz.2 (hall z hz.1)
  · have hpred : t.predecessor x = none := by
      simp [predecessor, h]
    rw [hpred]
    constructor
    · intro _ z hz hzx
      exact absurd ⟨z, Finset.mem_filter.mpr ⟨hz, hzx⟩⟩ h
    · intro _
      rfl

end XFastTrie

/--
The y-fast skeleton: an x-fast trie of representative keys, with a bucket of keys per
potential representative. In the classical structure each bucket is a balanced search
tree of Θ(w) keys; here buckets are `Finset`s, and the ordering invariant and split/merge
maintenance are deferred (see the module documentation). No complexity bound is claimed.
-/
public structure YFastTrie (w : Nat) where
  /-- The x-fast trie over representative keys. -/
  reps : XFastTrie w
  /-- The bucket owned by each key; only representatives own nonempty buckets. -/
  buckets : Fin (2 ^ w) → Finset (Fin (2 ^ w))

namespace YFastTrie

/-- All stored keys: the union of the representatives' buckets. Computed
from `reps.contents` (sparse), not by filtering the `2 ^ w`-element key
universe against an existential over all potential owners. -/
public def contents {w : Nat} (t : YFastTrie w) : Finset (Fin (2 ^ w)) :=
  t.reps.contents.biUnion t.buckets

/-- A key is stored exactly when it lies in some representative's bucket. -/
public theorem mem_contents_iff {w : Nat} (t : YFastTrie w) (x : Fin (2 ^ w)) :
    x ∈ t.contents ↔ ∃ r ∈ t.reps.contents, x ∈ t.buckets r := by
  simp [contents]

/--
The representative trie is a valid x-fast trie whose keys are exactly the
owners of nonempty buckets, stated pointwise (no universe-wide filter),
and every representative is itself a stored key, in its own bucket:
representatives are sampled from the stored keys, so a representative `0`
whose bucket is `{1}` (with `contents = {1}`) is not valid. The classical
bucket ordering invariant (keys of bucket `r` lie in the interval ending
at `r`) is deferred, so this is the y-fast skeleton only.
-/
public def Valid {w : Nat} (t : YFastTrie w) : Prop :=
  t.reps.Valid ∧ (∀ r, r ∈ t.reps.contents ↔ t.buckets r ≠ ∅) ∧
    ∀ r ∈ t.reps.contents, r ∈ t.buckets r

/-- Under validity, every representative is a stored key. -/
public theorem rep_mem_contents_of_valid {w : Nat} {t : YFastTrie w}
    (hv : t.Valid) {r : Fin (2 ^ w)} (hr : r ∈ t.reps.contents) :
    r ∈ t.contents := by
  rw [mem_contents_iff]
  exact ⟨r, hr, hv.2.2 r hr⟩

/-- Under validity, a key is stored exactly when it lies in some bucket
(the bucket's owner is then necessarily a representative). -/
public theorem mem_contents_iff_exists_of_valid {w : Nat} {t : YFastTrie w}
    (hv : t.Valid) (x : Fin (2 ^ w)) :
    x ∈ t.contents ↔ ∃ r, x ∈ t.buckets r := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    have hne : t.buckets r ≠ ∅ := by
      intro hempty
      rw [hempty] at hr
      simp at hr
    exact ⟨r, (hv.2.1 r).mpr hne, hr⟩

end YFastTrie

end Cslib.Algorithms.Lean
