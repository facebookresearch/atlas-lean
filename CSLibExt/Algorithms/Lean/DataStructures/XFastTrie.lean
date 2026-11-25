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
**x-fast trie.** An x-fast trie over $w$-bit keys consists of a finite set of stored keys in
$\{0, \dots, 2^w - 1\}$ together with, for each level $l \in \{0, \dots, w\}$, a finite set of
natural numbers, intended to hold the $l$-bit prefixes of the stored keys.

The classical per-level hash tables are modeled as finite sets, so no $O(\log w)$ successor bound
(or any other running-time bound) is claimed.
-/
public structure XFastTrie (w : Nat) where
  /-- The stored keys. -/
  contents : Finset (Fin (2 ^ w))
  /-- `levels l` holds the `l`-bit prefixes of the stored keys, for `l ≤ w`. -/
  levels : Fin (w + 1) → Finset Nat

namespace XFastTrie

/-- **Bit prefix of a key.** For natural numbers $l$ and $w$ and a $w$-bit key $x < 2^w$,
the length-$l$ prefix of $x$ is the natural number $\lfloor x / 2^{w-l} \rfloor$, where
$w - l$ is truncated subtraction (it is $0$ when $l > w$). For $l \le w$ these are the top
$l$ bits of $x$, a number below $2^l$. -/
public def prefixOf {w : Nat} (l : Nat) (x : Fin (2 ^ w)) : Nat :=
  x.val / 2 ^ (w - l)

/-- **The empty prefix is zero.** For every $w$-bit key $x < 2^w$, the length-$0$ prefix
of $x$ (the trie root) is $0$. -/
public theorem prefixOf_zero {w : Nat} (x : Fin (2 ^ w)) : prefixOf 0 x = 0 := by
  show x.val / 2 ^ (w - 0) = 0
  rw [Nat.sub_zero]
  exact Nat.div_eq_of_lt x.isLt

/-- **The full-length prefix of a key is the key.** For every $w$-bit key $x < 2^w$, the
length-$w$ prefix of $x$ equals $x$. -/
public theorem prefixOf_full {w : Nat} (x : Fin (2 ^ w)) : prefixOf w x = x.val := by
  simp [prefixOf]

/-- **A prefix fits in its length.** For natural numbers $l \le w$ and a $w$-bit key
$x < 2^w$, the length-$l$ prefix of $x$ is less than $2^l$. -/
public theorem prefixOf_lt {w l : Nat} (hl : l ≤ w) (x : Fin (2 ^ w)) :
    prefixOf l x < 2 ^ l := by
  show x.val / 2 ^ (w - l) < 2 ^ l
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
  calc
    x.val < 2 ^ w := x.isLt
    _ = 2 ^ l * 2 ^ (w - l) := by rw [← pow_add, Nat.add_sub_cancel' hl]

/-- **Valid x-fast trie.** An x-fast trie $t$ over $w$-bit keys is valid when, for every level
$l \in \{0, \dots, w\}$, the level-$l$ set of $t$ equals the set of $l$-bit prefixes (top $l$
bits) of the stored keys of $t$. -/
public def Valid {w : Nat} (t : XFastTrie w) : Prop :=
  ∀ l : Fin (w + 1), t.levels l = t.contents.image (fun y => prefixOf l.val y)

/-- **The empty x-fast trie.** The empty x-fast trie over $w$-bit keys stores no keys, and the
prefix set at each of its levels $0, 1, \dots, w$ is empty. -/
public def empty {w : Nat} : XFastTrie w :=
  ⟨∅, fun _ => ∅⟩

/-- **Insertion into an x-fast trie.** Inserting a $w$-bit key $x$ into an x-fast trie $t$ adds $x$
to the keys stored in $t$ and, for each level $0 \le l \le w$, adds the $l$-bit prefix of $x$ to
the prefix set at level $l$. -/
public def insert {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) : XFastTrie w :=
  ⟨Insert.insert x t.contents, fun l => Insert.insert (prefixOf l.val x) (t.levels l)⟩

/-- **The empty x-fast trie is valid.** For every $w$, the empty x-fast trie over $w$-bit keys,
which has no stored keys and every level empty, is valid. -/
public theorem valid_empty {w : Nat} : (empty : XFastTrie w).Valid := by
  intro l
  show (∅ : Finset Nat) = (∅ : Finset (Fin (2 ^ w))).image (fun y => prefixOf l.val y)
  simp

/-- **Insertion preserves validity of an x-fast trie.** If $t$ is a valid x-fast trie over
$w$-bit keys and $x \in \{0, \dots, 2^w - 1\}$, then the x-fast trie obtained from $t$ by
inserting $x$ is valid. -/
public theorem valid_insert {w : Nat} (t : XFastTrie w) (hv : t.Valid)
    (x : Fin (2 ^ w)) : (t.insert x).Valid := by
  intro l
  show Insert.insert (prefixOf l.val x) (t.levels l) =
    (Insert.insert x t.contents).image (fun y => prefixOf l.val y)
  simp only [Finset.image_insert, hv l]

/-- **Keys of an x-fast trie after insertion.** For every x-fast trie $t$ over $w$-bit keys and
every $w$-bit key $x$, the set of keys stored in the trie obtained by inserting $x$ into $t$ is
the set of keys stored in $t$ with $x$ added. -/
@[simp]
public theorem contents_insert {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    (t.insert x).contents = Insert.insert x t.contents :=
  rfl

/-- **Level probe of an x-fast trie.** For an x-fast trie $t$ over $w$-bit keys, a level
$0 \le l \le w$ and a $w$-bit key $x$, the probe of level $l$ of $t$ at $x$ returns true exactly
when the $l$-bit prefix of $x$ belongs to the prefix set stored at level $l$ of $t$.

When $t$ is valid, this holds exactly when some key stored in $t$ has the same $l$-bit prefix
as $x$. -/
public def hasPrefix {w : Nat} (t : XFastTrie w) (l : Fin (w + 1)) (x : Fin (2 ^ w)) :
    Bool :=
  decide (prefixOf l.val x ∈ t.levels l)

/-- **Level probes of a valid x-fast trie.** Let $t$ be a valid x-fast trie over $w$-bit keys,
let $0 \le l \le w$ and let $x$ be a $w$-bit key. The probe of level $l$ of $t$ at $x$ succeeds if
and only if some key $y$ stored in $t$ has the same $l$-bit prefix as $x$. -/
public theorem hasPrefix_iff {w : Nat} (t : XFastTrie w) (hv : t.Valid)
    (l : Fin (w + 1)) (x : Fin (2 ^ w)) :
    t.hasPrefix l x = true ↔ ∃ y ∈ t.contents, prefixOf l.val y = prefixOf l.val x := by
  show decide (prefixOf l.val x ∈ t.levels l) = true ↔ _
  rw [decide_eq_true_eq, hv l, Finset.mem_image]

/-- **Membership query in an x-fast trie.** For an x-fast trie $t$ over $w$-bit keys
and a key $x < 2^w$, the membership query of $x$ in $t$ answers true exactly when the
length-$w$ prefix of $x$, which is $x$ itself, lies in the prefix set that $t$ stores
for level $w$: a single probe of the deepest level, as in the classical structure. -/
public def member {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) : Bool :=
  t.hasPrefix ⟨w, Nat.lt_succ_self w⟩ x

/-- **The membership test of a valid x-fast trie is exact.** For a valid x-fast trie $t$ over
$w$-bit keys and a $w$-bit key $x$, the membership test of $t$ at $x$, which probes the deepest
level $w$, returns true if and only if $x$ is stored in $t$. -/
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

/-- **An inserted key passes the membership test.** For every x-fast trie $t$ over $w$-bit keys
and every $w$-bit key $x$, the membership test at $x$ of the trie obtained by inserting $x$ into
$t$ returns true.

No validity assumption on $t$ is needed: insertion puts the full-length prefix of $x$ directly
into the deepest level, which is the level the membership test probes. -/
public theorem member_insert_self {w : Nat} (t : XFastTrie w)
    (x : Fin (2 ^ w)) : (t.insert x).member x = true := by
  show (t.insert x).hasPrefix ⟨w, Nat.lt_succ_self w⟩ x = true
  show decide (prefixOf w x ∈
    (t.insert x).levels ⟨w, Nat.lt_succ_self w⟩) = true
  rw [decide_eq_true_eq]
  exact Finset.mem_insert_self _ _

/--
**Successor in an x-fast trie.** For an x-fast trie $t$ over $w$-bit keys and a key
$x \in \{0, \dots, 2^w - 1\}$, the successor of $x$ in $t$ is the least stored key of $t$ that is
greater than $x$ when some stored key is greater than $x$; otherwise $x$ has no successor in $t$.

It is computed directly from the stored key set rather than by the classical binary search over
the levels, so no $O(\log w)$ time bound is claimed.
-/
public def successor {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  if h : (t.contents.filter (fun y => x < y)).Nonempty then
    some ((t.contents.filter (fun y => x < y)).min' h)
  else
    none

/-- **Predecessor query in an x-fast trie.** For an x-fast trie $t$ over $w$-bit keys and
a key $x < 2^w$, the predecessor of $x$ in $t$ is the greatest key stored in $t$ that is
smaller than $x$, if such a key exists; otherwise the query returns no key. -/
public def predecessor {w : Nat} (t : XFastTrie w) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  if h : (t.contents.filter (fun y => y < x)).Nonempty then
    some ((t.contents.filter (fun y => y < x)).max' h)
  else
    none

/-- **Characterization of the x-fast trie successor.** Let $t$ be an x-fast trie over $w$-bit
keys and let $x$ and $y$ be keys in $\{0, \dots, 2^w - 1\}$. The successor of $x$ in $t$ exists
and equals $y$ if and only if $y$ is a stored key of $t$, $x < y$, and $y \le z$ for every stored
key $z$ of $t$ with $x < z$. -/
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

/-- **When an x-fast trie has no successor.** For an x-fast trie $t$ over $w$-bit keys
and a key $x < 2^w$, the successor query of $x$ in $t$ returns no key if and only if no
key stored in $t$ is greater than $x$. -/
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

/-- **Characterization of the x-fast trie predecessor.** For an x-fast trie $t$ over
$w$-bit keys and keys $x, y < 2^w$, the predecessor query of $x$ in $t$ returns $y$ if and
only if $y$ is stored in $t$, $y < x$, and every key $z$ stored in $t$ with $z < x$
satisfies $z \le y$. -/
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

/-- **When an x-fast trie has no predecessor.** For an x-fast trie $t$ over $w$-bit keys
and a key $x < 2^w$, the predecessor query of $x$ in $t$ returns no key if and only if
no key stored in $t$ is smaller than $x$. -/
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
**y-fast trie skeleton.** A y-fast trie skeleton over $w$-bit keys consists of an x-fast trie
over $w$-bit keys, whose stored keys are the representatives, together with a bucket $B_r$, a
finite set of keys, for every key $r \in \{0, \dots, 2^w - 1\}$.

In the classical structure each bucket is a balanced search tree of $\Theta(w)$ keys; here buckets
are plain finite sets, the bucket ordering invariant and the split and merge maintenance are not
modeled, and no complexity bound is claimed.
-/
public structure YFastTrie (w : Nat) where
  /-- The x-fast trie over representative keys. -/
  reps : XFastTrie w
  /-- The bucket owned by each key; only representatives own nonempty buckets. -/
  buckets : Fin (2 ^ w) → Finset (Fin (2 ^ w))

namespace YFastTrie

/-- **Keys of a y-fast trie.** Let $t$ be a y-fast trie over $w$-bit keys, let $R$ be the set of
keys stored in the representative x-fast trie of $t$, and for each $r \in R$ let $B(r)$ be the
bucket owned by $r$. The set of keys stored in $t$ is the union of the buckets of its
representatives, $\bigcup_{r \in R} B(r)$.

It is computed from the representatives alone, not by filtering all $2^w$ possible keys. -/
public def contents {w : Nat} (t : YFastTrie w) : Finset (Fin (2 ^ w)) :=
  t.reps.contents.biUnion t.buckets

/-- **Membership in a y-fast trie via representatives' buckets.** For every y-fast trie $t$ over
$w$-bit keys and every $w$-bit key $x$, $x$ is stored in $t$ if and only if $x$ lies in the bucket
owned by some representative of $t$, that is, by some key stored in the representative x-fast
trie of $t$. -/
public theorem mem_contents_iff {w : Nat} (t : YFastTrie w) (x : Fin (2 ^ w)) :
    x ∈ t.contents ↔ ∃ r ∈ t.reps.contents, x ∈ t.buckets r := by
  simp [contents]

/--
**Valid y-fast trie skeleton.** A y-fast trie skeleton $t$ over $w$-bit keys, with bucket $B_r$
owned by each key $r$, is valid when its representative x-fast trie is valid, a key $r$ is stored
in the representative x-fast trie exactly when its bucket $B_r$ is nonempty, and every key $r$
stored in the representative x-fast trie lies in its own bucket $B_r$.

So the representatives are sampled from the stored keys: a representative $0$ whose bucket is
$\{1\}$ is not valid. The classical bucket ordering invariant (the keys of bucket $B_r$ lie in
the interval ending at $r$) is not required, so this is the invariant of the skeleton only.
-/
public def Valid {w : Nat} (t : YFastTrie w) : Prop :=
  t.reps.Valid ∧ (∀ r, r ∈ t.reps.contents ↔ t.buckets r ≠ ∅) ∧
    ∀ r ∈ t.reps.contents, r ∈ t.buckets r

/-- **Representatives of a valid y-fast trie are stored keys.** If a y-fast trie $t$ over
$w$-bit keys is valid, then every key of the representative x-fast trie of $t$ is a stored
key of $t$. -/
public theorem rep_mem_contents_of_valid {w : Nat} {t : YFastTrie w}
    (hv : t.Valid) {r : Fin (2 ^ w)} (hr : r ∈ t.reps.contents) :
    r ∈ t.contents := by
  rw [mem_contents_iff]
  exact ⟨r, hr, hv.2.2 r hr⟩

/-- **Keys of a valid y-fast trie are the keys in buckets.** If $t$ is a valid y-fast trie over
$w$-bit keys, then a $w$-bit key $x$ is stored in $t$ if and only if $x$ lies in the bucket owned
by some $w$-bit key $r$ (such an owner $r$ is then necessarily a representative). -/
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
