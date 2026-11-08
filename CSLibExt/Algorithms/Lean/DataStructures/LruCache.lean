/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Least-recently-used caches

A list-based LRU cache of capacity `cap`, following the presentation in La Rocca, *Advanced
Algorithms and Data Structures*, Chapter 7. Entries are stored most-recent-first in a list of
key-value pairs. The structure bundles the two invariants: keys are pairwise distinct and the
number of entries never exceeds the capacity.

## Main definitions

* `LruCache` stores the entries together with proofs of the invariants.
* `LruCache.get` looks up a key and promotes its entry to the front on a hit.
* `LruCache.put` inserts or updates a key at the front, dropping entries beyond the capacity.

## Main statements

Lookups hit exactly on stored keys (`get_hit`, `get_miss`), a lookup right after a `put` returns
the stored value (`get_put`), the size and key-uniqueness invariants hold of every cache
(`size_le_cap`, `keys_nodup`), and a key evicted by `put` is the least recently used one
(`evicted_is_least_recent`). State transitions are characterized exactly: `get` permutes the
entries without changing any binding (`get_perm`, `mem_get_entries_iff`, `get_size`), and when
`put` evicts nothing its entries are the new binding plus all surviving old ones
(`mem_put_entries_iff_of_not_full`, `get_put_of_ne`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/-- An LRU cache of capacity `cap`: entries most-recent-first, with the bundled invariants that
keys are pairwise distinct and there are at most `cap` entries. -/
public structure LruCache (K : Type u) (V : Type v) (cap : Nat) where
  /-- The stored key-value pairs, most recently used first. -/
  entries : List (K × V)
  /-- Keys are pairwise distinct. -/
  nodup_keys : (entries.map Prod.fst).Nodup
  /-- The cache holds at most `cap` entries. -/
  length_le : entries.length ≤ cap

namespace LruCache

/-- Two caches with the same entries are equal; the bundled invariant proofs are irrelevant. -/
@[ext]
theorem ext {K : Type u} {V : Type v} {cap : Nat} {a b : LruCache K V cap}
    (h : a.entries = b.entries) : a = b := by
  cases a with
  | mk entries nodup length_le =>
    cases b with
    | mk entries' nodup' length_le' => simp_all

/-- Removes every entry whose key is `k` (at most one, under the uniqueness invariant). -/
def eraseKey {K : Type u} {V : Type v} [DecidableEq K] (k : K)
    (entries : List (K × V)) : List (K × V) :=
  entries.filter fun p => decide (p.1 ≠ k)

theorem mem_eraseKey {K : Type u} {V : Type v} [DecidableEq K] {k : K}
    {p : K × V} {entries : List (K × V)} :
    p ∈ eraseKey k entries ↔ p ∈ entries ∧ p.1 ≠ k := by
  simp [eraseKey, List.mem_filter]

theorem nodup_keys_eraseKey {K : Type u} {V : Type v} [DecidableEq K] {k : K}
    {entries : List (K × V)} (nodup : (entries.map Prod.fst).Nodup) :
    ((eraseKey k entries).map Prod.fst).Nodup :=
  nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)

theorem nodup_keys_cons_eraseKey {K : Type u} {V : Type v} [DecidableEq K] {k : K}
    {entries : List (K × V)} (nodup : (entries.map Prod.fst).Nodup) {p : K × V}
    (hp : p.1 = k) :
    ((p :: eraseKey k entries).map Prod.fst).Nodup := by
  rw [List.map_cons, List.nodup_cons]
  refine ⟨?_, nodup_keys_eraseKey nodup⟩
  rw [hp]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨q, hq, hq1⟩
  exact (mem_eraseKey.mp hq).2 hq1

theorem eq_of_mem_of_fst_eq {K : Type u} {V : Type v} :
    ∀ {entries : List (K × V)}, (entries.map Prod.fst).Nodup →
      ∀ {p q : K × V}, p ∈ entries → q ∈ entries → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | e :: entries, nodup, p, q, hp, hq, hfst => by
      rw [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases List.mem_cons.mp hq with h | hq
        · exact h.symm
        · exfalso
          apply nodup.1
          have h : q.1 ∈ entries.map Prod.fst := List.mem_map_of_mem hq
          rwa [← hfst] at h
      · rcases List.mem_cons.mp hq with hqe | hq
        · exfalso
          apply nodup.1
          have h : p.1 ∈ entries.map Prod.fst := List.mem_map_of_mem hp
          rwa [hfst, hqe] at h
        · exact eq_of_mem_of_fst_eq nodup.2 hp hq hfst

theorem length_eraseKey_add_one {K : Type u} {V : Type v} [DecidableEq K] :
    ∀ {entries : List (K × V)} {k : K} {v : V}, (k, v) ∈ entries →
      (entries.map Prod.fst).Nodup → (eraseKey k entries).length + 1 = entries.length
  | [], _, _, hmem, _ => by simp at hmem
  | e :: entries, k, v, hmem, nodup => by
      have hnodup : ((e :: entries).map Prod.fst).Nodup := nodup
      rw [List.map_cons, List.nodup_cons] at nodup
      by_cases he : e.1 = k
      · have heq : e = (k, v) :=
          eq_of_mem_of_fst_eq hnodup List.mem_cons_self hmem he
        subst heq
        have hfilter : eraseKey k entries = entries := by
          show entries.filter (fun p => decide (p.1 ≠ k)) = entries
          rw [List.filter_eq_self]
          intro p hp
          simp only [decide_eq_true_eq]
          intro hp1
          apply nodup.1
          have h : p.1 ∈ entries.map Prod.fst := List.mem_map_of_mem hp
          rwa [hp1] at h
        have hhead : eraseKey k ((k, v) :: entries) = eraseKey k entries := by
          simp [eraseKey]
        rw [hhead, hfilter]
        simp
      · have hmem' : (k, v) ∈ entries := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd (congrArg Prod.fst h.symm) he
          · exact h
        have hhead : eraseKey k (e :: entries) = e :: eraseKey k entries := by
          simp [eraseKey, he]
        rw [hhead]
        have ih := length_eraseKey_add_one hmem' nodup.2
        simp only [List.length_cons]
        omega

theorem length_eraseKey_le {K : Type u} {V : Type v} [DecidableEq K] {k : K}
    {entries : List (K × V)} :
    (eraseKey k entries).length ≤ entries.length := by
  have h : (entries.filter fun p => decide (p.1 ≠ k)).length ≤ entries.length :=
    List.length_filter_le _ _
  exact h

theorem perm_cons_eraseKey {K : Type u} {V : Type v} [DecidableEq K] :
    ∀ {entries : List (K × V)} {p : K × V}, (entries.map Prod.fst).Nodup →
      p ∈ entries → (p :: eraseKey p.1 entries).Perm entries
  | [], _, _, hp => by simp at hp
  | e :: entries, p, nodup, hp => by
      have hnodup : ((e :: entries).map Prod.fst).Nodup := nodup
      rw [List.map_cons, List.nodup_cons] at nodup
      by_cases he : e.1 = p.1
      · have hpq : p = e :=
          eq_of_mem_of_fst_eq hnodup hp List.mem_cons_self he.symm
        subst hpq
        have hfilter : eraseKey p.1 entries = entries := by
          show entries.filter (fun q => decide (q.1 ≠ p.1)) = entries
          rw [List.filter_eq_self]
          intro q hq
          simp only [decide_eq_true_eq]
          intro hq1
          apply nodup.1
          have h : q.1 ∈ entries.map Prod.fst := List.mem_map_of_mem hq
          rwa [hq1] at h
        have hhead : eraseKey p.1 (p :: entries) = eraseKey p.1 entries := by
          simp [eraseKey]
        rw [hhead, hfilter]
      · have hp' : p ∈ entries := by
          rcases List.mem_cons.mp hp with h | h
          · exact absurd (congrArg Prod.fst h).symm he
          · exact h
        have hhead : eraseKey p.1 (e :: entries) = e :: eraseKey p.1 entries := by
          simp [eraseKey, he]
        rw [hhead]
        exact (List.Perm.swap e p (eraseKey p.1 entries)).trans
          (List.Perm.cons e (perm_cons_eraseKey nodup.2 hp'))

theorem fst_of_find?_eq_some {K : Type u} {V : Type v} [DecidableEq K] {k : K}
    {p : K × V} {entries : List (K × V)}
    (hf : entries.find? (fun q => decide (q.1 = k)) = some p) : p.1 = k := by
  have h := List.find?_some hf
  simpa using h

theorem find?_eq_some_of_mem {K : Type u} {V : Type v} [DecidableEq K]
    {entries : List (K × V)} (nodup : (entries.map Prod.fst).Nodup) {k : K} {v : V}
    (hmem : (k, v) ∈ entries) :
    entries.find? (fun q => decide (q.1 = k)) = some (k, v) := by
  have hsome : (entries.find? (fun q => decide (q.1 = k))).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨(k, v), hmem, by simp⟩
  rcases hf : entries.find? (fun q => decide (q.1 = k)) with _ | p
  · simp [hf] at hsome
  · have hp : p = (k, v) :=
      eq_of_mem_of_fst_eq nodup (List.mem_of_find?_eq_some hf) hmem
        (fst_of_find?_eq_some hf)
    rw [hp] at hf
    exact hf

theorem find?_eq_none_of_not_mem_keys {K : Type u} {V : Type v} [DecidableEq K]
    {entries : List (K × V)} {k : K} (hk : k ∉ entries.map Prod.fst) :
    entries.find? (fun q => decide (q.1 = k)) = none := by
  rcases hf : entries.find? (fun q => decide (q.1 = k)) with _ | p
  · exact hf
  · exfalso
    apply hk
    rw [← fst_of_find?_eq_some hf]
    exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)

/-- The empty cache. -/
public def empty {K : Type u} {V : Type v} {cap : Nat} : LruCache K V cap where
  entries := []
  nodup_keys := by simp
  length_le := Nat.zero_le cap

/-- The cached keys, most recently used first. -/
public def keys {K : Type u} {V : Type v} {cap : Nat} (cache : LruCache K V cap) : List K :=
  cache.entries.map Prod.fst

/-- The number of cached entries. -/
public def size {K : Type u} {V : Type v} {cap : Nat} (cache : LruCache K V cap) : Nat :=
  cache.entries.length

/--
Looks up `k`. On a hit, returns the stored value and the cache with that entry promoted to the
front; on a miss, returns `none` and the unchanged cache.
-/
public def get {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) : Option V × LruCache K V cap :=
  match hf : cache.entries.find? (fun q => decide (q.1 = k)) with
  | some p =>
      (some p.2,
        ⟨p :: eraseKey k cache.entries,
         nodup_keys_cons_eraseKey cache.nodup_keys (fst_of_find?_eq_some hf),
         by
           have hmem : (k, p.2) ∈ cache.entries := by
             have hp : (k, p.2) = p :=
               Prod.ext (fst_of_find?_eq_some hf).symm rfl
             rw [hp]
             exact List.mem_of_find?_eq_some hf
           have hlen := length_eraseKey_add_one hmem cache.nodup_keys
           have hle := cache.length_le
           simp only [List.length_cons]
           omega⟩)
  | none => (none, cache)

/--
Inserts or updates the binding for `k` at the front of the cache, evicting the least recently
used entries if the cache would exceed its capacity.
-/
public def put {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (v : V) : LruCache K V cap where
  entries := ((k, v) :: eraseKey k cache.entries).take cap
  nodup_keys := by
    rw [List.map_take]
    exact (nodup_keys_cons_eraseKey cache.nodup_keys rfl).sublist
      (List.take_sublist cap _)
  length_le := by
    rw [List.length_take]
    exact Nat.min_le_left cap _

/-- The keys of any cache are pairwise distinct. -/
public theorem keys_nodup {K : Type u} {V : Type v} {cap : Nat} (cache : LruCache K V cap) :
    cache.keys.Nodup :=
  cache.nodup_keys

/-- The size of any cache is at most its capacity. -/
public theorem size_le_cap {K : Type u} {V : Type v} {cap : Nat} (cache : LruCache K V cap) :
    cache.size ≤ cap :=
  cache.length_le

/-- A lookup of an absent key misses and leaves the cache unchanged. -/
public theorem get_miss {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k : K} (hk : k ∉ cache.keys) :
    (cache.get k).1 = none ∧ (cache.get k).2 = cache := by
  have hf : cache.entries.find? (fun q => decide (q.1 = k)) = none :=
    find?_eq_none_of_not_mem_keys hk
  unfold get
  split
  next p hpf =>
    rw [hf] at hpf
    cases hpf
  next =>
    exact ⟨rfl, rfl⟩

/-- A lookup of a stored key returns its stored value. -/
public theorem get_hit {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k : K} {v : V} (hmem : (k, v) ∈ cache.entries) :
    (cache.get k).1 = some v := by
  have hf : cache.entries.find? (fun q => decide (q.1 = k)) = some (k, v) :=
    find?_eq_some_of_mem cache.nodup_keys hmem
  unfold get
  split
  next p hpf =>
    have hp : (k, v) = p := Option.some.inj (hf.symm.trans hpf)
    subst hp
    rfl
  next hpf =>
    rw [hf] at hpf
    cases hpf

/-- A successful lookup promotes the entry to the front of the cache. -/
public theorem get_promotes {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k : K} {v : V} (hmem : (k, v) ∈ cache.entries) :
    (cache.get k).2.entries.head? = some (k, v) := by
  have hf : cache.entries.find? (fun q => decide (q.1 = k)) = some (k, v) :=
    find?_eq_some_of_mem cache.nodup_keys hmem
  unfold get
  split
  next p hpf =>
    have hp : (k, v) = p := Option.some.inj (hf.symm.trans hpf)
    subst hp
    rfl
  next hpf =>
    rw [hf] at hpf
    cases hpf

/--
Looking up a key immediately after putting it returns the stored value, provided the capacity
is positive so the new entry is not itself evicted.
-/
public theorem get_put {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (v : V) (hcap : 0 < cap) :
    ((cache.put k v).get k).1 = some v := by
  apply get_hit
  obtain ⟨n, rfl⟩ : ∃ n, cap = n + 1 := ⟨cap - 1, by omega⟩
  show (k, v) ∈ ((k, v) :: eraseKey k cache.entries).take (n + 1)
  exact List.mem_cons_self

/-- `put` preserves the capacity bound. -/
public theorem put_size_le {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (v : V) : (cache.put k v).size ≤ cap :=
  size_le_cap _

/-- `put` preserves key uniqueness. -/
public theorem put_keys_nodup {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (v : V) : (cache.put k v).keys.Nodup :=
  keys_nodup _

/-- `get` preserves the capacity bound. -/
public theorem get_size_le {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) : (cache.get k).2.size ≤ cap :=
  size_le_cap _

/-- `get` preserves key uniqueness. -/
public theorem get_keys_nodup {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) : (cache.get k).2.keys.Nodup :=
  keys_nodup _

/-- Every entry stored by `put` is either the new binding or was already in the cache. -/
public theorem mem_put_entries {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k : K} {v : V} {p : K × V}
    (hp : p ∈ (cache.put k v).entries) :
    p = (k, v) ∨ (p ∈ cache.entries ∧ p.1 ≠ k) := by
  have hp' : p ∈ (k, v) :: eraseKey k cache.entries := List.mem_of_mem_take hp
  rcases List.mem_cons.mp hp' with rfl | hp''
  · exact Or.inl rfl
  · exact Or.inr (mem_eraseKey.mp hp'')

/-- `get` preserves exactly the stored bindings: promotion reorders but neither adds,
removes, nor changes any entry. -/
public theorem mem_get_entries_iff {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (p : K × V) :
    p ∈ (cache.get k).2.entries ↔ p ∈ cache.entries := by
  unfold get
  split
  next q hqf =>
    have hq1 : q.1 = k := fst_of_find?_eq_some hqf
    have hqmem : q ∈ cache.entries := List.mem_of_find?_eq_some hqf
    constructor
    · intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hqmem
      · exact (mem_eraseKey.mp hp).1
    · intro hp
      by_cases hp1 : p.1 = k
      · have hpq : p = q :=
          eq_of_mem_of_fst_eq cache.nodup_keys hp hqmem (by rw [hp1, hq1])
        rw [hpq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem q (mem_eraseKey.mpr ⟨hp, hp1⟩)
  next =>
    exact Iff.rfl

/-- The entries after `get` are a permutation of the entries before: the only effect of a
lookup on the cache state is reordering by promotion. -/
public theorem get_perm {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) :
    (cache.get k).2.entries.Perm cache.entries := by
  unfold get
  split
  next q hqf =>
    have hq1 : q.1 = k := fst_of_find?_eq_some hqf
    have h := perm_cons_eraseKey cache.nodup_keys (List.mem_of_find?_eq_some hqf)
    rwa [hq1] at h
  next =>
    exact List.Perm.refl _

/-- `get` does not change the number of stored entries. -/
public theorem get_size {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) :
    (cache.get k).2.size = cache.size :=
  (get_perm cache k).length_eq

/-- When `put` evicts nothing, because the cache is not full or the key replaces an
existing binding, the stored entries are characterized exactly: the new binding together
with every previously stored binding for a different key, values unchanged. -/
public theorem mem_put_entries_iff_of_not_full {K : Type u} {V : Type v} {cap : Nat}
    [DecidableEq K] {cache : LruCache K V cap} {k : K} {v : V} {p : K × V}
    (hroom : cache.size < cap ∨ k ∈ cache.keys) :
    p ∈ (cache.put k v).entries ↔ p = (k, v) ∨ (p ∈ cache.entries ∧ p.1 ≠ k) := by
  have hlen : ((k, v) :: eraseKey k cache.entries).length ≤ cap := by
    have hle : (eraseKey k cache.entries).length ≤ cache.entries.length :=
      length_eraseKey_le
    rcases hroom with h | h
    · simp only [List.length_cons]
      have hsize : cache.size = cache.entries.length := rfl
      omega
    · rcases List.mem_map.mp h with ⟨⟨k', w⟩, hmem, hk'⟩
      simp only [Prod.fst] at hk'
      subst hk'
      have h1 := length_eraseKey_add_one hmem cache.nodup_keys
      have h2 := cache.length_le
      simp only [List.length_cons]
      omega
  show p ∈ ((k, v) :: eraseKey k cache.entries).take cap ↔ _
  rw [List.take_of_length_le hlen]
  constructor
  · intro hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (mem_eraseKey.mp hp)
  · rintro (rfl | ⟨hp, hp1⟩)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_eraseKey.mpr ⟨hp, hp1⟩)

/-- With positive capacity, the binding stored by `put` is the most recent entry. -/
public theorem put_head? {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    (cache : LruCache K V cap) (k : K) (v : V) (hcap : 0 < cap) :
    (cache.put k v).entries.head? = some (k, v) := by
  obtain ⟨n, rfl⟩ : ∃ n, cap = n + 1 := ⟨cap - 1, by omega⟩
  rfl

/-- Looking up a different key after a `put` that evicts nothing returns exactly what the
lookup returned before the `put`: surviving bindings keep their values. -/
public theorem get_put_of_ne {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k k' : K} {v : V} (hne : k' ≠ k)
    (hroom : cache.size < cap ∨ k ∈ cache.keys) :
    ((cache.put k v).get k').1 = (cache.get k').1 := by
  by_cases hk' : k' ∈ cache.keys
  · rcases List.mem_map.mp hk' with ⟨⟨a, w⟩, hmem, ha⟩
    rw [show (a, w) = (k', w) from Prod.ext ha rfl] at hmem
    have hputmem : (k', w) ∈ (cache.put k v).entries := by
      rw [mem_put_entries_iff_of_not_full hroom]
      exact Or.inr ⟨hmem, hne⟩
    rw [get_hit hputmem, get_hit hmem]
  · have hk'miss : k' ∉ (cache.put k v).keys := by
      intro hkm
      rcases List.mem_map.mp hkm with ⟨p, hp, hp1⟩
      rw [mem_put_entries_iff_of_not_full hroom] at hp
      apply hk'
      rcases hp with rfl | ⟨hp, _⟩
      · simp only [Prod.fst] at hp1
        exact absurd hp1.symm hne
      · rw [← hp1]
        exact List.mem_map_of_mem hp
    rw [(get_miss hk'miss).1, (get_miss hk').1]

/--
The key evicted by inserting a new key is the least recently used one: if a stored key `k`
disappears after putting a key `k'` that was not in the cache, the cache was full and `k` was
the last (least recent) key.
-/
public theorem evicted_is_least_recent {K : Type u} {V : Type v} {cap : Nat} [DecidableEq K]
    {cache : LruCache K V cap} {k k' : K} {v : V}
    (hnew : k' ∉ cache.keys) (hk : k ∈ cache.keys)
    (hevicted : k ∉ (cache.put k' v).keys) :
    cache.keys.getLast? = some k ∧ cache.size = cap := by
  have herase : eraseKey k' cache.entries = cache.entries := by
    show cache.entries.filter (fun p => decide (p.1 ≠ k')) = cache.entries
    rw [List.filter_eq_self]
    intro p hp
    simp only [decide_eq_true_eq]
    intro hp1
    apply hnew
    show k' ∈ cache.entries.map Prod.fst
    rw [← hp1]
    exact List.mem_map_of_mem hp
  have hputkeys : (cache.put k' v).keys = (k' :: cache.keys).take cap := by
    show (((k', v) :: eraseKey k' cache.entries).take cap).map Prod.fst =
      (k' :: cache.keys).take cap
    rw [herase, List.map_take, List.map_cons]
    rfl
  rw [hputkeys] at hevicted
  set L := k' :: cache.keys with hL
  have hkL : k ∈ L := List.mem_cons_of_mem k' hk
  have hsplit : L.take cap ++ L.drop cap = L := List.take_append_drop cap L
  have hkdrop : k ∈ L.drop cap := by
    have hmem : k ∈ L.take cap ++ L.drop cap := by
      rw [hsplit]
      exact hkL
    rcases List.mem_append.mp hmem with h | h
    · exact absurd h hevicted
    · exact h
  have hlenL : L.length = cache.size + 1 := by
    rw [hL]
    simp [keys, size]
  have hle : cache.size ≤ cap := cache.length_le
  have hdrop_len : (L.drop cap).length = 1 := by
    have hlen := List.length_drop (i := cap) (l := L)
    have hpos : 0 < (L.drop cap).length := by
      cases h : L.drop cap with
      | nil =>
          rw [h] at hkdrop
          exact (List.not_mem_nil hkdrop).elim
      | cons a t =>
          simp
    omega
  have hsize : cache.size = cap := by
    have hlen := List.length_drop (i := cap) (l := L)
    omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hdrop_len
  have hak : k = a := by
    rw [ha] at hkdrop
    exact List.mem_singleton.mp hkdrop
  subst hak
  have hlastL : L.getLast? = some k := by
    rw [← hsplit, ha, List.getLast?_append]
    simp
  refine ⟨?_, hsize⟩
  rw [hL, List.getLast?_cons] at hlastL
  have hne : cache.keys.getLast? ≠ none := by
    rw [Ne, List.getLast?_eq_none_iff]
    exact List.ne_nil_of_mem hk
  rcases hgl : cache.keys.getLast? with _ | x
  · exact absurd hgl hne
  · rw [hgl] at hlastL
    simp at hlastL
    rw [hlastL]

end LruCache

end Cslib.Algorithms.Lean
