/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LruCache

/-!
# Tests for LRU caches

Client examples exercise capacity zero, insertion into a non-full cache, full-cache
eviction, replacement without duplicate keys, hit promotion, miss stability, and the
state-preservation laws. The final commands audit the transitive axioms of every
public theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LruCacheTests

open Cslib.Algorithms.Lean

private def c2 : LruCache Nat String 2 := LruCache.empty

-- Miss on the empty cache leaves it unchanged.
example : (c2.get 1).1 = none := by decide
example : (c2.get 1).2.entries = c2.entries := by decide

-- Insertion into a non-full cache, then hit.
example : ((c2.put 1 "one").get 1).1 = some "one" := by decide
example : (c2.put 1 "one").entries = [(1, "one")] := by decide
example : ((c2.put 1 "one").put 2 "two").entries = [(2, "two"), (1, "one")] := by decide

-- Hit promotion: key 1 becomes most recent.
example : (((c2.put 1 "one").put 2 "two").get 1).2.entries =
    [(1, "one"), (2, "two")] := by decide

-- Full-cache eviction: without promotion, 1 is least recent and is evicted by 3.
example : (((c2.put 1 "one").put 2 "two").put 3 "three").entries =
    [(3, "three"), (2, "two")] := by decide
-- After promoting 1, key 2 is least recent and is evicted instead.
example : ((((c2.put 1 "one").put 2 "two").get 1).2.put 3 "three").entries =
    [(3, "three"), (1, "one")] := by decide

-- Replacement updates the value without duplicating the key or evicting others.
example : ((c2.put 1 "one").put 1 "uno").entries = [(1, "uno")] := by decide
example : (((c2.put 1 "one").put 2 "two").put 1 "uno").entries =
    [(1, "uno"), (2, "two")] := by decide

-- Capacity zero stores nothing and every lookup misses.
private def c0 : LruCache Nat String 0 := LruCache.empty
example : (c0.put 1 "one").entries = [] := by decide
example : ((c0.put 1 "one").get 1).1 = none := by decide
example : (c0.put 1 "one").size = 0 := by decide

-- Capacity one keeps only the most recent binding.
private def c1 : LruCache Nat String 1 := LruCache.empty
example : ((c1.put 1 "one").put 2 "two").entries = [(2, "two")] := by decide

-- State-preservation laws through the public API.
example (c : LruCache Nat String 3) (k : Nat) (p : Nat × String) :
    p ∈ (c.get k).2.entries ↔ p ∈ c.entries := LruCache.mem_get_entries_iff c k p
example (c : LruCache Nat String 3) (k : Nat) :
    (c.get k).2.entries.Perm c.entries := LruCache.get_perm c k
example (c : LruCache Nat String 3) (k : Nat) :
    (c.get k).2.size = c.size := LruCache.get_size c k
example (c : LruCache Nat String 3) (v : String) :
    (c.put 7 v).entries.head? = some (7, v) := LruCache.put_head? c 7 v (by decide)
example (p : Nat × String) (h : c2.size < 2 ∨ 1 ∈ c2.keys) :
    p ∈ (c2.put 1 "one").entries ↔ p = (1, "one") ∨ (p ∈ c2.entries ∧ p.1 ≠ 1) :=
  LruCache.mem_put_entries_iff_of_not_full h
example (h : c2.size < 2 ∨ 1 ∈ c2.keys) :
    ((c2.put 1 "one").get 2).1 = (c2.get 2).1 :=
  LruCache.get_put_of_ne (by decide) h

/-- Extensionality: caches are equal exactly when their entries agree. -/
example (a b : LruCache Nat String 2) (h : a.entries = b.entries) : a = b :=
  LruCache.ext h
example (a b : LruCache Nat String 2) (h : a.entries = b.entries) : a = b := by
  apply LruCache.ext
  exact h
example (a b : LruCache Nat String 2) : a = b ↔ a.entries = b.entries :=
  LruCache.ext_iff
example : c2.put 1 "one" = c2.put 1 "one" := by
  apply LruCache.ext
  rfl

end Cslib.Algorithms.Lean.LruCacheTests

#print axioms Cslib.Algorithms.Lean.LruCache.keys_nodup
#print axioms Cslib.Algorithms.Lean.LruCache.size_le_cap
#print axioms Cslib.Algorithms.Lean.LruCache.get_miss
#print axioms Cslib.Algorithms.Lean.LruCache.get_hit
#print axioms Cslib.Algorithms.Lean.LruCache.get_promotes
#print axioms Cslib.Algorithms.Lean.LruCache.get_put
#print axioms Cslib.Algorithms.Lean.LruCache.mem_put_entries
#print axioms Cslib.Algorithms.Lean.LruCache.mem_get_entries_iff
#print axioms Cslib.Algorithms.Lean.LruCache.get_perm
#print axioms Cslib.Algorithms.Lean.LruCache.get_size
#print axioms Cslib.Algorithms.Lean.LruCache.mem_put_entries_iff_of_not_full
#print axioms Cslib.Algorithms.Lean.LruCache.put_head?
#print axioms Cslib.Algorithms.Lean.LruCache.get_put_of_ne
#print axioms Cslib.Algorithms.Lean.LruCache.evicted_is_least_recent
#print axioms Cslib.Algorithms.Lean.LruCache.put_size_le
#print axioms Cslib.Algorithms.Lean.LruCache.put_keys_nodup
#print axioms Cslib.Algorithms.Lean.LruCache.get_size_le
#print axioms Cslib.Algorithms.Lean.LruCache.get_keys_nodup
#print axioms Cslib.Algorithms.Lean.LruCache.ext
#print axioms Cslib.Algorithms.Lean.LruCache.ext_iff
