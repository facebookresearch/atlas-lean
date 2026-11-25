/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finmap

/-!
# Separate-chaining hash tables

A table has a positive finite bucket count and an explicit hash function. Each bucket is a
canonical `AList` chain, and `HashTable.Valid` requires keys to lie in their hash-selected bucket.

## Main definitions

* `HashTable` stores the bucket count and chains.
* `HashTable.empty`, `HashTable.lookup`, and `HashTable.insert` implement the table operations.
* `HashTable.abstraction` flattens the chains into a bucket-independent Mathlib `Finmap`.

## Main statements

Insertion preserves validity, returns the new value for its key, and preserves other lookups even
when keys collide. For valid tables, lookup and insertion agree with the finite-map abstraction.
No expected-time bound is claimed: the model includes no probability distribution on hashes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/--
**Hash table with separate chaining.** For a key type $\alpha$, a value type $\beta$ and a hash
function $h : \alpha \to \mathbb{N}$, a hash table with hash function $h$ consists of a positive
number $m$ of buckets and, for each bucket index $i < m$, a chain stored at bucket $i$: an
association list of key–value pairs whose keys are pairwise distinct. The structure itself does
not require keys to lie in their hash-selected bucket.

No expected constant-time bound is claimed because the model supplies neither a probability
distribution nor a probabilistic assumption about the hash function.
-/
public structure HashTable (α : Type u) (β : Type v) (hash : α → Nat) where
  /-- The positive number of chains in the table. -/
  bucketCount : Nat
  /-- The table has at least one chain. -/
  bucketCount_pos : 0 < bucketCount
  /-- The canonical association list stored at each bucket. -/
  buckets : Fin bucketCount → AList (fun _ : α => β)

namespace HashTable

private def bucketIndex {α : Type u} {β : Type v} {hash : α → Nat}
    (table : HashTable α β hash) (key : α) : Fin table.bucketCount :=
  ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩

/-- **Empty hash table.** For a hash function $h$ and a positive integer $m$, the empty hash table
with hash function $h$ has $m$ buckets, each holding the empty chain. -/
public def empty {α : Type u} {β : Type v} (hash : α → Nat)
    (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount) : HashTable α β hash where
  bucketCount := bucketCount
  bucketCount_pos := bucketCount_pos
  buckets := fun _ => ∅

/-- **Hash table lookup.** For a hash table with hash function $h$ and $m$ buckets, looking up
a key $k$ searches only the bucket with index $h(k) \bmod m$: the result is the value bound to
$k$ in that bucket's association list, or nothing if $k$ has no binding there. -/
public def lookup {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) : Option β :=
  AList.lookup key (table.buckets
    ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩)

/-- **Insertion into a hash table.** Inserting a key $k$ with value $v$ into a hash table with $m$
buckets and hash function $h$ keeps the bucket count and every bucket other than bucket
$h(k) \bmod m$, and replaces the chain at bucket $h(k) \bmod m$ by that chain with $k$ bound to
$v$: any earlier binding of $k$ in that chain is removed and the binding of $k$ to $v$ is added. -/
public def insert {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (value : β) (table : HashTable α β hash) : HashTable α β hash where
  bucketCount := table.bucketCount
  bucketCount_pos := table.bucketCount_pos
  buckets := Function.update table.buckets
    ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩
    (AList.insert key value (table.buckets
      ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩))

/-- **Valid hash table.** A hash table with hash function $h$ and $m$ buckets is valid when every
binding lies in its hash-selected bucket: for every bucket index $i < m$ and every key $k$, if
$k$ has a binding in bucket $i$, then $h(k) \bmod m = i$.

Keys within a single bucket are distinct automatically, since each bucket is an association list. -/
public def Valid {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (table : HashTable α β hash) : Prop :=
  ∀ (index : Fin table.bucketCount) (key : α),
    (AList.lookup key (table.buckets index)).isSome →
      (⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩ :
        Fin table.bucketCount) = index

/-- **Finite map represented by a hash table.** The finite map represented by a hash table with
$m$ buckets is built from the list of all bindings of buckets $0, 1, \dots, m - 1$, concatenated
in this order: it binds exactly the keys occurring in this list, and binds each such key to the
value of its first binding in the list. -/
public def abstraction {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (table : HashTable α β hash) : Finmap (fun _ : α => β) :=
  ((List.finRange table.bucketCount).flatMap fun index =>
    (table.buckets index).entries).toFinmap

/-- **The empty hash table is valid.** For every hash function $h$ and every positive bucket
count $m$, the empty hash table with hash function $h$ and $m$ buckets is valid. -/
public theorem valid_empty {α : Type u} {β : Type v} (hash : α → Nat) [DecidableEq α]
    (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount) :
    Valid (empty hash bucketCount bucketCount_pos : HashTable α β hash) := by
  intro index key present
  simp [empty] at present

/-- **Lookup in the empty hash table.** For every hash function $h$, every positive bucket count
$m$ and every key $k$, looking up $k$ in the empty hash table with hash function $h$ and $m$
buckets finds no value. -/
@[simp]
public theorem lookup_empty {α : Type u} {β : Type v} (hash : α → Nat) [DecidableEq α]
    (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount) (key : α) :
    lookup key (empty hash bucketCount bucketCount_pos : HashTable α β hash) = none := by
  simp [lookup, empty]

/-- **The empty hash table represents the empty map.** For every hash function $h$ and every
positive bucket count $m$, the finite map represented by the empty hash table with hash function
$h$ and $m$ buckets is the empty finite map. -/
@[simp]
public theorem abstraction_empty {α : Type u} {β : Type v} (hash : α → Nat) [DecidableEq α]
    (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount) :
    abstraction (empty hash bucketCount bucketCount_pos : HashTable α β hash) = ∅ := by
  change
    ((List.finRange bucketCount).flatMap fun _ =>
      ([] : List (Sigma fun _ : α => β))).toFinmap = ∅
  rw [List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl), Finmap.toFinmap_nil]

/-- **Hash table lookup after insertion.** For every hash table $T$, every key $k$ and every
value $v$, looking up $k$ in the table obtained by inserting $k$ with value $v$ into $T$ returns
$v$. -/
public theorem lookup_insert {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (value : β) (table : HashTable α β hash) :
    lookup key (insert key value table) = some value := by
  change AList.lookup key
    (Function.update table.buckets (bucketIndex table key)
      (AList.insert key value (table.buckets (bucketIndex table key)))
      (bucketIndex table key)) = some value
  simp

/-- **Insertion does not affect other keys.** For every hash table $T$, all keys $k \ne k'$ and
every value $v$, looking up $k'$ in the table obtained by inserting $k$ with value $v$ into $T$
gives the same result as looking up $k'$ in $T$, also when $k$ and $k'$ lie in the same bucket. -/
public theorem lookup_insert_of_ne {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key other : α) (value : β) (table : HashTable α β hash)
    (different : other ≠ key) :
    lookup other (insert key value table) = lookup other table := by
  by_cases sameBucket : bucketIndex table other = bucketIndex table key
  · change AList.lookup other
      (Function.update table.buckets (bucketIndex table key)
        (AList.insert key value (table.buckets (bucketIndex table key)))
        (bucketIndex table other)) = AList.lookup other (table.buckets (bucketIndex table other))
    rw [sameBucket]
    simp [different]
  · change AList.lookup other
      (Function.update table.buckets (bucketIndex table key)
        (AList.insert key value (table.buckets (bucketIndex table key)))
        (bucketIndex table other)) = AList.lookup other (table.buckets (bucketIndex table other))
    simp [sameBucket]

/-- **Insertion preserves validity of a hash table.** If a hash table is valid, then the table
obtained from it by inserting a key $k$ with value $v$ (adding a new binding for $k$, or
replacing the existing one) is again valid. -/
public theorem valid_insert {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (value : β) (table : HashTable α β hash) (valid : Valid table) :
    Valid (insert key value table) := by
  change ∀ (index : Fin table.bucketCount) (other : α),
    (AList.lookup other
      (Function.update table.buckets (bucketIndex table key)
        (AList.insert key value (table.buckets (bucketIndex table key))) index)).isSome →
      bucketIndex table other = index
  intro index other present
  by_cases updated : index = bucketIndex table key
  · subst index
    by_cases sameKey : other = key
    · subst other
      rfl
    · have oldPresent : (AList.lookup other (table.buckets (bucketIndex table key))).isSome := by
        simpa [sameKey] using present
      exact valid (bucketIndex table key) other oldPresent
  · have oldPresent : (AList.lookup other (table.buckets index)).isSome := by
      rw [Function.update_of_ne updated] at present
      exact present
    exact valid index other oldPresent

private theorem lookup_entries {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (table : HashTable α β hash) (valid : Valid table) (key : α)
    (indices : List (Fin table.bucketCount)) :
    List.dlookup key (indices.flatMap fun index => (table.buckets index).entries) =
      if bucketIndex table key ∈ indices then lookup key table else none := by
  induction indices with
  | nil => simp
  | cons index rest inductionHypothesis =>
      rw [List.flatMap_cons, List.dlookup_append]
      change (AList.lookup key (table.buckets index)).or
          (List.dlookup key (rest.flatMap fun i => (table.buckets i).entries)) = _
      rw [inductionHypothesis]
      by_cases selected : bucketIndex table key = index
      · subst index
        simp only [List.mem_cons, true_or, ite_true]
        change (lookup key table).or
          (if bucketIndex table key ∈ rest then lookup key table else none) = lookup key table
        cases lookup key table <;> simp
      · have absent : AList.lookup key (table.buckets index) = none := by
          by_contra present
          have isSome : (AList.lookup key (table.buckets index)).isSome :=
            Option.isSome_iff_ne_none.mpr present
          exact selected (valid index key isSome)
        simp [absent, selected]

/-- **Lookup agrees with the abstraction.** For every valid hash table $T$ and every key $k$,
looking up $k$ in the finite map represented by $T$ gives the same result as looking up $k$ in
$T$. -/
public theorem lookup_abstraction {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) (valid : Valid table) :
    Finmap.lookup key (abstraction table) = lookup key table := by
  rw [abstraction, Finmap.dlookup_list_toFinmap]
  rw [lookup_entries table valid key (List.finRange table.bucketCount)]
  simp

/-- **Insertion commutes with the abstraction.** For every valid hash table $T$, every key $k$ and
every value $v$, the finite map represented by the table obtained by inserting $k$ with value $v$
into $T$ equals the finite map represented by $T$ with $k$ bound to $v$, replacing any earlier
binding of $k$. -/
public theorem abstraction_insert {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (value : β) (table : HashTable α β hash)
    (valid : Valid table) :
    abstraction (insert key value table) = Finmap.insert key value (abstraction table) := by
  apply Finmap.ext_lookup
  intro other
  rw [lookup_abstraction other (insert key value table) (valid_insert key value table valid)]
  by_cases same : other = key
  · subst other
    rw [lookup_insert, Finmap.lookup_insert]
  · rw [lookup_insert_of_ne key other value table same]
    rw [Finmap.lookup_insert_of_ne _ same]
    exact (lookup_abstraction other table valid).symm

end HashTable

end Cslib.Algorithms.Lean
