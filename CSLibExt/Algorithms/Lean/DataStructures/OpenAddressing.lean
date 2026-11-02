/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Vector.Lemmas

/-!
# Open-addressing hash tables

An open-addressing table (CLRS, Section 11.4) stores at most one key-value pair per
slot. The table has `m` slots and a probe sequence `probe k 0, probe k 1, …` per key,
supplied as a parameter. `lookup` walks the key's probe sequence and stops at the
first slot holding the key (success), at the first empty slot (failure), or after `m`
probes (failure). `insert` walks the same sequence and stops at the first slot that
is empty or already holds the key, writing the new binding there; it returns `none`
when the first `m` probes are all occupied by other keys. For probe sequences that
are permutations of the slots, failure is exactly the statement that the table is
full, but no permutation property is assumed here.

## Main definitions

* `OpenAddressing` stores the slots as a `Vector (Option (K × V)) m`.
* `OpenAddressing.empty`, `OpenAddressing.lookup`, and `OpenAddressing.insert`
  implement the table operations by bounded recursion on a fuel of `m` attempts.
* `OpenAddressing.Valid` is the probe-closed invariant plus key uniqueness: every
  stored key is reached by its own probe sequence before any empty slot, and no key
  is stored in two different slots. Uniqueness is what makes `insert` a genuine
  replacement: in a valid table there is no stale second binding for the key.
* `OpenAddressing.linearProbe` and `OpenAddressing.doubleHashProbe` are the usual
  linear-probing and double-hashing probe sequences.

## Specification choice

Unlike separate chaining (`HashTable`), there is no bucket-independent `Finmap`
abstraction: with no uniqueness or permutation assumption on `probe`, the contents
of the table are specified instead by the `Stored` predicate, which states that some
slot holds the given binding; under `Valid` the binding for a key is unique
(`stored_unique`). The main correctness statements are that a successful
insert is found by `lookup` with the inserted value, that insertion preserves
`Valid`, that under `Valid` a lookup returns `some value` if and only if
`Stored table key value` (`lookup_eq_some_iff`), and that an insert leaves
every other key's stored binding and lookup unchanged (`stored_insert_of_ne`,
`lookup_insert_of_ne`).

Deletion is out of scope. Clearing a slot breaks probe-closedness for keys stored
later along the same probe sequence; CLRS repairs searches with a `DELETED`
tombstone marker, which this model does not have.

No expected-time bound is claimed: the model supplies neither a probability
distribution nor a uniform-hashing assumption about `probe`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/--
**Open-addressing hash table.** Let $K$ be a type of keys, $V$ a type of values, $m$ a natural
number, and $p$ a probe sequence assigning to each key $k$ and each $i \in \mathbb{N}$ a slot
$p(k, i) \in \{0, \dots, m - 1\}$. An open-addressing hash table with $m$ slots and probe
sequence $p$ consists of $m$ slots, each either empty or holding a single pair $(k, v)$ with
$k \in K$ and $v \in V$.

No expected constant-time bound is claimed because the model supplies neither a probability
distribution nor a uniform-hashing assumption about the probe sequence.
-/
public structure OpenAddressing (K : Type u) (V : Type v) (m : Nat)
    (probe : K → Nat → Fin m) where
  /-- The `m` slots, each empty or holding one key-value pair. -/
  slots : Vector (Option (K × V)) m

namespace OpenAddressing

/-- **Linear-probing probe sequence.** Given a hash function $h : K \to \mathbb{N}$ and a
number of slots $m > 0$, the $i$-th probe of a key $k$ is the slot $(h(k) + i) \bmod m$ in
$\{0, \dots, m - 1\}$. -/
public def linearProbe {K : Type u} (hash : K → Nat) (m : Nat) (hm : 0 < m) :
    K → Nat → Fin m :=
  fun k i => ⟨(hash k + i) % m, Nat.mod_lt _ hm⟩

/-- **Double-hashing probe sequence.** Given hash functions $h_1, h_2 : K \to \mathbb{N}$ and a
number of slots $m > 0$, the $i$-th probe of a key $k$ is the slot
$(h_1(k) + i \cdot h_2(k)) \bmod m$ in $\{0, \dots, m - 1\}$. -/
public def doubleHashProbe {K : Type u} (hash1 hash2 : K → Nat) (m : Nat)
    (hm : 0 < m) : K → Nat → Fin m :=
  fun k i => ⟨(hash1 k + i * hash2 k) % m, Nat.mod_lt _ hm⟩

variable {K : Type u} {V : Type v} {m : Nat} {probe : K → Nat → Fin m}

variable [DecidableEq K]

/-- **Empty open-addressing table.** The open-addressing table with $m$ slots and a given probe
sequence in which every slot is empty. -/
public def empty : OpenAddressing K V m probe :=
  ⟨Vector.replicate m none⟩

/--
**Bounded lookup scan.** Given a table with $m$ slots and probe sequence $p$, a key $k$, a
starting index $s$ and a budget $f$ of probes, examine the slots $p(k, s), p(k, s + 1), \dots$ in
order, for at most $f$ probes. The scan returns the value bound to $k$ in the first examined slot
that holds a binding for $k$, and returns no value if it first reaches an empty slot or exhausts
the budget.

This is the helper behind lookup, which starts at index $0$ with budget $m$.
-/
def lookupAux (table : OpenAddressing K V m probe) (key : K) (start : Nat) :
    Nat → Option V
  | 0 => none
  | fuel + 1 =>
      match table.slots.get (probe key start) with
      | none => none
      | some (k', value) =>
          if k' = key then some value else lookupAux table key (start + 1) fuel

/--
**Lookup in an open-addressing table.** Let $T$ be an open-addressing hash table with $m$ slots
and probe sequence $p$, and let $k$ be a key. The lookup of $k$ in $T$ inspects the slots
$p(k, 0), p(k, 1), \dots, p(k, m - 1)$ in this order. It returns the value $v$ of the first
inspected slot that holds a pair $(k, v)$, and returns nothing if an empty slot is inspected
first or if none of the $m$ inspected slots holds the key $k$.
-/
public def lookup (table : OpenAddressing K V m probe) (key : K) : Option V :=
  lookupAux table key 0 m

/--
**Bounded insertion scan.** Given a table with $m$ slots and probe sequence $p$, a key $k$, a
value $v$, a starting index $s$ and a budget $f$ of probes, examine the slots
$p(k, s), p(k, s + 1), \dots$ in order, for at most $f$ probes. At the first examined slot that
is empty or holds a binding for $k$, the scan returns the table with that slot overwritten by the
binding $k \mapsto v$ and every other slot unchanged; if all $f$ examined slots hold bindings for
other keys (in particular if $f = 0$), it fails and returns no table.

This is the helper behind insertion, which starts at index $0$ with budget $m$.
-/
def insertAux (table : OpenAddressing K V m probe) (key : K) (value : V)
    (start : Nat) : Nat → Option (OpenAddressing K V m probe)
  | 0 => none
  | fuel + 1 =>
      match table.slots.get (probe key start) with
      | none =>
          some ⟨table.slots.set (probe key start).val (some (key, value))
            (probe key start).isLt⟩
      | some (k', _) =>
          if k' = key then
            some ⟨table.slots.set (probe key start).val (some (key, value))
              (probe key start).isLt⟩
          else
            insertAux table key value (start + 1) fuel

/--
**Insertion into an open-addressing table.** To insert the binding $k \mapsto v$ into a table
with $m$ slots and probe sequence $p$, examine the slots $p(k, 0), p(k, 1), \dots, p(k, m - 1)$
in order. At the first one that is empty or already holds a binding for $k$, write $k \mapsto v$
there, leaving every other slot unchanged, and return the updated table. If all $m$ examined
slots hold bindings for other keys, the insertion fails and returns no table.
-/
public def insert (table : OpenAddressing K V m probe) (key : K) (value : V) :
    Option (OpenAddressing K V m probe) :=
  insertAux table key value 0 m

/--
**Valid open-addressing tables.** Let $T$ be an open-addressing table with $m$ slots and probe
sequence $p$, where $p(k, i) \in \{0, \dots, m - 1\}$ is the slot visited by the $i$-th probe of
key $k$. Then $T$ is valid when it satisfies two conditions. Probe-closedness: whenever slot $j$
holds a binding $k \mapsto v$, there is an $i < m$ with $p(k, i) = j$ such that the slots
$p(k, i')$ are occupied for all $i' < i$; this is what lets a lookup stop at the first empty
slot. Key uniqueness: if slots $j_1$ and $j_2$ hold bindings with the same key $k$, then
$j_1 = j_2$; so each key has at most one binding and insertion genuinely replaces it.
-/
public def Valid (table : OpenAddressing K V m probe) : Prop :=
  (∀ (j : Fin m) (key : K) (value : V), table.slots.get j = some (key, value) →
    ∃ i < m, probe key i = j ∧
      ∀ i' < i, (table.slots.get (probe key i')).isSome) ∧
  (∀ (j₁ j₂ : Fin m) (key : K) (value₁ value₂ : V),
    table.slots.get j₁ = some (key, value₁) →
    table.slots.get j₂ = some (key, value₂) → j₁ = j₂)

/--
**Stored binding in an open-addressing table.** An open-addressing hash table $T$ stores the
binding $k \mapsto v$ when some slot of $T$ holds the pair $(k, v)$.
-/
public def Stored (table : OpenAddressing K V m probe) (key : K) (value : V) :
    Prop :=
  ∃ j : Fin m, table.slots.get j = some (key, value)

omit [DecidableEq K] in
private theorem slots_get_set (slots : Vector (Option (K × V)) m) (i j : Fin m)
    (a : Option (K × V)) :
    (slots.set i.val a i.isLt).get j = if i = j then a else slots.get j := by
  change (slots.set i.val a i.isLt)[j.val] =
    if i = j then a else slots[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

omit [DecidableEq K] in
omit [DecidableEq K] in
private theorem slots_get_set_self (slots : Vector (Option (K × V)) m) (i : Fin m)
    (a : Option (K × V)) :
    (slots.set i.val a i.isLt).get i = a := by
  simp [slots_get_set]

omit [DecidableEq K] in
omit [DecidableEq K] in
private theorem slots_get_set_ne (slots : Vector (Option (K × V)) m) (i j : Fin m)
    (a : Option (K × V)) (different : i ≠ j) :
    (slots.set i.val a i.isLt).get j = slots.get j := by
  simp [slots_get_set, different]

omit [DecidableEq K] in
private theorem slots_get_replicate (i : Fin m) :
    (Vector.replicate m (none : Option (K × V))).get i = none := by
  change (Vector.replicate m (none : Option (K × V)))[i.val] = none
  simp

private theorem stored_of_lookupAux_eq_some (table : OpenAddressing K V m probe)
    (key : K) :
    ∀ (start fuel : Nat) (value : V),
      lookupAux table key start fuel = some value → Stored table key value := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro value found
      simp [lookupAux] at found
  | succ fuel inductionHypothesis =>
      intro value found
      cases slot : table.slots.get (probe key start) with
      | none => simp [lookupAux, slot] at found
      | some pair =>
          obtain ⟨otherKey, otherValue⟩ := pair
          by_cases same : otherKey = key
          · have equalValues : otherValue = value := by
              simpa [lookupAux, slot, same] using found
            exact ⟨probe key start, by rw [slot, same, equalValues]⟩
          · simp [lookupAux, slot, same] at found
            exact inductionHypothesis (start + 1) value found

private theorem lookupAux_eq_some_of_first (table : OpenAddressing K V m probe)
    (key : K) :
    ∀ (start fuel attempts : Nat) (value : V), attempts < fuel →
      table.slots.get (probe key (start + attempts)) = some (key, value) →
      (∀ e < attempts, ∃ (otherKey : K) (otherValue : V),
        table.slots.get (probe key (start + e)) = some (otherKey, otherValue) ∧
          otherKey ≠ key) →
      lookupAux table key start fuel = some value := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro attempts value withinFuel _ _
      exact absurd withinFuel (Nat.not_lt_zero attempts)
  | succ fuel inductionHypothesis =>
      intro attempts value withinFuel target earlier
      cases slot : table.slots.get (probe key start) with
      | none =>
          cases attempts with
          | zero =>
              simp only [Nat.add_zero] at target
              rw [slot] at target
              exact absurd target (by simp)
          | succ attempts =>
              obtain ⟨otherKey, otherValue, occupied, unusedDifferent⟩ :=
                earlier 0 (Nat.zero_lt_succ attempts)
              simp only [Nat.add_zero] at occupied
              rw [slot] at occupied
              exact absurd occupied (by simp)
      | some pair =>
          obtain ⟨otherKey, otherValue⟩ := pair
          by_cases same : otherKey = key
          · cases attempts with
            | zero =>
                simp only [Nat.add_zero] at target
                rw [slot] at target
                simp only [Option.some.injEq, Prod.mk.injEq] at target
                simp [lookupAux, slot, same, target.2]
            | succ attempts =>
                obtain ⟨firstKey, firstValue, occupied, different⟩ :=
                  earlier 0 (Nat.zero_lt_succ attempts)
                simp only [Nat.add_zero] at occupied
                rw [slot] at occupied
                simp only [Option.some.injEq, Prod.mk.injEq] at occupied
                exact absurd (occupied.1.symm.trans same) different
          · cases attempts with
            | zero =>
                simp only [Nat.add_zero] at target
                rw [slot] at target
                simp only [Option.some.injEq, Prod.mk.injEq] at target
                exact absurd target.1 same
            | succ attempts =>
                have target' :
                    table.slots.get (probe key (start + 1 + attempts)) =
                      some (key, value) := by
                  rw [show start + 1 + attempts = start + (attempts + 1) by omega]
                  exact target
                have earlier' :
                    ∀ e < attempts, ∃ (otherKey : K) (otherValue : V),
                      table.slots.get (probe key (start + 1 + e)) =
                          some (otherKey, otherValue) ∧ otherKey ≠ key := by
                  intro e beforeAttempts
                  obtain ⟨otherKey, otherValue, occupied, different⟩ :=
                    earlier (e + 1) (by omega)
                  refine ⟨otherKey, otherValue, ?_, different⟩
                  rw [show start + 1 + e = start + (e + 1) by omega]
                  exact occupied
                simp only [lookupAux, slot, same]
                exact inductionHypothesis (start + 1) attempts value
                  (by omega) target' earlier'

private theorem lookupAux_isSome_of_reachable (table : OpenAddressing K V m probe)
    (key : K) :
    ∀ (start fuel attempts : Nat) (value : V), attempts < fuel →
      table.slots.get (probe key (start + attempts)) = some (key, value) →
      (∀ e < attempts, (table.slots.get (probe key (start + e))).isSome) →
      (lookupAux table key start fuel).isSome := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro attempts value withinFuel _ _
      exact absurd withinFuel (Nat.not_lt_zero attempts)
  | succ fuel inductionHypothesis =>
      intro attempts value withinFuel target earlier
      cases slot : table.slots.get (probe key start) with
      | none =>
          cases attempts with
          | zero =>
              simp only [Nat.add_zero] at target
              rw [slot] at target
              exact absurd target (by simp)
          | succ attempts =>
              have occupied := earlier 0 (Nat.zero_lt_succ attempts)
              simp [slot] at occupied
      | some pair =>
          obtain ⟨otherKey, otherValue⟩ := pair
          by_cases same : otherKey = key
          · simp [lookupAux, slot, same]
          · cases attempts with
            | zero =>
                simp only [Nat.add_zero] at target
                rw [slot] at target
                simp only [Option.some.injEq, Prod.mk.injEq] at target
                exact absurd target.1 same
            | succ attempts =>
                have target' :
                    table.slots.get (probe key (start + 1 + attempts)) =
                      some (key, value) := by
                  rw [show start + 1 + attempts = start + (attempts + 1) by omega]
                  exact target
                have earlier' :
                    ∀ e < attempts,
                      (table.slots.get (probe key (start + 1 + e))).isSome := by
                  intro e beforeAttempts
                  have occupied := earlier (e + 1) (by omega)
                  rwa [show start + 1 + e = start + (e + 1) by omega]
                simp only [lookupAux, slot, same]
                exact inductionHypothesis (start + 1) attempts value
                  (by omega) target' earlier'

private theorem insertAux_spec (table : OpenAddressing K V m probe) (key : K)
    (value : V) :
    ∀ (start fuel : Nat) (updated : OpenAddressing K V m probe),
      insertAux table key value start fuel = some updated →
      ∃ attempts < fuel,
        updated.slots = table.slots.set (probe key (start + attempts)).val
            (some (key, value)) (probe key (start + attempts)).isLt ∧
        (∀ e < attempts, ∃ (otherKey : K) (otherValue : V),
          table.slots.get (probe key (start + e)) =
              some (otherKey, otherValue) ∧ otherKey ≠ key) ∧
        (table.slots.get (probe key (start + attempts)) = none ∨
          ∃ oldValue : V,
            table.slots.get (probe key (start + attempts)) =
              some (key, oldValue)) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro updated inserted
      simp [insertAux] at inserted
  | succ fuel inductionHypothesis =>
      intro updated inserted
      cases slot : table.slots.get (probe key start) with
      | none =>
          have updatedEq : updated =
              ⟨table.slots.set (probe key start).val (some (key, value))
                (probe key start).isLt⟩ := by
            have step : insertAux table key value start (fuel + 1) =
                some ⟨table.slots.set (probe key start).val (some (key, value))
                  (probe key start).isLt⟩ := by
              simp [insertAux, slot]
            rw [step] at inserted
            exact (Option.some.inj inserted).symm
          refine ⟨0, Nat.zero_lt_succ fuel, ?_, ?_, ?_⟩
          · rw [updatedEq]
            simp
          · intro e beforeZero
            exact absurd beforeZero (Nat.not_lt_zero e)
          · exact Or.inl (by simpa using slot)
      | some pair =>
          obtain ⟨otherKey, otherValue⟩ := pair
          by_cases same : otherKey = key
          · have updatedEq : updated =
                ⟨table.slots.set (probe key start).val (some (key, value))
                  (probe key start).isLt⟩ := by
              have step : insertAux table key value start (fuel + 1) =
                  some ⟨table.slots.set (probe key start).val (some (key, value))
                    (probe key start).isLt⟩ := by
                simp [insertAux, slot, same]
              rw [step] at inserted
              exact (Option.some.inj inserted).symm
            refine ⟨0, Nat.zero_lt_succ fuel, ?_, ?_, ?_⟩
            · rw [updatedEq]
              simp
            · intro e beforeZero
              exact absurd beforeZero (Nat.not_lt_zero e)
            · exact Or.inr ⟨otherValue, by simpa [same] using slot⟩
          · have step : insertAux table key value (start + 1) fuel =
                some updated := by
              have unfoldStep : insertAux table key value start (fuel + 1) =
                  insertAux table key value (start + 1) fuel := by
                simp [insertAux, slot, same]
              rw [unfoldStep] at inserted
              exact inserted
            obtain ⟨attempts, withinFuel, slotsEq, earlier, target⟩ :=
              inductionHypothesis (start + 1) updated step
            refine ⟨attempts + 1, by omega, ?_, ?_, ?_⟩
            · have indexEq : probe key (start + (attempts + 1)) =
                  probe key (start + 1 + attempts) := by
                congr 1
                omega
              rw [indexEq]
              exact slotsEq
            · intro e beforeAttempts
              cases e with
              | zero =>
                  exact ⟨otherKey, otherValue, by simpa using slot, same⟩
              | succ e =>
                  obtain ⟨firstKey, firstValue, occupied, different⟩ :=
                    earlier e (by omega)
                  refine ⟨firstKey, firstValue, ?_, different⟩
                  have indexEq : probe key (start + (e + 1)) =
                      probe key (start + 1 + e) := by
                    congr 1
                    omega
                  rw [indexEq]
                  exact occupied
            · have indexEq : probe key (start + (attempts + 1)) =
                  probe key (start + 1 + attempts) := by
                congr 1
                omega
              rw [indexEq]
              exact target

private theorem occupied_of_insertAux_eq_none
    (table : OpenAddressing K V m probe) (key : K) (value : V) :
    ∀ (start fuel : Nat), insertAux table key value start fuel = none →
      ∀ attempts < fuel, ∃ (otherKey : K) (otherValue : V),
        table.slots.get (probe key (start + attempts)) =
            some (otherKey, otherValue) ∧ otherKey ≠ key := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _ attempts withinFuel
      exact absurd withinFuel (Nat.not_lt_zero attempts)
  | succ fuel inductionHypothesis =>
      intro failed attempts withinFuel
      cases slot : table.slots.get (probe key start) with
      | none => simp [insertAux, slot] at failed
      | some pair =>
          obtain ⟨otherKey, otherValue⟩ := pair
          by_cases same : otherKey = key
          · simp [insertAux, slot, same] at failed
          · cases attempts with
            | zero =>
                exact ⟨otherKey, otherValue, by simpa using slot, same⟩
            | succ attempts =>
                have step : insertAux table key value (start + 1) fuel =
                    none := by
                  have unfoldStep : insertAux table key value start
                      (fuel + 1) =
                      insertAux table key value (start + 1) fuel := by
                    simp [insertAux, slot, same]
                  rw [unfoldStep] at failed
                  exact failed
                obtain ⟨firstKey, firstValue, occupied, different⟩ :=
                  inductionHypothesis (start + 1) step attempts (by omega)
                refine ⟨firstKey, firstValue, ?_, different⟩
                have indexEq : probe key (start + (attempts + 1)) =
                    probe key (start + 1 + attempts) := by
                  congr 1
                  omega
                rw [indexEq]
                exact occupied

private theorem lookupAux_empty (key : K) :
    ∀ (start fuel : Nat),
      lookupAux (empty : OpenAddressing K V m probe) key start fuel = none := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel _ =>
      have slot : (empty : OpenAddressing K V m probe).slots.get
          (probe key start) = none :=
        slots_get_replicate (probe key start)
      simp [lookupAux, slot]

omit [DecidableEq K] in
/--
**The empty open-addressing table is valid.** For all types $K$ and $V$, every number of
slots $m$ and every probe sequence $p$, which assigns to each key $k$ and each $i \in \mathbb{N}$
a slot $p(k, i) \in \{0, \dots, m - 1\}$, the empty table with $m$ slots and probe sequence $p$,
in which every slot is vacant, is valid: it is probe-closed and no key is stored in two
different slots.
-/
public theorem valid_empty :
    Valid (empty : OpenAddressing K V m probe) := by
  constructor
  · intro j key value occupied
    have vacant : (empty : OpenAddressing K V m probe).slots.get j = none :=
      slots_get_replicate j
    rw [vacant] at occupied
    exact absurd occupied (by simp)
  · intro j₁ _ key _ _ occupied _
    have vacant : (empty : OpenAddressing K V m probe).slots.get j₁ = none :=
      slots_get_replicate j₁
    rw [vacant] at occupied
    exact absurd occupied (by simp)

/-- **Lookup in the empty open-addressing table.** For every key $k$, looking up $k$ in the empty
open-addressing table returns no value. -/
@[simp]
public theorem lookup_empty (key : K) :
    lookup (empty : OpenAddressing K V m probe) key = none := by
  simp only [lookup]
  exact lookupAux_empty key 0 m

/--
**Lookup after a successful open-addressing insertion.** If inserting the binding $k \mapsto v$
into an open-addressing hash table $T$ succeeds and yields the table $T'$, then looking up $k$
in $T'$ returns $v$. No validity assumption on $T$ is needed.
-/
public theorem lookup_insert (table : OpenAddressing K V m probe) (key : K)
    (value : V) (updated : OpenAddressing K V m probe)
    (inserted : insert table key value = some updated) :
    lookup updated key = some value := by
  have insertedAux : insertAux table key value 0 m = some updated := by
    simpa [insert] using inserted
  obtain ⟨attempts, withinFuel, slotsEq, earlier, target⟩ :=
    insertAux_spec table key value 0 m updated insertedAux
  simp only [lookup]
  apply lookupAux_eq_some_of_first updated key 0 m attempts value withinFuel
  · rw [slotsEq]
    exact slots_get_set_self table.slots (probe key (0 + attempts))
      (some (key, value))
  · intro e beforeAttempts
    obtain ⟨otherKey, otherValue, occupied, different⟩ :=
      earlier e beforeAttempts
    by_cases sameSlot : probe key (0 + e) = probe key (0 + attempts)
    · cases target with
      | inl vacant =>
          rw [sameSlot, vacant] at occupied
          exact absurd occupied (by simp)
      | inr old =>
          obtain ⟨oldValue, oldOccupied⟩ := old
          rw [sameSlot, oldOccupied] at occupied
          simp only [Option.some.injEq, Prod.mk.injEq] at occupied
          exact absurd occupied.1.symm different
    · refine ⟨otherKey, otherValue, ?_, different⟩
      rw [slotsEq, slots_get_set_ne table.slots (probe key (0 + attempts))
        (probe key (0 + e)) (some (key, value))
        (fun equal => sameSlot equal.symm)]
      exact occupied

/--
**Insertion preserves validity of an open-addressing table.** Let $T$ be a valid table with $m$
slots and probe sequence $p$, whose keys have decidable equality. If inserting the binding
$k \mapsto v$ into $T$ (adding it, or replacing the binding already stored for $k$) succeeds and
returns the table $T'$, then $T'$ is valid: it is probe-closed and no key is stored in two
different slots.
-/
public theorem valid_insert (table : OpenAddressing K V m probe) (key : K)
    (value : V) (updated : OpenAddressing K V m probe) (valid : Valid table)
    (inserted : insert table key value = some updated) :
    Valid updated := by
  have insertedAux : insertAux table key value 0 m = some updated := by
    simpa [insert] using inserted
  obtain ⟨attempts, withinFuel, slotsEq, earlier, target⟩ :=
    insertAux_spec table key value 0 m updated insertedAux
  obtain ⟨hReach, hUnique⟩ := valid
  have writtenValue : updated.slots.get (probe key (0 + attempts)) =
      some (key, value) := by
    rw [slotsEq]
    exact slots_get_set_self table.slots (probe key (0 + attempts))
      (some (key, value))
  have unchangedElsewhere : ∀ j : Fin m,
      j ≠ probe key (0 + attempts) →
      updated.slots.get j = table.slots.get j := by
    intro j different
    rw [slotsEq, slots_get_set_ne table.slots (probe key (0 + attempts)) j
      (some (key, value)) (fun equal => different equal.symm)]
  have occupiedMono : ∀ j : Fin m, (table.slots.get j).isSome →
      (updated.slots.get j).isSome := by
    intro j occupied
    by_cases sameSlot : j = probe key (0 + attempts)
    · rw [sameSlot, writtenValue]
      rfl
    · rw [unchangedElsewhere j sameSlot]
      exact occupied
  have hOldKeyOnly : ∀ (j : Fin m) (v : V),
      table.slots.get j = some (key, v) → j = probe key (0 + attempts) := by
    intro j v hj
    cases target with
    | inr old =>
        obtain ⟨oldValue, hold⟩ := old
        exact hUnique j _ key v oldValue hj (by simpa using hold)
    | inl vacant =>
        obtain ⟨i, _, hpi, hearlier⟩ := hReach j key v hj
        by_cases hlt : i < attempts
        · exfalso
          obtain ⟨ok, _, hocc, hdiff⟩ := earlier i hlt
          simp only [Nat.zero_add] at hocc
          rw [hpi, hj] at hocc
          simp only [Option.some.injEq, Prod.mk.injEq] at hocc
          exact hdiff hocc.1.symm
        · by_cases heq : i = attempts
          · subst heq
            simpa using hpi.symm
          · exfalso
            have hgt : attempts < i := by omega
            have hocc := hearlier attempts hgt
            simp only [Nat.zero_add] at vacant
            rw [vacant] at hocc
            exact absurd hocc (by simp)
  constructor
  · intro j storedKey storedValue stored
    by_cases sameSlot : j = probe key (0 + attempts)
    · rw [sameSlot, writtenValue] at stored
      simp only [Option.some.injEq, Prod.mk.injEq] at stored
      obtain ⟨rfl, rfl⟩ := stored
      refine ⟨attempts, withinFuel, by simpa using sameSlot.symm, ?_⟩
      intro e beforeAttempts
      obtain ⟨unusedKey, unusedValue, occupiedEarlier, unusedDifferent⟩ :=
        earlier e beforeAttempts
      have occupiedUpdated :=
        occupiedMono (probe key (0 + e)) (by rw [occupiedEarlier]; rfl)
      simpa using occupiedUpdated
    · have storedOld : table.slots.get j = some (storedKey, storedValue) := by
        rw [unchangedElsewhere j sameSlot] at stored
        exact stored
      obtain ⟨i, withinSlots, probeEq, earlierOccupied⟩ :=
        hReach j storedKey storedValue storedOld
      exact ⟨i, withinSlots, probeEq,
        fun e beforeI => occupiedMono _ (earlierOccupied e beforeI)⟩
  · intro j₁ j₂ k v₁ v₂ h₁ h₂
    by_cases hj₁ : j₁ = probe key (0 + attempts)
    · by_cases hj₂ : j₂ = probe key (0 + attempts)
      · rw [hj₁, hj₂]
      · rw [hj₁, writtenValue] at h₁
        simp only [Option.some.injEq, Prod.mk.injEq] at h₁
        have hk : k = key := h₁.1.symm
        have h₂old : table.slots.get j₂ = some (key, v₂) := by
          rw [unchangedElsewhere j₂ hj₂] at h₂
          rw [hk] at h₂
          exact h₂
        exact absurd (hOldKeyOnly j₂ v₂ h₂old) hj₂
    · by_cases hj₂ : j₂ = probe key (0 + attempts)
      · rw [hj₂, writtenValue] at h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h₂
        have hk : k = key := h₂.1.symm
        have h₁old : table.slots.get j₁ = some (key, v₁) := by
          rw [unchangedElsewhere j₁ hj₁] at h₁
          rw [hk] at h₁
          exact h₁
        exact absurd (hOldKeyOnly j₁ v₁ h₁old) hj₁
      · have h₁old : table.slots.get j₁ = some (k, v₁) := by
          rw [unchangedElsewhere j₁ hj₁] at h₁
          exact h₁
        have h₂old : table.slots.get j₂ = some (k, v₂) := by
          rw [unchangedElsewhere j₂ hj₂] at h₂
          exact h₂
        exact hUnique j₁ j₂ k v₁ v₂ h₁old h₂old

/--
**Open-addressing lookup returns only stored bindings.** If looking up a key $k$ in an
open-addressing hash table $T$ returns the value $v$, then $T$ stores the binding $k \mapsto v$.
No validity assumption is needed.
-/
public theorem stored_of_lookup_eq_some (table : OpenAddressing K V m probe)
    (key : K) (value : V) (found : lookup table key = some value) :
    Stored table key value := by
  have foundAux : lookupAux table key 0 m = some value := by
    simpa [lookup] using found
  exact stored_of_lookupAux_eq_some table key 0 m value foundAux

/-- **Lookup of an absent key fails.** Let $T$ be an open-addressing table and $k$ a key such that
no slot of $T$ stores a binding $k \mapsto v$ for any value $v$. Then looking up $k$ in $T$ returns
no value. No validity assumption on $T$ is needed. -/
public theorem lookup_eq_none_of_not_stored (table : OpenAddressing K V m probe)
    (key : K) (absent : ∀ value : V, ¬ Stored table key value) :
    lookup table key = none := by
  cases result : lookup table key with
  | none => rfl
  | some value =>
      exact absurd (stored_of_lookup_eq_some table key value result)
        (absent value)

/--
**Valid open-addressing tables find every stored key.** If a valid open-addressing hash table
$T$ stores the binding $k \mapsto v$, then looking up $k$ in $T$ returns some value.
-/
public theorem lookup_isSome_of_stored (table : OpenAddressing K V m probe)
    (key : K) (value : V) (valid : Valid table)
    (stored : Stored table key value) :
    (lookup table key).isSome := by
  obtain ⟨j, occupied⟩ := stored
  obtain ⟨i, withinSlots, probeEq, earlierOccupied⟩ :=
    valid.1 j key value occupied
  simp only [lookup]
  apply lookupAux_isSome_of_reachable table key 0 m i value withinSlots
  · have probeEq' : probe key (0 + i) = j := by simpa using probeEq
    rw [probeEq']
    exact occupied
  · intro e beforeI
    have occupiedEarlier := earlierOccupied e beforeI
    simpa using occupiedEarlier

/--
**Open-addressing lookup succeeds exactly on stored keys.** Let $T$ be a valid open-addressing
hash table and $k$ a key. Looking up $k$ in $T$ returns a value if and only if $T$ stores a
binding $k \mapsto v$ for some value $v$.

This membership characterization is used in place of a finite-map abstraction of the table.
-/
public theorem lookup_isSome_iff (table : OpenAddressing K V m probe) (key : K)
    (valid : Valid table) :
    (lookup table key).isSome ↔ ∃ value : V, Stored table key value := by
  constructor
  · intro found
    obtain ⟨value, foundEq⟩ := Option.isSome_iff_exists.mp found
    exact ⟨value, stored_of_lookup_eq_some table key value foundEq⟩
  · rintro ⟨value, stored⟩
    exact lookup_isSome_of_stored table key value valid stored

omit [DecidableEq K] in
/--
**Bindings in a valid open-addressing table are unique.** If a valid open-addressing hash
table $T$ stores both $k \mapsto v_1$ and $k \mapsto v_2$, then $v_1 = v_2$.
-/
public theorem stored_unique (table : OpenAddressing K V m probe)
    (valid : Valid table) {key : K} {value₁ value₂ : V}
    (stored₁ : Stored table key value₁) (stored₂ : Stored table key value₂) :
    value₁ = value₂ := by
  obtain ⟨j₁, h₁⟩ := stored₁
  obtain ⟨j₂, h₂⟩ := stored₂
  have sameSlot : j₁ = j₂ := valid.2 j₁ j₂ key value₁ value₂ h₁ h₂
  subst sameSlot
  rw [h₁] at h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₂
  exact h₂.2

/--
**Lookup in a valid table returns exactly the stored binding.** Let $T$ be a valid
open-addressing table, $k$ a key and $v$ a value. Then looking up $k$ in $T$ returns $v$ if and
only if the binding $k \mapsto v$ is stored in some slot of $T$.

Together with the fact that lookup after a successful insertion of $k \mapsto v$ returns $v$, this
says that a successful insertion really replaces the old binding: no other value for $k$ remains
stored afterwards.
-/
public theorem lookup_eq_some_iff (table : OpenAddressing K V m probe)
    (key : K) (value : V) (valid : Valid table) :
    lookup table key = some value ↔ Stored table key value := by
  constructor
  · exact stored_of_lookup_eq_some table key value
  · intro stored
    have isSome := lookup_isSome_of_stored table key value valid stored
    obtain ⟨value', foundEq⟩ := Option.isSome_iff_exists.mp isSome
    have stored' := stored_of_lookup_eq_some table key value' foundEq
    have : value' = value := stored_unique table valid stored' stored
    rw [foundEq, this]

/--
**Open-addressing insertion leaves other keys' bindings unchanged.** Let $T$ be an
open-addressing hash table, and suppose that inserting the binding $k \mapsto v$ into $T$
succeeds and yields the table $T'$. Then for every key $k' \neq k$ and every value $v'$, the
table $T'$ stores $k' \mapsto v'$ if and only if $T$ stores $k' \mapsto v'$.

No validity assumption is needed: the insertion writes a single slot, previously empty or
previously holding $k$, and leaves every other slot unchanged.
-/
public theorem stored_insert_of_ne (table : OpenAddressing K V m probe) (key : K)
    (value : V) (updated : OpenAddressing K V m probe)
    (inserted : insert table key value = some updated) {other : K}
    (different : other ≠ key) {otherValue : V} :
    Stored updated other otherValue ↔ Stored table other otherValue := by
  have insertedAux : insertAux table key value 0 m = some updated := by
    simpa [insert] using inserted
  obtain ⟨attempts, _, slotsEq, _, target⟩ :=
    insertAux_spec table key value 0 m updated insertedAux
  have writtenValue : updated.slots.get (probe key (0 + attempts)) =
      some (key, value) := by
    rw [slotsEq]
    exact slots_get_set_self table.slots (probe key (0 + attempts))
      (some (key, value))
  have unchangedElsewhere : ∀ j : Fin m,
      j ≠ probe key (0 + attempts) →
      updated.slots.get j = table.slots.get j := by
    intro j differentSlot
    rw [slotsEq, slots_get_set_ne table.slots (probe key (0 + attempts)) j
      (some (key, value)) (fun equal => differentSlot equal.symm)]
  constructor
  · rintro ⟨j, hj⟩
    by_cases sameSlot : j = probe key (0 + attempts)
    · rw [sameSlot, writtenValue] at hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      exact absurd hj.1.symm different
    · exact ⟨j, by rw [unchangedElsewhere j sameSlot] at hj; exact hj⟩
  · rintro ⟨j, hj⟩
    by_cases sameSlot : j = probe key (0 + attempts)
    · cases target with
      | inl vacant =>
          rw [sameSlot] at hj
          rw [hj] at vacant
          exact absurd vacant (by simp)
      | inr old =>
          obtain ⟨oldValue, oldOccupied⟩ := old
          rw [sameSlot, oldOccupied] at hj
          simp only [Option.some.injEq, Prod.mk.injEq] at hj
          exact absurd hj.1.symm different
    · exact ⟨j, by rw [unchangedElsewhere j sameSlot]; exact hj⟩

/--
**Insertion does not affect lookups of other keys.** Let $T$ be a valid open-addressing table and
suppose inserting the binding $k \mapsto v$ into $T$ succeeds with result $T'$. Then for every key
$k' \ne k$, looking up $k'$ in $T'$ gives the same result as looking up $k'$ in $T$.

Together with the fact that looking up $k$ in $T'$ returns $v$, this is the map-update
specification of insertion, matching the corresponding statement for separate chaining.
-/
public theorem lookup_insert_of_ne (table : OpenAddressing K V m probe) (key : K)
    (value : V) (updated : OpenAddressing K V m probe) (valid : Valid table)
    (inserted : insert table key value = some updated) {other : K}
    (different : other ≠ key) :
    lookup updated other = lookup table other := by
  have validUpdated : Valid updated :=
    valid_insert table key value updated valid inserted
  cases result : lookup table other with
  | none =>
      apply lookup_eq_none_of_not_stored
      intro otherValue storedUpdated
      have storedTable : Stored table other otherValue :=
        (stored_insert_of_ne table key value updated inserted different).mp
          storedUpdated
      have found : lookup table other = some otherValue :=
        (lookup_eq_some_iff table other otherValue valid).mpr storedTable
      rw [result] at found
      exact absurd found (by simp)
  | some otherValue =>
      have storedTable : Stored table other otherValue :=
        stored_of_lookup_eq_some table other otherValue result
      have storedUpdated : Stored updated other otherValue :=
        (stored_insert_of_ne table key value updated inserted different).mpr
          storedTable
      exact (lookup_eq_some_iff updated other otherValue validUpdated).mpr
        storedUpdated

/--
**Failed open-addressing insertion finds every probed slot taken.** Let $T$ be an
open-addressing hash table with $m$ slots and probe sequence $p$. If inserting a binding
$k \mapsto v$ into $T$ fails, then for every $i < m$ the slot $p(k, i)$ holds a pair
$(k', v')$ with $k' \neq k$.

For probe sequences that are permutations of the slots, this says that every slot of the table
holds a key other than $k$.
-/
public theorem occupied_of_insert_eq_none (table : OpenAddressing K V m probe)
    (key : K) (value : V) (failed : insert table key value = none) :
    ∀ attempts < m, ∃ (otherKey : K) (otherValue : V),
      table.slots.get (probe key attempts) = some (otherKey, otherValue) ∧
        otherKey ≠ key := by
  have failedAux : insertAux table key value 0 m = none := by
    simpa [insert] using failed
  intro attempts withinSlots
  have occupied := occupied_of_insertAux_eq_none table key value 0 m failedAux
    attempts withinSlots
  simpa using occupied

end OpenAddressing

end Cslib.Algorithms.Lean
