/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Vector.Lemmas

/-!
# Cuckoo hashing

A cuckoo hash table (Demaine, MIT 6.851 *Advanced Data Structures*, Lecture 10) keeps two
tables of `m` slots each and two hash functions `h1 h2 : K → Fin m`. A key `k` may only ever
sit in `table1[h1 k]` or in `table2[h2 k]`, so `lookup` checks exactly those two slots.
Insertion first overwrites an existing binding for the key in place; otherwise it runs the
eviction loop: write the new pair into `table1[h1 k]`, move the evicted occupant to its
other slot, and so on, alternating tables. The loop is bounded by an explicit fuel and
returns `none` on exhaustion, which models the trigger for a rehash; rehashing itself is
not modeled.

## Main definitions

* `CuckooHashing` stores the two slot vectors.
* `CuckooHashing.empty`, `CuckooHashing.lookup`, and `CuckooHashing.insert` are the
  operations; `insert` takes a fuel bound and returns an `Option` table.
* `CuckooHashing.Valid` is the placement invariant: every stored entry sits at `h1` of its
  key in the first table or at `h2` of its key in the second.
* `CuckooHashing.Stored` says a binding occurs in some slot of either table, and
  `CuckooHashing.KeyDet` says each key is stored with at most one value.

## Main statements

A successful insertion preserves `Valid` and `KeyDet` (`valid_insert`, `keyDet_insert`) and
stores the inserted binding. Lookup is sound
unconditionally (a found value is stored) and complete under `Valid`: a stored key is
found, and under the additional `KeyDet` it is found with its stored value. Under `Valid`
and `KeyDet`, looking up a successfully inserted key returns the inserted value. No
expected constant-time bound is claimed: the model supplies no probability distribution or
independence assumption on `h1` and `h2`, and insert failure is possible for any fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/--
**Cuckoo hash table.** Given a type $K$ of keys, a type $V$ of values, a number $m$ of slots,
and two hash functions $h_1, h_2 : K \to \{0, \dots, m - 1\}$, a cuckoo hash table consists of
two tables, each a vector of $m$ slots; every slot is either empty or holds a key–value pair
$(k, v)$ with $k \in K$ and $v \in V$. The structure itself does not require a pair $(k, v)$ to
sit at slot $h_1(k)$ of the first table or at slot $h_2(k)$ of the second.

No expected constant-time bound is claimed because the model supplies neither a probability
distribution nor an independence assumption about the hashes.
-/
public structure CuckooHashing (K : Type u) (V : Type v) (m : Nat)
    (h1 h2 : K → Fin m) where
  /-- The first table; key `k` may occupy slot `h1 k`. -/
  table1 : Vector (Option (K × V)) m
  /-- The second table; key `k` may occupy slot `h2 k`. -/
  table2 : Vector (Option (K × V)) m

namespace CuckooHashing

variable {K : Type u} {V : Type v} {m : Nat} {h1 h2 : K → Fin m}

variable [DecidableEq K]

/-- **Empty cuckoo hash table.** The empty cuckoo hash table has every slot of both tables
vacant. -/
public def empty : CuckooHashing K V m h1 h2 :=
  ⟨Vector.replicate m none, Vector.replicate m none⟩

/--
**Placement invariant of a cuckoo hash table.** A cuckoo hash table with hash functions
$h_1, h_2$ satisfies the placement invariant when every pair $(k, v)$ in slot $i$ of the first
table has $i = h_1(k)$, and every pair $(k, v)$ in slot $i$ of the second table has
$i = h_2(k)$.

This is what lets lookup check only two slots.
-/
public def Valid (table : CuckooHashing K V m h1 h2) : Prop :=
  (∀ (i : Fin m) (key : K) (value : V),
    table.table1.get i = some (key, value) → i = h1 key) ∧
    ∀ (i : Fin m) (key : K) (value : V),
      table.table2.get i = some (key, value) → i = h2 key

/--
**Binding stored in a cuckoo hash table.** A key $k$ is stored with value $v$ in a cuckoo hash
table when the pair $(k, v)$ occupies some slot of the first table or some slot of the second
table.
-/
public def Stored (table : CuckooHashing K V m h1 h2) (key : K) (value : V) : Prop :=
  (∃ i : Fin m, table.table1.get i = some (key, value)) ∨
    ∃ i : Fin m, table.table2.get i = some (key, value)

/--
**Key determinism of a cuckoo hash table.** A cuckoo hash table is key-deterministic when each
key is stored with at most one value: for every key $k$ and values $v_1, v_2$, if the bindings
$k \mapsto v_1$ and $k \mapsto v_2$ are both stored in the table, then $v_1 = v_2$. Duplicate
copies of the same pair are allowed.
-/
public def KeyDet (table : CuckooHashing K V m h1 h2) : Prop :=
  ∀ (key : K) (v₁ v₂ : V), Stored table key v₁ → Stored table key v₂ → v₁ = v₂

private theorem get_set (slots : Vector (Option (K × V)) m) (i j : Fin m)
    (a : Option (K × V)) :
    (slots.set i.val a i.isLt).get j = if i = j then a else slots.get j := by
  change (slots.set i.val a i.isLt)[j.val] = if i = j then a else slots[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

private theorem get_set_self (slots : Vector (Option (K × V)) m) (i : Fin m)
    (a : Option (K × V)) :
    (slots.set i.val a i.isLt).get i = a := by
  simp [get_set]

private theorem get_set_ne (slots : Vector (Option (K × V)) m) (i j : Fin m)
    (a : Option (K × V)) (different : i ≠ j) :
    (slots.set i.val a i.isLt).get j = slots.get j := by
  simp [get_set, different]

private theorem get_replicate (i : Fin m) :
    (Vector.replicate m (none : Option (K × V))).get i = none := by
  change (Vector.replicate m (none : Option (K × V)))[i.val] = none
  simp

private theorem stored_update1_self (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (key : K) (value : V) :
    Stored (⟨table.table1.set s.val (some (key, value)) s.isLt, table.table2⟩ : CuckooHashing K V m h1 h2) key value :=
  Or.inl ⟨s, get_set_self table.table1 s (some (key, value))⟩

private theorem stored_update2_self (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (key : K) (value : V) :
    Stored (⟨table.table1, table.table2.set s.val (some (key, value)) s.isLt⟩ : CuckooHashing K V m h1 h2) key value :=
  Or.inr ⟨s, get_set_self table.table2 s (some (key, value))⟩

private theorem stored_update1_elim (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (a : Option (K × V)) {key : K} {value : V}
    (stored : Stored (⟨table.table1.set s.val a s.isLt, table.table2⟩ : CuckooHashing K V m h1 h2) key value) :
    a = some (key, value) ∨ Stored table key value := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · by_cases same : s = i
    · subst i
      exact Or.inl (by rw [get_set_self] at hi; exact hi)
    · exact Or.inr (Or.inl ⟨i, by rwa [get_set_ne table.table1 s i a same] at hi⟩)
  · exact Or.inr (Or.inr ⟨i, hi⟩)

private theorem stored_update2_elim (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (a : Option (K × V)) {key : K} {value : V}
    (stored : Stored (⟨table.table1, table.table2.set s.val a s.isLt⟩ : CuckooHashing K V m h1 h2) key value) :
    a = some (key, value) ∨ Stored table key value := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inr (Or.inl ⟨i, hi⟩)
  · by_cases same : s = i
    · subst i
      exact Or.inl (by rw [get_set_self] at hi; exact hi)
    · exact Or.inr (Or.inr ⟨i, by rwa [get_set_ne table.table2 s i a same] at hi⟩)

private theorem stored_update1_of_stored_ne (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (a : Option (K × V)) {key : K} {value : V} (stored : Stored table key value)
    (notAtSlot : table.table1.get s ≠ some (key, value)) :
    Stored (⟨table.table1.set s.val a s.isLt, table.table2⟩ : CuckooHashing K V m h1 h2) key value := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · have different : s ≠ i := fun equal => notAtSlot (equal ▸ hi)
    exact Or.inl ⟨i, by rwa [get_set_ne table.table1 s i a different]⟩
  · exact Or.inr ⟨i, hi⟩

private theorem stored_update2_of_stored_ne (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (a : Option (K × V)) {key : K} {value : V} (stored : Stored table key value)
    (notAtSlot : table.table2.get s ≠ some (key, value)) :
    Stored (⟨table.table1, table.table2.set s.val a s.isLt⟩ : CuckooHashing K V m h1 h2) key value := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl ⟨i, hi⟩
  · have different : s ≠ i := fun equal => notAtSlot (equal ▸ hi)
    exact Or.inr ⟨i, by rwa [get_set_ne table.table2 s i a different]⟩

private theorem valid_update1 (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (valid : Valid table) :
    Valid (⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt, table.table2⟩ : CuckooHashing K V m h1 h2) := by
  constructor
  · intro i otherKey otherValue occupied
    by_cases same : h1 key = i
    · subst i
      rw [get_set_self] at occupied
      simp only [Option.some.injEq, Prod.mk.injEq] at occupied
      exact congrArg h1 occupied.1
    · rw [get_set_ne table.table1 (h1 key) i (some (key, value)) same] at occupied
      exact valid.1 i otherKey otherValue occupied
  · exact valid.2

private theorem valid_update2 (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (valid : Valid table) :
    Valid (⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ : CuckooHashing K V m h1 h2) := by
  constructor
  · exact valid.1
  · intro i otherKey otherValue occupied
    by_cases same : h2 key = i
    · subst i
      rw [get_set_self] at occupied
      simp only [Option.some.injEq, Prod.mk.injEq] at occupied
      exact congrArg h2 occupied.1
    · rw [get_set_ne table.table2 (h2 key) i (some (key, value)) same] at occupied
      exact valid.2 i otherKey otherValue occupied

/--
**The empty cuckoo hash table satisfies the placement invariant.** For any hash functions
$h_1, h_2$ into $m$ slots, the empty cuckoo hash table, with every slot of both tables vacant,
satisfies the placement invariant.
-/
public theorem valid_empty : Valid (empty : CuckooHashing K V m h1 h2) := by
  constructor
  · intro i _ _ occupied
    have vacant : (empty : CuckooHashing K V m h1 h2).table1.get i = none :=
      get_replicate i
    rw [vacant] at occupied
    simp at occupied
  · intro i _ _ occupied
    have vacant : (empty : CuckooHashing K V m h1 h2).table2.get i = none :=
      get_replicate i
    rw [vacant] at occupied
    simp at occupied

/-- **The empty cuckoo hash table is key-deterministic.** No key is stored with two different
values in the empty cuckoo hash table, vacuously. -/
public theorem keyDet_empty : KeyDet (empty : CuckooHashing K V m h1 h2) := by
  intro _ _ _ stored _
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · have vacant : (empty : CuckooHashing K V m h1 h2).table1.get i = none :=
      get_replicate i
    rw [vacant] at hi
    simp at hi
  · have vacant : (empty : CuckooHashing K V m h1 h2).table2.get i = none :=
      get_replicate i
    rw [vacant] at hi
    simp at hi

/--
**Cuckoo eviction loop.** The eviction loop takes a cuckoo hash table with hash functions $h_1$
and $h_2$, a key–value pair $(k, v)$, a choice of the first or second table, and a natural
number as fuel, and either returns a table or fails. With fuel $0$ it fails. With fuel $n + 1$
and the first table chosen, it writes $(k, v)$ into slot $h_1(k)$ of the first table; if that
slot was empty it returns the resulting table, and otherwise it repeats on the resulting table
with the evicted pair, the second table and fuel $n$. With the second table chosen it does the
same at slot $h_2(k)$ of the second table and continues with the first table.
-/
def insertAux (table : CuckooHashing K V m h1 h2) (cur : K × V) (first : Bool) :
    Nat → Option (CuckooHashing K V m h1 h2)
  | 0 => none
  | fuel + 1 =>
      if first then
        match table.table1.get (h1 cur.1) with
        | none =>
            some ⟨table.table1.set (h1 cur.1).val (some cur) (h1 cur.1).isLt, table.table2⟩
        | some occ =>
            insertAux
              ⟨table.table1.set (h1 cur.1).val (some cur) (h1 cur.1).isLt, table.table2⟩
              occ false fuel
      else
        match table.table2.get (h2 cur.1) with
        | none =>
            some ⟨table.table1, table.table2.set (h2 cur.1).val (some cur) (h2 cur.1).isLt⟩
        | some occ =>
            insertAux
              ⟨table.table1, table.table2.set (h2 cur.1).val (some cur) (h2 cur.1).isLt⟩
              occ true fuel

private theorem stored_insertAux (table : CuckooHashing K V m h1 h2) (cur : K × V)
    (first : Bool) :
    ∀ (fuel : Nat) (updated : CuckooHashing K V m h1 h2),
      insertAux table cur first fuel = some updated →
      Stored updated cur.1 cur.2 ∧ ∀ (key : K) (value : V),
        Stored table key value → Stored updated key value := by
  intro fuel
  induction fuel generalizing table cur first with
  | zero =>
      intro updated inserted
      simp [insertAux] at inserted
  | succ fuel ih =>
      intro updated inserted
      obtain ⟨ck, cv⟩ := cur
      cases first with
      | true =>
          cases slot : table.table1.get (h1 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩ := by
                have step : insertAux table (ck, cv) true (fuel + 1) =
                    some ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt,
                      table.table2⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              constructor
              · exact stored_update1_self table (h1 ck) ck cv
              · intro key value stored
                apply stored_update1_of_stored_ne table (h1 ck) (some (ck, cv)) stored
                rw [slot]
                simp
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩
                  (ok, ov) false fuel = some updated := by
                simpa [insertAux, slot] using inserted
              obtain ⟨hcur, hmono⟩ := ih _ _ _ _ hrec
              constructor
              · exact hmono ck cv (stored_update1_self table (h1 ck) ck cv)
              · intro key value stored
                by_cases atSlot : table.table1.get (h1 ck) = some (key, value)
                · rw [slot] at atSlot
                  simp only [Option.some.injEq, Prod.mk.injEq] at atSlot
                  obtain ⟨rfl, rfl⟩ := atSlot
                  exact hcur
                · exact hmono key value
                    (stored_update1_of_stored_ne table (h1 ck) (some (ck, cv)) stored atSlot)
      | false =>
          cases slot : table.table2.get (h2 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                have step : insertAux table (ck, cv) false (fuel + 1) =
                    some ⟨table.table1,
                      table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              constructor
              · exact stored_update2_self table (h2 ck) ck cv
              · intro key value stored
                apply stored_update2_of_stored_ne table (h2 ck) (some (ck, cv)) stored
                rw [slot]
                simp
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩
                  (ok, ov) true fuel = some updated := by
                simpa [insertAux, slot] using inserted
              obtain ⟨hcur, hmono⟩ := ih _ _ _ _ hrec
              constructor
              · exact hmono ck cv (stored_update2_self table (h2 ck) ck cv)
              · intro key value stored
                by_cases atSlot : table.table2.get (h2 ck) = some (key, value)
                · rw [slot] at atSlot
                  simp only [Option.some.injEq, Prod.mk.injEq] at atSlot
                  obtain ⟨rfl, rfl⟩ := atSlot
                  exact hcur
                · exact hmono key value
                    (stored_update2_of_stored_ne table (h2 ck) (some (ck, cv)) stored atSlot)

private theorem stored_of_stored_insertAux (table : CuckooHashing K V m h1 h2) (cur : K × V)
    (first : Bool) :
    ∀ (fuel : Nat) (updated : CuckooHashing K V m h1 h2),
      insertAux table cur first fuel = some updated →
      ∀ (key : K) (value : V), Stored updated key value →
        Stored table key value ∨ (key, value) = cur := by
  intro fuel
  induction fuel generalizing table cur first with
  | zero =>
      intro updated inserted
      simp [insertAux] at inserted
  | succ fuel ih =>
      intro updated inserted key value stored
      obtain ⟨ck, cv⟩ := cur
      cases first with
      | true =>
          cases slot : table.table1.get (h1 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩ := by
                have step : insertAux table (ck, cv) true (fuel + 1) =
                    some ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt,
                      table.table2⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              rcases stored_update1_elim table (h1 ck) (some (ck, cv)) stored with
                heq | hold
              · exact Or.inr (Option.some.inj heq).symm
              · exact Or.inl hold
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩
                  (ok, ov) false fuel = some updated := by
                simpa [insertAux, slot] using inserted
              rcases ih _ _ _ _ hrec key value stored with hold | heq
              · rcases stored_update1_elim table (h1 ck) (some (ck, cv)) hold with
                  heq' | hold'
                · exact Or.inr (Option.some.inj heq').symm
                · exact Or.inl hold'
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
                exact Or.inl (Or.inl ⟨h1 ck, slot⟩)
      | false =>
          cases slot : table.table2.get (h2 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                have step : insertAux table (ck, cv) false (fuel + 1) =
                    some ⟨table.table1,
                      table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              rcases stored_update2_elim table (h2 ck) (some (ck, cv)) stored with
                heq | hold
              · exact Or.inr (Option.some.inj heq).symm
              · exact Or.inl hold
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩
                  (ok, ov) true fuel = some updated := by
                simpa [insertAux, slot] using inserted
              rcases ih _ _ _ _ hrec key value stored with hold | heq
              · rcases stored_update2_elim table (h2 ck) (some (ck, cv)) hold with
                  heq' | hold'
                · exact Or.inr (Option.some.inj heq').symm
                · exact Or.inl hold'
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
                exact Or.inl (Or.inr ⟨h2 ck, slot⟩)

private theorem valid_insertAux (table : CuckooHashing K V m h1 h2) (cur : K × V)
    (first : Bool) :
    ∀ (fuel : Nat) (updated : CuckooHashing K V m h1 h2),
      insertAux table cur first fuel = some updated → Valid table → Valid updated := by
  intro fuel
  induction fuel generalizing table cur first with
  | zero =>
      intro updated inserted
      simp [insertAux] at inserted
  | succ fuel ih =>
      intro updated inserted valid
      obtain ⟨ck, cv⟩ := cur
      cases first with
      | true =>
          cases slot : table.table1.get (h1 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩ := by
                have step : insertAux table (ck, cv) true (fuel + 1) =
                    some ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt,
                      table.table2⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              exact valid_update1 table ck cv valid
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1.set (h1 ck).val (some (ck, cv)) (h1 ck).isLt, table.table2⟩
                  (ok, ov) false fuel = some updated := by
                simpa [insertAux, slot] using inserted
              exact ih _ _ _ _ hrec (valid_update1 table ck cv valid)
      | false =>
          cases slot : table.table2.get (h2 ck) with
          | none =>
              have hUpdated : updated =
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                have step : insertAux table (ck, cv) false (fuel + 1) =
                    some ⟨table.table1,
                      table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩ := by
                  simp [insertAux, slot]
                rw [step] at inserted
                exact (Option.some.inj inserted).symm
              subst hUpdated
              exact valid_update2 table ck cv valid
          | some occ =>
              obtain ⟨ok, ov⟩ := occ
              have hrec : insertAux
                  ⟨table.table1, table.table2.set (h2 ck).val (some (ck, cv)) (h2 ck).isLt⟩
                  (ok, ov) true fuel = some updated := by
                simpa [insertAux, slot] using inserted
              exact ih _ _ _ _ hrec (valid_update2 table ck cv valid)

/--
**Cuckoo hash table lookup.** For a cuckoo hash table $T$ with hash functions $h_1$ and $h_2$ and a
key $k$, the lookup of $k$ in $T$ returns $v$ if slot $h_1(k)$ of the first table holds a pair
$(k, v)$; otherwise it returns $v$ if slot $h_2(k)$ of the second table holds a pair $(k, v)$;
otherwise it returns nothing. No other slot is examined.
-/
public def lookup (table : CuckooHashing K V m h1 h2) (key : K) : Option V :=
  match table.table1.get (h1 key) with
  | some (k₁, v₁) =>
      if k₁ = key then some v₁
      else
        match table.table2.get (h2 key) with
        | some (k₂, v₂) => if k₂ = key then some v₂ else none
        | none => none
  | none =>
      match table.table2.get (h2 key) with
      | some (k₂, v₂) => if k₂ = key then some v₂ else none
      | none => none

/-- **Lookup in the empty cuckoo hash table.** Looking up any key in the empty cuckoo hash table
finds no value. -/
@[simp]
public theorem lookup_empty (key : K) :
    lookup (empty : CuckooHashing K V m h1 h2) key = none := by
  have e1 : (empty : CuckooHashing K V m h1 h2).table1.get (h1 key) = none :=
    get_replicate _
  have e2 : (empty : CuckooHashing K V m h1 h2).table2.get (h2 key) = none :=
    get_replicate _
  simp [lookup, e1, e2]

/--
**Cuckoo lookup finds a key in its first-table slot.** Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$, let $k$ be a key and $v$ a value. If slot $h_1(k)$ of the first table of
$T$ holds the pair $(k, v)$, then looking up $k$ in $T$ returns $v$.
-/
public theorem lookup_eq_some_of_table1 (table : CuckooHashing K V m h1 h2) (key : K)
    (value : V) (atSlot : table.table1.get (h1 key) = some (key, value)) :
    lookup table key = some value := by
  simp [lookup, atSlot]

/--
**Cuckoo lookup finds a key in its second-table slot.** Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$, let $k$ be a key and $v$ a value. If slot $h_2(k)$ of the second table
of $T$ holds the pair $(k, v)$ and slot $h_1(k)$ of the first table of $T$ holds no pair whose key
is $k$, then looking up $k$ in $T$ returns $v$.
-/
public theorem lookup_eq_some_of_table2 (table : CuckooHashing K V m h1 h2) (key : K)
    (value : V) (atSlot : table.table2.get (h2 key) = some (key, value))
    (notFirst : ∀ v₁, table.table1.get (h1 key) ≠ some (key, v₁)) :
    lookup table key = some value := by
  cases first : table.table1.get (h1 key) with
  | none => simp [lookup, first, atSlot]
  | some pair =>
      obtain ⟨k₁, v₁⟩ := pair
      by_cases same : k₁ = key
      · exact absurd (by rw [first, same] : table.table1.get (h1 key) = some (key, v₁))
          (notFirst v₁)
      · simp [lookup, first, atSlot, same]

/--
**Soundness of cuckoo lookup.** Let $T$ be a cuckoo hash table with hash functions $h_1$ and $h_2$,
let $k$ be a key and $v$ a value. If looking up $k$ in $T$ returns $v$, then the binding
$k \mapsto v$ is stored in some slot of the first or the second table of $T$.
-/
public theorem lookup_sound (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (found : lookup table key = some value) : Stored table key value := by
  cases first : table.table1.get (h1 key) with
  | none =>
      cases second : table.table2.get (h2 key) with
      | none => simp [lookup, first, second] at found
      | some pair =>
          obtain ⟨k₂, v₂⟩ := pair
          by_cases same : k₂ = key
          · have hv : v₂ = value := by
              simpa [lookup, first, second, same] using found
            exact Or.inr ⟨h2 key, by rw [second, same, hv]⟩
          · simp [lookup, first, second, same] at found
  | some pair =>
      obtain ⟨k₁, v₁⟩ := pair
      by_cases same : k₁ = key
      · have hv : v₁ = value := by
          simpa [lookup, first, same] using found
        exact Or.inl ⟨h1 key, by rw [first, same, hv]⟩
      · cases second : table.table2.get (h2 key) with
        | none => simp [lookup, first, second, same] at found
        | some pair₂ =>
            obtain ⟨k₂, v₂⟩ := pair₂
            by_cases same₂ : k₂ = key
            · have hv : v₂ = value := by
                simpa [lookup, first, second, same, same₂] using found
              exact Or.inr ⟨h2 key, by rw [second, same₂, hv]⟩
            · simp [lookup, first, second, same, same₂] at found

private theorem stored_at_hash (table : CuckooHashing K V m h1 h2) (valid : Valid table)
    (key : K) (value : V) (stored : Stored table key value) :
    table.table1.get (h1 key) = some (key, value) ∨
      table.table2.get (h2 key) = some (key, value) := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · have placed := valid.1 i key value hi
    subst placed
    exact Or.inl hi
  · have placed := valid.2 i key value hi
    subst placed
    exact Or.inr hi

/--
**Cuckoo lookup finds every stored key.** Let $T$ be a cuckoo hash table with hash functions $h_1$
and $h_2$ that satisfies the placement invariant, and let $k$ be a key and $v$ a value. If the
binding $k \mapsto v$ is stored in some slot of either table of $T$, then looking up $k$ in $T$
returns some value.

The returned value may differ from $v$ when $k$ is stored with two different values; when $T$
stores each key with at most one value, it is $v$.
-/
public theorem lookup_isSome_of_stored (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (key : K) (value : V) (stored : Stored table key value) :
    (lookup table key).isSome := by
  rcases stored_at_hash table valid key value stored with atFirst | atSecond
  · rw [lookup_eq_some_of_table1 table key value atFirst]
    rfl
  · cases first : table.table1.get (h1 key) with
    | none =>
        rw [lookup_eq_some_of_table2 table key value atSecond (by
          intro v₁ hv
          rw [first] at hv
          simp at hv)]
        rfl
    | some pair =>
        obtain ⟨k₁, v₁⟩ := pair
        by_cases same : k₁ = key
        · have atFirst : table.table1.get (h1 key) = some (key, v₁) := by
            rw [first, same]
          rw [lookup_eq_some_of_table1 table key v₁ atFirst]
          rfl
        · have notFirst : ∀ v₁', table.table1.get (h1 key) ≠ some (key, v₁') := by
            intro v₁' hv
            rw [first] at hv
            simp only [Option.some.injEq, Prod.mk.injEq] at hv
            exact same hv.1
          rw [lookup_eq_some_of_table2 table key value atSecond notFirst]
          rfl

/-- **Cuckoo lookup finds every stored binding.** Let $T$ be a cuckoo hash table that satisfies
the placement invariant and is key-deterministic. For every key $k$ and value $v$, if the
binding $k \mapsto v$ is stored in $T$, then looking up $k$ in $T$ returns $v$. -/
public theorem lookup_eq_some_of_stored (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (det : KeyDet table) (key : K) (value : V)
    (stored : Stored table key value) :
    lookup table key = some value := by
  rcases stored_at_hash table valid key value stored with atFirst | atSecond
  · exact lookup_eq_some_of_table1 table key value atFirst
  · cases first : table.table1.get (h1 key) with
    | none =>
        exact lookup_eq_some_of_table2 table key value atSecond (by
          intro v₁ hv
          rw [first] at hv
          simp at hv)
    | some pair =>
        obtain ⟨k₁, v₁⟩ := pair
        by_cases same : k₁ = key
        · have atFirst : table.table1.get (h1 key) = some (key, v₁) := by
            rw [first, same]
          have storedFirst : Stored table key v₁ := Or.inl ⟨h1 key, atFirst⟩
          have equal : v₁ = value := det key v₁ value storedFirst stored
          rw [lookup_eq_some_of_table1 table key v₁ atFirst, equal]
        · have notFirst : ∀ v₁', table.table1.get (h1 key) ≠ some (key, v₁') := by
            intro v₁' hv
            rw [first] at hv
            simp only [Option.some.injEq, Prod.mk.injEq] at hv
            exact same hv.1
          exact lookup_eq_some_of_table2 table key value atSecond notFirst

/-- **Cuckoo lookup finds exactly the stored bindings.** Let $T$ be a cuckoo hash table that
satisfies the placement invariant and is key-deterministic. For every key $k$ and value $v$,
looking up $k$ in $T$ returns $v$ if and only if the binding $k \mapsto v$ is stored in $T$. -/
public theorem lookup_eq_some_iff_stored (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (det : KeyDet table) (key : K) (value : V) :
    lookup table key = some value ↔ Stored table key value :=
  ⟨lookup_sound table key value, lookup_eq_some_of_stored table valid det key value⟩

/--
**Slot holds a key.** A slot of a cuckoo hash table is either empty or holds a pair $(k, v)$ of a
key and a value. For a slot $s$ and a key $k'$, this test is true when $s$ holds a pair whose key
is $k'$, and false when $s$ is empty or holds a pair with a different key.
-/
def slotHasKey (slot : Option (K × V)) (key : K) : Bool :=
  match slot with
  | some pair => decide (pair.1 = key)
  | none => false

private theorem slotHasKey_iff {slot : Option (K × V)} {key : K} :
    slotHasKey slot key = true ↔ ∃ value, slot = some (key, value) := by
  cases slot with
  | none => simp [slotHasKey]
  | some pair =>
      obtain ⟨k, v⟩ := pair
      show decide (k = key) = true ↔ ∃ value, some (k, v) = some (key, value)
      rw [decide_eq_true_eq]
      constructor
      · intro same
        exact ⟨v, by rw [same]⟩
      · rintro ⟨value, h⟩
        exact (Prod.mk.inj (Option.some.inj h)).1

/--
**Cuckoo hash insertion.** Inserting a key $k$ with value $v$ into a cuckoo hash table with hash
functions $h_1$ and $h_2$, with fuel $n$, either returns a table or fails. If slot $h_1(k)$ of
the first table holds a binding for $k$, that slot is overwritten with $(k, v)$, and slot
$h_2(k)$ of the second table is cleared if it also holds a binding for $k$, so no stale
competing value remains. Otherwise, if slot $h_2(k)$ of the second table holds a binding for
$k$, that slot is overwritten with $(k, v)$. Otherwise the eviction loop runs on $(k, v)$,
starting with the first table, with fuel $n$, and its result is returned. Failure, when the
loop exhausts its fuel, models the rehash trigger of the classical algorithm.
-/
public def insert (table : CuckooHashing K V m h1 h2) (key : K) (value : V) (fuel : Nat) :
    Option (CuckooHashing K V m h1 h2) :=
  if slotHasKey (table.table1.get (h1 key)) key then
    some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
      if slotHasKey (table.table2.get (h2 key)) key then
        table.table2.set (h2 key).val none (h2 key).isLt
      else table.table2⟩
  else if slotHasKey (table.table2.get (h2 key)) key then
    some ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩
  else
    insertAux table (key, value) true fuel

private theorem valid_clear2 (table : CuckooHashing K V m h1 h2) (s : Fin m)
    (valid : Valid table) :
    Valid (⟨table.table1, table.table2.set s.val none s.isLt⟩ : CuckooHashing K V m h1 h2) := by
  constructor
  · exact valid.1
  · intro i otherKey otherValue occupied
    by_cases same : s = i
    · subst i
      rw [get_set_self] at occupied
      simp at occupied
    · rw [get_set_ne table.table2 s i none same] at occupied
      exact valid.2 i otherKey otherValue occupied

private theorem stored_replace1_elim (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (key : K) (value : V) {other : K} {otherValue : V}
    (stored : Stored (⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
      if slotHasKey (table.table2.get (h2 key)) key then
        table.table2.set (h2 key).val none (h2 key).isLt
      else table.table2⟩ : CuckooHashing K V m h1 h2) other otherValue) :
    (other = key ∧ otherValue = value) ∨ (Stored table other otherValue ∧ other ≠ key) := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · by_cases same : h1 key = i
    · subst i
      rw [get_set_self] at hi
      have h := Prod.mk.inj (Option.some.inj hi)
      exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · rw [get_set_ne table.table1 (h1 key) i _ same] at hi
      by_cases hother : other = key
      · subst hother
        exact absurd (valid.1 i _ _ hi).symm same
      · exact Or.inr ⟨Or.inl ⟨i, hi⟩, hother⟩
  · by_cases dup : slotHasKey (table.table2.get (h2 key)) key = true
    · rw [if_pos dup] at hi
      by_cases same : h2 key = i
      · subst i
        rw [get_set_self] at hi
        simp at hi
      · rw [get_set_ne table.table2 (h2 key) i none same] at hi
        by_cases hother : other = key
        · subst hother
          exact absurd (valid.2 i _ _ hi).symm same
        · exact Or.inr ⟨Or.inr ⟨i, hi⟩, hother⟩
    · rw [if_neg dup] at hi
      by_cases hother : other = key
      · subst hother
        have hi2 : i = h2 other := valid.2 i _ _ hi
        subst hi2
        exact absurd (slotHasKey_iff.mpr ⟨otherValue, hi⟩) dup
      · exact Or.inr ⟨Or.inr ⟨i, hi⟩, hother⟩

private theorem stored_replace2_elim (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (key : K) (value : V)
    (hasFirst : ¬ slotHasKey (table.table1.get (h1 key)) key = true)
    {other : K} {otherValue : V}
    (stored : Stored (⟨table.table1,
      table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ :
      CuckooHashing K V m h1 h2) other otherValue) :
    (other = key ∧ otherValue = value) ∨ (Stored table other otherValue ∧ other ≠ key) := by
  rcases stored with ⟨i, hi⟩ | ⟨i, hi⟩
  · by_cases hother : other = key
    · subst hother
      have hi2 : i = h1 other := valid.1 i _ _ hi
      subst hi2
      exact absurd (slotHasKey_iff.mpr ⟨otherValue, hi⟩) hasFirst
    · exact Or.inr ⟨Or.inl ⟨i, hi⟩, hother⟩
  · by_cases same : h2 key = i
    · subst i
      rw [get_set_self] at hi
      have h := Prod.mk.inj (Option.some.inj hi)
      exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · rw [get_set_ne table.table2 (h2 key) i _ same] at hi
      by_cases hother : other = key
      · subst hother
        exact absurd (valid.2 i _ _ hi).symm same
      · exact Or.inr ⟨Or.inr ⟨i, hi⟩, hother⟩

/--
**Cuckoo insertion stores the inserted binding.** Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$. If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel
$f$ succeeds and returns the table $T'$, then the binding $k \mapsto v$ is stored in some slot of
either table of $T'$.
-/
public theorem stored_insert (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (fuel : Nat) (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated) :
    Stored updated key value := by
  by_cases hasFirst : slotHasKey (table.table1.get (h1 key)) key = true
  · have hUpdated : updated =
        ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
          if slotHasKey (table.table2.get (h2 key)) key then
            table.table2.set (h2 key).val none (h2 key).isLt
          else table.table2⟩ := by
      have step : insert table key value fuel =
          some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            if slotHasKey (table.table2.get (h2 key)) key then
              table.table2.set (h2 key).val none (h2 key).isLt
            else table.table2⟩ := by
        simp [insert, hasFirst]
      rw [step] at inserted
      exact (Option.some.inj inserted).symm
    subst hUpdated
    exact Or.inl ⟨h1 key, get_set_self table.table1 (h1 key) (some (key, value))⟩
  · by_cases hasSecond : slotHasKey (table.table2.get (h2 key)) key = true
    · have hUpdated : updated =
          ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
        have step : insert table key value fuel =
            some ⟨table.table1,
              table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
          simp [insert, hasFirst, hasSecond]
        rw [step] at inserted
        exact (Option.some.inj inserted).symm
      subst hUpdated
      exact stored_update2_self table (h2 key) key value
    · have hAux : insertAux table (key, value) true fuel = some updated := by
        simpa [insert, hasFirst, hasSecond] using inserted
      exact (stored_insertAux table (key, value) true fuel updated hAux).1

/--
**Cuckoo insertion preserves the placement invariant.** Let $T$ be a cuckoo hash table that
satisfies the placement invariant. If inserting the binding $k \mapsto v$ into $T$ (which
replaces an existing binding for $k$ in place) with some fuel bound succeeds and returns the
table $T'$, then $T'$ satisfies the placement invariant.
-/
public theorem valid_insert (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (fuel : Nat) (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated) (valid : Valid table) :
    Valid updated := by
  by_cases hasFirst : slotHasKey (table.table1.get (h1 key)) key = true
  · have hUpdated : updated =
        ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
          if slotHasKey (table.table2.get (h2 key)) key then
            table.table2.set (h2 key).val none (h2 key).isLt
          else table.table2⟩ := by
      have step : insert table key value fuel =
          some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            if slotHasKey (table.table2.get (h2 key)) key then
              table.table2.set (h2 key).val none (h2 key).isLt
            else table.table2⟩ := by
        simp [insert, hasFirst]
      rw [step] at inserted
      exact (Option.some.inj inserted).symm
    subst hUpdated
    by_cases dup : slotHasKey (table.table2.get (h2 key)) key = true
    · rw [if_pos dup]
      exact valid_clear2 _ (h2 key) (valid_update1 table key value valid)
    · rw [if_neg dup]
      exact valid_update1 table key value valid
  · by_cases hasSecond : slotHasKey (table.table2.get (h2 key)) key = true
    · have hUpdated : updated =
          ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
        have step : insert table key value fuel =
            some ⟨table.table1,
              table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
          simp [insert, hasFirst, hasSecond]
        rw [step] at inserted
        exact (Option.some.inj inserted).symm
      subst hUpdated
      exact valid_update2 table key value valid
    · have hAux : insertAux table (key, value) true fuel = some updated := by
        simpa [insert, hasFirst, hasSecond] using inserted
      exact valid_insertAux table (key, value) true fuel updated hAux valid

/-- **Cuckoo insertion preserves key determinism.** Let $T$ be a cuckoo hash table that
satisfies the placement invariant and is key-deterministic. If inserting a key $k$ with value
$v$ into $T$ with some fuel succeeds with result $T'$, then $T'$ is key-deterministic. In
particular, replacement leaves no stale copy of $k$ with a different value in the other slot. -/
public theorem keyDet_insert (table : CuckooHashing K V m h1 h2) (key : K) (value : V)
    (fuel : Nat) (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated)
    (valid : Valid table) (det : KeyDet table) :
    KeyDet updated := by
  by_cases hasFirst : slotHasKey (table.table1.get (h1 key)) key = true
  · have hUpdated : updated =
        ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
          if slotHasKey (table.table2.get (h2 key)) key then
            table.table2.set (h2 key).val none (h2 key).isLt
          else table.table2⟩ := by
      have step : insert table key value fuel =
          some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            if slotHasKey (table.table2.get (h2 key)) key then
              table.table2.set (h2 key).val none (h2 key).isLt
            else table.table2⟩ := by
        simp [insert, hasFirst]
      rw [step] at inserted
      exact (Option.some.inj inserted).symm
    subst hUpdated
    intro other v₁ v₂ stored₁ stored₂
    rcases stored_replace1_elim table valid key value stored₁ with ⟨hk₁, hv₁⟩ | ⟨hold₁, hne₁⟩
    · rcases stored_replace1_elim table valid key value stored₂ with ⟨-, hv₂⟩ | ⟨-, hne₂⟩
      · rw [hv₁, hv₂]
      · exact absurd hk₁ hne₂
    · rcases stored_replace1_elim table valid key value stored₂ with ⟨hk₂, -⟩ | ⟨hold₂, -⟩
      · exact absurd hk₂ hne₁
      · exact det other v₁ v₂ hold₁ hold₂
  · by_cases hasSecond : slotHasKey (table.table2.get (h2 key)) key = true
    · have hUpdated : updated =
          ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
        have step : insert table key value fuel =
            some ⟨table.table1,
              table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
          simp [insert, hasFirst, hasSecond]
        rw [step] at inserted
        exact (Option.some.inj inserted).symm
      subst hUpdated
      intro other v₁ v₂ stored₁ stored₂
      rcases stored_replace2_elim table valid key value hasFirst stored₁ with
        ⟨hk₁, hv₁⟩ | ⟨hold₁, hne₁⟩
      · rcases stored_replace2_elim table valid key value hasFirst stored₂ with
          ⟨-, hv₂⟩ | ⟨-, hne₂⟩
        · rw [hv₁, hv₂]
        · exact absurd hk₁ hne₂
      · rcases stored_replace2_elim table valid key value hasFirst stored₂ with
          ⟨hk₂, -⟩ | ⟨hold₂, -⟩
        · exact absurd hk₂ hne₁
        · exact det other v₁ v₂ hold₁ hold₂
    · have hAux : insertAux table (key, value) true fuel = some updated := by
        simpa [insert, hasFirst, hasSecond] using inserted
      have absent : ∀ v₀, ¬ Stored table key v₀ := by
        intro v₀ stored₀
        rcases stored_at_hash table valid key v₀ stored₀ with atFirst | atSecond
        · exact hasFirst (slotHasKey_iff.mpr ⟨v₀, atFirst⟩)
        · exact hasSecond (slotHasKey_iff.mpr ⟨v₀, atSecond⟩)
      intro other v₁ v₂ stored₁ stored₂
      rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
        other v₁ stored₁ with hold₁ | heq₁
      · rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
          other v₂ stored₂ with hold₂ | heq₂
        · exact det other v₁ v₂ hold₁ hold₂
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₂
          exact absurd hold₁ (absent v₁)
      · rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
          other v₂ stored₂ with hold₂ | heq₂
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
          exact absurd hold₂ (absent v₂)
        · have e₁ : v₁ = value := (Prod.mk.inj heq₁).2
          have e₂ : v₂ = value := (Prod.mk.inj heq₂).2
          rw [e₁, e₂]

/--
**Cuckoo lookup returns an inserted value.** Let $T$ be a cuckoo hash table with hash functions
$h_1$ and $h_2$ that satisfies the placement invariant and stores each key with at most one value.
If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds and returns the
table $T'$, then looking up $k$ in $T'$ returns $v$.
-/
public theorem lookup_insert (table : CuckooHashing K V m h1 h2) (valid : Valid table)
    (det : KeyDet table) (key : K) (value : V) (fuel : Nat)
    (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated) :
    lookup updated key = some value := by
  by_cases hasFirst : slotHasKey (table.table1.get (h1 key)) key = true
  · have hUpdated : updated =
        ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
          if slotHasKey (table.table2.get (h2 key)) key then
            table.table2.set (h2 key).val none (h2 key).isLt
          else table.table2⟩ := by
      have step : insert table key value fuel =
          some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            if slotHasKey (table.table2.get (h2 key)) key then
              table.table2.set (h2 key).val none (h2 key).isLt
            else table.table2⟩ := by
        simp [insert, hasFirst]
      rw [step] at inserted
      exact (Option.some.inj inserted).symm
    subst hUpdated
    exact lookup_eq_some_of_table1 _ key value
      (get_set_self table.table1 (h1 key) (some (key, value)))
  · by_cases hasSecond : slotHasKey (table.table2.get (h2 key)) key = true
    · have hUpdated : updated =
          ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
        have step : insert table key value fuel =
            some ⟨table.table1,
              table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
          simp [insert, hasFirst, hasSecond]
        rw [step] at inserted
        exact (Option.some.inj inserted).symm
      subst hUpdated
      apply lookup_eq_some_of_table2 _ key value
        (get_set_self table.table2 (h2 key) (some (key, value)))
      intro v₁ hv
      have hasKey : slotHasKey (table.table1.get (h1 key)) key = true :=
        slotHasKey_iff.mpr ⟨v₁, hv⟩
      exact hasFirst hasKey
    · have hAux : insertAux table (key, value) true fuel = some updated := by
        simpa [insert, hasFirst, hasSecond] using inserted
      have absent : ∀ v₀, ¬ Stored table key v₀ := by
        intro v₀ stored₀
        rcases stored_at_hash table valid key v₀ stored₀ with atFirst | atSecond
        · exact hasFirst (slotHasKey_iff.mpr ⟨v₀, atFirst⟩)
        · exact hasSecond (slotHasKey_iff.mpr ⟨v₀, atSecond⟩)
      have detUpdated : KeyDet updated := by
        intro other v₁ v₂ stored₁ stored₂
        rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
          other v₁ stored₁ with hold₁ | heq₁
        · rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
            other v₂ stored₂ with hold₂ | heq₂
          · exact det other v₁ v₂ hold₁ hold₂
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₂
            exact absurd hold₁ (absent v₁)
        · rcases stored_of_stored_insertAux table (key, value) true fuel updated hAux
            other v₂ stored₂ with hold₂ | heq₂
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
            exact absurd hold₂ (absent v₂)
          · have e₁ : v₁ = value := (Prod.mk.inj heq₁).2
            have e₂ : v₂ = value := (Prod.mk.inj heq₂).2
            rw [e₁, e₂]
      exact lookup_eq_some_of_stored updated
        (valid_insertAux table (key, value) true fuel updated hAux valid) detUpdated
        key value (stored_insertAux table (key, value) true fuel updated hAux).1

/--
**Cuckoo insertion preserves the bindings of other keys.** Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$ that satisfies the placement invariant. Suppose inserting (or replacing)
the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds and returns the table $T'$. Then for every
key $k' \ne k$ and every value $v'$, the binding $k' \mapsto v'$ is stored in $T'$ if and only if
it is stored in $T$.
-/
public theorem stored_insert_iff_of_ne (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (key : K) (value : V) (fuel : Nat)
    (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated)
    {other : K} {otherValue : V} (different : other ≠ key) :
    Stored updated other otherValue ↔ Stored table other otherValue := by
  by_cases hasFirst : slotHasKey (table.table1.get (h1 key)) key = true
  · have hUpdated : updated =
        ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
          if slotHasKey (table.table2.get (h2 key)) key then
            table.table2.set (h2 key).val none (h2 key).isLt
          else table.table2⟩ := by
      have step : insert table key value fuel =
          some ⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            if slotHasKey (table.table2.get (h2 key)) key then
              table.table2.set (h2 key).val none (h2 key).isLt
            else table.table2⟩ := by
        simp [insert, hasFirst]
      rw [step] at inserted
      exact (Option.some.inj inserted).symm
    subst hUpdated
    obtain ⟨v₀, hv₀⟩ := slotHasKey_iff.mp hasFirst
    have notAtFirst : table.table1.get (h1 key) ≠ some (other, otherValue) := by
      rw [hv₀]
      intro hEq
      exact different (Prod.mk.inj (Option.some.inj hEq)).1.symm
    constructor
    · intro stored
      rcases stored_replace1_elim table valid key value stored with
        ⟨hk, -⟩ | ⟨hold, -⟩
      · exact absurd hk different
      · exact hold
    · intro stored
      have step1 : Stored (⟨table.table1.set (h1 key).val (some (key, value))
          (h1 key).isLt, table.table2⟩ : CuckooHashing K V m h1 h2)
          other otherValue :=
        stored_update1_of_stored_ne table (h1 key) (some (key, value)) stored notAtFirst
      by_cases dup : slotHasKey (table.table2.get (h2 key)) key = true
      · rw [if_pos dup]
        obtain ⟨v₁, hv₁⟩ := slotHasKey_iff.mp dup
        have notAtSecond : table.table2.get (h2 key) ≠ some (other, otherValue) := by
          rw [hv₁]
          intro hEq
          exact different (Prod.mk.inj (Option.some.inj hEq)).1.symm
        exact stored_update2_of_stored_ne
          (⟨table.table1.set (h1 key).val (some (key, value)) (h1 key).isLt,
            table.table2⟩ : CuckooHashing K V m h1 h2)
          (h2 key) none step1 notAtSecond
      · rw [if_neg dup]
        exact step1
  · by_cases hasSecond : slotHasKey (table.table2.get (h2 key)) key = true
    · have hUpdated : updated =
          ⟨table.table1, table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
        have step : insert table key value fuel =
            some ⟨table.table1,
              table.table2.set (h2 key).val (some (key, value)) (h2 key).isLt⟩ := by
          simp [insert, hasFirst, hasSecond]
        rw [step] at inserted
        exact (Option.some.inj inserted).symm
      subst hUpdated
      obtain ⟨v₀, hv₀⟩ := slotHasKey_iff.mp hasSecond
      have notAtSecond : table.table2.get (h2 key) ≠ some (other, otherValue) := by
        rw [hv₀]
        intro hEq
        exact different (Prod.mk.inj (Option.some.inj hEq)).1.symm
      constructor
      · intro stored
        rcases stored_replace2_elim table valid key value hasFirst stored with
          ⟨hk, -⟩ | ⟨hold, -⟩
        · exact absurd hk different
        · exact hold
      · intro stored
        exact stored_update2_of_stored_ne table (h2 key) (some (key, value))
          stored notAtSecond
    · have hAux : insertAux table (key, value) true fuel = some updated := by
        simpa [insert, hasFirst, hasSecond] using inserted
      constructor
      · intro stored
        rcases stored_of_stored_insertAux table (key, value) true fuel updated
          hAux other otherValue stored with hold | heq
        · exact hold
        · exact absurd (Prod.mk.inj heq).1 different
      · intro stored
        exact (stored_insertAux table (key, value) true fuel updated hAux).2
          other otherValue stored

/--
**Cuckoo insertion leaves lookups of other keys unchanged.** Let $T$ be a cuckoo hash table with
hash functions $h_1$ and $h_2$ that satisfies the placement invariant and stores each key with at
most one value. If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds
and returns the table $T'$, then for every key $k' \ne k$, looking up $k'$ in $T'$ gives the same
result as looking up $k'$ in $T$: either both return nothing or both return the same value.
-/
public theorem lookup_insert_of_ne (table : CuckooHashing K V m h1 h2)
    (valid : Valid table) (det : KeyDet table) (key : K) (value : V)
    (fuel : Nat) (updated : CuckooHashing K V m h1 h2)
    (inserted : insert table key value fuel = some updated)
    {other : K} (different : other ≠ key) :
    lookup updated other = lookup table other := by
  have validUpdated : Valid updated :=
    valid_insert table key value fuel updated inserted valid
  have detUpdated : KeyDet updated :=
    keyDet_insert table key value fuel updated inserted valid det
  have iffStored : ∀ v, Stored updated other v ↔ Stored table other v :=
    fun v => stored_insert_iff_of_ne table valid key value fuel updated
      inserted different
  cases hOld : lookup table other with
  | none =>
      cases hNew : lookup updated other with
      | none => rfl
      | some v =>
          have hold : Stored table other v :=
            (iffStored v).mp (lookup_sound updated other v hNew)
          rw [lookup_eq_some_of_stored table valid det other v hold] at hOld
          simp at hOld
  | some v =>
      have hnew : Stored updated other v :=
        (iffStored v).mpr (lookup_sound table other v hOld)
      rw [lookup_eq_some_of_stored updated validUpdated detUpdated other v hnew]

end CuckooHashing

end Cslib.Algorithms.Lean
