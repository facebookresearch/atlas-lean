/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTable

/-!
# Sequential idempotent requests over `HashTable`

One memo step `serve`: a lookup hit returns the stored response with the
table unchanged; a miss runs the handler and inserts its response. Serving
twice is stable, validity and handler agreement are preserved, and hash
collisions need no law on the hash function.
D1: only HashTable facts are proved; no other map type appears.
D2: keys use propositional = under DecidableEq, not BEq; hash needs no law.
D3: specifications are plain equations, not program-logic triples.
D4: unchanged means literal table equality; agreement means lookup equality.
No concurrency, crash-recovery, or external-effect behavior is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

namespace HashTable

/-- One memo step: a hit returns the stored response, a miss runs the handler and inserts it. -/
public def serve {κ : Type u} {ρ : Type v} [DecidableEq κ]
    {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash) : ρ × HashTable κ ρ hash :=
  match HashTable.lookup key t with
  | some r => (r, t)
  | none =>
      let response := handler key
      (response, HashTable.insert key response t)

/-- A lookup hit serves the stored response with the table unchanged. -/
public theorem serve_of_lookup_eq_some {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash) {r : ρ}
    (hmem : HashTable.lookup key t = some r) :
    serve handler key t = (r, t) := by
  unfold serve
  rw [hmem]

/-- A lookup miss serves the handler value and inserts it into the table. -/
public theorem serve_of_lookup_eq_none {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash)
    (hmiss : HashTable.lookup key t = none) :
    serve handler key t =
      (handler key, HashTable.insert key (handler key) t) := by
  unfold serve
  rw [hmiss]

/-- After serving a key, the key looks up to the served response. -/
public theorem lookup_serve_self {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash) :
    HashTable.lookup key (serve handler key t).2 =
      some (serve handler key t).1 := by
  cases hmem : HashTable.lookup key t with
  | some r =>
      rw [serve_of_lookup_eq_some handler key t hmem]
      exact hmem
  | none =>
      rw [serve_of_lookup_eq_none handler key t hmem]
      exact HashTable.lookup_insert key (handler key) t

/-- Serving one key leaves lookups of every other key unchanged. -/
public theorem lookup_serve_of_ne {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key other : κ)
    (t : HashTable κ ρ hash) (hne : other ≠ key) :
    HashTable.lookup other (serve handler key t).2 =
      HashTable.lookup other t := by
  cases hmem : HashTable.lookup key t with
  | some r =>
      rw [serve_of_lookup_eq_some handler key t hmem]
  | none =>
      rw [serve_of_lookup_eq_none handler key t hmem]
      exact HashTable.lookup_insert_of_ne key other (handler key) t hne

/-- Serving twice is the same as serving once. -/
public theorem serve_serve {κ : Type u} {ρ : Type v} [DecidableEq κ]
    {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash) :
    serve handler key (serve handler key t).2 = serve handler key t := by
  have hmem := lookup_serve_self (handler := handler) (key := key) (t := t)
  rw [serve_of_lookup_eq_some handler key _ hmem]

/-- Serving a key preserves table validity. -/
public theorem valid_serve {κ : Type u} {ρ : Type v} [DecidableEq κ]
    {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash) (hvalid : HashTable.Valid t) :
    HashTable.Valid (serve handler key t).2 := by
  cases hmem : HashTable.lookup key t with
  | some r =>
      rw [serve_of_lookup_eq_some handler key t hmem]
      exact hvalid
  | none =>
      rw [serve_of_lookup_eq_none handler key t hmem]
      exact HashTable.valid_insert key (handler key) t hvalid

/-- On a handler-agreeing table, serving answers the handler value. -/
public theorem fst_serve_of_agree {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash)
    (agree : ∀ k r, HashTable.lookup k t = some r → r = handler k) :
    (serve handler key t).1 = handler key := by
  cases hmem : HashTable.lookup key t with
  | some r =>
      rw [serve_of_lookup_eq_some handler key t hmem]
      exact agree key r hmem
  | none =>
      rw [serve_of_lookup_eq_none handler key t hmem]

/-- Serving a key preserves handler agreement for every key. -/
public theorem agree_serve {κ : Type u} {ρ : Type v} [DecidableEq κ]
    {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t : HashTable κ ρ hash)
    (agree : ∀ k r, HashTable.lookup k t = some r → r = handler k)
    (k : κ) (r : ρ)
    (hmem : HashTable.lookup k (serve handler key t).2 = some r) :
    r = handler k := by
  cases hlook : HashTable.lookup key t with
  | some stored =>
      rw [serve_of_lookup_eq_some handler key t hlook] at hmem
      exact agree k r hmem
  | none =>
      rw [serve_of_lookup_eq_none handler key t hlook] at hmem
      have hdec : k = key ∨ k ≠ key := Decidable.em (k = key)
      cases hdec with
      | inl heq =>
          subst heq
          rw [HashTable.lookup_insert] at hmem
          cases hmem
          rfl
      | inr hne =>
          have hsame :=
            HashTable.lookup_insert_of_ne key k (handler key) t hne
          rw [hsame] at hmem
          exact agree k r hmem

/-- Lookup-level exclusion witness with no concurrency semantics: from one
snapshot with a lookup miss, every evaluation of the miss branch answers the
handler value and records the handler value, while chaining one serve makes
the next serve hit. -/
public theorem stale_serves_run_handler {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t0 : HashTable κ ρ hash)
    (hmiss : HashTable.lookup key t0 = none) :
    (serve handler key t0).1 = handler key ∧
      HashTable.lookup key (serve handler key t0).2 = some (handler key) := by
  have hrun : (serve handler key t0).1 = handler key := by
    have h := serve_of_lookup_eq_none handler key t0 hmiss
    exact congrArg Prod.fst h
  have hrec := lookup_serve_self (handler := handler) (key := key) (t := t0)
  rw [hrun] at hrec
  exact ⟨hrun, hrec⟩

/-- Lookup-level hit after one serve, with no concurrency semantics: the
second serve answers the first serve's response. Proved via C4. -/
public theorem chained_serve_hits {κ : Type u} {ρ : Type v}
    [DecidableEq κ] {hash : κ → Nat} (handler : κ → ρ) (key : κ)
    (t0 : HashTable κ ρ hash) :
    (serve handler key (serve handler key t0).2).1 =
      (serve handler key t0).1 :=
  congrArg Prod.fst (serve_serve handler key t0)

end HashTable

end Cslib.Algorithms.Lean
