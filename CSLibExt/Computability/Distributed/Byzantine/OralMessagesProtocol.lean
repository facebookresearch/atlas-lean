/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Byzantine generals: the oral messages algorithm as an oral-message protocol
-/
module

public import CSLibExt.Computability.Distributed.Byzantine.Impossibility
public import CSLibExt.Computability.Distributed.Byzantine.OralMessages

/-!
# `OM(m)` as an `OralProtocol`, and the bound `3 m < n` in one model

`OralMessages.lean` proves Theorem 1 of Lamport, Shostak and Pease (more than `3 m` generals, at
most `m` traitors) for the recursive function `om`, with its own model of the traitors, and
`Impossibility.lean` proves that, when there are at least two orders, no `OralProtocol` tolerates
`m` traitors among `n` generals if `3 ≤ n ≤ 3 m`. This file runs `OM(m)` as an `OralProtocol`, so
that both halves hold in one model: if there are at least three generals and at least two
orders, some protocol with state and message types in `Type (max u v)` solves the Byzantine
generals problem with commander `c` and at most `m` traitors if and only if `3 m < n`.

The protocol is the exponential information gathering form of `OM(m)`. A general's state is a
table of values indexed by relay paths, latest sender first: the entry at `q :: τ`, written in
round `τ.length`, is the value the general received from `q` for the path `τ`. In round `r` every
general sends its table to every general, and each receiver copies the entry at `τ` of the table
it got from `q` to its own entry at `q :: τ`, for every sender `q` and every path `τ` of length
`r`. The commander's table holds its order at the empty path. After `m + 1` rounds a general
decides by evaluating `om` on its table.

## Main definitions

* `OralMessages.toProtocol c m`: `OM(m)` with commander `c` as an `OralProtocol` whose states
  and messages are tables of values.
* `OralMessages.advOfMessages`: the relays of the traitors in `om` that match given messages of
  the traitors in `toProtocol`.

## Main results

* `OralMessages.decision_toProtocol_of_le`: after any number `r ≥ m + 1` of rounds every
  general decides the value of `om` in which the loyal generals are those outside the set of
  traitors and the traitors relay as `advOfMessages` reads off their messages.
  `OralMessages.decision_toProtocol` is the case `r = m + 1`.
* `OralMessages.solves_toProtocol`: with more than `3 m` generals, `toProtocol c m` solves the
  problem with commander `c` and at most `m` traitors in `m + 1` rounds.
* `exists_solves_iff_three_mul_lt_card`: with at least three generals and at least two orders,
  some protocol whose state and message types lie in `Type (max u v)` solves the problem with
  commander `c` and at most `m` traitors if and only if there are more than `3 m` generals.

## Implementation notes

A message is the sender's whole table, and a receiver reads only its entries for the paths of
the current length. A traitor's message is an arbitrary table, so it fixes a value for every
path, independently for each round and each recipient; `advOfMessages` reads off the values that
`om` uses. The decision runs `om` with no loyal general and with the table as the relays, so that
every value `om` uses is the one the general recorded.

The characterization quantifies over state and message types in `Type (max u v)`, the universe
of the tables `List G → V`; the impossibility half holds in every universe
(`Impossibility.OralProtocol.not_solves_of_card_le_three_mul`).

## References

* L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on
  Programming Languages and Systems 4(3), 1982: §2 (impossibility results) and §3 (algorithm
  `OM(m)`, Theorem 1).
* N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 6 (exponential
  information gathering).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Distributed.Byzantine

open Impossibility

namespace OralMessages

variable {G : Type u} {V : Type v} [DecidableEq G] [DecidableEq V] [Inhabited V]

/-- The oral messages algorithm `OM(m)` with commander `c`, as an `OralProtocol` meant to run for
`m + 1` rounds. States and messages are tables of values indexed by relay paths, latest sender
first. The commander starts with its order in every entry, and every other general with
`default` in every entry. In round `r` every general sends its table to every general, and a
receiver sets its entry at `q :: τ` to the entry at `τ` of the table it got from `q`, for every
sender `q` and every path `τ` of length `r`; its other entries stay. A general `p` decides the
value `om` gives for commander `c` and lieutenants `Finset.univ.erase c` when every value `p`
receives is read from its table: `om` runs with no loyal general and with the table as the
relays. -/
def toProtocol [Fintype G] (c : G) (m : ℕ) : OralProtocol G V (List G → V) (List G → V) where
  init _ _ := default
  initCommander v _ := v
  send _ _ s _ := s
  recv r _ s msg := fun
    | [] => s []
    | q :: τ => if τ.length = r then msg q τ else s (q :: τ)
  decide p s := om (fun _ ↦ False) (fun σ _ ↦ s σ.reverse) m c (Finset.univ.erase c) default [] p

/-- The relays of the traitors in `om` that match the messages `adv` of the traitors in
`toProtocol`: a traitor `q` relaying along the path `path ++ [q]` sends to `p` the entry at
`path.reverse` of the table it sends to `p` in round `path.length`. The empty path, which `om`
never uses, gets `default`. -/
def advOfMessages (adv : ℕ → G → G → List G → V) (σ : List G) (p : G) : V :=
  match σ.reverse with
  | [] => default
  | q :: τ => adv τ.length q p τ

omit [DecidableEq G] [DecidableEq V] in
/-- A traitor `q` relaying along `path ++ [q]` sends to `p` the entry at `path.reverse` of the
table it sends to `p` in round `path.length`. -/
@[simp]
theorem advOfMessages_append_singleton (adv : ℕ → G → G → List G → V) (path : List G)
    (q p : G) : advOfMessages adv (path ++ [q]) p = adv path.length q p path.reverse := by
  simp [advOfMessages]

section Execution

variable [Fintype G] (c : G) (m : ℕ) (v : V) (traitors : Finset G)
  (adv : ℕ → G → G → List G → V)

/-- After `r ≥ τ.length` rounds the entry at `τ` of a table is what it was after `τ.length`
rounds: round `r'` writes only the entries for paths of length `r' + 1`. -/
private theorem state_eq_state_length (r : ℕ) (p : G) (τ : List G) (h : τ.length ≤ r) :
    (toProtocol c m).state c v traitors adv r p τ =
      (toProtocol c m).state c v traitors adv τ.length p τ := by
  induction r with
  | zero => rw [Nat.le_zero.mp h]
  | succ r ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [OralProtocol.state_succ, ← ih (by omega)]
      cases τ with
      | nil => rfl
      | cons q τ =>
        simp only [List.length_cons] at h
        simp [toProtocol, show τ.length ≠ r by omega]
    · rw [h]

/-- The entry at `q :: τ` of the table of `p` is written in round `τ.length`: it is the message of
the traitor `q` at `τ`, or the entry at `τ` of the table of the loyal general `q` after
`τ.length` rounds. -/
private theorem state_cons (p q : G) (τ : List G) :
    (toProtocol c m).state c v traitors adv (τ.length + 1) p (q :: τ) =
      if q ∈ traitors then adv τ.length q p τ
      else (toProtocol c m).state c v traitors adv τ.length q τ := by
  rw [OralProtocol.state_succ]
  by_cases hq : q ∈ traitors
  · simp [toProtocol, OralProtocol.inbox, hq]
  · simp [toProtocol, OralProtocol.inbox, hq]

/-- The commander's table holds its order at the empty path. -/
private theorem state_zero_commander : (toProtocol c m).state c v traitors adv 0 c [] = v := by
  simp [OralProtocol.state_zero, OralProtocol.initState_self, toProtocol]

/-- When `c'` holds the value it recorded for `path`, the value that `q` receives from `c'` in
`om` is the entry that the protocol writes at `c' :: path.reverse` in the table of `q`. -/
private theorem received_eq (c' : G) (path : List G) (q : G) :
    received (· ∉ traitors) (advOfMessages adv) c'
        ((toProtocol c m).state c v traitors adv path.length c' path.reverse) path q =
      (toProtocol c m).state c v traitors adv (path.length + 1) q (c' :: path.reverse) := by
  have h := state_cons c m v traitors adv q c' path.reverse
  rw [List.length_reverse] at h
  rw [h, received]
  by_cases hc : c' ∈ traitors
  · simp [hc]
  · simp [hc]

/-- `OM(k)` from commander `c'` with superiors `path`, where `c'` holds the value it recorded for
`path`, gives `p` the value that `om` computes from any table of `p` that agrees with the entries
the protocol writes for all paths of length at most `path.length + k + 1`. -/
private theorem om_eq_om_table (p : G) (tbl : List G → V) (k : ℕ) :
    ∀ (c' : G) (S : Finset G) (path : List G) (v' : V),
      (∀ τ : List G, τ.length ≤ path.length + k + 1 →
        tbl τ = (toProtocol c m).state c v traitors adv τ.length p τ) →
      om (· ∉ traitors) (advOfMessages adv) k c' S
          ((toProtocol c m).state c v traitors adv path.length c' path.reverse) path p =
        om (fun _ ↦ False) (fun σ _ ↦ tbl σ.reverse) k c' S v' path p := by
  have hrecv : ∀ (c' : G) (path : List G) (v' : V), (∀ τ : List G, τ.length ≤ path.length + 1 →
      tbl τ = (toProtocol c m).state c v traitors adv τ.length p τ) →
      received (· ∉ traitors) (advOfMessages adv) c'
          ((toProtocol c m).state c v traitors adv path.length c' path.reverse) path p =
        received (fun _ ↦ False) (fun σ _ ↦ tbl σ.reverse) c' v' path p := by
    intro c' path v' htbl
    rw [received_eq, received, ite_eq_right not_false, htbl _ (by simp)]
    simp
  induction k with
  | zero =>
    intro c' S path v' htbl
    rw [om, om]
    exact hrecv c' path v' fun τ hτ ↦ htbl τ (by omega)
  | succ k ih =>
    intro c' S path v' htbl
    rw [om, om]
    congr 1
    refine Multiset.map_congr rfl fun q _ ↦ ?_
    split_ifs with hqp
    · exact hrecv c' path v' fun τ hτ ↦ htbl τ (by omega)
    · rw [received_eq]
      have h := ih q (S.erase q) (path ++ [c'])
        (received (fun _ ↦ False) (fun σ _ ↦ tbl σ.reverse) c' v' path q)
        fun τ hτ ↦ htbl τ (by simp only [List.length_append, List.length_singleton] at hτ; omega)
      simpa only [List.length_append, List.length_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append] using h

/-- **`toProtocol` runs `OM(m)`.** After any number `r ≥ m + 1` of rounds of `toProtocol c m`
with commander `c`, order `v`, traitors `traitors` and traitor messages `adv`, every general `p`
decides the value of `om` in which the loyal generals are those outside `traitors` and the
traitors relay `advOfMessages adv`. Rounds after the first `m + 1` write only the entries for
paths longer than `m + 1`, which the decision does not read. -/
theorem decision_toProtocol_of_le {r : ℕ} (hr : m + 1 ≤ r) (p : G) :
    (toProtocol c m).decision c v traitors adv r p =
      om (· ∉ traitors) (advOfMessages adv) m c (Finset.univ.erase c) v [] p := by
  have h := om_eq_om_table c m v traitors adv p
    ((toProtocol c m).state c v traitors adv r p) m c (Finset.univ.erase c) [] default
    fun τ hτ ↦ state_eq_state_length c m v traitors adv r p τ
      (by simp only [List.length_nil] at hτ; omega)
  rw [List.length_nil, List.reverse_nil, state_zero_commander] at h
  exact h.symm

/-- `toProtocol c m` runs `OM(m)` in `m + 1` rounds: the case `r = m + 1` of
`decision_toProtocol_of_le`. -/
theorem decision_toProtocol (p : G) :
    (toProtocol c m).decision c v traitors adv (m + 1) p =
      om (· ∉ traitors) (advOfMessages adv) m c (Finset.univ.erase c) v [] p :=
  decision_toProtocol_of_le c m v traitors adv le_rfl p

end Execution

/-- **`OM(m)` solves the Byzantine generals problem as an oral-message protocol** (Theorem 1 of
Lamport, Shostak and Pease). If there are more than `3 m` generals of a finite type, then
`toProtocol c m` satisfies IC1 and IC2 after `m + 1` rounds, for every order, every set of at most
`m` traitors and every behavior of the traitors. -/
theorem solves_toProtocol [Fintype G] (c : G) {m : ℕ} (hG : 3 * m < Fintype.card G) :
    (toProtocol (V := V) c m).Solves c m (m + 1) := by
  intro v traitors ht adv
  obtain ⟨h1, h2⟩ := byzantine_generals (loyal := (· ∉ traitors)) (adv := advOfMessages adv) c v
    hG ((Finset.card_le_card fun x hx ↦ by simpa using hx).trans ht)
  refine ⟨fun i j hi hj hit hjt ↦ ?_, fun hc i hi hit ↦ ?_⟩
  · rw [decision_toProtocol, decision_toProtocol]
    exact h1 i j hi hj hit hjt
  · rw [decision_toProtocol]
    exact h2 hc i hi hit

end OralMessages

variable {G : Type u} {V : Type v} [DecidableEq G]

/-- **The Byzantine generals problem with oral messages is solvable exactly when there are more
than `3 m` generals** (Lamport, Shostak and Pease). Let the generals form a finite type with at
least three elements, and let there be at least two orders. Some `OralProtocol` whose state and
message types lie in `Type (max u v)` solves the problem with commander `c` and at most `m`
traitors, in some number of rounds, if and only if `3 m` is less than the number of generals. In
that case `OM(m)` solves it in `m + 1` rounds (`OralMessages.solves_toProtocol`); otherwise no
protocol, in any universe, solves it
(`Impossibility.OralProtocol.not_solves_of_card_le_three_mul`). -/
theorem exists_solves_iff_three_mul_lt_card [Fintype G] [Nontrivial V] (c : G) (m : ℕ)
    (h3 : 3 ≤ Fintype.card G) :
    (∃ (σ M : Type (max u v)) (P : OralProtocol G V σ M) (T : ℕ), P.Solves c m T) ↔
      3 * m < Fintype.card G := by
  constructor
  · rintro ⟨σ, M, P, T, hP⟩
    by_contra h
    exact P.not_solves_of_card_le_three_mul c h3 (by omega) T hP
  · intro h
    classical
    have : Inhabited V := ⟨Classical.arbitrary V⟩
    exact ⟨_, _, OralMessages.toProtocol c m, m + 1, OralMessages.solves_toProtocol c h⟩

end Cslib.Distributed.Byzantine
