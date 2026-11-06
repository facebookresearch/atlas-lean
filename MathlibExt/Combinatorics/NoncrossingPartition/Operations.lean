/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `306b05307ce5e07e232dc0c0f350c714e8df4107`.
Original formalization by Tsutomu Okano (@toskua) with Avocado (internal agent
identity); ported with permission.
-/

module

public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
import MathlibExt.Combinatorics.Finpartition.Card

/-!
# Extremal noncrossing partitions: discrete and indiscrete

This file defines the discrete and indiscrete partitions, their order
instances and block formulas, and the arity-zero uniqueness results.
-/

@[expose] public section

open Finpartition Finset

namespace NoncrossingPartition

/-- **The discrete partition is noncrossing.** For every natural number $n$, the discrete
partition of $\{0, \dots, n-1\}$, whose blocks are the singletons, is noncrossing. -/
theorem isNoncrossing_bot (n : ℕ) : IsNoncrossing (⊥ : SetPartition n) := by
  intro hcross
  obtain ⟨a, b, c, d, hab, hbc, _hcd, heq_ac, _heq_bd, _hne⟩ := hcross
  cases n with
  | zero =>
    exact Fin.elim0 a
  | succ n =>
    have ha_mem : a ∈ (Finset.univ : Finset (Fin (Nat.succ n))) := mem_univ a
    have hc_mem : c ∈ (Finset.univ : Finset (Fin (Nat.succ n))) := mem_univ c
    have h_parts_a : ({a} : Finset (Fin (Nat.succ n))) ∈
        (⊥ : SetPartition (Nat.succ n)).parts := by
      rw [parts_bot, mem_map]
      exact ⟨a, ha_mem, rfl⟩
    have h_parts_c : ({c} : Finset (Fin (Nat.succ n))) ∈
        (⊥ : SetPartition (Nat.succ n)).parts := by
      rw [parts_bot, mem_map]
      exact ⟨c, hc_mem, rfl⟩
    have h_part_a : (⊥ : SetPartition (Nat.succ n)).part a = {a} :=
      (⊥ : SetPartition (Nat.succ n)).part_eq_of_mem h_parts_a (mem_singleton_self a)
    have h_part_c : (⊥ : SetPartition (Nat.succ n)).part c = {c} :=
      (⊥ : SetPartition (Nat.succ n)).part_eq_of_mem h_parts_c (mem_singleton_self c)
    have h_single_eq : ({a} : Finset (Fin (Nat.succ n))) = {c} := by
      calc {a} = (⊥ : SetPartition (Nat.succ n)).part a := h_part_a.symm
        _ = (⊥ : SetPartition (Nat.succ n)).part c := heq_ac
        _ = {c} := h_part_c
    have h_a_mem_c : a ∈ ({c} : Finset (Fin (Nat.succ n))) := by
      rw [← h_single_eq]
      exact mem_singleton_self a
    have h_a_eq_c : a = c := mem_singleton.mp h_a_mem_c
    have h_b_lt_a : b < a := h_a_eq_c.symm ▸ hbc
    exact (ne_of_lt (lt_trans hab h_b_lt_a)) rfl

/-- **The indiscrete partition is noncrossing.** For every natural number $n$, the indiscrete
partition of $\{0, \dots, n-1\}$, the coarsest partition of this set, is noncrossing. -/
theorem isNoncrossing_top (n : ℕ) : IsNoncrossing (⊤ : SetPartition n) := by
  intro hcross
  obtain ⟨a, b, _c, _d, _hab, _hbc, _hcd, _heq_ac, heq_bd, hne⟩ := hcross
  cases n with
  | zero =>
    exact Fin.elim0 a
  | succ n =>
    have ha_mem : a ∈ (Finset.univ : Finset (Fin (Nat.succ n))) := mem_univ a
    have hb_mem : b ∈ (Finset.univ : Finset (Fin (Nat.succ n))) := mem_univ b
    have h_part_a_mem : (⊤ : SetPartition (Nat.succ n)).part a ∈
        (⊤ : SetPartition (Nat.succ n)).parts :=
      ((⊤ : SetPartition (Nat.succ n)).part_mem).mpr ha_mem
    have h_part_b_mem : (⊤ : SetPartition (Nat.succ n)).part b ∈
        (⊤ : SetPartition (Nat.succ n)).parts :=
      ((⊤ : SetPartition (Nat.succ n)).part_mem).mpr hb_mem
    have h_sub := Finpartition.parts_top_subset
      (Finset.univ : Finset (Fin (Nat.succ n)))
    have h_a_eq : (⊤ : SetPartition (Nat.succ n)).part a = Finset.univ :=
      mem_singleton.mp (h_sub h_part_a_mem)
    have h_b_eq : (⊤ : SetPartition (Nat.succ n)).part b = Finset.univ :=
      mem_singleton.mp (h_sub h_part_b_mem)
    exact hne (by rw [h_a_eq, h_b_eq])

/-- **Discrete noncrossing partition.** For a natural number $n$, the discrete noncrossing
partition of $\{0, \dots, n-1\}$ is the finest partition of this set, whose blocks are the
singletons $\{a\}$ for $a \in \{0, \dots, n-1\}$; it is noncrossing. -/
def discrete (n : ℕ) : NoncrossingPartition n :=
  ⟨⊥, isNoncrossing_bot n⟩

/-- **The indiscrete noncrossing partition.** For a natural number $n$, the indiscrete noncrossing
partition of $\{0, \dots, n-1\}$ is the coarsest partition of this set: its only block is the whole
set when $n > 0$, and it has no blocks when $n = 0$. It is noncrossing. -/
def indiscrete (n : ℕ) : NoncrossingPartition n :=
  ⟨⊤, isNoncrossing_top n⟩

@[simp]
theorem discrete_val (n : ℕ) : (discrete n).val = ⊥ := rfl

@[simp]
theorem indiscrete_val (n : ℕ) : (indiscrete n).val = ⊤ := rfl

instance (n : ℕ) : Bot (NoncrossingPartition n) where
  bot := discrete n

instance (n : ℕ) : Top (NoncrossingPartition n) where
  top := indiscrete n

instance (n : ℕ) : OrderBot (NoncrossingPartition n) where
  bot_le P := by
    change (⊥ : SetPartition n) ≤ P.val
    exact bot_le

instance (n : ℕ) : OrderTop (NoncrossingPartition n) where
  le_top P := by
    change P.val ≤ (⊤ : SetPartition n)
    exact le_top

/-- **The block of a point in the discrete noncrossing partition.** For every natural number
$n$ and every $a \in \{0, \dots, n-1\}$, the block containing $a$ in the discrete noncrossing
partition of $\{0, \dots, n-1\}$ is the singleton $\{a\}$. -/
@[simp]
theorem block_discrete (n : ℕ) (a : Fin n) : block (discrete n) a = {a} := by
  by_cases hn : n = 0
  · subst hn
    exact Fin.elim0 a
  · have ha_mem : a ∈ (Finset.univ : Finset (Fin n)) := mem_univ a
    have h_parts : ({a} : Finset (Fin n)) ∈ (⊥ : SetPartition n).parts := by
      rw [parts_bot, mem_map]
      exact ⟨a, ha_mem, rfl⟩
    exact (⊥ : SetPartition n).part_eq_of_mem h_parts (mem_singleton_self a)

/-- **The block of a point in the indiscrete noncrossing partition.** For every natural number
$n$ and every $a \in \{0, \dots, n-1\}$, the block containing $a$ in the indiscrete noncrossing
partition of $\{0, \dots, n-1\}$ is the whole set $\{0, \dots, n-1\}$.

For $n = 0$ there is no such $a$, so the statement is vacuous. -/
@[simp]
theorem block_indiscrete (n : ℕ) (a : Fin n) : block (indiscrete n) a = Finset.univ := by
  by_cases hn : n = 0
  · subst hn
    exact Fin.elim0 a
  · have ha_mem : a ∈ (Finset.univ : Finset (Fin n)) := mem_univ a
    have h_part_mem : (⊤ : SetPartition n).part a ∈ (⊤ : SetPartition n).parts :=
      ((⊤ : SetPartition n).part_mem).mpr ha_mem
    exact mem_singleton.mp (parts_top_subset (Finset.univ : Finset (Fin n)) h_part_mem)

/-- **The discrete noncrossing partition consists of the singletons.** For every natural number
$n$, the set of blocks of the discrete noncrossing partition of $\{0, \dots, n-1\}$ is exactly
the set of singletons $\{a\}$ with $a \in \{0, \dots, n-1\}$. -/
@[simp]
theorem discrete_parts (n : ℕ) :
    (discrete n).val.parts =
      (Finset.univ : Finset (Fin n)).map ⟨singleton, singleton_injective⟩ :=
  rfl

/-- **The indiscrete partition of the empty set has no blocks.** For $n = 0$, the set of blocks
of the indiscrete noncrossing partition of $\{0, \dots, n-1\}$, the empty set, is empty. -/
@[simp]
theorem indiscrete_parts_zero : (indiscrete 0).val.parts = ∅ := by
  rfl

/-- **The discrete partition of the empty set has no blocks.** For $n = 0$, the discrete
noncrossing partition of the empty set $\{0, \dots, n-1\}$ has no blocks: its set of blocks is
empty. -/
@[simp]
theorem discrete_parts_zero : (discrete 0).val.parts = ∅ := by
  rfl

/-- **The indiscrete partition of a nonempty set has a single block.** For a natural number $n$
with $0 < n$, the set of blocks of the indiscrete noncrossing partition of $\{0, \dots, n-1\}$ is
$\{\{0, \dots, n-1\}\}$: its only block is the whole set. -/
theorem indiscrete_parts_pos {n : ℕ} (hn : 0 < n) :
    (indiscrete n).val.parts = {Finset.univ} := by
  have h0 : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := mem_univ _
  have h_ne : (Finset.univ : Finset (Fin n)) ≠ ∅ := ne_empty_of_mem h0
  have h_not_bot : (Finset.univ : Finset (Fin n)) ≠ (⊥ : Finset (Fin n)) := by
    intro h
    exact h_ne h
  have h_top : (⊤ : SetPartition n) = Finpartition.indiscrete h_not_bot :=
    dite_eq_right h_not_bot
  calc (indiscrete n).val.parts = (⊤ : SetPartition n).parts := rfl
    _ = (Finpartition.indiscrete h_not_bot).parts := by rw [h_top]
    _ = {Finset.univ} := rfl

/-- **Characterization of the discrete noncrossing partition.** Let $n$ be a natural number. A
noncrossing partition $P$ of $\{0, \dots, n-1\}$ equals the discrete noncrossing partition if
and only if $P$, viewed as a set partition, is the finest partition of $\{0, \dots, n-1\}$. -/
theorem eq_discrete_iff_val_eq_bot {n : ℕ} {P : NoncrossingPartition n} :
    P = discrete n ↔ P.val = ⊥ := by
  constructor
  · intro h
    rw [h, discrete_val]
  · intro h
    exact ext h

/-- **Characterization of the indiscrete noncrossing partition.** Let $n$ be a natural number.
A noncrossing partition $P$ of $\{0, \dots, n-1\}$ equals the indiscrete noncrossing partition
if and only if $P$, viewed as a set partition, is the coarsest partition of
$\{0, \dots, n-1\}$. -/
theorem eq_indiscrete_iff_val_eq_top {n : ℕ} {P : NoncrossingPartition n} :
    P = indiscrete n ↔ P.val = ⊤ := by
  constructor
  · intro h
    rw [h, indiscrete_val]
  · intro h
    exact ext h

/-- **A partition whose blocks are all the whole set is indiscrete.** Let $n$ be a natural number
and let $P$ be a noncrossing partition of $\{0, \dots, n-1\}$. If for every
$a \in \{0, \dots, n-1\}$ the block of $P$ containing $a$ is the whole set $\{0, \dots, n-1\}$,
then $P$ is the indiscrete noncrossing partition. -/
theorem eq_indiscrete_of_forall_block_eq_univ {n : ℕ} (P : NoncrossingPartition n)
    (h : ∀ a : Fin n, block P a = Finset.univ) : P = indiscrete n := by
  rw [eq_indiscrete_iff_val_eq_top]
  by_cases hn : n = 0
  · subst hn
    have h_univ_bot : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := rfl
    have h_parts_P : P.val.parts = ∅ := parts_eq_empty_iff.mpr h_univ_bot
    have h_parts_top : (⊤ : SetPartition 0).parts = ∅ := rfl
    exact Finpartition.ext (by rw [h_parts_P, h_parts_top])
  · by_contra h_ne_top
    have ha : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have h_mem : block P ha ∈ P.val.parts := block_mem_parts P ha
    have h_lt : (block P ha).card < (Finset.univ : Finset (Fin n)).card :=
      Finpartition.card_lt_of_ne_top P.val h_ne_top h_mem
    rw [h ha] at h_lt
    exact Nat.lt_irrefl _ h_lt

/-!
### Arity-zero uniqueness
-/

/-- Canonical `Unique` instance for `NoncrossingPartition 0`. -/
instance : Unique (NoncrossingPartition 0) where
  default := indiscrete 0
  uniq P := by
    have hP : P.val.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr rfl
    have hEq : P.val = (indiscrete 0).val :=
      Finpartition.ext (by rw [hP, indiscrete_parts_zero])
    exact ext hEq

/-- **The empty set has a unique noncrossing partition.** For $n = 0$, every noncrossing partition
of $\{0, \dots, n-1\}$, the empty set, equals the indiscrete noncrossing partition of this set. -/
theorem eq_indiscrete_zero (P : NoncrossingPartition 0) : P = indiscrete 0 :=
  Subsingleton.elim P (indiscrete 0)

/-- **Discrete and indiscrete partitions agree on the empty set.** For $n = 0$, the discrete and
the indiscrete noncrossing partitions of the empty set $\{0, \dots, n-1\}$ are equal. -/
@[simp]
theorem discrete_zero_eq_indiscrete_zero : discrete 0 = indiscrete 0 :=
  eq_indiscrete_zero (discrete 0)

/-- **The only noncrossing partition of the empty set is the discrete one.** For $n = 0$, every
noncrossing partition of the empty set $\{0, \dots, n-1\}$ equals the discrete noncrossing
partition. -/
theorem eq_discrete_zero (P : NoncrossingPartition 0) : P = discrete 0 := by
  rw [discrete_zero_eq_indiscrete_zero]
  exact eq_indiscrete_zero P

end NoncrossingPartition
