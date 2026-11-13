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

public import MathlibExt.Combinatorics.NoncrossingPartition.Operations
import MathlibExt.Combinatorics.Finpartition.Card
import MathlibExt.Combinatorics.Finpartition.Atomise
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Embedding.Set

/-!
# Small-arity classification for noncrossing partitions

This file classifies noncrossing partitions through arity three and gives
finite equivalences used to evaluate sums over proper partitions.
-/

@[expose] public section

open Finpartition Finset

namespace NoncrossingPartition

/-- **Noncrossing partitions of one point are indiscrete.** Every noncrossing partition of the
one-point set $\{0\}$ equals the indiscrete noncrossing partition of $\{0\}$. -/
theorem eq_indiscrete_one (P : NoncrossingPartition 1) : P = indiscrete 1 := by
  rw [eq_indiscrete_iff_val_eq_top]
  have hs : (Finset.univ : Finset (Fin 1)).Nonempty := ⟨⟨0, by decide⟩, mem_univ _⟩
  rw [Finpartition.eq_top_iff_card_parts_eq_one P.val hs]
  have h_ge : 1 ≤ P.val.parts.card :=
    Finpartition.one_le_card_parts_of_nonempty P.val hs
  have h_le : P.val.parts.card ≤ 1 := by
    have h := Finpartition.card_parts_le_card (P := P.val)
    have h_univ : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
    omega
  omega

/-- **The discrete and indiscrete partitions of a two-element set differ.** The discrete
noncrossing partition of $\{0, 1\}$ is not equal to the indiscrete noncrossing partition of
$\{0, 1\}$. -/
theorem discrete_two_ne_indiscrete_two : discrete 2 ≠ indiscrete 2 := by
  intro h
  have h_discrete : (discrete 2).val.parts.card = 2 := by
    rw [discrete_parts, card_map]
    simp
  have h_indiscrete : (indiscrete 2).val.parts.card = 1 := by
    rw [indiscrete_parts_pos (by decide)]
    simp
  have h_eq : (discrete 2).val.parts.card = (indiscrete 2).val.parts.card := by
    rw [h]
  rw [h_discrete, h_indiscrete] at h_eq
  exact absurd h_eq (by decide)

/-- **Classification of noncrossing partitions of a two-element set.** Every noncrossing partition
of $\{0, 1\}$ is either the discrete or the indiscrete noncrossing partition of $\{0, 1\}$. -/
theorem eq_discrete_or_indiscrete_two (P : NoncrossingPartition 2) :
    P = discrete 2 ∨ P = indiscrete 2 := by
  have hs : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨⟨0, by decide⟩, mem_univ _⟩
  have h_le : P.val.parts.card ≤ 2 := by
    have h := Finpartition.card_parts_le_card (P := P.val)
    have h_univ : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
    omega
  have h_ge : 1 ≤ P.val.parts.card :=
    Finpartition.one_le_card_parts_of_nonempty P.val hs
  have h_choice : P.val.parts.card = 1 ∨ P.val.parts.card = 2 := by omega
  rcases h_choice with h1 | h2
  · right
    rw [eq_indiscrete_iff_val_eq_top, Finpartition.eq_top_iff_card_parts_eq_one P.val hs]
    exact h1
  · left
    rw [eq_discrete_iff_val_eq_bot, eq_bot_iff_card_parts_eq_card]
    have h_univ : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
    omega

/-- Provide `Unique (NoncrossingPartition 1)` via `eq_indiscrete_one`. -/
instance : Unique (NoncrossingPartition 1) where
  default := indiscrete 1
  uniq P := eq_indiscrete_one P

/-- **Noncrossing partitions of the empty set.** There is exactly one noncrossing partition of the
empty set, that is, of $\{0, \dots, n-1\}$ for $n = 0$. -/
@[simp]
theorem card_zero : Fintype.card (NoncrossingPartition 0) = 1 :=
  Fintype.card_unique

/-- **Noncrossing partitions of a one-element set.** There is exactly one noncrossing partition
of $\{0\}$. -/
@[simp]
theorem card_one : Fintype.card (NoncrossingPartition 1) = 1 :=
  Fintype.card_unique

def twoEquiv : NoncrossingPartition 2 ≃ Fin 2 where
  toFun P := if P = discrete 2 then 0 else 1
  invFun
    | 0 => discrete 2
    | 1 => indiscrete 2
  left_inv P := by
    by_cases h : P = discrete 2
    · simp [h]
    · have hP : P = indiscrete 2 := by
        rcases eq_discrete_or_indiscrete_two P with hD | hI
        · exact absurd hD h
        · exact hI
      have h_if : (if P = discrete 2 then (0 : Fin 2) else 1) = 1 := ite_eq_right h
      calc (match (if P = discrete 2 then (0 : Fin 2) else 1) with
            | 0 => discrete 2
            | 1 => indiscrete 2) = indiscrete 2 := by rw [h_if]
        _ = P := hP.symm
  right_inv
    | 0 => by simp
    | 1 => by
      have h_ne : ¬ indiscrete 2 = discrete 2 := fun h => discrete_two_ne_indiscrete_two h.symm
      simp [h_ne]

/-- **Noncrossing partitions of a two-element set.** There are exactly two noncrossing partitions
of $\{0, 1\}$. -/
@[simp]
theorem card_two : Fintype.card (NoncrossingPartition 2) = 2 := by
  rw [Fintype.card_congr twoEquiv]
  simp

@[simp]
theorem twoEquiv_apply_discrete : twoEquiv (discrete 2) = 0 := by
  simp [twoEquiv]

@[simp]
theorem twoEquiv_apply_indiscrete : twoEquiv (indiscrete 2) = 1 := by
  have h_ne : ¬ indiscrete 2 = discrete 2 := fun h => discrete_two_ne_indiscrete_two h.symm
  simp [twoEquiv, h_ne]

@[simp]
theorem twoEquiv_symm_apply_zero : (twoEquiv.symm 0) = discrete 2 := rfl

@[simp]
theorem twoEquiv_symm_apply_one : (twoEquiv.symm 1) = indiscrete 2 := rfl

/-- **The proper noncrossing partition of two points.** Call a noncrossing partition of $\{0, 1\}$
proper if it is not the indiscrete one. This is the bijection from a one-element set onto the set
of proper noncrossing partitions of $\{0, 1\}$, sending its element to the discrete noncrossing
partition; in particular the discrete partition is the only proper one. -/
def properTwoEquiv : Unit ≃ { P : NoncrossingPartition 2 // P ≠ indiscrete 2 } where
  toFun _ := ⟨discrete 2, discrete_two_ne_indiscrete_two⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv := by
    intro ⟨P, hP⟩
    have h_eq : P = discrete 2 := by
      rcases eq_discrete_or_indiscrete_two P with hD | hI
      · exact hD
      · exact absurd hI hP
    exact Subtype.ext h_eq.symm

@[simp]
theorem properTwoEquiv_apply : properTwoEquiv () = ⟨discrete 2, discrete_two_ne_indiscrete_two⟩ :=
  rfl

@[simp]
theorem properTwoEquiv_symm_apply (P : NoncrossingPartition 2) (hP : P ≠ indiscrete 2) :
    properTwoEquiv.symm ⟨P, hP⟩ = () :=
  rfl

/-!
### Arity three – two-block constructor and classification
-/

private lemma card_univ_fin_three : (Finset.univ : Finset (Fin 3)).card = 3 := by
  simp

private lemma univ_ne_bot_fin_three :
    (Finset.univ : Finset (Fin 3)) ≠ (⊥ : Finset (Fin 3)) := by
  intro h
  have h_mem : (0 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)) := mem_univ _
  rw [h] at h_mem
  simp at h_mem

private lemma sum_card_parts_three (P : NoncrossingPartition 3) :
    ∑ B ∈ P.val.parts, B.card = 3 := by
  have h_sum := P.val.sum_card_parts
  rw [card_univ_fin_three] at h_sum
  exact h_sum

private lemma one_le_card_of_mem_parts_three {P : NoncrossingPartition 3}
    {B : Finset (Fin 3)} (hB : B ∈ P.val.parts) : 1 ≤ B.card := by
  have h_nonempty : B.Nonempty := P.val.nonempty_of_mem_parts hB
  exact one_le_card.mpr h_nonempty

private lemma parts_nonempty_three (P : NoncrossingPartition 3) :
    P.val.parts.Nonempty := by
  rw [Finpartition.parts_nonempty_iff]
  exact univ_ne_bot_fin_three

private lemma card_erase_fin_three (a : Fin 3) :
    (Finset.univ.erase a).card = 2 := by
  rw [Finset.card_erase_of_mem (mem_univ a), card_univ_fin_three]

private lemma erase_nonempty_fin_three (a : Fin 3) : (Finset.univ.erase a).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h_eq
  have h_card : (Finset.univ.erase a).card = 0 := by rw [h_eq]; simp
  rw [card_erase_fin_three] at h_card
  omega

private lemma card_twoBlockParts (a : Fin 3) :
    ({ {a}, Finset.univ.erase a } : Finset (Finset (Fin 3))).card = 2 := by
  have h_ne : ({a} : Finset (Fin 3)) ≠ Finset.univ.erase a := by
    intro h_eq
    have h1 : ({a} : Finset (Fin 3)).card = 1 := by simp
    have h2 : (Finset.univ.erase a).card = 2 := card_erase_fin_three a
    have h : ({a} : Finset (Fin 3)).card = (Finset.univ.erase a).card := by rw [h_eq]
    omega
  have h_notMem : ({a} : Finset (Fin 3)) ∉
      ({Finset.univ.erase a} : Finset (Finset (Fin 3))) := by
    rw [mem_singleton]
    exact h_ne
  have h_eq : ({ {a}, Finset.univ.erase a } : Finset (Finset (Fin 3))) =
      insert {a} {Finset.univ.erase a} := rfl
  rw [h_eq, card_insert_of_notMem h_notMem, card_singleton]

/-- **Two-block partition of three points.** For $a \in \{0, 1, 2\}$, this is the noncrossing
partition of $\{0, 1, 2\}$ whose blocks are $\{a\}$ and $\{0, 1, 2\} \setminus \{a\}$. -/
def twoBlockPartition (a : Fin 3) : NoncrossingPartition 3 :=
  ⟨Finpartition.atomise Finset.univ ({ {a} } : Finset (Finset (Fin 3))),
    isNoncrossing_of_le_three (by decide) _⟩

@[simp]
theorem twoBlockPartition_parts (a : Fin 3) :
    (twoBlockPartition a).val.parts = { {a}, Finset.univ.erase a } := by
  have hB_sub : ({a} : Finset (Fin 3)) ⊆ Finset.univ := by
    intro x _
    exact mem_univ x
  have hB_ne : ({a} : Finset (Fin 3)).Nonempty := ⟨a, mem_singleton_self a⟩
  have h_sdiff_eq_erase :
      Finset.univ \ ({a} : Finset (Fin 3)) = Finset.univ.erase a :=
    Finset.sdiff_singleton_eq_erase a _
  have h_compl : (Finset.univ \ ({a} : Finset (Fin 3))).Nonempty := by
    rw [h_sdiff_eq_erase]
    exact erase_nonempty_fin_three a
  have h_def : (twoBlockPartition a).val =
      Finpartition.atomise Finset.univ ({ {a} } : Finset (Finset (Fin 3))) := rfl
  have h_atom := Finpartition.atomise_singleton_parts hB_sub hB_ne h_compl
  rw [h_def, h_atom, h_sdiff_eq_erase]

@[simp]
theorem twoBlockPartition_parts_card (a : Fin 3) :
    (twoBlockPartition a).val.parts.card = 2 := by
  rw [twoBlockPartition_parts]
  exact card_twoBlockParts a

private lemma biUnion_two_eq_union (B1 B2 : Finset (Fin 3)) :
    (insert B1 {B2} : Finset (Finset (Fin 3))).biUnion id = B1 ∪ B2 := by
  ext x
  constructor
  · intro hx
    rw [mem_biUnion] at hx
    obtain ⟨y, hy_mem, hx_in_y⟩ := hx
    rw [mem_insert, mem_singleton] at hy_mem
    rcases hy_mem with rfl | rfl
    · exact mem_union_left _ hx_in_y
    · exact mem_union_right _ hx_in_y
  · intro hx
    rw [mem_biUnion]
    rw [mem_union] at hx
    rcases hx with hx_B1 | hx_B2
    · exact ⟨B1, mem_insert_self B1 {B2}, hx_B1⟩
    · exact ⟨B2, mem_insert_of_mem (mem_singleton_self B2), hx_B2⟩

private lemma union_two_blocks_eq_univ (P : NoncrossingPartition 3)
    (B1 B2 : Finset (Fin 3)) (h_eq : P.val.parts = insert B1 {B2}) :
    B1 ∪ B2 = Finset.univ := by
  have h_biUnion : P.val.parts.biUnion id = Finset.univ := P.val.biUnion_parts
  rw [h_eq] at h_biUnion
  rw [biUnion_two_eq_union B1 B2] at h_biUnion
  exact h_biUnion

private lemma erase_eq_of_singleton_union_disjoint (B1 B2 : Finset (Fin 3))
    (a : Fin 3) (h_B1_eq : B1 = {a})
    (h_union : B1 ∪ B2 = Finset.univ) (h_disj : Disjoint B1 B2) :
    B2 = Finset.univ.erase a := by
  ext x
  constructor
  · intro hx
    rw [mem_erase]
    constructor
    · intro h_x_eq_a
      have h_x_in_B1 : x ∈ B1 := by rw [h_B1_eq, mem_singleton]; exact h_x_eq_a
      have h_not_disj : ¬ Disjoint B1 B2 := by
        rw [Finset.not_disjoint_iff]
        exact ⟨x, h_x_in_B1, hx⟩
      exact absurd h_disj h_not_disj
    · have h_B2_sub : B2 ⊆ B1 ∪ B2 := subset_union_right
      have h_mem : x ∈ B1 ∪ B2 := h_B2_sub hx
      rw [h_union] at h_mem
      exact h_mem
  · intro hx
    rw [mem_erase] at hx
    obtain ⟨h_ne_a, h_mem_univ⟩ := hx
    have h_x_not_in_B1 : x ∉ B1 := by
      rw [h_B1_eq, mem_singleton]
      exact h_ne_a
    have h_x_in_union : x ∈ B1 ∪ B2 := h_union ▸ h_mem_univ
    rw [mem_union] at h_x_in_union
    rcases h_x_in_union with h_in_B1 | h_in_B2
    · exact absurd h_in_B1 h_x_not_in_B1
    · exact h_in_B2

private lemma erase_eq_of_singleton_union_disjoint' (B1 B2 : Finset (Fin 3))
    (a : Fin 3) (h_B2_eq : B2 = {a})
    (h_union : B1 ∪ B2 = Finset.univ) (h_disj : Disjoint B1 B2) :
    B1 = Finset.univ.erase a := by
  ext x
  constructor
  · intro hx
    rw [mem_erase]
    constructor
    · intro h_x_eq_a
      have h_x_in_B2 : x ∈ B2 := by rw [h_B2_eq, mem_singleton]; exact h_x_eq_a
      have h_not_disj : ¬ Disjoint B1 B2 := by
        rw [Finset.not_disjoint_iff]
        exact ⟨x, hx, h_x_in_B2⟩
      exact absurd h_disj h_not_disj
    · have h_B1_sub : B1 ⊆ B1 ∪ B2 := subset_union_left
      have h_mem : x ∈ B1 ∪ B2 := h_B1_sub hx
      rw [h_union] at h_mem
      exact h_mem
  · intro hx
    rw [mem_erase] at hx
    obtain ⟨h_ne_a, h_mem_univ⟩ := hx
    have h_x_not_in_B2 : x ∉ B2 := by
      rw [h_B2_eq, mem_singleton]
      exact h_ne_a
    have h_x_in_union : x ∈ B1 ∪ B2 := h_union ▸ h_mem_univ
    rw [mem_union] at h_x_in_union
    rcases h_x_in_union with h_in_B1 | h_in_B2
    · exact h_in_B1
    · exact absurd h_in_B2 h_x_not_in_B2

private lemma exists_block_card_one_of_card_two_three (P : NoncrossingPartition 3)
    (h_card : P.val.parts.card = 2) :
    ∃ B ∈ P.val.parts, B.card = 1 := by
  have h_sum : ∑ B ∈ P.val.parts, B.card = 3 := sum_card_parts_three P
  obtain ⟨B1, B2, h_ne, h_eq_parts⟩ := Finset.card_eq_two.mp h_card
  have h_B1_mem : B1 ∈ P.val.parts := by rw [h_eq_parts]; simp
  have h_B2_mem : B2 ∈ P.val.parts := by rw [h_eq_parts]; simp
  have h_one_le_B1 : 1 ≤ B1.card := one_le_card_of_mem_parts_three h_B1_mem
  have h_one_le_B2 : 1 ≤ B2.card := one_le_card_of_mem_parts_three h_B2_mem
  have h_notMem : B1 ∉ ({B2} : Finset (Finset (Fin 3))) := by
    rw [mem_singleton]
    exact h_ne
  have h_sum_pair : B1.card + B2.card = 3 := by
    calc B1.card + B2.card
        = B1.card + ∑ B ∈ ({B2} : Finset _), B.card := by rw [sum_singleton]
      _ = ∑ B ∈ insert B1 {B2}, B.card := (sum_insert h_notMem).symm
      _ = ∑ B ∈ P.val.parts, B.card := by rw [h_eq_parts]
      _ = 3 := h_sum
  by_cases h_B1_one : B1.card = 1
  · exact ⟨B1, h_B1_mem, h_B1_one⟩
  · have h_B2_one : B2.card = 1 := by omega
    exact ⟨B2, h_B2_mem, h_B2_one⟩

private lemma parts_eq_twoBlock_imp_eq_twoBlock (P : NoncrossingPartition 3)
    (a : Fin 3) (h_parts : P.val.parts = { {a}, Finset.univ.erase a }) :
    P = twoBlockPartition a := by
  have h_val : P.val = (twoBlockPartition a).val := by
    apply Finpartition.ext
    rw [h_parts, twoBlockPartition_parts]
  exact ext h_val

private lemma twoBlockPartition_injective :
    Function.Injective (twoBlockPartition : Fin 3 → NoncrossingPartition 3) := by
  intro a b h_eq
  have h_val_eq : (twoBlockPartition a).val = (twoBlockPartition b).val := by
    rw [h_eq]
  have h_parts_eq : ({ {a}, Finset.univ.erase a } : Finset (Finset (Fin 3))) =
      { {b}, Finset.univ.erase b } := by
    calc { {a}, Finset.univ.erase a } = (twoBlockPartition a).val.parts := by
          rw [twoBlockPartition_parts]
      _ = (twoBlockPartition b).val.parts := by rw [h_val_eq]
      _ = { {b}, Finset.univ.erase b } := by rw [twoBlockPartition_parts]
  have h_mem_a : ({a} : Finset (Fin 3)) ∈
      ({ {a}, Finset.univ.erase a } : Finset (Finset (Fin 3))) := by simp
  have h_mem_a_in_b : ({a} : Finset (Fin 3)) ∈
      ({ {b}, Finset.univ.erase b } : Finset (Finset (Fin 3))) := by
    rw [← h_parts_eq]
    exact h_mem_a
  rw [mem_insert, mem_singleton] at h_mem_a_in_b
  rcases h_mem_a_in_b with h_eq_singleton | h_eq_erase
  · have h_a_mem_b : a ∈ ({b} : Finset (Fin 3)) := by
      rw [← h_eq_singleton]
      exact mem_singleton_self a
    rw [mem_singleton] at h_a_mem_b
    exact h_a_mem_b
  · exfalso
    have h_card_left : ({a} : Finset (Fin 3)).card = 1 := by simp
    have h_card_right : (Finset.univ.erase b).card = 2 := card_erase_fin_three b
    have h_card_eq : ({a} : Finset (Fin 3)).card = (Finset.univ.erase b).card := by
      rw [h_eq_erase]
    omega

private lemma twoBlockPartition_surjective_on_two_blocks (P : NoncrossingPartition 3)
    (h_card : P.val.parts.card = 2) : ∃ a, P = twoBlockPartition a := by
  have h_exists := exists_block_card_one_of_card_two_three P h_card
  obtain ⟨B, hB_mem, hB_card_one⟩ := h_exists
  obtain ⟨a, hBa⟩ := card_eq_one.mp hB_card_one
  have h_B_eq_singleton : B = {a} := hBa
  obtain ⟨B1, B2, h_ne, h_eq_parts⟩ := Finset.card_eq_two.mp h_card
  have h_B1_mem : B1 ∈ P.val.parts := by rw [h_eq_parts]; simp
  have h_B2_mem : B2 ∈ P.val.parts := by rw [h_eq_parts]; simp
  have h_disj : Disjoint B1 B2 := P.val.disjoint h_B1_mem h_B2_mem h_ne
  have h_union : B1 ∪ B2 = Finset.univ :=
    union_two_blocks_eq_univ P B1 B2 h_eq_parts
  have h_B_eq : B = B1 ∨ B = B2 := by
    rw [h_eq_parts] at hB_mem
    simp only [mem_insert, mem_singleton] at hB_mem
    rcases hB_mem with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h_B_eq with h_eq_B1 | h_eq_B2
  · have h_B1_singleton : B1 = {a} := by rw [← h_eq_B1]; exact h_B_eq_singleton
    have h_B2_erase : B2 = Finset.univ.erase a :=
      erase_eq_of_singleton_union_disjoint B1 B2 a h_B1_singleton h_union h_disj
    have h_parts_eq : P.val.parts = { {a}, Finset.univ.erase a } := by
      calc P.val.parts = insert B1 {B2} := h_eq_parts
        _ = insert {a} {Finset.univ.erase a} := by rw [h_B1_singleton, h_B2_erase]
        _ = { {a}, Finset.univ.erase a } := rfl
    exact ⟨a, parts_eq_twoBlock_imp_eq_twoBlock P a h_parts_eq⟩
  · have h_B2_singleton : B2 = {a} := by rw [← h_eq_B2]; exact h_B_eq_singleton
    have h_B1_erase : B1 = Finset.univ.erase a :=
      erase_eq_of_singleton_union_disjoint' B1 B2 a h_B2_singleton h_union h_disj
    have h_parts_eq : P.val.parts = { {a}, Finset.univ.erase a } := by
      calc P.val.parts = insert B1 {B2} := h_eq_parts
        _ = insert (Finset.univ.erase a) {{a}} := by rw [h_B1_erase, h_B2_singleton]
        _ = { {a}, Finset.univ.erase a } := by
            ext p
            simp [mem_insert, mem_singleton]
            tauto
    exact ⟨a, parts_eq_twoBlock_imp_eq_twoBlock P a h_parts_eq⟩

/-- **Noncrossing partitions of three points have one, two or three blocks.** Every noncrossing
partition of $\{0, 1, 2\}$ has one, two, or three blocks. -/
theorem three_card_one_two_three (P : NoncrossingPartition 3) :
    P.val.parts.card = 1 ∨ P.val.parts.card = 2 ∨ P.val.parts.card = 3 := by
  have h_le : P.val.parts.card ≤ 3 := by
    have h := Finpartition.card_parts_le_card (P := P.val)
    have h_univ : (Finset.univ : Finset (Fin 3)).card = 3 := card_univ_fin_three
    omega
  have hs : (Finset.univ : Finset (Fin 3)).Nonempty := ⟨⟨0, by decide⟩, mem_univ _⟩
  have h_ge : 1 ≤ P.val.parts.card :=
    Finpartition.one_le_card_parts_of_nonempty P.val hs
  omega

/-- **A noncrossing partition of three points with one block is indiscrete.** If a noncrossing
partition $P$ of $\{0, 1, 2\}$ has exactly one block, then $P$ is the indiscrete noncrossing
partition of $\{0, 1, 2\}$. -/
theorem eq_indiscrete_of_card_one_three (P : NoncrossingPartition 3)
    (h_card : P.val.parts.card = 1) : P = indiscrete 3 := by
  rw [eq_indiscrete_iff_val_eq_top]
  have hs : (Finset.univ : Finset (Fin 3)).Nonempty := ⟨⟨0, by decide⟩, mem_univ _⟩
  rw [Finpartition.eq_top_iff_card_parts_eq_one P.val hs]
  exact h_card

/-- **A noncrossing partition of three points with three blocks is discrete.** If a noncrossing
partition $P$ of $\{0, 1, 2\}$ has exactly three blocks, then $P$ is the discrete noncrossing
partition of $\{0, 1, 2\}$. -/
theorem eq_discrete_of_card_three_three (P : NoncrossingPartition 3)
    (h_card : P.val.parts.card = 3) : P = discrete 3 := by
  rw [eq_discrete_iff_val_eq_bot, eq_bot_iff_card_parts_eq_card]
  have h_univ : (Finset.univ : Finset (Fin 3)).card = 3 := card_univ_fin_three
  omega

/-- **Classification of noncrossing partitions of a three-element set.** Every noncrossing
partition $P$ of $\{0, 1, 2\}$ is the discrete noncrossing partition of $\{0, 1, 2\}$, the
indiscrete noncrossing partition of $\{0, 1, 2\}$, or, for some $a \in \{0, 1, 2\}$, the
two-block noncrossing partition whose blocks are $\{a\}$ and $\{0, 1, 2\} \setminus \{a\}$. -/
theorem eq_discrete_or_indiscrete_or_twoBlock_three (P : NoncrossingPartition 3) :
    P = discrete 3 ∨ P = indiscrete 3 ∨ ∃ a : Fin 3, P = twoBlockPartition a := by
  have h_card := three_card_one_two_three P
  rcases h_card with h1 | h2 | h3
  · exact Or.inr (Or.inl (eq_indiscrete_of_card_one_three P h1))
  · have h_exists := twoBlockPartition_surjective_on_two_blocks P h2
    exact Or.inr (Or.inr h_exists)
  · exact Or.inl (eq_discrete_of_card_three_three P h3)

/-- **The discrete and indiscrete partitions of a three-element set differ.** The discrete
noncrossing partition of $\{0, 1, 2\}$ is not equal to the indiscrete noncrossing partition of
$\{0, 1, 2\}$. -/
theorem discrete_three_ne_indiscrete_three :
    discrete 3 ≠ indiscrete 3 := by
  intro h
  have h_discrete : (discrete 3).val.parts.card = 3 := by
    rw [discrete_parts, Finset.card_map]
    simp
  have h_indiscrete : (indiscrete 3).val.parts.card = 1 := by
    rw [indiscrete_parts_pos (by decide)]
    simp
  have h_card : (discrete 3).val.parts.card = (indiscrete 3).val.parts.card := by
    rw [h]
  omega

/-- **The two-block partitions of three points are not indiscrete.** For every
$a \in \{0, 1, 2\}$, the noncrossing partition of $\{0, 1, 2\}$ with blocks $\{a\}$ and
$\{0, 1, 2\} \setminus \{a\}$ is different from the indiscrete noncrossing partition of
$\{0, 1, 2\}$. -/
theorem twoBlockPartition_ne_indiscrete_three (a : Fin 3) :
    twoBlockPartition a ≠ indiscrete 3 := by
  intro h
  have h_indiscrete : (indiscrete 3).val.parts.card = 1 := by
    rw [indiscrete_parts_pos (by decide)]
    simp
  have h_card : (twoBlockPartition a).val.parts.card =
      (indiscrete 3).val.parts.card := by rw [h]
  rw [twoBlockPartition_parts_card, h_indiscrete] at h_card
  exact absurd h_card (by decide)

/-- **Enumerating the two-block noncrossing partitions of three points.** The map sending
$a \in \{0, 1, 2\}$ to the partition of $\{0, 1, 2\}$ with blocks $\{a\}$ and
$\{0, 1, 2\} \setminus \{a\}$ is a bijection from $\{0, 1, 2\}$ onto the set of noncrossing
partitions of $\{0, 1, 2\}$ with exactly two blocks. -/
noncomputable def twoBlockEquiv :
    Fin 3 ≃ { P : NoncrossingPartition 3 // P.val.parts.card = 2 } :=
  Equiv.ofBijective
    (fun a => ⟨twoBlockPartition a, twoBlockPartition_parts_card a⟩)
    ⟨by
      intro a b h_eq
      have h_val : twoBlockPartition a = twoBlockPartition b := by
        have := congrArg Subtype.val h_eq
        exact this
      exact twoBlockPartition_injective h_val,
     by
      intro ⟨P, hP⟩
      obtain ⟨a, ha⟩ := twoBlockPartition_surjective_on_two_blocks P hP
      exact ⟨a, Subtype.ext ha.symm⟩⟩

@[simp]
theorem twoBlockEquiv_apply (a : Fin 3) :
    (twoBlockEquiv a).val = twoBlockPartition a :=
  rfl

@[simp]
theorem twoBlockEquiv_apply_parts_card (a : Fin 3) :
    (twoBlockEquiv a).val.val.parts.card = 2 :=
  twoBlockPartition_parts_card a

/-- **Enumerating the proper noncrossing partitions of three points.** Call a noncrossing
partition of $\{0, 1, 2\}$ proper if it is not the indiscrete one. Adjoin an extra element $\ast$
to $\{0, 1, 2\}$; this is the bijection from $\{\ast, 0, 1, 2\}$ onto the set of proper
noncrossing partitions of $\{0, 1, 2\}$ that sends $\ast$ to the discrete noncrossing partition
and each $a \in \{0, 1, 2\}$ to the noncrossing partition with blocks $\{a\}$ and
$\{0, 1, 2\} \setminus \{a\}$. -/
noncomputable def properThreeEquiv :
    Option (Fin 3) ≃ { P : NoncrossingPartition 3 // P ≠ indiscrete 3 } := by
  classical
  let optEquiv : Option (Fin 3) ≃ Unit ⊕ Fin 3 :=
    { toFun
      | none => Sum.inl ()
      | some a => Sum.inr a
      invFun
      | Sum.inl _ => none
      | Sum.inr a => some a
      left_inv := by
        intro o
        cases o <;> rfl
      right_inv := by
        intro s
        cases s with
        | inl u => cases u; rfl
        | inr _ => rfl }
  let discEquiv : Unit ≃ { P : NoncrossingPartition 3 // P = discrete 3 } :=
    { toFun _ := ⟨discrete 3, rfl⟩
      invFun _ := ()
      left_inv _ := rfl
      right_inv := fun ⟨P, hP⟩ => Subtype.ext hP.symm }
  have h_disj : Disjoint (fun P : NoncrossingPartition 3 => P = discrete 3)
                         (fun P => P.val.parts.card = 2) := by
    rw [Pi.disjoint_iff]
    intro P
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    have h_disc : (discrete 3).val.parts.card = 3 := by
      rw [discrete_parts, Finset.card_map]
      simp
    have : P.val.parts.card = 3 := h1 ▸ h_disc
    omega
  have h_iff : ∀ P : NoncrossingPartition 3,
      (P = discrete 3 ∨ P.val.parts.card = 2) ↔ P ≠ indiscrete 3 := by
    intro P
    constructor
    · rintro (rfl | hcard) h_eq
      · exact discrete_three_ne_indiscrete_three h_eq
      · have h_ind_card : (indiscrete 3).val.parts.card = 1 := by
          rw [indiscrete_parts_pos (by decide)]
          simp
        have : P.val.parts.card = 1 := h_eq ▸ h_ind_card
        omega
    · intro h_ne
      have h_class := eq_discrete_or_indiscrete_or_twoBlock_three P
      rcases h_class with h_disc | h_ind | ⟨a, ha⟩
      · exact Or.inl h_disc
      · exact absurd h_ind h_ne
      · exact Or.inr (ha ▸ twoBlockPartition_parts_card a)
  let sumEquiv := discEquiv.sumCongr twoBlockEquiv
  let orSymm :=
    (subtypeOrEquiv (fun P : NoncrossingPartition 3 => P = discrete 3)
      (fun P => P.val.parts.card = 2) h_disj).symm
  let classEquiv :
      { P : NoncrossingPartition 3 // P = discrete 3 ∨ P.val.parts.card = 2 } ≃
        { P : NoncrossingPartition 3 // P ≠ indiscrete 3 } :=
    Equiv.subtypeEquivProp (funext fun P => propext (h_iff P))
  exact optEquiv.trans (sumEquiv.trans (orSymm.trans classEquiv))

@[simp]
theorem properThreeEquiv_none :
    properThreeEquiv none =
      ⟨discrete 3, discrete_three_ne_indiscrete_three⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem properThreeEquiv_some (a : Fin 3) :
    properThreeEquiv (some a) =
      ⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem properThreeEquiv_symm_discrete :
    properThreeEquiv.symm ⟨discrete 3, discrete_three_ne_indiscrete_three⟩ = none := by
  have h_apply : properThreeEquiv (properThreeEquiv.symm
      ⟨discrete 3, discrete_three_ne_indiscrete_three⟩) =
      ⟨discrete 3, discrete_three_ne_indiscrete_three⟩ := by
    simp [Equiv.apply_symm_apply]
  have h_none : properThreeEquiv none =
      (⟨discrete 3, discrete_three_ne_indiscrete_three⟩ :
        { P : NoncrossingPartition 3 // P ≠ indiscrete 3 }) :=
    properThreeEquiv_none
  have h_eq : properThreeEquiv (properThreeEquiv.symm
      ⟨discrete 3, discrete_three_ne_indiscrete_three⟩) = properThreeEquiv none := by
    rw [h_apply, h_none]
  exact properThreeEquiv.injective h_eq

@[simp]
theorem properThreeEquiv_symm_twoBlock (a : Fin 3) :
    properThreeEquiv.symm
        ⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩ =
      some a := by
  have h_apply : properThreeEquiv (properThreeEquiv.symm
      ⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩) =
      ⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩ := by
    simp [Equiv.apply_symm_apply]
  have h_some : properThreeEquiv (some a) =
      (⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩ :
        { P : NoncrossingPartition 3 // P ≠ indiscrete 3 }) :=
    properThreeEquiv_some a
  have h_eq : properThreeEquiv (properThreeEquiv.symm
      ⟨twoBlockPartition a, twoBlockPartition_ne_indiscrete_three a⟩) =
      properThreeEquiv (some a) := by
    rw [h_apply, h_some]
  exact properThreeEquiv.injective h_eq

/-- **Noncrossing partitions of a three-element set.** There are exactly five noncrossing
partitions of $\{0, 1, 2\}$. -/
@[simp]
theorem card_three : Fintype.card (NoncrossingPartition 3) = 5 := by
  classical
  have h_eq_indiscrete : { P : NoncrossingPartition 3 // P = indiscrete 3 } ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨indiscrete 3, rfl⟩
      left_inv := fun ⟨_, h⟩ => Subtype.ext h.symm
      right_inv := fun _ => rfl }
  have h_eq_proper : { P : NoncrossingPartition 3 // P ≠ indiscrete 3 } ≃ Option (Fin 3) :=
    properThreeEquiv.symm
  have h_sum : NoncrossingPartition 3 ≃ Unit ⊕ Option (Fin 3) :=
    Equiv.trans (Equiv.sumCompl (fun P => P = indiscrete 3)).symm
      (Equiv.sumCongr h_eq_indiscrete h_eq_proper)
  calc Fintype.card (NoncrossingPartition 3)
      = Fintype.card (Unit ⊕ Option (Fin 3)) := Fintype.card_congr h_sum
    _ = 5 := by simp

end NoncrossingPartition
