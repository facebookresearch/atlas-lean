/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: extracted default-padded finite products from the tensor-network
definitions, named the shared API, and generalized the distributivity results.
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Finite products with prescribed default values

`piFinsetOn P T d` consists of functions whose value lies in `T i` when `P i` holds
and equals `d` otherwise. The value type need not be finite.

Adapted from `Groundwork.tuples` and its calculus in
`eth/proof/networks/Groundwork/Net/{Defs,Calculus}.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
It is a shared construction used by tensor-network states, edge labels and contraction.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Fintype

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite tuples constrained on `P` and equal to a prescribed default elsewhere. -/
def piFinsetOn (P : ι → Prop) [DecidablePred P] (T : ι → Finset σ) (d : σ) :
    Finset (ι → σ) :=
  piFinset fun i => if P i then T i else {d}

/-- Membership gives the allowed values on the active indices and the default off them. -/
@[simp] theorem mem_piFinsetOn (P : ι → Prop) [DecidablePred P]
    (T : ι → Finset σ) (d : σ) (t : ι → σ) :
    t ∈ piFinsetOn P T d ↔ ∀ i, (P i → t i ∈ T i) ∧ (¬P i → t i = d) := by
  unfold piFinsetOn
  rw [mem_piFinset]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]

/-- Inactive coordinates contribute one choice, so only active coordinates enter the product. -/
theorem card_piFinsetOn (P : ι → Prop) [DecidablePred P]
    (T : ι → Finset σ) (d : σ) :
    (piFinsetOn P T d).card = ∏ i with P i, (T i).card := by
  unfold piFinsetOn
  rw [card_piFinset, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Distribute a product of finite sums over the default-padded tuples of choices. -/
theorem sum_piFinsetOn_prod {R : Type*} [CommSemiring R]
    (P : ι → Prop) [DecidablePred P] (T : ι → Finset σ) (d : σ) (H : ι → σ → R) :
    ∑ t ∈ piFinsetOn P T d, ∏ i with P i, H i (t i) =
      ∏ i with P i, ∑ x ∈ T i, H i x := by
  unfold piFinsetOn
  have h := Finset.prod_univ_sum (fun i => if P i then T i else {d})
    (fun i x => if P i then H i x else (1 : R))
  simp only [Finset.prod_filter]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi <;> simp

/-- Products of factorized functions factor through the tuples of their labels. -/
theorem prod_sum_eq_sum_piFinsetOn_mul {R : Type*} [CommSemiring R]
    (P : ι → Prop) [DecidablePred P] (T : ι → Finset σ) (d : σ)
    (f g : ι → σ → R) :
    ∏ i with P i, ∑ x ∈ T i, f i x * g i x =
      ∑ t ∈ piFinsetOn P T d, (∏ i with P i, f i (t i)) * ∏ i with P i, g i (t i) := by
  rw [← sum_piFinsetOn_prod P T d]
  simp only [Finset.prod_mul_distrib]

/-- Prescribed active coordinates have exactly one completion with the chosen default. -/
theorem existsUnique_piFinsetOn (P : ι → Prop) [DecidablePred P]
    (T : ι → Finset σ) (d : σ) (t : ι → σ) (ht : ∀ i, P i → t i ∈ T i) :
    ∃! b : ι → σ, b ∈ piFinsetOn P T d ∧ ∀ i, P i → b i = t i := by
  refine ⟨fun i => if P i then t i else d, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_piFinsetOn]
    intro i
    constructor
    · intro hi
      simpa [hi] using ht i hi
    · intro hi
      simp [hi]
  · intro i hi
    simp [hi]
  · intro b hb
    funext i
    by_cases hi : P i
    · simpa [hi] using hb.2 i hi
    · simpa [hi] using ((mem_piFinsetOn P T d b).mp hb.1 i).2 hi

end Fintype
