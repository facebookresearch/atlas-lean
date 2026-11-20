/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm.lean`
and
`P2M/Sol/S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Abel

@[expose] public section

namespace CasimirGL3

variable {A : Type*} [Ring A]

/-- The three Casimir elements attached to a family `E i j` in a ring `A`:
the trace, the quadratic contraction, and the cubic contraction. In the
 motivating example `E i j` are the archimedean derivative operators of
`GL₃`, acting on smooth vectors. -/
public def casimir1 (E : Fin 3 → Fin 3 → A) : A :=
  ∑ i : Fin 3, E i i

/-- See `casimir1`. -/
public def casimir2 (E : Fin 3 → Fin 3 → A) : A :=
  ∑ i : Fin 3, ∑ j : Fin 3, E i j * E j i

/-- See `casimir1`. -/
public def casimir3 (E : Fin 3 → Fin 3 → A) : A :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, E i j * (E j k * E k i)

theorem casimir1_eq_sum (E : Fin 3 → Fin 3 → A) :
    casimir1 E = ∑ i : Fin 3, E i i :=
  rfl

theorem casimir2_eq_sum (E : Fin 3 → Fin 3 → A) :
    casimir2 E = ∑ i : Fin 3, ∑ j : Fin 3, E i j * E j i :=
  rfl

theorem casimir3_eq_sum (E : Fin 3 → Fin 3 → A) :
    casimir3 E = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      E i j * (E j k * E k i) :=
  rfl

/-- The `𝔤𝔩₃` bracket relations for a family `E i j`: the commutator of
`E a b` with `E c d` is `δ b c • E a d - δ d a • E c b`. This is the only
input from the archimedean derivative operators used in the proof. -/
public def IsBracketFamily (E : Fin 3 → Fin 3 → A) : Prop :=
  ∀ a b c d : Fin 3, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

variable {E : Fin 3 → Fin 3 → A}

private theorem bracket_swap (hE : IsBracketFamily E) (a b c d : Fin 3) :
    E a b * E c d = E c d * E a b +
      ((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by
  rw [← hE a b c d]
  abel

private theorem bracket_swap_mul (hE : IsBracketFamily E) (a b c d : Fin 3) (w : A) :
    E a b * (E c d * w) = E c d * (E a b * w) +
      ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * w := by
  rw [← mul_assoc, bracket_swap hE a b c d, add_mul, mul_assoc]

private theorem mul_ite (P : Prop) [Decidable P] (w x : A) :
    (w * if P then x else 0) = if P then w * x else 0 := by
  split_ifs
  · rfl
  · exact mul_zero w

private theorem ite_mul (P : Prop) [Decidable P] (x w : A) :
    ((if P then x else 0) * w) = if P then x * w else 0 := by
  split_ifs
  · rfl
  · exact zero_mul w

private theorem cas2_summand (hE : IsBracketFamily E) (a b i j : Fin 3) :
    E a b * (E i j * E j i) +
          (if j = a then E i b * E j i else 0) +
        (if i = a then E i j * E j b else 0) =
      E i j * (E j i * E a b) +
          (if b = i then E a j * E j i else 0) +
        (if b = j then E i j * E a i else 0) := by
  rw [bracket_swap_mul hE a b i j, bracket_swap hE a b j i]
  simp only [mul_add, mul_sub, sub_mul, mul_ite, ite_mul]
  abel

private theorem cas2_piece₁ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if b = i then E a j * E j i else 0) =
      ∑ j : Fin 3, E a j * E j b := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas2_piece₂ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if j = a then E i b * E j i else 0) =
      ∑ i : Fin 3, E i b * E a i := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas2_piece₃ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if b = j then E i j * E a i else 0) =
      ∑ i : Fin 3, E i b * E a i := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas2_piece₄ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if i = a then E i j * E j b else 0) =
      ∑ j : Fin 3, E a j * E j b := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mul_casimir2 (hE : IsBracketFamily E) (a b : Fin 3) :
    E a b * casimir2 E = casimir2 E * E a b := by
  have hA : E a b * casimir2 E = ∑ i : Fin 3, ∑ j : Fin 3,
      E a b * (E i j * E j i) := by
    simp only [casimir2, Finset.mul_sum]
  have hB : casimir2 E * E a b = ∑ i : Fin 3, ∑ j : Fin 3,
      E i j * (E j i * E a b) := by
    simp only [casimir2, Finset.sum_mul, mul_assoc]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ =>
    Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun j _ =>
      cas2_summand hE a b i j
  simp only [Finset.sum_add_distrib] at hsum
  rw [cas2_piece₂, cas2_piece₄, cas2_piece₁, cas2_piece₃] at hsum
  rw [hA, hB]
  refine add_right_cancel (b := (∑ i : Fin 3, E i b * E a i) +
    ∑ j : Fin 3, E a j * E j b) ?_
  rw [← add_assoc, hsum]
  abel

private theorem cas1_summand (hE : IsBracketFamily E) (a b i : Fin 3) :
    E a b * E i i + (if i = a then E i b else 0) =
      E i i * E a b + (if b = i then E a i else 0) := by
  rw [bracket_swap hE a b i i]
  abel

private theorem mul_casimir1 (hE : IsBracketFamily E) (a b : Fin 3) :
    E a b * casimir1 E = casimir1 E * E a b := by
  have hA : E a b * casimir1 E = ∑ i : Fin 3, E a b * E i i := by
    simp only [casimir1, Finset.mul_sum]
  have hB : casimir1 E * E a b = ∑ i : Fin 3, E i i * E a b := by
    simp only [casimir1, Finset.sum_mul]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ =>
    cas1_summand hE a b i
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hsum
  rw [hA, hB]
  exact add_right_cancel hsum

private theorem cas3_summand (hE : IsBracketFamily E) (a b i j k : Fin 3) :
    E a b * (E i j * (E j k * E k i)) +
          (if j = a then E i b * (E j k * E k i) else 0) +
        (if k = a then E i j * (E j b * E k i) else 0) +
      (if i = a then E i j * (E j k * E k b) else 0) =
      E i j * (E j k * (E k i * E a b)) +
          (if b = i then E a j * (E j k * E k i) else 0) +
        (if b = j then E i j * (E a k * E k i) else 0) +
      (if b = k then E i j * (E j k * E a i) else 0) := by
  rw [bracket_swap_mul hE a b i j, bracket_swap_mul hE a b j k,
    bracket_swap hE a b k i]
  simp only [mul_add, mul_sub, sub_mul, mul_ite, ite_mul]
  abel

private theorem cas3_piece₁ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = i then E a j * (E j k * E k i) else 0)) =
      ∑ j : Fin 3, ∑ k : Fin 3, E a j * (E j k * E k b) := by
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
  · intro i _ hi
    simp only [hi.symm, if_false, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

private theorem cas3_piece₂ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if j = a then E i b * (E j k * E k i) else 0)) =
      ∑ i : Fin 3, ∑ k : Fin 3, E i b * (E a k * E k i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas3_piece₃ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = j then E i j * (E a k * E k i) else 0)) =
      ∑ i : Fin 3, ∑ k : Fin 3, E i b * (E a k * E k i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas3_piece₄ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if k = a then E i j * (E j b * E k i) else 0)) =
      ∑ i : Fin 3, ∑ j : Fin 3, E i j * (E j b * E a i) := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas3_piece₅ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = k then E i j * (E j k * E a i) else 0)) =
      ∑ i : Fin 3, ∑ j : Fin 3, E i j * (E j b * E a i) := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas3_piece₆ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if i = a then E i j * (E j k * E k b) else 0)) =
      ∑ j : Fin 3, ∑ k : Fin 3, E a j * (E j k * E k b) := by
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
  · intro i _ hi
    simp only [hi, if_false, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem mul_casimir3 (hE : IsBracketFamily E) (a b : Fin 3) :
    E a b * casimir3 E = casimir3 E * E a b := by
  have hA : E a b * casimir3 E = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      E a b * (E i j * (E j k * E k i)) := by
    simp only [casimir3, Finset.mul_sum]
  have hB : casimir3 E * E a b = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      E i j * (E j k * (E k i * E a b)) := by
    simp only [casimir3, Finset.sum_mul, mul_assoc]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ =>
    Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun j _ =>
      Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun k _ =>
        cas3_summand hE a b i j k
  simp only [Finset.sum_add_distrib] at hsum
  rw [cas3_piece₂, cas3_piece₄, cas3_piece₆, cas3_piece₁, cas3_piece₃,
    cas3_piece₅] at hsum
  rw [hA, hB]
  refine add_right_cancel
    (b := (∑ i : Fin 3, ∑ k : Fin 3, E i b * (E a k * E k i)) +
      (∑ i : Fin 3, ∑ j : Fin 3, E i j * (E j b * E a i)) +
        ∑ j : Fin 3, ∑ k : Fin 3, E a j * (E j k * E k b)) ?_
  rw [← add_assoc, ← add_assoc, hsum]
  abel

private theorem casimir1_mul_casimir2 (hE : IsBracketFamily E) :
    casimir1 E * casimir2 E = casimir2 E * casimir1 E := by
  simp only [casimir1, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_casimir2 hE a a

private theorem casimir1_mul_casimir3 (hE : IsBracketFamily E) :
    casimir1 E * casimir3 E = casimir3 E * casimir1 E := by
  simp only [casimir1, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_casimir3 hE a a

private theorem casimir2_mul_casimir3 (hE : IsBracketFamily E) :
    casimir2 E * casimir3 E = casimir3 E * casimir2 E := by
  simp only [casimir2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, mul_casimir3 hE j i, ← mul_assoc, mul_casimir3 hE i j, mul_assoc]


/-- The first Casimir commutes with every generator of a bracket family. -/
public theorem casimir1_commute_generator (hE : IsBracketFamily E) (i j : Fin 3) :
    Commute (casimir1 E) (E i j) :=
  (mul_casimir1 hE i j).symm

/-- The second Casimir commutes with every generator of a bracket family. -/
public theorem casimir2_commute_generator (hE : IsBracketFamily E) (i j : Fin 3) :
    Commute (casimir2 E) (E i j) :=
  (mul_casimir2 hE i j).symm

/-- The third Casimir commutes with every generator of a bracket family. -/
public theorem casimir3_commute_generator (hE : IsBracketFamily E) (i j : Fin 3) :
    Commute (casimir3 E) (E i j) :=
  (mul_casimir3 hE i j).symm

/-- The first and second Casimirs of a bracket family commute. -/
public theorem commute_casimir1_casimir2 (hE : IsBracketFamily E) :
    Commute (casimir1 E) (casimir2 E) :=
  casimir1_mul_casimir2 hE

/-- The first and third Casimirs of a bracket family commute. -/
public theorem commute_casimir1_casimir3 (hE : IsBracketFamily E) :
    Commute (casimir1 E) (casimir3 E) :=
  casimir1_mul_casimir3 hE

/-- The second and third Casimirs of a bracket family commute. -/
public theorem commute_casimir2_casimir3 (hE : IsBracketFamily E) :
    Commute (casimir2 E) (casimir3 E) :=
  casimir2_mul_casimir3 hE

/-- The Casimir elements of a `𝔤𝔩₃` bracket family commute with every
generator of the family, and they commute with each other. In the motivating
example the generators are the archimedean derivative operators on smooth
vectors for `GL₃`, and the Casimirs are the operators `casimir1`,
`casimir2`, and `casimir3` built from them. -/
public theorem casimir_comm_and_generator_comm (hE : IsBracketFamily E) :
    (∀ i j : Fin 3,
      casimir1 E * E i j = E i j * casimir1 E ∧
        casimir2 E * E i j = E i j * casimir2 E ∧
          casimir3 E * E i j = E i j * casimir3 E) ∧
      casimir1 E * casimir2 E = casimir2 E * casimir1 E ∧
        casimir1 E * casimir3 E = casimir3 E * casimir1 E ∧
          casimir2 E * casimir3 E = casimir3 E * casimir2 E :=
  ⟨fun i j => ⟨(casimir1_commute_generator hE i j).eq,
      (casimir2_commute_generator hE i j).eq,
      (casimir3_commute_generator hE i j).eq⟩,
    (commute_casimir1_casimir2 hE).eq, (commute_casimir1_casimir3 hE).eq,
    (commute_casimir2_casimir3 hE).eq⟩

end CasimirGL3
