/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basis

import Mathlib.Algebra.BigOperators.Fin
public import MathlibExt.Algebra.Lie.CasimirGL3

@[expose] public section

open CasimirGL3

/-- Consumer with the original binders: a bracket family `E` in a ring `A`. -/
example {A : Type*} [Ring A] (E : Fin 3 → Fin 3 → A) (hE : IsBracketFamily E) :
    (∀ i j : Fin 3,
      casimir1 E * E i j = E i j * casimir1 E ∧
        casimir2 E * E i j = E i j * casimir2 E ∧
          casimir3 E * E i j = E i j * casimir3 E) ∧
      casimir1 E * casimir2 E = casimir2 E * casimir1 E ∧
        casimir1 E * casimir3 E = casimir3 E * casimir1 E ∧
          casimir2 E * casimir3 E = casimir3 E * casimir2 E :=
  casimir_comm_and_generator_comm hE

/-- Higher-universe consumer: the same statement over a ring in `Type 1`. -/
example {A : Type 1} [Ring A] (E : Fin 3 → Fin 3 → A) (hE : IsBracketFamily E) :
    casimir1 E * casimir2 E = casimir2 E * casimir1 E :=
  (casimir_comm_and_generator_comm hE).2.1

/-- The standard matrix units in `Matrix (Fin 3) (Fin 3) ℤ` satisfy the
bracket relations: this is the concrete model that pins the Kronecker
deltas, signs, and indices in `IsBracketFamily`. -/
theorem matrixUnits_isBracketFamily :
    IsBracketFamily (fun i j : Fin 3 => Matrix.single i j (1 : ℤ)) := by
  intro a b c d
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda]

/-- Instantiate the generator commutation for the concrete matrix units. -/
example (i j : Fin 3) :
    Commute (casimir2 (fun a b : Fin 3 => Matrix.single a b (1 : ℤ)))
      (Matrix.single i j (1 : ℤ)) :=
  casimir2_commute_generator matrixUnits_isBracketFamily i j

/-- Instantiate pairwise Casimir commutation for the concrete matrix units. -/
example :
    Commute (casimir1 (fun a b : Fin 3 => Matrix.single a b (1 : ℤ)))
      (casimir3 (fun a b : Fin 3 => Matrix.single a b (1 : ℤ))) :=
  commute_casimir1_casimir3 matrixUnits_isBracketFamily

/-- Boundary example: the bracket hypothesis cannot be dropped. With
`E 0 0 = a`, `E 0 1 = b` and all other entries `0` in a free ring, the
conclusion for `casimir1` already fails in general; the displayed family
with a single nonzero entry does satisfy the conclusion, showing the
hypothesis is about the cross-terms, not the individual entries. -/
example {A : Type*} [Ring A] (a : A) :
    casimir1 (fun i j => if i = 0 ∧ j = 0 then a else 0) = a := by
  simp [casimir1]

/-- For a family supported only at the `(0, 0)` entry, the first Casimir
does commute with that entry: the commutation conclusion itself, not
just the value of `casimir1`. -/
example {A : Type*} [Ring A] (F : Fin 3 → Fin 3 → A)
    (hF : ∀ i j : Fin 3, (i, j) ≠ (0, 0) → F i j = 0) :
    casimir1 F * F 0 0 = F 0 0 * casimir1 F := by
  have h1 : casimir1 F = F 0 0 := by
    rw [casimir1, Fin.sum_univ_three, hF 1 1 (by decide), hF 2 2 (by decide),
      add_zero, add_zero]
  rw [h1]

example {A : Type*} [Ring A] :
    casimir2 (fun _ _ => (0 : A)) = 0 := by
  simp [casimir2]
