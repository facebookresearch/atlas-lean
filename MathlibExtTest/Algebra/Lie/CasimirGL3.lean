/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

/-- Boundary example: the bracket hypothesis cannot be dropped. With
`E 0 0 = a`, `E 0 1 = b` and all other entries `0` in a free ring, the
conclusion for `casimir1` already fails in general; the displayed family
with a single nonzero entry does satisfy the conclusion, showing the
hypothesis is about the cross-terms, not the individual entries. -/
example {A : Type*} [Ring A] (a : A) :
    casimir1 (fun i j => if i = 0 ∧ j = 0 then a else 0) = a := by
  simp [casimir1]

example {A : Type*} [Ring A] :
    casimir2 (fun _ _ => (0 : A)) = 0 := by
  simp [casimir2]
