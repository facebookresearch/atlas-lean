/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.FKS

@[expose] public section

/-- Boundary check: the existence statement instantiates with
one key, one function, one bucket. -/
example : ∃ hh : Fin 1, (∑ b : Fin (Fintype.card (Fin 1) ^ 2),
      ((Finset.univ.filter (fun y : Fin 1 =>
        (0 : Fin (Fintype.card (Fin 1) ^ 2)) = b)).card : ℝ) *
        ((Finset.univ.filter (fun y : Fin 1 =>
          (0 : Fin (Fintype.card (Fin 1) ^ 2)) = b)).card - 1)) <
    (Fintype.card (Fin 1) : ℝ) :=
  fks_exists_good_hash (K := Fin 1) (H := Fin 1)
    (fun _ _ => (0 : Fin (Fintype.card (Fin 1) ^ 2)))
    (fun x y hxy => (hxy (Subsingleton.elim x y)).elim)
    (by decide) (by decide)
