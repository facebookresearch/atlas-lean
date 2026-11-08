/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Diophantine

open MetaMathlibExt

-- The whole space and the empty set are Diophantine.
example : IsDiophantine (RingHom.id ℤ) (Set.univ : Set (Fin 2 → ℤ)) :=
  isDiophantine_univ _ 2

example : IsDiophantine (Int.castRingHom ℚ) (∅ : Set (Fin 1 → ℚ)) :=
  isDiophantine_empty _ 1

-- `{0} ⊆ ℤ` is the zero set of the coordinate `x₁`.
example : IsDiophantineSet (RingHom.id ℤ) ({0} : Set ℤ) :=
  ⟨0, {MvPolynomial.X (Sum.inl 0)}, fun x => by simp⟩

-- Unfolding a set-level statement to the `Fin 1` form.
example (S : Set ℚ) (h : IsDiophantine (Int.castRingHom ℚ) {x : Fin 1 → ℚ | x 0 ∈ S}) :
    IsDiophantineSet (Int.castRingHom ℚ) S :=
  (isDiophantineSet_iff _ _).2 h
