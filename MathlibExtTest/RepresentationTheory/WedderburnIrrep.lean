/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.WedderburnIrrep
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace MathlibExtTest.RepresentationTheory.WedderburnIrrep

set_option linter.style.haveILetI false

open CharacterTheory

/-- For `S₃` over `ℂ`, the Wedderburn–Artin decomposition has blocks whose
representations are all irreducible: the block representations supplied
by `CharacterTheory.wedderburnIrrep` satisfy the theorem. -/
example : ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ (Equiv.Perm (Fin 3)) ≃ₐ[ℂ]
      Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ),
    ∀ i, (wedderburnIrrep ℂ (Equiv.Perm (Fin 3)) e i).IsIrreducible := by
  haveI : NeZero ((Nat.card (Equiv.Perm (Fin 3)) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr (by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      exact Nat.factorial_ne_zero 3)⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ
      (MonoidAlgebra ℂ (Equiv.Perm (Fin 3)))
  exact ⟨n, d, hd, e, fun i => by
    haveI : NeZero (d i) := hd i
    exact wedderburnIrrep_isIrreducible ℂ (Equiv.Perm (Fin 3)) e i⟩

/-- The `i`-th Wedderburn block representation of `S₃` lives on a space
of dimension `d i`. -/
example (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    Module.finrank ℂ (Fin (d i) → ℂ) = d i := by
  simp

#print axioms CharacterTheory.wedderburnIrrep_isIrreducible

end MathlibExtTest.RepresentationTheory.WedderburnIrrep
